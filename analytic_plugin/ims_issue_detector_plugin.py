import re
from dataclasses import dataclass, asdict
from typing import List, Dict, Optional, Tuple

"""
IMS COBOL Static Checker
---------------------------------
- Input: Full COBOL source text (stdin or function call)
- Output: List[dict] of findings -> {rule_id, severity, message, line}

What this heuristic parser checks (current rule set)
---------------------------------------------------
IMS call surface & linkage
  * IMS-001  Invalid or unresolved DL/I function code (first USING arg not a known code/WS const).
  * IMS-002  Missing/invalid PCB as the 2nd USING argument (CHKP/XRST exempt).
  * IMS-010  LINKAGE PCBs must appear in PROCEDURE DIVISION USING; every LINKAGE PCB must be in USING.
  * IMS-011  Function-code variable used in CALL must be declared in WORKING-STORAGE.
  * IMS-012  Any PCB referenced in a CALL must be present in PROCEDURE DIVISION USING.

Status handling (harvested FILE STATUS vars and PCB status fields only)
  * IMS-020  No nearby status check after a DL/I call (skips CHKP/XRST; bounded forward scan).
  * IMS-021  Sequential retrieval present (GN/GHN/GNP) but no visible 'GB' handling anywhere (program-wide).
  * IMS-022  For each GN/GHN call, no visible local handling of 'GB' near the call (IF/EVALUATE blocks scanned, incl. nested).
  * IMS-024  A conditional that tests a harvested status var lacks a default path (ELSE / WHEN OTHER).
  * IMS-INIT-STATUS  Loop tests status in PERFORM … UNTIL before it can be valid (with priming/first-stmt heuristics).
  * IMS-170  No nearby status/audit behavior after certain IMS usage (see GSAM audit heuristic below).

GSAM handling
  * IMS-130  COBOL WRITE on a GSAM-assigned file/record — must use DL/I ISRT via GSAM PCB.
  * IMS-131  COBOL READ/REWRITE/DELETE on a GSAM-assigned file/record — must use DL/I calls.
  * IMS-132  Explicit OPEN/CLOSE on GSAM dataset — unnecessary; IMS manages GSAM open/close.

Checkpointing & IOPCB
  * IMS-140  CHKP/XRST must use the IOPCB; flagged if a DB PCB is used instead.
  * IMS-141  IOPCB required in LINKAGE and PROCEDURE DIVISION USING when CHKP/XRST present.
  * IMS-142  Expect symbolic CHKP when XRST/restart token is present; warns on basic CHKP form (heuristic).
  * IMS-143  CHKP/XRST passed a non-IOPCB while an IOPCB symbol exists — should use IOPCB.

SSA correctness & DL/I arg sanity
  * IMS-160  SSA malformed — e.g., operator field defined as PIC X(3) instead of PIC X(2),
             or operator/value outside the parentheses.
  * IMS-161  SSA misuse — MOVE from IO-area fields into SSA targets (heuristic).
  * IMS-162  DL/I arg-order sanity for GU/GN/GHU/GHN/ISRT: expected func, PCB, IO-AREA, then [SSA...].
             Flags when arg3 looks like SSA and arg4 looks like a buffer (heuristic).
  * IMS-163  ISRT without any SSA while SSAs appear to be present/declared elsewhere (Warning).
  
  GSAM audit discipline
  * IMS-170  If GSAM is present in FILE-CONTROL and the program issues GN/GHN, expect a nearby ISRT in the same
             block or in the immediately PERFORMed paragraph (one-level follow).

COBOL file I/O hygiene
  * COB-110  WRITE target must be a FILE SECTION 01 record (from an FD).
  * COB-111  WRITE requires the owning file to be OPENed in OUTPUT/EXTEND/I-O.
             (Suppressed for GSAM-bound FDs; IMS-132 covers explicit OPEN/CLOSE.)
  * COB-120  Any file that’s OPEN/READ/WRITE/REWRITE/DELETE/START/CLOSE must have a `FILE STATUS IS <var>` binding.
             (Suppressed for GSAM-bound FDs; IMS-130/131/132 report the GSAM misuse.)

Parser/heuristic notes
----------------------
- DL/I calls via CALL 'CBLTDLI' / 'DFSLI000' USING … with multi-line accumulation and stopper verbs.
- Recognizes literal function codes or WS constants (e.g., DLI-GHN VALUE 'GHN ').
- Harvests LINKAGE PCBs and PROCEDURE USING (incl. ENTRY 'DLITCBL'), FILE STATUS vars, WS function-code constants,
  FD→01 maps, OPEN modes, SELECT/ASSIGN (for GSAM).
- Status proximity checks allow one paragraph label skip and scan IF/EVALUATE windows for references.
- GN/GHN local 'GB' handling scans whole IF/EVALUATE blocks (and nested) before stopping at natural boundaries.
- GNP parent-positioning: short look-back for GU/GN/GHU/GHN on same PCB.
- COBOL I/O mapping: WRITE target validated against harvested FILE SECTION 01s; owner FD open-mode checked.
- GSAM misuse detection based on SELECT…ASSIGN to GSAM and record→FD reverse map.
- CHKP/XRST heuristics: require IOPCB presence/usage; symbolic CHKP expected if XRST/token context is detected.
- SSA heuristics: operator PIC length 2; literal forms with parentheses; separate sanity check for arg order (IMS-162).
- REPL heuristics: expect an uppercase edit routine near REPL (style/safety).
- GSAM audit: after GN/GHN, look inline and (optionally) in one immediately PERFORMed paragraph for ISRT.
"""


IMS_FUNCS = {'GU', 'GN', 'GNP', 'GHU', 'GHN', 'ISRT', 'REPL', 'DLET', 'CHKP', 'XRST'}
HOLD_FUNCS = {'GHU', 'GHN'}
RETR_FUNCS = {'GU', 'GN', 'GNP', 'GHU', 'GHN'}
UPDATE_FUNCS = {'REPL', 'DLET'}


@dataclass
class Finding:
    rule_id: str
    severity: str
    message: str
    line: Optional[int] = None

    def to_dict(self):
        return asdict(self)


class IMSCobolChecker:
    def __init__(self, text: str):
        self.text = text
        self.lines = [ln.rstrip('\n') for ln in text.splitlines()]
        self.findings: List[Finding] = []

        # Symbols discovered
        self.linkage_pcbs: List[str] = []  # variable names in LINKAGE SECTION (01-level with 'PCB')
        self.status_field_names: List[str] = []  # names like STATUS-CODE / PCB-STATUS
        self.status_decl_line: Dict[str, int] = {}
        self.status_pic_ok: Dict[str, bool] = {}
        self.ws_func_consts: Dict[str, str] = {}  # WS constants mapping name -> function e.g., DLI-GHN -> GHN
        self.using_params: List[str] = []  # PROCEDURE DIVISION USING names
        self.ws_names: List[str] = []  # names declared in WS
        self.linkage_names: List[str] = []  # any names in LINKAGE

        # DL/I calls collected: (line_idx, func, pcb_name, arg_names)
        self.calls: List[Tuple[int, str, str, List[str]]] = []
        self.call_raw_tokens: List[str] = []

    # --------------- helpers ---------------
    def _add(self, rule_id: str, severity: str, message: str, line: Optional[int] = None):
        self.findings.append(Finding(rule_id, severity, message, None if line is None else line + 1))

    def _find_cbltdli_calls(self):
        return self.calls  # already parsed by _parse_calls()

    def _is_iopcb_name(self, name: str) -> bool:
        """Heuristic name check for IOPCB."""
        return bool(re.search(r'\bIO[-]?PCB\b', name, re.IGNORECASE))

    # --------------- parse ---------------
    def parse(self):
        self._parse_working_storage()
        self._parse_linkage()
        self._harvest_status_names()
        self._parse_procedure_using()
        self._parse_calls()

    def _parse_working_storage(self):
        in_ws = False
        for i, ln in enumerate(self.lines):
            u = ln.upper()
            if u.strip().startswith('WORKING-STORAGE SECTION'):
                in_ws = True
                continue
            if in_ws and (u.strip().startswith('LINKAGE SECTION') or u.strip().startswith('PROCEDURE DIVISION')):
                in_ws = False
            if not in_ws:
                continue
            # collect declared names
            m01 = re.search(r'^\s*0?1\s+([A-Z0-9-]+)\b', u)
            m05 = re.search(r'^\s*0?5\s+([A-Z0-9-]+)\b', u)
            if m01:
                self.ws_names.append(m01.group(1))
            if m05:
                self.ws_names.append(m05.group(1))
            # WS function constants: VALUE 'GU' / 'GHN ' etc.
            mfunc = re.search(r"\b([A-Z0-9-]+)\b\s+PIC\b.*?VALUE\s+'\s*([A-Z ]{2,4})\s*'", u)
            if mfunc:
                name = mfunc.group(1)
                val = mfunc.group(2).replace(' ', '')  # normalize: 'GHN ' -> 'GHN'
                if val in IMS_FUNCS:
                    self.ws_func_consts[name] = val

    def _parse_linkage(self):
        in_linkage = False
        current_01: Optional[str] = None
        for i, ln in enumerate(self.lines):
            u = ln.upper()
            if u.strip().startswith('LINKAGE SECTION'):
                in_linkage = True
                continue
            if in_linkage and u.strip().startswith('PROCEDURE DIVISION'):
                in_linkage = False
            if not in_linkage:
                continue
            m01 = re.search(r'^\s*0?1\s+([A-Z0-9-]+)\b', u)
            if m01:
                current_01 = m01.group(1)
                self.linkage_names.append(current_01)
                if 'PCB' in current_01:
                    self.linkage_pcbs.append(current_01)
                continue
            # status field names under a PCB
            if current_01 and 'PCB' in current_01:
                if re.search(r'\b(PCB-STATUS|STATUS\s*-\s*CODE)\b', u):
                    # capture original-case name for later search
                    m2 = re.search(r'([A-Za-z0-9-]*STATUS[\s-]*CODE|PCB-STATUS)', ln)
                    if m2:
                        name = m2.group(1).strip()
                        if name not in self.status_field_names:
                            self.status_field_names.append(name)
                # quick status pic check (best-effort; may be on same line)
                if re.search(r'STATUS\s*-\s*CODE\b.*PIC\s+X\(\s*2\s*\)', u) or re.search(r'PCB-STATUS\b.*PIC\s+X\(\s*2\s*\)', u):
                    pass

            # also collect any lower levels for linkage_names
            m05 = re.search(r'^\s*0?5\s+([A-Z0-9-]+)\b', u)
            if m05:
                self.linkage_names.append(m05.group(1))

    def _parse_procedure_using(self):
        # PROCEDURE DIVISION USING ...
        for i, ln in enumerate(self.lines):
            if 'PROCEDURE DIVISION' in ln.upper():
                block = ln
                j = i + 1
                while '.' not in block and j < len(self.lines):
                    block += ' ' + self.lines[j]
                    j += 1
                uu = block.upper()
                if 'USING' in uu:
                    after = uu.split('USING', 1)[1]
                    names = [n.strip().rstrip('.') for n in re.split(r'[, \t]+', after) if re.match(r'[A-Za-z0-9-]+\.?,?', n)]
                    self.using_params = [n.replace('.', '').upper() for n in names if re.match(r'^[A-Za-z0-9-]+$', n)]
                break  # done scanning for PROCEDURE DIVISION

        # ENTRY 'DLITCBL' USING ... (IMS programs)
        for i, ln in enumerate(self.lines):
            u = ln.upper()
            if "ENTRY 'DLITCBL'" in u and 'USING' in u:
                block = ln
                j = i + 1
                while '.' not in block and j < len(self.lines):
                    block += ' ' + self.lines[j]
                    j += 1
                uu = block.upper()
                after = uu.split('USING', 1)[1]
                names = [n.strip().rstrip('.') for n in re.split(r'[, \t]+', after) if re.match(r'[A-Za-z0-9-]+\.?,?', n)]
                entry_params = [n.replace('.', '').upper() for n in names if re.match(r'^[A-Za-z0-9-]+$', n)]
                # Merge with any PROCEDURE DIVISION USING params
                self.using_params = sorted(set(self.using_params) | set(entry_params))
                break

    def _parse_calls(self):
        call_re = re.compile(r"CALL\s+'(CBLTDLI|DFSLI000)'\s+USING\s+(.+)$", re.IGNORECASE)
        stopper = re.compile(r'^\s*(IF|ELSE|WHEN|END-IF|EVALUATE|END-EVALUATE|PERFORM|END-PERFORM|MOVE|DISPLAY|CALL|EXIT|GOBACK|STOP\s+RUN)\b', re.IGNORECASE)

        i = 0
        while i < len(self.lines):
            ln = self.lines[i]
            m = call_re.search(ln)
            if not m:
                i += 1
                continue

            # Start with the tail after USING on the same line
            using = ln.split('USING', 1)[1].strip()
            j = i + 1

            # Accumulate continuation lines until either:
            #  - we see a terminating period in the accumulated text, OR
            #  - the next line starts with a new COBOL sentence/verb (stopper)
            while '.' not in using and j < len(self.lines):
                nxt = self.lines[j]
                if stopper.search(nxt):
                    break
                using += ' ' + nxt.strip()
                j += 1

            # Strip COBOL passing phrases and ADDRESS OF
            using = re.sub(r'\bBY\s+(?:REFERENCE|CONTENT|VALUE)\b', '', using, flags=re.IGNORECASE)
            using = re.sub(r'\bADDRESS\s+OF\s+', '', using, flags=re.IGNORECASE)

            # Normalize and split by commas OR whitespace; drop empties; strip trailing punctuation
            # while keeping quoted strings intact
            using = using.strip().rstrip('.')
            raw_args = [tok.strip().rstrip('.,') for tok in re.findall(r"'[^']*'|\"[^\"]*\"|[^,\s]+", using)]

            func_token_raw = raw_args[0] if raw_args else ''
            func_uc = func_token_raw.upper()

            # Strip optional quotes around the first argument
            func_uc_stripped = func_uc.strip('\'"')

            # Use stripped version to resolve function
            if func_uc_stripped in IMS_FUNCS:
                func = func_uc_stripped
            else:
                func = self.ws_func_consts.get(func_uc, 'UNKNOWN')  # keep existing WS-const mapping

            pcb = raw_args[1].upper() if len(raw_args) > 1 else ''
            arg_names = [a.upper() for a in raw_args]

            self.calls.append((i, func, pcb, arg_names))
            self.call_raw_tokens.append(func_token_raw)
            i = j if j > i else i + 1

    def _norm(self, s: str) -> str:
        """Uppercase and remove all non-alphanumerics (hyphens/spaces) for robust matching."""

        return re.sub(r'[^A-Z0-9]', '', s.upper())

    def _harvest_status_names(self):
        """
        Robustly collect *real* status fields to avoid false positives.
        Collects only:
          A) File status vars from 'FILE STATUS IS <var>' in FILE-CONTROL
          B) PCB status fields (PIC XX) within LINKAGE 01-level PCBs that are
             listed in PROCEDURE DIVISION USING

        Populates:
          - self.status_field_names : list[str]  (names as in source)
          - self.status_decl_line   : dict[name-> int|None]
          - self.status_pic_ok      : dict[name-> bool|None]  (True if PIC XX found,
                                                               False if non-XX PIC found,
                                                               None if no PIC seen)
        """

        # Outputs (match legacy contract)
        self.status_field_names = []
        self.status_decl_line = {}
        self.status_pic_ok = {}

        # ----------------- helpers -----------------
        def add_name(name, decl_line=None, pic_ok=None):
            # Keep original case/dashes as seen
            if name not in self.status_field_names:
                self.status_field_names.append(name)
            if name not in self.status_decl_line:
                self.status_decl_line[name] = decl_line
            if name not in self.status_pic_ok:
                self.status_pic_ok[name] = pic_ok

        def norm(s):  # uppercase for matching
            return (s or '').upper()

        def is_pic_xx(text):
            return bool(re.search(r'\bPIC\s+(?:X\s*\(\s*0*2\s*\)|XX)(?=\s*[)\.\,\;\:]|\s|$)', text, re.IGNORECASE))

        lvl_name_re = re.compile(r'^\s*0?([0-4]?[1-9])\s+([A-Z0-9\-]+)\b', re.IGNORECASE)
        pic_on_line = re.compile(r'\bPIC\b[^\n]*', re.IGNORECASE)
        file_status_clause = re.compile(r'\bFILE\s+STATUS\s+IS\s+([A-Z0-9\-]+)\b', re.IGNORECASE)

        # ----------------- A) FILE STATUS harvest -----------------
        in_file_control = False
        file_status_vars = []  # (name, clause_line_index)
        for i, ln in enumerate(self.lines):
            U = norm(ln)
            if 'FILE-CONTROL' in U:
                in_file_control = True
                continue
            if in_file_control and ('DATA DIVISION' in U or 'PROCEDURE DIVISION' in U):
                in_file_control = False
            if not in_file_control:
                continue

            for m in file_status_clause.finditer(ln):
                var = m.group(1)  # original case
                file_status_vars.append((var, i))

        # Locate declarations for file status vars in DATA/LINKAGE/WORKING
        if file_status_vars:
            data_started = False
            for i, ln in enumerate(self.lines):
                U = norm(ln)
                if 'DATA DIVISION' in U:
                    data_started = True
                    continue
                if not data_started:
                    continue

                m = lvl_name_re.search(ln)
                if not m:
                    continue
                level = int(m.group(1))
                name = m.group(2)
                if not (1 <= level <= 49):
                    continue

                # If this line declares any harvested var, record it
                for var, _cl in list(file_status_vars):
                    if re.search(rf'\b{re.escape(var)}\b', ln, re.IGNORECASE):
                        # capture PIC (this line only; wrapped PICs will be resolved by rule later)
                        pic_text = pic_on_line.search(ln)
                        add_name(var, decl_line=i, pic_ok=(is_pic_xx(pic_text.group(0)) if pic_text else None))

        # Add any FILE STATUS names not found in data division yet (decl_line=None)
        for var, cl in file_status_vars:
            if var not in self.status_decl_line:
                add_name(var, decl_line=None, pic_ok=None)

        # ----------------- B) PCB status harvest (LINKAGE + USING + used as PCB) -----------------
        # 1) Collect USING identifiers from PROCEDURE DIVISION USING
        using_ids = set()
        proc_seen = False
        for i, ln in enumerate(self.lines):
            U = norm(ln)
            if 'PROCEDURE DIVISION' in U:
                proc_seen = True
            if not proc_seen:
                continue
            # crude but works: pull tokens after USING on the same line
            m = re.search(r'\bUSING\b(.*)$', ln, re.IGNORECASE)
            if m:
                tail = m.group(1)
                # split on commas/spaces; keep COBOL-ish identifiers
                for tok in re.findall(r'[A-Z0-9\-]+', tail.upper()):
                    using_ids.add(tok)

        if not using_ids:
            return  # nothing else to harvest

        # 2) Walk LINKAGE, find 01-level items whose names are in USING
        in_link = False
        current_01 = None
        current_01_name = None
        current_01_line = None

        def flush_current_01():
            nonlocal current_01, current_01_name, current_01_line
            current_01 = None
            current_01_name = None
            current_01_line = None

        for i, ln in enumerate(self.lines):
            U = norm(ln)

            if 'LINKAGE SECTION' in U:
                in_link = True
                flush_current_01()
                continue
            if in_link and 'PROCEDURE DIVISION' in U:
                in_link = False
            if not in_link:
                continue

            m = lvl_name_re.search(ln)
            if not m:
                continue
            level = int(m.group(1))
            name = m.group(2)  # original case as appears on line

            if level == 1:
                # starting a new 01 block
                flush_current_01()
                if name.upper() in using_ids:
                    current_01 = True
                    current_01_name = name
                    current_01_line = i
                continue

            if not current_01:
                continue  # ignore fields not under a USING PCB 01

            # Under a tracked 01: look for a PIC XX field (preferably with STATUS in name, but not required)
            # If multiple, we will record the first we see.
            # Try to pick the tight one with PIC XX.
            pic_text = pic_on_line.search(ln)
            if pic_text and is_pic_xx(pic_text.group(0)):
                # record this child as the PCB status field
                add_name(name, decl_line=i, pic_ok=True)
                # Only record the first PIC XX child; others ignored
                # (Do not break; there might be other fields we don't want, but the rule will still pass.)
                continue
            # If the child has PIC but not XX, note it (pic_ok=False) only if it *looks* like a status name
            if pic_text and re.search(r'(PCB-STATUS|STATUS|STAT)\b', name, re.IGNORECASE):
                add_name(name, decl_line=i, pic_ok=False)

        # Done. The rule that verifies PIC X(2) will consult:
        #   - self.status_field_names
        #   - self.status_decl_line[name]
        #   - self.status_pic_ok[name]

    def _harvest_fd_record_to_file(self):
        """
        Build/refresh a mapping of FILE SECTION 01-record names -> owning FD name.
        - Scans the entire FD/SD block for *all* 01 records (not just the first).
        - Stops at the next FD/SD, Section boundary, or Division boundary.
        - Ignores 01s outside FILE SECTION.
        Produces:
          self.rec_to_file: Dict[RECORD_01_NAME] -> FD_NAME   (UPPERCASE)
          self.fd_record_names: Set[RECORD_01_NAME]
        """

        lines = getattr(self, 'lines', []) or []
        n = len(lines)

        self.rec_to_file = {}
        self.fd_record_names = set()

        # bound to FILE SECTION
        file_sec_start = None
        for idx, ln in enumerate(lines):
            if re.search(r'^\s*FILE\s+SECTION\s*\.', ln, re.IGNORECASE):
                file_sec_start = idx
                break
        if file_sec_start is None:
            return

        boundary = re.compile(
            r'^\s*(WORKING-STORAGE|LINKAGE|LOCAL-STORAGE|REPORT|COMMUNICATION)\s+SECTION\s*\.'
            r'|^\s*[A-Z-]+\s+DIVISION\s*\.',
            re.IGNORECASE,
        )
        i = file_sec_start + 1
        while i < n and not boundary.search(lines[i]):
            m_fd = re.match(r'^\s*(FD|SD)\s+([A-Z0-9-]+)\s*\.', lines[i], re.IGNORECASE)
            if not m_fd:
                i += 1
                continue

            current_fd = m_fd.group(2).upper()
            i += 1

            while i < n and not boundary.search(lines[i]):
                if re.match(r'^\s*(FD|SD)\s+[A-Z0-9-]+\s*\.', lines[i], re.IGNORECASE):
                    break
                m01 = re.match(r'^\s*01\s+([A-Z0-9-]+)\b', lines[i], re.IGNORECASE)
                if m01:
                    rec = m01.group(1).upper()
                    self.rec_to_file[rec] = current_fd
                    self.fd_record_names.add(rec)
                i += 1

        # keep attrs present even if empty (helps static analyzers)
        self.rec_to_file = getattr(self, 'rec_to_file', {}) or {}
        self.fd_record_names = getattr(self, 'fd_record_names', set()) or set()

    def _harvest_file_status_clauses(self):
        self.file_to_status = {}  # FILE-NAME (from SELECT) -> status var name (or None)
        self.select_files = set()

        in_fc = False
        cur_file = None
        sel_re = re.compile(r'^\s*SELECT\s+([A-Z0-9\-]+)\b', re.IGNORECASE)
        fs_re = re.compile(r'\bFILE\s+STATUS\s+IS\s+([A-Z0-9\-]+)\b', re.IGNORECASE)

        for i, ln in enumerate(self.lines):
            U = ln.upper()
            if 'FILE-CONTROL' in U:
                in_fc = True
                continue
            if in_fc and ('DATA DIVISION' in U or 'INPUT-OUTPUT SECTION' in U or 'FILE SECTION' in U):
                in_fc = False
            if not in_fc:
                continue

            msel = sel_re.search(ln)
            if msel:
                cur_file = msel.group(1).upper()
                self.select_files.add(cur_file)
                self.file_to_status.setdefault(cur_file, None)

                # Also try to capture FILE STATUS on the same line
                mfs_inline = fs_re.search(ln)
                if mfs_inline:
                    self.file_to_status[cur_file] = mfs_inline.group(1).upper()

                continue

            mfs = fs_re.search(ln)
            if mfs and cur_file:
                self.file_to_status[cur_file] = mfs.group(1).upper()

    def _has_near_status_check(self, call_line: int, pcb_name: str | None = None, lookahead: int = 12) -> bool:
        """
        Scan forward up to `lookahead` non-label, non-empty lines for an IF/EVALUATE
        that references a status-like symbol. Allows skipping a single paragraph label
        line (e.g., "PARA-1.") right after the call.

        Assumes `call_line` is a 0-based index into `self.lines`.
        """

        lines = getattr(self, 'lines', []) or []
        n = len(lines)
        if not (0 <= call_line < n):
            return False

        # Build candidate status names:
        # - harvested names, if available
        # - common patterns
        # - any token ending with "-STATUS"
        harvested = {s.upper() for s in (getattr(self, 'status_field_names', []) or [])}
        common = {'DB-STAT', 'PCB-STATUS', 'IOPCB-STATUS', 'DB-STATUS', 'STATUS'}
        text_upper = '\n'.join(lines).upper()
        dyn = {m.group(0).upper() for m in re.finditer(r'\b[A-Z0-9][A-Z0-9-]*-STATUS\b', text_upper)}
        status_like = harvested | common | dyn

        # If we know the PCB symbol, also accept PCB-NAME and PCB-NAME-STATUS as hits
        pcb_keys = set()
        if pcb_name:
            k = str(pcb_name).upper().replace(' ', '-')
            if k:
                pcb_keys.update({k, f'{k}-STATUS'})

        para_label_re = re.compile(r'^\s*[A-Z0-9][A-Z0-9-]*\.\s*$')
        scanned = 0
        j = call_line + 1
        label_skipped = False

        while j < n and scanned < lookahead:
            ln = lines[j]
            up = ln.upper()

            # Allow skipping a single paragraph label line without counting it
            if (not label_skipped) and para_label_re.match(ln):
                label_skipped = True
                j += 1
                continue

            # Count only non-empty lines toward lookahead window
            if up.strip():
                scanned += 1

            # Accept IF/EVALUATE lines that reference any status-like token
            if 'IF' in up or 'EVALUATE' in up:
                if any(name in up for name in status_like) or any(k in up for k in pcb_keys):
                    return True
                # Also accept generic "STATUS" mention within a control statement
                if 'STATUS' in up:
                    return True

                # For multi-line EVALUATE, take a small window
                if 'EVALUATE' in up:
                    win = '\n'.join(lu.upper() for lu in lines[j : min(n, j + 24)])
                    if any(name in win for name in status_like) or 'STATUS' in win or any(k in win for k in pcb_keys):
                        return True

            j += 1

        return False

    # --------------- rules ---------------
    def rule_structure_using_pcbs(self):
        # IMS-010: require USING list when LINKAGE PCBs exist. Fire only for IMS programs (have at least one PCB in LINKAGE).
        if not self.linkage_pcbs:
            return

        if not self.using_params:
            self._add('IMS-010', 'Error', 'LINKAGE PCBs present but PROCEDURE DIVISION lacks USING clause.')
            return

        for pcb in self.linkage_pcbs:
            if pcb not in self.using_params:
                # If the PCB is declared in LINKAGE, not received in PROC USING or ENTRY USING,
                # but is used in a CALL, emit the IMS-010 finding.
                used_in_call = any(pcb == call_pcb for _, _, call_pcb, _ in self.calls)
                if used_in_call:
                    self._add('IMS-010', 'Error', 'LINKAGE PCBs present but PROCEDURE DIVISION lacks USING clause.')
                else:
                    self._add('IMS-010', 'Error', f'PCB {pcb} is declared in LINKAGE but not in PROCEDURE DIVISION USING list.')

    def rule_invalid_function(self):
        # IMS-001: invalid or unresolved function
        for i, func, pcb, args in self.calls:
            if func == 'UNKNOWN':
                self._add('IMS-001', 'Error', 'Unresolved DL/I function code in CALL (first USING argument).', i)
            elif func not in IMS_FUNCS:
                self._add('IMS-001', 'Error', f'Invalid DL/I function code: {func}', i)

    def rule_missing_pcb_second_arg(self):
        # IMS-002: ensure second argument looks like PCB
        for i, func, pcb, args in self.calls:
            # allow CHKP/XRST without a PCB
            if func in {'CHKP', 'XRST'}:
                continue

            if len(args) < 2:
                self._add('IMS-002', 'Error', 'DL/I call missing PCB parameter as second USING argument.', i)
                continue
            # If we have known LINKAGE PCBs, require membership; else heuristic: contains 'PCB'
            known_pcbs_uc = [p.upper() for p in self.linkage_pcbs]
            if known_pcbs_uc:
                if pcb not in known_pcbs_uc:
                    self._add('IMS-002', 'Error', f'Second argument "{pcb}" is not a declared LINKAGE PCB.', i)
            else:
                if 'PCB' not in pcb:
                    self._add('IMS-002', 'Warning', f'Second argument "{pcb}" does not resemble a PCB name.', i)

    def rule_function_var_declared(self):
        """
        IMS-011: Operation token *variable* must be declared in WORKING-STORAGE.

        Noise trim:
          - If the operation token at the call site is UNQUOTED (i.e., a bare verb like GU/GN/REPL),
            IMS-150 will handle the "form" violation (must be quoted 4-char literal or WS PIC X(4)).
            In that case, suppress IMS-011 here to avoid duplicate noise.
            IMS-150 was not part of the rule subset tested in the paper and thus does not appear in the published
            version of the checker.
        """
        ws_uc = {n.upper() for n in getattr(self, 'ws_names', set())}
        call_tokens = getattr(self, 'call_raw_tokens', []) or []
        for idx, meta in enumerate(getattr(self, 'calls', [])):
            call_line = meta[0] if meta else None
            if idx >= len(call_tokens):
                continue
            tok = call_tokens[idx].strip()
            if not tok:
                continue

            # If token is unquoted, let IMS-150 handle form issues (dedupe).
            if not ((tok.startswith("'") and tok.endswith("'")) or (tok.startswith('"') and tok.endswith('"'))):
                continue

            payload = tok.strip('\'"').upper()
            # If it's a literal op (e.g., 'GU  '), IMS-011 is not applicable
            if (
                payload in getattr(self, 'IMS_FUNCS', set())
                if hasattr(self, 'IMS_FUNCS')
                else {'GU', 'GN', 'GHU', 'GHN', 'REPL', 'DLET', 'ISRT', 'CHKP', 'XRST'}
            ):
                continue

            # Otherwise it's meant to be a WS var; ensure it's declared
            if payload not in ws_uc:
                self._add('IMS-011', 'Error', f'Function code variable "{tok}" not declared in WORKING-STORAGE.', call_line)

    def rule_call_pcb_in_using(self):
        # IMS-012: PCB referenced in a CALL should appear in PROCEDURE DIVISION USING. Fires only if there are PCBs declared in LINKAGE.
        if not self.linkage_pcbs:
            return

        using_uc = set(self.using_params)
        for _i, _func, pcb, _args in self.calls:
            if pcb and using_uc and pcb not in using_uc:
                self._add('IMS-012', 'Error', f'PCB {pcb} used in CALL not present in PROCEDURE DIVISION USING list.', _i)

    def rule_status_checked_after_call(self):
        """
        IMS-020 — No nearby status check after a DL/I call (skips CHKP/XRST).
        Uses a proximity helper to recognize IF/EVALUATE checks right after the call.
        """

        calls = getattr(self, 'calls', []) or []
        lines = getattr(self, 'lines', []) or []

        for i, func, pcb, args in calls:
            if func in {'CHKP', 'XRST'}:
                continue

            checked = False

            # early proximity short-circuit
            if self._has_near_status_check(i, pcb_name=pcb, lookahead=12):
                checked = True

            # (Optional) very small same-line check
            if not checked and re.search(r'\bSTATUS\b', lines[i] if 0 <= i < len(lines) else '', re.IGNORECASE):
                checked = True

            if not checked:
                self._add('IMS-020', 'Warning', f'No status check near {func} call.', i)

    def rule_perform_until_status_init(self):
        """
        IMS-INIT-STATUS: flag when a loop tests PCB status before it can be valid.

        Suppress when:
          - PERFORM WITH TEST AFTER
          - Explicit init before loop (any MOVE ... TO <status>)
          - Status 'primed' by a prior IMS call followed by a status check
          - A recent status check (IF/EVALUATE on status) appears shortly before the loop

        Formerly downgraded to Info when the first statement inside the loop is an IMS call
        followed quickly by a status check (initialize-on-first-call pattern). Now emits Warning.
        """

        status_tokens_uc = [s.upper() for s in (self.status_field_names or ['STATUS-CODE', 'PCB-STATUS'])]

        call_re = re.compile(r"CALL\s+'(?:CBLTDLI|DFSLI000)'\b", re.IGNORECASE)
        stopper_fwd = re.compile(r'^\s*(END-IF|END-EVALUATE|END-PERFORM|GOBACK|EXIT|STOP\s+RUN)\b', re.IGNORECASE)

        def _has_status_token(u: str) -> bool:
            uu = u.upper()
            return any(tok in uu for tok in status_tokens_uc)

        def _explicit_init_before(line_idx: int) -> bool:
            # Any MOVE ... TO <status> (lenient)
            move_to_re = re.compile(r'\bMOVE\b.+\bTO\b.+', re.IGNORECASE)
            for j in range(max(0, line_idx - 200), line_idx):
                ln = self.lines[j]
                if move_to_re.search(ln) and _has_status_token(ln):
                    return True
            return False

        def _primed_by_prior_call(line_idx: int) -> bool:
            # Find a CALL; between that CALL and the loop, see a status IF/EVALUATE
            j = line_idx - 1
            back_limit = max(0, line_idx - 200)
            while j >= back_limit:
                uj = self.lines[j].upper()
                if call_re.search(uj):
                    for k in range(j + 1, line_idx):
                        uk = self.lines[k].upper()
                        if ('IF ' in uk or 'EVALUATE' in uk) and _has_status_token(uk):
                            return True
                        if call_re.search(uk):
                            break
                j -= 1
            return False

        def _recent_status_check_before(line_idx: int) -> bool:
            # Any status IF/EVALUATE within a recent window before the loop
            for j in range(max(0, line_idx - 80), line_idx):
                uj = self.lines[j].upper()
                if ('IF ' in uj or 'EVALUATE' in uj) and _has_status_token(uj):
                    return True
            return False

        def _first_stmt_inside_is_call_with_quick_check(loop_idx: int) -> bool:
            # First non-blank after PERFORM is CALL; soon after there's a status IF
            j = loop_idx + 1
            while j < len(self.lines) and not self.lines[j].strip():
                j += 1
            if j < len(self.lines) and call_re.search(self.lines[j]):
                for k in range(j + 1, min(len(self.lines), j + 12)):
                    uk = self.lines[k].upper()
                    if 'IF ' in uk and _has_status_token(uk):
                        return True
                    if stopper_fwd.search(self.lines[k]) or call_re.search(self.lines[k]):
                        break
            return False

        for i, ln in enumerate(self.lines):
            u = ln.upper()
            if 'PERFORM' in u and 'UNTIL' in u and _has_status_token(u):
                if 'WITH TEST AFTER' in u:
                    continue
                if _explicit_init_before(i):
                    continue
                if _primed_by_prior_call(i):
                    continue
                if _recent_status_check_before(i):
                    continue
                if _first_stmt_inside_is_call_with_quick_check(i):
                    self._add(
                        'IMS-INIT-STATUS',
                        'Warning',
                        'Loop tests PCB status before explicit initialization; loop body starts with an IMS call and immediately checks status.',
                        i,
                    )
                else:
                    self._add('IMS-INIT-STATUS', 'Warning', 'Loop tests PCB status before explicit initialization.', i)

    def rule_loop_gb_exit(self):
        """
        IMS-022: For GN/GHN, ensure there's visible handling of GB (end-of-database/message)
        near the call. We search forward until a natural boundary:
          - next CALL 'CBLTDLI' / 'DFSLI000'
          - END-PERFORM / GOBACK / EXIT / STOP RUN
          - or a max distance (safety cap)
          - if the next construct is an IF...END-IF, scan the whole IF/ELSE
            block (and any nested EVALUATEs) for GB handling, even if other DL/I calls
            appear inside the THEN branch
        and look for GB checks tied to the status field.
        """

        # Bring in Tuple type for the existing annotation used below
        try:
            from typing import Tuple
        except Exception:
            pass

        # Make sure calls were harvested
        if not getattr(self, 'calls', None):
            self.calls = self._find_cbltdli_calls()

        # Ensure status fields are available (the code below relies on them)
        if not getattr(self, 'status_field_names', None):
            self._harvest_status_names()

        status_tokens_uc = [s.upper() for s in (self.status_field_names or ['STATUS-CODE', 'PCB-STATUS'])]

        def _line_has_status(u: str) -> bool:
            U = u.upper()
            return any(tok in U for tok in status_tokens_uc)

        def _scan_evaluate_block(start_idx: int, end_limit: int) -> bool:
            """Within an EVALUATE on status, detect WHEN 'GB' before END-EVALUATE."""
            j = start_idx + 1
            while j < end_limit:
                U = self.lines[j].upper()
                if "WHEN 'GB'" in U or re.search(r"WHEN\s+['\"]GB['\"]", U, re.IGNORECASE):
                    return True
                if 'END-EVALUATE' in U:
                    return False
                j += 1
            return False

        def _scan_if_block(start_idx: int) -> Tuple[int, bool]:
            """
            Given an IF at start_idx, return (end_idx, found_gb).
            Tracks nested IF/END-IF and searches the whole block for GB handling:
              - IF ... STATUS = 'GB'
              - any line with 'GB' and a status token
              - EVALUATE <status> ... WHEN 'GB'
            """
            nest = 0
            found_gb = False
            i = start_idx
            end_idx = start_idx
            while i < len(self.lines):
                U = self.lines[i].upper()
                if U.strip().startswith('IF '):
                    nest += 1
                    # Check for IF ... = 'GB'
                    if ("'GB'" in U or re.search(r'\bGB\b', U)) and _line_has_status(U):
                        found_gb = True
                elif 'END-IF' in U:
                    nest -= 1
                    if nest == 0:
                        end_idx = i
                        break
                else:
                    # Any plain line with GB tied to a status token
                    if ("'GB'" in U or re.search(r'\bGB\b', U)) and _line_has_status(U):
                        found_gb = True
                    # EVALUATE on status -> look for WHEN 'GB'
                    if 'EVALUATE' in U and _line_has_status(U):
                        if _scan_evaluate_block(i, len(self.lines)):
                            found_gb = True
                i += 1
            return end_idx, found_gb

        # Build a lightweight gate so we only demand GB handling when warranted
        #        (a) ignore IOPCB, (b) require loop context or ≥2 sequential reads on same PCB

        utext = [ln.upper() for ln in (self.lines or [])]

        def _is_seq_read(func: str) -> bool:
            # minimal change: keep GN/GHN as before, but also accept GNP (safe enhancement)
            return (func or '').upper() in {'GN', 'GHN', 'GNP'}  # ADDED: include GNP

        def _is_in_loop(idx: int) -> bool:
            win = ' '.join(utext[max(0, idx - 6) : idx + 6])
            return bool(re.search(r'\bPERFORM\b.*\bUNTIL\b|\bVARYING\b', win))

        # Compute per-PCB need for GB handling
        per_pcb_reads = {}
        for ci, cf, cpcb, _cargs in self.calls or []:
            pcb_uc = (cpcb or '').upper()
            if pcb_uc:
                per_pcb_reads.setdefault(pcb_uc, []).append((ci, cf))

        for call_idx, func, pcb, args in self.calls:
            if not _is_seq_read(func):
                continue

            # Ignore IOPCB
            if 'IOPCB' in (pcb or '').upper():
                continue

            # Only demand GB if (loop around this call) OR (≥2 seq reads on same PCB)
            need_gb = False
            if _is_in_loop(call_idx):
                need_gb = True
            else:
                reads = per_pcb_reads.get((pcb or '').upper(), [])
                seq_reads_on_pcb = [1 for (_i, _f) in reads if _is_seq_read(_f)]
                if len(seq_reads_on_pcb) >= 2:
                    need_gb = True
            if not need_gb:
                continue

            has_gb = False

            # Search forward a reasonable window for nearby handling
            j = call_idx + 1
            end_limit = min(len(self.lines), call_idx + 60)

            while j < end_limit and not has_gb:
                U = self.lines[j].upper()

                # Direct GB line tied to a status token
                if ("'GB'" in U or re.search(r'\bGB\b', U)) and _line_has_status(U):
                    has_gb = True
                    break

                # EVALUATE <status> ... WHEN 'GB'
                if 'EVALUATE' in U and _line_has_status(U):
                    if _scan_evaluate_block(j, end_limit):
                        has_gb = True
                        break

                # IF ... scan the *entire* IF/ELSE block (do not stop at inner DL/I calls)
                if U.strip().startswith('IF '):
                    block_end, found = _scan_if_block(j)
                    if found:
                        has_gb = True
                        break
                    # skip to end of the IF block and continue scanning after it
                    j = block_end + 1
                    continue

                j += 1

            if not has_gb:
                self._add('IMS-022', 'Warning', f'No visible GB handling near {func} call.', call_idx)

    def rule_status_coverage(self):
        """
        IMS-021 + IMS-024 (scoped to real status variables):
          - IMS-021: Require GB handling only when sequential retrieval is present (GN/GHN/GNP).
                     Count GB handling in IF/EVALUATE even if the variable name isn't a classic
                     "status-like" token. Also recognize *-CODE / *-RESPONSE-CODE names.
          - IMS-024: Require a default/unexpected status handler (ELSE or WHEN OTHER) only for
                     conditionals that test a harvested status variable.
        """

        lines = getattr(self, 'lines', []) or []
        if not lines:
            return
        utext = [ln.upper() for ln in lines]
        text_upper = '\n'.join(utext)

        # Ensure harvested set exists
        if not getattr(self, 'status_field_names', None):
            self._harvest_status_names()
        status_tokens_uc = {s.upper() for s in (self.status_field_names or [])}

        # Expanded status-like detection: *-STATUS, *-CODE, *-RESPONSE-CODE
        dyn_status_tokens = set()
        for pat in (r'\b[A-Z0-9][A-Z0-9-]*-STATUS\b', r'\b[A-Z0-9][A-Z0-9-]*-CODE\b', r'\b[A-Z0-9][A-Z0-9-]*-RESPONSE-CODE\b'):
            for m in re.finditer(pat, text_upper, re.IGNORECASE):
                dyn_status_tokens.add(m.group(0).upper())

        # ---------------- IMS-021: GB handling (only with sequential retrieval present)

        if not getattr(self, 'calls', None):
            self.calls = self._find_cbltdli_calls()

        def _is_seq_read(func):
            return (func or '').upper() in {'GN', 'GHN', 'GNP'}

        def _is_iopcb(pcb):
            return 'IOPCB' in (pcb or '').upper()

        # Compute retrieval_present conservatively:
        #   - ignore IOPCB
        #   - require either ≥2 seq-reads on same PCB OR a seq-read inside a PERFORM loop
        retrieval_present = False
        per_pcb = {}
        for _i, _f, _pcb, _args in self.calls or []:
            pcb_uc = (_pcb or '').upper()
            per_pcb.setdefault(pcb_uc, []).append((_i, _f, pcb_uc, _args))

        for pcb_uc, seq in per_pcb.items():
            if not pcb_uc or _is_iopcb(pcb_uc):
                continue
            seq_reads = [(i, f) for (i, f, _p, _a) in seq if _is_seq_read(f)]
            if len(seq_reads) >= 2:
                retrieval_present = True
                break
            if len(seq_reads) == 1:
                i0, _ = seq_reads[0]
                win = ' '.join(utext[max(0, i0 - 6) : i0 + 6])
                if re.search(r'\bPERFORM\b.*\bUNTIL\b|\bVARYING\b', win):
                    retrieval_present = True
                    break

        if retrieval_present:
            has_gb = False

            # Helper patterns (accept literal 'GB' checks regardless of var name)
            if_cmp_gb = re.compile(r"\bIF\b[\s\S]{0,160}?\b(=|IS)\s*'GB'\b", re.IGNORECASE)
            when_lit_gb = re.compile(r"\bWHEN\b\s*'GB'\b", re.IGNORECASE)
            when_cmp_gb = re.compile(r"\bWHEN\b[\s\S]{0,40}?[A-Z0-9\-]+\s*(=|IS)\s*'GB'\b", re.IGNORECASE)

            # (a) Line-level IF … 'GB'
            for up in utext:
                if if_cmp_gb.search(up):
                    has_gb = True
                    break

            # (b) EVALUATE blocks with WHEN 'GB' or WHEN <sym> = 'GB'
            if not has_gb:
                i = 0
                while i < len(utext):
                    up = utext[i]
                    if 'EVALUATE' in up:
                        j = i + 1
                        while j < len(utext) and 'END-EVALUATE' not in utext[j]:
                            if when_lit_gb.search(utext[j]) or when_cmp_gb.search(utext[j]):
                                has_gb = True
                                break
                            j += 1
                        if has_gb:
                            break
                        i = j
                    i += 1

            if not has_gb:
                self._add('IMS-021', 'Error', "Program performs sequential retrieval but never handles 'GB' (end-of-db) anywhere.")

        # ---------------- IMS-024: default/unexpected branch for harvested status vars

        def block_has_else(start_idx: int) -> bool:
            j = start_idx + 1
            while j < len(utext):
                uu = utext[j]
                if re.search(r'\bELSE\b', uu):
                    return True
                if 'END-IF' in uu:
                    return False
                j += 1
            return False

        def block_has_when_other(start_idx: int) -> bool:
            j = start_idx + 1
            while j < len(utext):
                uu = utext[j]
                if 'WHEN OTHER' in uu:
                    return True
                if 'END-EVALUATE' in uu:
                    return False
                j += 1
            return False

        saw_status_check = False
        missing_default_reports = []

        for idx, up in enumerate(utext):
            # EVALUATE <harvested-status-var>
            if 'EVALUATE' in up and any(tok in up for tok in status_tokens_uc):
                saw_status_check = True
                if not block_has_when_other(idx):
                    missing_default_reports.append(idx)

            # IF <harvested-status-var>
            if 'IF ' in up and any(tok in up for tok in status_tokens_uc):
                saw_status_check = True
                if not block_has_else(idx):
                    missing_default_reports.append(idx)

        if saw_status_check and missing_default_reports:
            self._add('IMS-024', 'Error', 'No default/unexpected status handling found (ELSE or WHEN OTHER).', missing_default_reports[0])

    def rule_write_target_is_fd_record(self):
        if not hasattr(self, 'fd_record_names'):
            self._harvest_fd_record_to_file()
        write_re = re.compile(r'^\s*WRITE\s+([A-Z0-9\-]+)\b', re.IGNORECASE)

        for i, ln in enumerate(self.lines):
            m = write_re.search(ln)
            if not m:
                continue
            tgt = m.group(1).upper()
            if tgt not in self.fd_record_names:
                self._add('COB-110', 'Error', f"WRITE target '{tgt}' is not a FILE SECTION 01 record.", i)

    def rule_write_requires_output_open(self):
        """
        COB-111 — WRITE / REWRITE / DELETE requires the owning file to be OPEN in OUTPUT/EXTEND/I-O.
        Suppress for GSAM-bound FDs (IMS handles GSAM open/close; IMS-132 covers explicit OPEN/CLOSE).
        """

        lines = getattr(self, 'lines', []) or []

        # record->FD map
        if not getattr(self, 'rec_to_file', None) and hasattr(self, '_harvest_fd_record_to_file'):
            self._harvest_fd_record_to_file()
        rec_to_file = getattr(self, 'rec_to_file', {}) or {}
        fd_record_names = set(getattr(self, 'fd_record_names', set())) or set(rec_to_file.keys())

        # SELECT map to identify GSAM FDs
        text = '\n'.join(lines)
        m_fc = re.search(r'^\s*FILE-CONTROL\s*\.', text, re.IGNORECASE | re.MULTILINE)
        m_fs = re.search(r'^\s*FILE\s+SECTION\s*\.', text, re.IGNORECASE | re.MULTILINE)
        start = m_fc.start() if m_fc else 0
        end = m_fs.start() if (m_fc and m_fs and m_fs.start() > m_fc.start()) else len(text)
        fc_blob = text[start:end]

        gsam_fds = set()
        for m in re.finditer(r'^\s*SELECT\s+([A-Z0-9\-]+)\s+ASSIGN\s+TO\s+([^.\n]+)\.', fc_blob, re.IGNORECASE | re.MULTILINE):
            fd = m.group(1).upper()
            tgt = m.group(2).upper()
            if 'GSAM' in tgt:
                gsam_fds.add(fd)

        # OPEN modes map
        open_modes = {}  # FD -> {'INPUT','OUTPUT','I-O','EXTEND'}
        mode_kw = {'INPUT', 'OUTPUT', 'I-O', 'EXTEND'}
        for ln in lines:
            u = ln.upper()
            if not u.lstrip().startswith('OPEN'):
                continue
            tokens = re.findall(r'\b[A-Z0-9-]+\b', u)
            cur_mode = None
            for tok in tokens[1:]:
                if tok in mode_kw:
                    cur_mode = tok
                else:
                    if cur_mode:
                        open_modes.setdefault(tok, set()).add(cur_mode)

        # Validate WRITE / REWRITE / DELETE targets
        write_like = re.compile(r'^\s*(WRITE|REWRITE|DELETE)\s+([A-Z0-9\-]+)\b', re.IGNORECASE)

        for i, ln in enumerate(lines):
            m = write_like.search(ln)
            if not m:
                continue
            op = m.group(1).upper()  # WRITE / REWRITE / DELETE (optional: include in message)
            rec = m.group(2).upper()
            if rec not in fd_record_names:
                continue  # COB-110 covers "not a FILE SECTION 01 record"
            owner_fd = rec_to_file.get(rec)
            if not owner_fd:
                continue

            # Suppress for GSAM
            if owner_fd in gsam_fds:
                continue

            modes = open_modes.get(owner_fd, set())
            if not ({'OUTPUT', 'I-O', 'EXTEND'} & modes):
                self._add('COB-111', 'Error', f"{op} of '{rec}' requires file '{owner_fd}' to be OPEN in OUTPUT/EXTEND/I-O.", i)

    def rule_file_requires_status_clause(self):
        """
        COB-120: If a file is OPENed/READ/WRITEn/etc., require a FILE STATUS IS binding.
        Emits one error per file missing a status var.

        Noise trim:
          - Suppress COB-120 for GSAM-bound FDs (ASSIGN TO ...GSAM...), since IMS-130/131/132 already report the misuse.
        """

        # Ensure prerequisites are harvested
        if not hasattr(self, 'file_to_status'):
            self._harvest_file_status_clauses()
        if not hasattr(self, 'rec_to_file') or not hasattr(self, 'fd_record_names'):
            self._harvest_fd_record_to_file()

        lines = getattr(self, 'lines', []) or []

        # -------- Determine GSAM-bound files from FILE-CONTROL --------
        text_blob = '\n'.join(lines)
        m_fc = re.search(r'^\s*FILE-CONTROL\s*\.', text_blob, re.IGNORECASE | re.MULTILINE)
        m_fs = re.search(r'^\s*FILE\s+SECTION\s*\.', text_blob, re.IGNORECASE | re.MULTILINE)
        fc_start = m_fc.start() if m_fc else 0
        fc_end = m_fs.start() if (m_fc and m_fs and m_fs.start() > m_fc.start()) else len(text_blob)
        fc_blob = text_blob[fc_start:fc_end]

        # Map SELECTed file -> ASSIGN target (multi-line safe)
        # Accept SELECT ... ASSIGN TO <target> ... . (across lines, up to the terminating period)
        select_map: dict[str, str] = {}
        for m in re.finditer(r'^\s*SELECT\s+([A-Z0-9\-]+)\s+ASSIGN\s+TO\s+([\s\S]*?)\.', fc_blob, re.IGNORECASE | re.MULTILINE):
            fd = m.group(1).upper()
            tgt = m.group(2)  # may span lines (e.g., "GSAMAUD\n  ORGANIZATION IS SEQUENTIAL")
            select_map[fd] = tgt

        gsam_files = {fd for fd, tgt in select_map.items() if 'GSAM' in str(tgt).upper()}

        # -------- Collect files that are actually used by COBOL I/O verbs --------
        op_re = re.compile(r'\b(OPEN|READ|WRITE|REWRITE|DELETE|CLOSE|START)\b', re.IGNORECASE)
        token_re = re.compile(r'\b[A-Z0-9\-]+\b', re.IGNORECASE)

        files_used: set[str] = set()

        # Known SELECTed files if harvested
        selected = {k.upper() for k in getattr(self, 'select_files', set())}

        for ln in lines:
            if not op_re.search(ln):
                continue

            toks = [t.upper() for t in token_re.findall(ln)]

            # Any token that is a SELECTed file name → count as used
            for t in toks:
                if t in selected:
                    files_used.add(t)

            # Record names mapped back to their FD (e.g., "WRITE CUSTOMER-REC")
            for t in toks:
                if t in getattr(self, 'rec_to_file', {}):
                    files_used.add(self.rec_to_file[t])

        # -------- Emit COB-120 for non-GSAM files missing FILE STATUS --------
        for fil in sorted(files_used):
            # Noise trim: skip GSAM-bound files; IMS-130/131/132 will already flag the misuse.
            if fil in gsam_files:
                continue

            if self.file_to_status.get(fil) in (None, ''):
                self._add(
                    'COB-120',
                    'Error',
                    f"File '{fil}' is used (OPEN/READ/WRITE/REWRITE/DELETE/START/CLOSE) without a `FILE STATUS IS <var>` binding in FILE-CONTROL.",
                )

    def rule_gsam_fd_misuse(self):
        """
        IMS-130 — COBOL WRITE on a GSAM-assigned file/record (GSAM expects DL/I ISRT)
        IMS-131 — COBOL READ/REWRITE/DELETE on a GSAM-assigned file/record
        IMS-132 — Explicit OPEN/CLOSE of a GSAM-assigned file (IMS manages GSAM open/close)
        """

        lines = getattr(self, 'lines', []) or []
        text = '\n'.join(lines)

        # Build SELECT map from FILE-CONTROL
        m_fc = re.search(r'^\s*FILE-CONTROL\s*\.', text, re.IGNORECASE | re.MULTILINE)
        m_fs = re.search(r'^\s*FILE\s+SECTION\s*\.', text, re.IGNORECASE | re.MULTILINE)
        start = m_fc.start() if m_fc else 0
        end = m_fs.start() if (m_fc and m_fs and m_fs.start() > m_fc.start()) else len(text)
        fc_blob = text[start:end]

        select_map = {}  # FD -> ASSIGN target (raw; may span lines)
        for m in re.finditer(r'^\s*SELECT\s+([A-Z0-9\-]+)\s+ASSIGN\s+TO\s+([\s\S]*?)\.', fc_blob, re.IGNORECASE | re.MULTILINE):
            fd = m.group(1).upper()
            tgt = m.group(2)
            select_map[fd] = tgt

        # GSAM-bound FDs via ASSIGN target
        gsam_files = {fd for fd, tgt in select_map.items() if 'GSAM' in str(tgt).upper()}

        # Ensure record→FD exists (for WRITE <record> etc.)
        if not getattr(self, 'rec_to_file', None) and hasattr(self, '_harvest_fd_record_to_file'):
            self._harvest_fd_record_to_file()
        rec_to_file = getattr(self, 'rec_to_file', {}) or {}

        # Helpers
        verb_re = re.compile(r'^\s*(OPEN|CLOSE|READ|WRITE|REWRITE|DELETE)\s+([A-Z0-9\-]+)', re.IGNORECASE)

        def _is_open_close_on_gsam(line: str) -> bool:
            up = line.lstrip().upper()
            if not (up.startswith('OPEN') or up.startswith('CLOSE')):
                return False
            tokens = re.findall(r'\b[A-Z0-9-]+\b', up)
            return any(tok in gsam_files for tok in tokens)

        def _is_cobol_io_on_gsam(line: str):
            m = verb_re.search(line)
            if not m:
                return (None, None, False)
            verb = m.group(1).upper()
            tgt = m.group(2).upper()
            owner = tgt if tgt in gsam_files else rec_to_file.get(tgt)
            is_gsam = owner in gsam_files if owner else False
            return verb, tgt, is_gsam

        seen = set()  # (line_idx, rule_id) throttle

        for i, ln in enumerate(lines):
            # IMS-132: explicit OPEN/CLOSE on GSAM
            if _is_open_close_on_gsam(ln):
                key = (i, 'IMS-132')
                if key not in seen:
                    self._add('IMS-132', 'Warning', 'Explicit OPEN/CLOSE on GSAM data set; IMS manages GSAM open/close.', i)
                    seen.add(key)

            # IMS-130/131: COBOL file I/O on GSAM
            verb, tgt, is_gsam = _is_cobol_io_on_gsam(ln)
            if not is_gsam or verb is None:
                continue

            if verb == 'WRITE':
                key = (i, 'IMS-130')
                if key not in seen:
                    self._add('IMS-130', 'Error', f"COBOL WRITE on GSAM target '{tgt}' (or its record). Use DL/I ISRT via GSAM PCB.", i)
                    seen.add(key)
            elif verb in {'READ', 'REWRITE', 'DELETE'}:
                key = (i, 'IMS-131')
                if key not in seen:
                    self._add('IMS-131', 'Error', f"COBOL {verb} on GSAM target '{tgt}' (or its record) is not valid; use DL/I calls.", i)
                    seen.add(key)

    def rule_checkpoint_iopcb(self):
        """
        IMS-140/IMS-141 — CHKP/XRST & IOPCB
          * IMS-140  CHKP/XRST must use the IOPCB; flagged if a DB PCB is used instead.
          * IMS-141  IOPCB required in LINKAGE and PROCEDURE DIVISION USING when CHKP/XRST present.
        """
        io_pcbs = [p for p in self.linkage_pcbs if self._is_iopcb_name(p)]
        calls = getattr(self, 'calls', [])

        # Detect other usages that imply IOPCB is actually used (ISRT to IOPCB, or PCB named IOPCB)
        io_pcbs_uc = {p.upper() for p in io_pcbs}
        uses_isrt_iopcb = any(func == 'ISRT' and (pcb or '').upper() in io_pcbs_uc for _, func, pcb, _ in calls)
        mentions_iopcb = any((pcb or '').upper() in io_pcbs_uc for _, _, pcb, _ in calls)

        # If CHKP/XRST exist, we expect an IOPCB in LINKAGE and USING
        has_chkp_xrst = any(func in {'CHKP', 'XRST'} for _, func, _, _ in calls)
        if has_chkp_xrst and not io_pcbs:
            # No IOPCB declared at all
            for i, func, _pcb, _ in calls:
                if func in {'CHKP', 'XRST'}:
                    self._add('IMS-141', 'Error', 'CHKP/XRST present but no IOPCB declared in LINKAGE/USING.', i)

        # If IOPCB exists, ensure it’s listed in USING
        using_set = set(self.using_params or [])
        # ADDED: only demand USING when IOPCB is actually used (CHKP/XRST present, or ISRT to IOPCB, or PCB named IOPCB)
        if has_chkp_xrst or uses_isrt_iopcb or mentions_iopcb:
            for iop in io_pcbs:
                if iop not in using_set:
                    self._add(
                        'IMS-141',
                        'Error',
                        f"IOPCB '{iop}' not listed in PROCEDURE DIVISION USING.",
                        next((ix for ix, ln in enumerate(self.lines) if 'PROCEDURE DIVISION' in ln.upper()), None),
                    )

        # Ensure CHKP/XRST use the IOPCB
        io_pcbs_uc = {p.upper() for p in io_pcbs}
        for i, func, pcb, _ in calls:
            if func in {'CHKP', 'XRST'} and io_pcbs_uc and pcb not in io_pcbs_uc:
                self._add('IMS-140', 'Error', f'{func} must use IOPCB; found PCB {pcb}.', i)

    def rule_ssa_shape(self):
        """
        IMS-160/IMS-161 — SSA correctness
          * IMS-160  Malformed SSA: operator field as PIC X(3) (should be X(2)), or operator/value outside parentheses.
          * IMS-161  SSA misuse: suspicious MOVE into SSA fields from IO-area (heuristic).
        """
        # X(3) operator fields like: PIC X(3) VALUE '>='  (should be X(2))
        for i, ln in enumerate(self.lines):
            U = ln.upper()
            if 'SSA' in U and 'PIC X(3)' in U and ("'>='" in U or "'<='" in U or "'>'" in U or "'<'" in U or "'='" in U):
                self._add('IMS-160', 'Error', 'SSA operator field should be PIC X(2), not PIC X(3).', i)

        # Heuristic: MOVE ... TO ... IN <*-SSA>
        for i, ln in enumerate(self.lines):
            if re.search(r'\bMOVE\b.+\bTO\b.+\bIN\s+[A-Z0-9-]+-SSA\b', ln, re.IGNORECASE):
                self._add('IMS-161', 'Error', 'Suspicious MOVE into SSA field; SSA should be composed text, not IO-area fields.', i)

    def rule_symbolic_chkp_expected(self):
        """
        IMS-142 — Expect symbolic CHKP when XRST/restart token is present.
        Warn if CHKP appears to be the basic (non-symbolic) form.
        Heuristics used:
          - Preconditions: XRST call present OR restart/token area mentioned anywhere in source.
          - For each CHKP call line, if we cannot detect a length argument before any area(s),
            or parsed args <= 2, treat it as 'basic' and warn.
        """

        lines = getattr(self, 'lines', []) or []
        text = '\n'.join(lines)

        # Preconditions
        has_xrst = any(func == 'XRST' for _, func, _, _ in getattr(self, 'calls', []))
        has_token = bool(re.search(r'\b(RESTART|TOKEN)\b', text, re.IGNORECASE))
        if not (has_xrst or has_token):
            return

        # Collect token-ish mentions by line to prefer *local* token context around CHKP lines
        token_lines = set()
        for idx, ln in enumerate(lines):
            if re.search(r'\b(RESTART|TOKEN)\b', ln, re.IGNORECASE):
                token_lines.add(idx)

        # Inspect CHKP calls
        for i, func, pcb, args in getattr(self, 'calls', []):
            if func != 'CHKP':
                continue

            # If there's no XRST globally, require a local token context near this CHKP
            if not has_xrst:
                # within ±5 lines of the CHKP line, is there a token-ish mention?
                has_local_token = any(abs(i - tl) <= 5 for tl in token_lines)
                if not has_local_token:
                    continue  # Skip warning for CHKP far away from any token context

            # Quick structural check: basic CHKP is typically <= 2 args (IOPCB + one area)
            is_basic = len(args) <= 2

            # Source-line pattern: look for a numeric 'length' between CHKP and the first area
            # Accept either integer literals or names containing LEN/LENGTH as a length argument.
            if not is_basic:
                ln = lines[i] if 0 <= i < len(lines) else ''
                # Normalize and look for lengthy token after CHKP, before a likely area name
                after = ln.upper().split('CHKP', 1)[-1]
                has_len_token = bool(re.search(r'\b\d+\b|\bLEN(GTH)?\b|-LEN\b', after))
                if not has_len_token:
                    # still treat as basic if no obvious length token appears
                    is_basic = True

            if is_basic:
                self._add('IMS-142', 'Warning', 'Symbolic CHKP expected with XRST/restart token; basic CHKP detected.', i)

    def rule_chkp_xrst_uses_iopcb(self):
        """
        IMS-143: CHKP/XRST should use the IOPCB. If an IOPCB symbol exists in the program
        and a CHKP/XRST call passes a different PCB as arg#2, flag an Error.
        (Distinct from IMS-141, which is about the IOPCB being missing entirely.)
        """

        calls = getattr(self, 'calls', []) or []
        lines = getattr(self, 'lines', []) or []
        text = '\n'.join(lines)

        # Harvest IOPCB-looking names from LINKAGE (liberal, since generators vary naming)
        # We scan only LINKAGE..PROCEDURE DIVISION block to avoid WS noise.
        m_lk = re.search(r'^\s*LINKAGE\s+SECTION\s*\.', text, re.IGNORECASE | re.MULTILINE)
        m_pd = re.search(r'^\s*PROCEDURE\s+DIVISION\b', text, re.IGNORECASE | re.MULTILINE)
        lk_blob = text[m_lk.start() : m_pd.start()] if (m_lk and m_pd and m_pd.start() > m_lk.start()) else text

        iopcb_candidates = set()
        for m in re.finditer(r'\bIOPCB[A-Z0-9\-]*\b', lk_blob, re.IGNORECASE):
            iopcb_candidates.add(m.group(0).upper())

        # If your checker has a harvested set, union it.
        iopcb_candidates |= {n.upper() for n in getattr(self, 'iopcb_names', set())}

        if not iopcb_candidates:
            return  # Without any IOPCB symbol in program, IMS-141 covers the "missing" case.

        for i, func, pcb, args in calls:
            if func not in {'CHKP', 'XRST'}:
                continue
            pcb_name = (str(pcb) if pcb is not None else '').upper()
            if pcb_name and (pcb_name not in iopcb_candidates):
                self._add('IMS-143', 'Error', f'{func} passed non-IOPCB "{pcb_name}". Expected IOPCB.', i)

    def rule_dli_arg_order_sanity(self):
        """
        IMS-162: DL/I arg-order sanity for GU/GN/GHU/GHN/ISRT.
          Expected order: func, PCB, IO-AREA, [SSA...]
          If arg3 "looks like" an SSA and arg4 "looks like" a buffer, flag an Error.
        Notes:
          * Heuristic only; we don't require SSA presence here (that's IMS-161).
          * We avoid firing when we cannot read at least 4 args.
        """

        calls = getattr(self, 'calls', []) or []

        def looks_like_ssa(tok: str) -> bool:
            if not tok:
                return False
            u = tok.upper().strip()
            if u.endswith('-SSA') or 'SSA' in u:
                return True
            # SSA literals often contain '(' qualifiers ')'
            if (u.startswith("'") and u.endswith("'")) or (u.startswith('"') and u.endswith('"')):
                inner = u[1:-1]
                if '(' in inner and ')' in inner:
                    return True
            return False

        def looks_like_buffer(tok: str) -> bool:
            if not tok:
                return False
            u = str(tok).upper().strip().strip('"\'')

            # Normalize separators for IOAREA variants
            norm = re.sub(r'[\s\-_]', '', u)  # "LINK-IO AREA" -> "LINKIOAREA"
            if 'IOAREA' in norm or 'IOBUFFER' in norm or 'IOBUF' in norm:
                return True

            # Common IO area / record / segment tokens
            buffer_markers = (
                'IO-AREA',
                'IO AREA',
                'LINK-IOAREA',
                'LINK-IO-AREA',
                'WS-IOAREA',
                'AREA',
                'BUFFER',
                'BUF',
                'DATA',
                'PAYLOAD',
                '-REC',
                '-RECORD',
                ' RECORD',
                '-SEG',
                '-SEGMENT',
                ' SEGMENT',
            )
            if any(marker in u for marker in buffer_markers):
                return True

            # Avoid misclassifying obvious SSA-ish names
            if 'SSA' in u:
                return False

            return False

        for i, func, pcb, args in calls:
            if func not in {'GU', 'GN', 'GHU', 'GHN', 'ISRT'}:
                continue
            # args are post-PCB: [arg3, arg4, ...]
            arg3 = args[0] if (isinstance(args, (list, tuple)) and len(args) >= 1) else None
            arg4 = args[1] if (isinstance(args, (list, tuple)) and len(args) >= 2) else None
            if not (arg3 and arg4):
                continue

            if looks_like_ssa(str(arg3)) and looks_like_buffer(str(arg4)):
                self._add('IMS-162', 'Error', f'{func} call: arg3 looks like SSA and arg4 like buffer; expected arg3=IO-AREA, arg4+=SSA.', i)

    def rule_isrt_ssa_presence(self):
        """
        IMS-163: ISRT should normally have at least one SSA when the program constructs SSAs.
        We emit a Warning when ISRT is called with only IO-AREA (no SSA) while SSAs appear
        to be present/declared somewhere in the program.
        """

        calls = getattr(self, 'calls', []) or []
        lines = getattr(self, 'lines', []) or []
        text = '\n'.join(lines).upper()

        # If we can't see any SSA symbols/literals in the program at all, don't nag.
        has_any_ssa_artifacts = bool(
            re.search(r'\b[A-Z0-9][A-Z0-9-]*-SSA\b', text) or re.search(r"'[^']*\([^']*\)'", text)  # literals with ( ... ) like 'SEG(KEY(...))'
        )
        if not has_any_ssa_artifacts:
            return

        for i, func, pcb, args in calls:
            if func != 'ISRT':
                continue
            # args[0] is IO-AREA (expected), args[1:] are SSAs (if any)
            has_ssa = False
            if isinstance(args, (list, tuple)) and len(args) >= 2:
                for a in args[1:]:
                    if a is None:
                        continue
                    u = str(a).upper()
                    if u.endswith('-SSA') or 'SSA' in u:
                        has_ssa = True
                        break
                    if (u.startswith("'") and u.endswith("'")) and ('(' in u and ')' in u):
                        has_ssa = True
                        break
            if not has_ssa:
                self._add('IMS-163', 'Warning', 'ISRT called without any SSA (program appears to define/use SSAs elsewhere).', i)

    def rule_gsam_audit_after_gn(self):
        """
        IMS-170: Heuristic audit discipline — if GSAM is present in FILE-CONTROL, and the
        program issues GN/GHN, expect to find an ISRT nearby (same block).
        Improvement: if a PERFORM <para> appears shortly after GN/GHN, follow one level
        into that paragraph and scan for an ISRT there (common audit helper pattern).
        """

        lines = getattr(self, 'lines', []) or []
        if not lines:
            return
        text = '\n'.join(lines)

        # Detect GSAM presence (from FILE-CONTROL SELECT ... ASSIGN TO ...)
        m_fc = re.search(r'^\s*FILE-CONTROL\s*\.', text, re.IGNORECASE | re.MULTILINE)
        m_fs = re.search(r'^\s*FILE\s+SECTION\s*\.', text, re.IGNORECASE | re.MULTILINE)
        fc_start = m_fc.start() if m_fc else 0
        fc_end = m_fs.start() if (m_fc and m_fs and m_fs.start() > m_fc.start()) else len(text)
        fc_blob = text[fc_start:fc_end].upper()
        has_gsam = 'GSAM' in fc_blob
        if not has_gsam:
            return

        calls = getattr(self, 'calls', []) or []
        n = len(lines)

        # Paragraph index for one-level follow
        para_re = re.compile(r'^\s*([A-Z0-9][A-Z0-9-]*)\.\s*$')
        para_index = {}  # name -> start line
        for idx, ln in enumerate(lines):
            m = para_re.match(ln)
            if m:
                para_index[m.group(1).upper()] = idx

        def next_para_start(from_idx: int) -> int:
            j = from_idx + 1
            while j < n:
                if para_re.match(lines[j]):
                    return j
                j += 1
            return n

        isrt_line_re = re.compile(r"CALL\b.*\bCBLTDLI\b.*\bUSING\b.*\b('ISRT'|\"ISRT\"|\bISRT\b)", re.IGNORECASE)

        def has_isrt_window(start: int, lookahead_nonempty: int = 14) -> bool:
            scanned = 0
            j = start + 1
            while j < n and scanned < lookahead_nonempty:
                up = lines[j].upper()
                if up.strip():
                    scanned += 1
                if isrt_line_re.search(lines[j]):
                    return True
                # Stop early at a new paragraph once we've scanned a few lines
                if scanned >= 6 and para_re.match(lines[j]):
                    break
                j += 1
            return False

        def has_isrt_in_paragraph(para_name_uc: str, max_scan_lines: int = 20) -> bool:
            start = para_index.get(para_name_uc)
            if start is None:
                return False
            end = next_para_start(start)
            limit = min(end, start + 1 + max_scan_lines)
            for j in range(start + 1, limit):
                if isrt_line_re.search(lines[j]):
                    return True
            return False

        perform_re = re.compile(r'\bPERFORM\s+([A-Z0-9][A-Z0-9-]*)\b', re.IGNORECASE)

        for i, func, pcb, args in calls:
            if func not in {'GN', 'GHN'}:
                continue

            # 1) Look inline after the GN/GHN
            if has_isrt_window(i):
                continue

            # 2) If a PERFORM <para> appears within a short window, follow into that paragraph
            #    (scan the first ~8 non-empty lines for a PERFORM)
            scanned = 0
            j = i + 1
            followed = False
            while j < n and scanned < 8:
                up = lines[j].upper()
                if up.strip():
                    scanned += 1

                m = perform_re.search(lines[j])
                if m:
                    para_name_uc = m.group(1).upper()
                    if has_isrt_in_paragraph(para_name_uc, max_scan_lines=20):
                        followed = True
                        break
                    # If we PERFORM THRU, still count the entry paragraph
                # Stop early if we hit a new paragraph label
                if para_re.match(lines[j]) and scanned >= 4:
                    break
                j += 1

            if not followed:
                self._add('IMS-170', 'Warning', f'No nearby ISRT after {func}; expected audit insert in the same block or immediate PERFORMed paragraph.', i)

    # --------------- run ---------------
    def analyze_cobol(self) -> Optional[List[Dict]]:
        if not self.text:
            return None

        self.parse()

        # ---- IMS rules ----
        self.rule_structure_using_pcbs()
        self.rule_invalid_function()
        self.rule_function_var_declared()
        self.rule_call_pcb_in_using()
        self.rule_missing_pcb_second_arg()
        self.rule_status_checked_after_call()
        self.rule_perform_until_status_init()
        self.rule_loop_gb_exit()
        self.rule_status_coverage()
        self.rule_isrt_ssa_presence()
        self.rule_write_target_is_fd_record()
        self.rule_write_requires_output_open()
        self.rule_file_requires_status_clause()
        self.rule_gsam_fd_misuse()
        self.rule_gsam_audit_after_gn()
        self.rule_symbolic_chkp_expected()
        self.rule_checkpoint_iopcb()
        self.rule_chkp_xrst_uses_iopcb()
        self.rule_ssa_shape()
        self.rule_dli_arg_order_sanity()


        return [f.to_dict() for f in self.findings]

if __name__ == '__main__':
    cobol_prog = """
           IDENTIFICATION DIVISION.
       PROGRAM-ID. GHNCALL.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.

       DATA DIVISION.
       WORKING-STORAGE SECTION.

       01 DL-I-CODES.
           05 DLI-GHN        PIC X(4) VALUE 'GHN '.
           05 DLI-REPL      PIC X(4) VALUE 'REPL'.

       01 IO-AREA.
           05 DEPT-ID        PIC X(5).
           05 DEPT-NAME      PIC X(30).
           05 COURSE-ID      PIC X(5).
           05 COURSE-NAME    PIC X(30).
           05 STUDENT-ID     PIC X(5).
           05 STUDENT-NAME   PIC X(25).

       01 NEW-NAME          PIC X(25) VALUE 'UPDATED NAME'.

       LINKAGE SECTION.

       01 STUDENT-PCB.
           05 DBD-NAME        PIC X(8).
           05 SEG-LEVEL       PIC XX.
           05 STATUS-CODE     PIC XX.
           05 PROC-OPTIONS    PIC X(4).
           05 FILLER          PIC X(4).
           05 SEGMENT-NAME-FB PIC X(8).
           05 LENGTH-KEY-FB   PIC S9(5) COMP.
           05 NUM-SENSITIVES  PIC S9(5) COMP.
           05 KEY-FEEDBACK    PIC X(50).

       PROCEDURE DIVISION.
           DISPLAY "=== BEGIN: STUDENT RECORD UPDATE USING GHN ===".

           PERFORM UNTIL STATUS-CODE NOT = '  '
               CALL 'CBLTDLI' USING DLI-GHN,
                                    STUDENT-PCB,
                                    IO-AREA

             IF STATUS-CODE = '  '
               DISPLAY "STUDENT FOUND: " STUDENT-ID " - " STUDENT-NAME

                   MOVE NEW-NAME TO STUDENT-NAME

                   CALL 'CBLTDLI' USING DLI-REPL,
                                        STUDENT-PCB,
                                        IO-AREA

                   IF STATUS-CODE = '  '
                       DISPLAY "-- NAME UPDATED TO: " STUDENT-NAME
                   ELSE
                       DISPLAY "** REPL FAILED. STATUS = " STATUS-CODE
                   END-IF

               ELSE
                 IF STATUS-CODE = 'GB'
                    DISPLAY "** END OF DATABASE **"
                  ELSE
                    DISPLAY "** ERROR: STATUS = " STATUS-CODE
                 END-IF
             END-IF

           END-PERFORM.

           GOBACK.
    """
    results = IMSCobolChecker(cobol_prog).analyze_cobol()
    for res in results:
        print(res)
