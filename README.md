This repository is an appendix for the **Beyond Blind Spots: Analytic Hints for Mitigating LLM-Based Evaluation Pitfalls** paper.

It contains the following supplementary information:

**analytic_plugin dir** - contains the code of the analytic plugin, whose outputs have been injected into the prompts of the "judge-with-hints".

**nl2c_judge_propmts dir** - contains the prompts for the 3 types of judges we ran in the paper:
 - *nl2c_laaj_no_issues.txt* - the prompt of the native judge, without analytic hints.
 - *nl2c_laaj_analytic_issues_naive.txt* - the naive prompt of the judge with analytic hints.
 - *nl2c_laaj_analytic_issues_best.txt* - the optimized prompt of the judge with analytic hints.

**test_set dir** - contains the dataset used in the paper and the prompts used to generate it.
 - *cobol_instruction_pairs.xlsx* - contains the (instructions, cobol) pairs used in the paper. The cobol code has been generated from the instructions.
 - *code_gen.txt* - the prompt used to generate the cobol code from the instructions.
