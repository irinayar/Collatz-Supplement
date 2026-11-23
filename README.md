# Collatz supplement

Supplementary material for the Collatz manuscripts (version v8 onward) by Irina Yaroshevskaya: computational certificates, datasets, CRT inventories, packaged scripts and reproducibility instructions. The manuscript itself, research notes and audit reports are not part of this repository.

| Path | Contents |
|---|---|
| `datasets/` | Rule inventories, CRT inventories, family certificates, result files (JSON/log), with the original `tmp/...` structure |
| `scripts/ledger_scripts.zip` | Python accounting and checking scripts for the ledger (unzip into `datasets/` so `tmp/...` paths resolve) |
| `scripts/chatgpt_python_scripts.zip` | Independent Python check scripts written by ChatGPT, unchanged (368 files, grouped by source attachment) |
| `scripts/claude_csharp_programs.zip` | Check programs written by Claude (C#, 233 files) with `template.csproj` |
| `lean/` | Lean 4 formalization (11 modules: elementary lemmas, first-crossing horizon lemma, phase/run/cylinder identities, exact constants, explicit examples) with build script and README |
| `verifiers/` | PowerShell exact verifiers and a C# suite of exhaustive scans of the first-return band, with README |
| `REPRODUCE.md` | How to verify hashes and rerun the checks |
| `MANIFEST_SHA256.txt` | SHA-256 of every file except itself |

Densities reported with the ledger are natural densities of a named union of descent and conditional smaller-start rules, not percentages of integers certified to converge. Scripts are published as produced and are not audited line by line. Mathematical discussion, review and calculations were assisted by OpenAI's ChatGPT and Codex and Anthropic's Claude. License: MIT.
