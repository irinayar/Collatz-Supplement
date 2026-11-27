# Collatz supplement

Supplementary material for the Collatz manuscripts (version v8 onward) by Irina Yaroshevskaya: computational certificates, datasets, CRT inventories, packaged scripts and reproducibility instructions. The manuscript itself, research notes and audit reports are not part of this repository.

| Path | Contents |
|---|---|
| `datasets/` | Rule inventories, CRT inventories, family certificates, result files (JSON/log), with the original `tmp/...` structure |
| `scripts/ledger_scripts.zip` | Python accounting and checking scripts for the ledger (unzip into `datasets/` so `tmp/...` paths resolve) |
| `scripts/chatgpt_python_scripts.zip` | Independent Python check scripts written by ChatGPT, unchanged (463 files, grouped by source attachment) |
| `scripts/claude_csharp_programs.zip` | Check programs written by Claude (C#, 289 files) with `template.csproj` |
| `lean/` | Lean 4 formalization (11 modules: elementary lemmas, first-crossing horizon lemma, phase/run/cylinder identities, exact constants, explicit examples) with build script and README; and `CollatzMeetings.lean`, a further self-contained module on smaller-origin meeting families |
| `verifiers/` | PowerShell exact verifiers and a C# suite of exhaustive scans of the first-return band, with README (section 5 describes the K182-K190 Python checkers and certificates, which live in `datasets/` and `scripts/ledger_scripts.zip`) |
| `verifiers/exact_checks_2026-11-25/` | C# checks added 25 November 2026: equal-count displacements, smaller-origin rule families, ancestor and crossing bounds, certificate pullbacks and a residual counting model; see its README |
| `verifiers/exact_checks_2026-11-26/` | C# checks added 26 November 2026: first-crossing windows, the depth-41 ternary closure, smaller-origin and meeting families, union densities of the listed classes and equal-count checks; see its README |
| `verifiers/exact_checks_2026-11-27/` | C# checks added 27 November 2026: meeting families, count-layer and later-endpoint censuses, exclusions, local cell counts and fixed-base recounts; see its README |
| `REPLAY_INDEX_CURRENT_ARTICLES.md` | Which program verifies which section of the current articles |
| `REPRODUCE.md` | How to verify hashes and rerun the checks |
| `MANIFEST_SHA256.txt` | SHA-256 of every file except itself |

Densities reported with the ledger are natural densities of a named union of descent and conditional smaller-start rules, not percentages of integers certified to converge. Scripts are published as produced and are not audited line by line. Mathematical discussion, review and calculations were assisted by OpenAI's ChatGPT and Codex and Anthropic's Claude. License: MIT.
