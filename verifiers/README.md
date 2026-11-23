# Verifiers: exact checks and exhaustive scans

Environment: Windows PowerShell 5.1 and the .NET 8 SDK. No Python is needed. The Lean modules are in `../lean`.

## 1. Exact verifiers (`powershell/`)
Run all: `powershell -NoProfile -File powershell/run_all.ps1` (about 2-3 minutes).

| Script | Checks |
|---|---|
| `verify_constants.ps1` | 29 exact comparisons with big-integer rationals (mirrors `CollatzConstants.lean`); ends with `ALL PASS` |
| `verify_k179_residue_tree.ps1` | the 32,768-leaf residue tree of the mixed pairs: all residues distinct, minimum at mask 25847 equals the stated `m15`, and `3*56*m15*7153 >= 1669158*(4(2^256-1)+1)` |
| `verify_80bit_example.ps1` | rebuilds the 80-bit nonempty-core return: 121 odd transitions, 192 steps, 54 resets, phase 13.7327, least source of its cylinder, 5321822482652343082370 thresholds |
| `verify_cylinders_and_repetition.ps1` | the cylinders `43 mod 64` and `379 mod 512`, the polynomial shifts, and the repetition criterion `k_max = floor((v2(Z)-1)/E)` on 20,000 starts |
| `verify_k180_words.ps1` | the six balanced four-block words: offsets `B`, multiplier sums `C0`, coefficients `K_word` |

PowerShell variable names are case-insensitive; the scripts use distinct names.

## 2. Exhaustive scans of the first-return band (`CollatzChecks/`, C#)
`cd CollatzChecks; dotnet build -c Release; dotnet run -c Release --no-build -- <check> <args>` with `<check>` one of:
`qgscan N`, `qgrecords N`, `tail n...`, `allsource n...`, `runs174 n...`, `runs176 n...`, `toll n...`, `census range N` / `census single n...`,
`relaxedcore n QMIN`, `lastexp n...`, `collision n...`, `stopdp t...`. Each examines all odd sources of the band at the given thresholds
(total phase tails, all-source charge, run-level inequalities, signed budget, relaxed core, last-exponent law, collisions, stopping-code weights).
Thresholds up to `1e8` take seconds, `1e9` about 10-25 seconds, `1e10` about 1.5-4 minutes. These are finite computations below `2^71`:
observations, not theorems, and none is used as a bound in the reductions.

## 3. K180 balanced four-block words: checker and certificate
- `datasets/tmp/balanced_pair_audit/audit.json`, `checkpoint.json`, `saved_tests.json`: the certificates of the exhaustive depth-8 residue tree (6^8 = 1,679,616 codes), the six-word table and the saved-trajectory tests.
- `scripts/ledger_scripts.zip` contains `tmp/balanced_check.py` (exhaustive checker; imports the guard prefix of `tmp/k2_overlap/audit.py`, which is in the same archive) and `tmp/balanced_saved_check.py`; unzip into `datasets/` so the `tmp/...` paths resolve, then run from `datasets/`: `python tmp/balanced_check.py`.
- An independently written C# check of the same tree: `verifiers/CollatzChecks` subcommand `k180tree 8` (about 7 seconds; all 1,679,616 residues distinct, minimum residue `21346342495854702470833795683269374440106412456159662460927218553844507600380763285371` at code `[2, 4, 4, 1, 4, 4, 2, 0]`, and `3*56*m8*7551629537 >= 1814421282246*(4(2^272-1)+1)`). The inequality is claimed only from depth 8 on (a smaller depth reports `False`, as expected).
- `verifiers/powershell/verify_k180_words.ps1`: the six words (offsets `B`, sums `C0`, coefficients `K_word`).

## 4. K181 aggregate signed compensation: checks and certificates
- `datasets/tmp/compensation_packet_audit/input/`: the inputs (`exact_compensation_seeds.json`, `source_cylinder_controls.json`) and the exact certificates (`exact_signed_compensation_certificate.json`, `source_cylinder_carleson_certificate.json`) of the two standalone verifiers; `datasets/tmp/compensation_packet_audit/audit.json` is the reproduction report (regenerated certificates equal the supplied ones after newline normalization).
- `scripts/ledger_scripts.zip` contains `tmp/compensation_packet_audit/input/verify_exact_signed_compensation.py`, `verify_source_cylinder_carleson.py`, `exact_compensation_profile_support.py` (unzip into `datasets/`; run each from its folder, optionally with `--output result.json`) and the reproduction driver `tmp/compensation_packet_check.py` (its input archive of the original packet is not published; the driver documents the comparison method).
- Independent checks written separately: `verifiers/CollatzChecks` subcommand `k181 n...` (all runs of all genuine returns: `f <= delta`, telescoping, the exact identity `kappa W_U = R_U + D_F + sum_off f`, criterion (14) for positive credit, inequality (15) for single-input runs) and `verifiers/powershell/verify_k181_constants.ps1` (exact constants `2797/200`, `73485/3904`, `3000/2797`, `8850/170617`, `1837125/1364936`, `Y* = 116073/3904000`, `4899/3904`).
- Not published: the six-note homogeneous audit (its provenance names internal review files) and the chronological signed-cover certificates of that audit. The unrestricted targets `Z <= 116073/3904000` and its relaxed form are not proved.
