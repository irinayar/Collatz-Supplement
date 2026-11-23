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
