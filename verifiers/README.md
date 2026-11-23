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

## 5. K182-K190 checks and certificates (aggregate tail, short-run occupation, source counts, prefix capacities, singleton charge and phase caps, occurrence budget)
- Uniform long-run aggregate tail (K182/K183): `datasets/tmp/uniform_aggregate_audit/input/uniform_long_run_tail_certificate.json` and `endpoint_potential_obstruction_certificate.json` are the exact certificates of the two standalone verifiers `tmp/uniform_aggregate_audit/input/verify_uniform_long_run_tail.py` and `verify_endpoint_potential_obstruction.py` (in `scripts/ledger_scripts.zip`; unzip into `datasets/`, run each with `--output result.json` and compare with the certificate after newline normalization). `tmp/uniform_aggregate_audit/shifted_tail_check.py` writes `shifted_tail_checks.json` (the shifted-cutoff count rows and the exact maximum).
- Finite exact checks of the later notes, each a standalone Python checker `tmp/<name>/check.py` (standard library only; they import the exact profile replay `tmp/compensation_packet_audit/input/exact_compensation_profile_support.py` and the guard prefix of `tmp/k2_overlap/audit.py`, both in the same archive) with the result file `tmp/<name>/checks.json`:

| Folder | Note | Content |
|---|---|---|
| `short_run_occupation` | K184 | exact R-charge and short-run occupation on the saved profiles |
| `short_source_counts` | K185 | exact source counts for two and three phase-eligible core (2,2) occurrences |
| `shared_prefix_counts` | K186 | shared-prefix capacities and the return-height horizon |
| `singleton_charge_bounds` | K187 | phase potential with last-run overshoot on the saved singleton survivors |
| `unresolved_phase_caps` | K188 | prefix-only eventual-phase caps, including the unresolved source `u = 2^256 - 1` |
| `topological_capacity` | K189 | prefix-partition and refinement checks on finite source fibres, the symmetric-difference metric, the binary-mass countermodel (reads `unresolved_phase_caps/checks.json`) |
| `occurrence_budget` | K190 | direct charge bound `gamma*b` and the necessary-cost filter |

  Run order (each reads earlier result files): `short_source_counts`, `shared_prefix_counts`, `singleton_charge_bounds`, `unresolved_phase_caps`, `topological_capacity`, `occurrence_budget`; run from `datasets/`: `python tmp/<name>/check.py`. The checkers carry hardware-limit preambles (1 GiB, 120 s).
- Independent C# checks of some of these statements are in `scripts/claude_csharp_programs.zip` (for example `k186_horizon_check`, `k187_potential_check`, `k188_singleton_cap_check`, `k190_direct_charge_check`).
- All of these are finite exact computations on saved or constructed sources; they are not proofs of the uniform aggregate bound, which remains open. Internal audit reports and note-level provenance are not published.
