# Lean 4 formalization of the Collatz lemmas (11 modules)

Lean 4.35.0 with Mathlib (specific imports only; `import Mathlib.Tactic` is too slow for these checks). Every module compiles with exit code 0, no `sorry`,
and every theorem depends only on `propext`, `Classical.choice`, `Quot.sound` (some on fewer; `#print axioms` lines are at the end of the files).

Build everything from scratch in dependency order (about 4 minutes): `LEAN=/path/to/lean MATHLIB_PACKAGES=/path/to/.lake/packages ./build_all.sh`
(oleans in `./build`, logs `build_<Module>.log`). A single module (earlier modules built first): `... ./build_all.sh CollatzCrossing`.
`check_lean.sh` checks one file that imports only Mathlib (e.g. `CollatzSeparation.lean`).

Dependency order: `CollatzElementary` -> {`CollatzSeparation`, `LemmaE`, `CollatzCrossing`, `CollatzPhase`} -> `CollatzFirstReturn` -> `CollatzExamples`;
independent of Elementary: `CollatzConstants`, `CollatzRuns`, `CollatzCylinders`, `CollatzSpend`.

| Module | Content |
|---|---|
| `CollatzElementary` | `T`, `Tit`, `oddc`, `numr`; growth bounds, `T_collision`, fibres, all-odd barrier, repeat rigidity (`Tit_congr`, `Tit_gap`), `product_factor`, `Tit_affine`, `Tit_add`, block defect divisibility |
| `CollatzSeparation` | origin slope / separation lemmas, `block_identity`, `block_absorb`, `periodic_word_dvd` |
| `LemmaE` | arithmetic core of the successor-count inequality (`lemma_E`, `lemma_E_pos`) |
| `CollatzCrossing` | horizon lemma `crossing_descent`: if the coefficient has not crossed before step `j`, crosses at `j`, and `a 2^j < 3n(2^j - 3^a)`, then `T^j n < n`; `bernoulli_nat`, `state_ge`, `correction_bound` (integer form of `G <= (1+1/(3n))^a`) |
| `CollatzPhase` | phase `Q_i = U_i/3^(a_i)`: `phase_affine`, `phase_step_odd/even`, `phase_mono`, correction product `phase_prod`, `rho_formula`, `rho_nonpos_Q_lt_five`, signed flux `flux_step/flux_sum`, `numr_not_dvd_three` |
| `CollatzRuns` | maximal runs: `xr`, exact correction `run_correction`, `run_output`, `run_b_le`, signed budget `psi_bound` (`a psi <= [2-3z]_+`), `psi_single`, `expanding_growth` (`b/a >= 9/8`), `expanding_psi` (`psi <= 6(1/a-1/b)`), `Kcoef_antitone`, `block_bound` |
| `CollatzCylinders` | one power of two in a window of ratio < 2, `residue_spacing`, `cylinder_odd_arrival`, `cylinder_unique_mod`, `first_exponent_one`, explicit blocks `blockA1`/`blockA2`, polynomial certificates, mixed pairs `pair_du`/`pair_ud`/`pair_expands` |
| `CollatzSpend` | `span_telescope`, `span_budget`, `weighted_sum_le`, `split_identity`, `split_nonneg`, `window_count`, `central_mass_bound` |
| `CollatzFirstReturn` | `Genuine n u j`; `genuine_unique_length`, `genuine_states_distinct`, `genuine_source_odd`, `genuine_source_mod4`, `genuine_of_bounds` |
| `CollatzConstants` | every exact numeric comparison (`norm_num`): `3^99 < 2^160`, `3000^22 < 2^256`, `4*193^39 < 200^39`, the 21/125 allocations, `159c < T < 160c`, the mixed-sector inequality, the K3/K4/K(e=3)/K(two shorts) coefficients, the K179 constants, the exponential majorant `< 367/250`, and the real-log certificate `log(47/32) > 189480/493039` |
| `CollatzExamples` | by `decide +kernel`: the 80-bit nonempty-core return is a genuine first return for all 5321822482652343082370 odd thresholds in its interval with phase `> 13`; the g = 46 high-phase witness (phase `> 11`); the n = 55 control |

Not formalized: the canonical packing computation (7.9 million groups; external exact certificate), the finite bases, the profile-count theorems, and the unproved aggregate bounds.
The exact and numerical counterparts are in `../verifiers`.

## CollatzMeetings.lean (added 27 November 2026)

A self-contained module using core Lean 4.35.0 only (no Mathlib); check it with `lean CollatzMeetings.lean` (a few seconds). No `sorry`, no `native_decide`, no added axioms; the `#print axioms` lines at the end show at most `propext` and `Quot.sound`.

It proves that a finite check at the base values certifies a meeting family `T^k(n0 + N h) = T^l(m0 + M h)` with `0 < m < n` and fixed parity words for every `h`; applies this to 151 listed families (`all_families`); proves two families with the common partner `m = 717 + 729 h` at arbitrarily late source times, for every length of the intervening odd run (`delayed_short`, `delayed_long`); and records even padding and several integer comparisons. It does not show that every integer lies in a family, and it does not formalize any census, density or analytic bound.
