# Replay index for the current articles (24 November 2026)

Exact-arithmetic and brute-force programs written while preparing the current Collatz, Collatz II and Collatz III sources. All are in `scripts/claude_csharp_programs.zip` (C#, .NET 9; unzip, create an empty folder, copy `template.csproj` and the chosen `.cs` file as `Program.cs`, run `dotnet run -c Release`). Programs that take arguments say so in their first comment lines (`m86_early_meeting_scan`: `N bits`, e.g. `10000000 26`; `whitney_crossings_check`: `Lmax`, e.g. `21`). Status: run by their author; not independently re-run by a second party. Each program reproduces the exact numbers quoted in the article section named below.

| Program | Article section |
|---|---|
| `future_suffix_sector_bounds_check` | Collatz III, initial six-type and R/C sectors, contracting chains, union and residual arithmetic |
| `positive_alphabet_and_audit_corrections_check` | Collatz III, positive-alphabet masses, multiplicity construction, phase-bin envelope and selector corrections |
| `all_odd_forcing_window_bruteforce_check` | Collatz III, residue window for an all-odd prefix |
| `entrance_toll_cap13_triple_check` | Collatz III, toll 1/(120y), 86,332 exclusions, cap 13, genuine triple, toll limits, category-B cylinder |
| `exceptional_pair_law_bruteforce_check` | Collatz III, exceptional pair law |
| `cycle_bridge_replay_check`, `cycle_bridge_log_enclosure_check` | Collatz III, rotation identity, mechanical words, spread criterion, nonbalanced control |
| `interior_merger_exponent_gap_coalescence_check` | Collatz III, exponent gap, interior mergers, coalescence fixture |
| `closing_bridge_constants_check`, `mask_boundary_identity_check` | Collatz III, conditional bridge constants and mask-boundary identity |
| `payment_reassignment_arithmetic_check` | Collatz III, reassigned payment ledger arithmetic |
| `synchronous_meeting_elementary_bound_check`, `finite_base_meeting_thresholds_replay_check` | Collatz III, synchronous-meeting bounds (8673; 76,929,449; 586,464,555) |
| `fibre_residue_certificates_replay_check`, `early_synchronous_meeting_bruteforce_check` | Collatz III, inverse fibres, greedy failure, early synchronous-meeting theorem |
| `collatztwo_finite_certificates_replay_check` | Collatz II, finite-band, B_b and tail certificates |
| `periodic_word_realiser_lemma_check`, `q_set_b_mod_3m_compositions_replay_check` | Collatz II, realiser size and Q-numbers |
| `monotonicity_dfs_k6_9_check`, `valuation_reduction_threshold_check` | Collatz II, minimum-origin monotonicity data and valuation reductions |
| `crude_cycle_inequality_vs_2pow71_check`, `m86_early_meeting_scan`, `whitney_crossings_check` | Collatz, further finite observations |

## Added: later finite claims (24 November 2026)

Each C# program below that uses exact fractions must be compiled together with `replay_fraction_type.cs`. The path argument of the first two is the `datasets/tmp` folder (after cloning); `first_gate_1900_fixture_replay` takes `datasets/tmp/first_phase_gate`.

| Program | Article section and data |
|---|---|
| `k194_moment_bellman_histogram_replay` | Collatz III, K194 moment certificate (3553 cells, 21621 branches), constant C64, phase and late-sector constants, run mass, population maxima, inverse-residue histogram; data `datasets/tmp/collatz_three_v4/` |
| `k196_latecap_stopped_occurrence_replay` | Collatz III, 321 saved-prefix cap checks (120 improvements), 18 high-floor profiles, occurrence budget; data `datasets/tmp/compensation_packet_audit/`, `singleton_charge_bounds/`, `unresolved_phase_caps/`, `occurrence_budget/` |
| `first_gate_1900_fixture_replay` | Collatz III, 1900 small-band profiles, 19 credit inequalities, high-floor suffix fixture; data `datasets/tmp/first_phase_gate/` |
| `k166_screen_fibre_replay` (argument: `datasets/tmp/numerator_code_audit/audit.json`) | Collatz II, K166 screen (947 prefixes, 19 in the strip) and thirteen inverse fibres; data `datasets/tmp/joint_strip_fibre/` |
| `arc292_exact_count_replay` | Collatz III, the bound of 292 sources at a unit gate |
| `monotonicity_finite_proof_check` (argument 19), `monotonicity_packed_table_check_improved_threshold` (arguments k and table bits), `exact_max_G_and_range` (argument 1073741821) | Collatz II, strict monotonicity through k = 19 for all endpoints, through k = 28 for x >= 3, and the separation range to 2^30 - 3 |
| `six_even_census_independent_check`, `six_even_placement_rules_check`, `seven_even_census_independent_check`, `six_seven_overlay_bounds_check` | Collatz, local six- and seven-even censuses and their overlay. Their large census data files are not stored in this repository |

The Python checkers supplied for these claims are in `scripts/ledger_scripts.zip` under their `tmp/...` paths; several of them execute the resource-limit header of `tmp/k2_overlap/audit.py`. The C# programs reimplement the same algorithms on the same inputs: they check arithmetic and transcription, not the design of the arguments, and imported theorems (the uniform source count) are not re-proved. Not included: the uniform-complement producer certificate (only its reconstruction exists) and the local census data files.
