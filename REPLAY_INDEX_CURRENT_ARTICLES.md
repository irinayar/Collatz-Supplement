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

Not included: the large certificates of the K194 Bellman/moment result, the 18-profile histogram, the 1,900 small-band checks, the cap improvements of K195-K201, and the enumerations of the minimum-origin monotonicity through k = 19 and k = 28; their evidence is not yet packaged here and the articles label them accordingly.
