# Exact checks added 25 November 2026

Environment: .NET SDK 9.0 (C#). No Python. Run each from this folder with `dotnet run --project <name> -c Release -- <arguments>`.
Each program was run once from these files before publication and reported no failed check. They are computer checks by one implementation each. They are not formal proofs, none proves the Collatz conjecture, and the measures they compute are conditional counting-model quantities, not densities of convergent integers.

| Program | Arguments | What it checks | Time |
|---|---|---|---|
| `carry_displacements` | none | equal-count displacement sets for 8 to 15 even steps (reverse closure, state counts), no positive partner through depth 17, stated word identities and meetings | 2-3 min |
| `zero_tail_template` | `data/finite_ledger_119.csv` | smaller-origin classes of the template 1^r (01)^s 0^(k+1); remaining conditional mass against the 119-rule ledger and one further rule | seconds |
| `expanding_ancestors_and_crossing` | `data/finite_ledger_119.csv` | expanding ancestor words through 14 odd steps, all-length tail bound, first coefficient crossing lower bounds, zero-tail height table | seconds |
| `direct_ancestors` | `data/affine_ledger_120.csv data/finite_ledger_119.csv` | 120 affine meeting certificates and their slope band, 73 admissible count pairs below 10^12, suffix envelope, finite origin check | seconds |
| `certificate_pullback` | `data/affine_ledger_120.csv` | 232 progressions obtained by pulling the certificates back through prefixes of length at most 12, with exact union measures (relative to the 120 certificate classes only) | seconds |
| `unbounded_valuation_examples` | none | actual equal-count meetings whose displacement is divisible by high powers of 3 | seconds |
| `residual_interval_certificate` | `data/residual_depth53_table.csv` | interval certification of limit bounds for a residual counting model (outward-rounded floating point, final sums exact rationals) | under 1 min |
| `residual_ratio_limit` | five census files, see below | the same model: exact recurrence to depth 10,000, floating-point recurrence and ratio tests | 1-2 min |

`residual_ratio_limit` takes, in order: `data/finite_ledger_119.csv`, `data/projected181.csv`, the six-even census `certificates_e0to6.csv`, the seven-even census `direct7.sorted`, and `data/residual821.csv`. The two census files are large and are NOT included here, so this program cannot be rerun from this repository alone. Their SHA-256 values are:
- certificates_e0to6.csv (91041101 bytes): `dd7cf37e38bec7e63b390051f943a8cf15cbc64a4faf95dd6946f77ece52ba0e`
- direct7.sorted (30626137 bytes): `6ed87dea77fb3756c04be42da9ae36ca589e8945288dc7ed91f2fbe1b262d790`

`data/residual_depth53_table.csv` was exported from that census computation; the interval certificate takes it as input.

## Added later: even budgets 16 to 19

| Program | Arguments | What it checks | Time, memory |
|---|---|---|---|
| `carry_budgets_16_17` | `15 16 17` | filtered equal-count displacement sets for the listed even budgets (bit-array reverse closure), with a replayed witness of maximal 3-adic valuation | seconds, under 1 GB |
| `carry_budget_18` | none | budgets 17 and 18 with a second, more compact layout; replays a budget-19 witness for displacement 3^8 | seconds, about 1 GB |
| `lift_seven_odd_steps` | none | an actual meeting behind seven odd steps (displacement 128) | seconds |
| `lift_eight_odd_steps` | none | an actual meeting behind eight odd steps (displacement 256) | seconds |

Budgets 8 to 15 are covered by `carry_displacements` above. Budgets up to 18 show no displacement divisible by 3^8, so the budget-19 witness shows that valuation 8 first occurs at 19. The full size of the budget-19 set is not checked by any program here.
