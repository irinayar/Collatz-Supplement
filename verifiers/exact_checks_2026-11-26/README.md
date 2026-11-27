# Exact checks added 26 November 2026

Environment: .NET SDK 9.0 (C#). Run from this folder with `dotnet run --project weighted_windows -c Release`.

| Program | Arguments | What it checks | Time, memory |
|---|---|---|---|
| `weighted_windows` | none | phase-localized weighted window capacity (44 odd inputs, charges 0/2/3, budget 28): reconstructs the 73 admissible (odd count, length) pairs below 10^12 and excludes 7 of them for a first coefficient crossing without descent, 8 when the odd inputs are distinct or for shortest direct ancestors (66, 65, 65 remain) | seconds, small memory |

All decisive comparisons are in exact integer or rational arithmetic. The program was run once from these files with the output above. It is a computer check of necessary conditions on a single trajectory: it uses crossing and suffix bounds proved elsewhere, does not show that any remaining pair occurs, says nothing about trajectories that never cross or about more than 10^12 odd steps, and does not prove the Collatz conjecture.

## Further checks added 26 November 2026

Environment: .NET SDK 9.0 (C#). Run from this folder with `dotnet run --project <name> -c Release -- <arguments>`.

Several programs read the depth-41 classification of the residue `103 mod 8192` (128 MB). It is not stored here. Create it first; the program writes the file when it is absent and then compares it with its own computation:

    dotnet run --project regen_predecessor_labels -c Release -- labels.bin

In the table, `data/...` files are in the `data` folder. `UNION` stands for `data/finite_ledger_119.csv data/parents27.txt labels.bin data/previous_cylinders.csv data/pullbacks.txt`.

| Program | Arguments | What it checks | Time, peak memory |
|---|---|---|---|
| `regen_predecessor_labels` | `labels.bin` | predecessor labels (budgets 0 to 9) for the `2^28` sources `103 + 8192 i` at depth 41 | 19 s, 550 MB |
| `ternary_closure_check` | `data/ternary_classes.csv` | slope table and direct search of smaller origins on full periods of ternary lifts | 14 s, small |
| `ternary_masks` | `labels.bin data/finite_ledger_119.csv data/previous_cylinders.csv data/projected181.csv` | exact ternary witness masks and what remains after the finite mixed rules | 40 s, 170 MB |
| `ternary_structure_check` | `labels.bin data/finite_ledger_119.csv` | witness sets against translates of the expanding-ancestor sets | 7 s, 170 MB |
| `mod81_minima_check` | none | minimum origins at the endpoints 4 and 5 modulo 81 | 2 s, 730 MB |
| `companion_rule_marginal` | `data/finite_ledger_119.csv data/parents27.txt` | the family `n = 2247 + 2592 h` and its exact added density at depths 32 and 100 | 1 s, small |
| `companion_rule_bruteforce32` | `data/finite_ledger_119.csv data/parents27.txt` | the depth-32 value of the previous line by direct enumeration | 6 s, small |
| `prefix5_families_check` | `data/prefix5_families.csv data/finite_ledger_119.csv` | the 59 five-step meeting families | 1 s, small |
| `c44_ledger_contribution` | `data/finite_ledger_119.csv data/parents27.txt data/prefix5_families.csv` | the inverse-word catalogue behind `1101` and `11101` and its part on multiples of 3 | 1 s, small |
| `meeting_families_check` | `data/meetings22.csv` | 22 further meeting families: parity words, common values and the identity giving all parameters | 1 s, small |
| `union_ledger` | `UNION data/meetings22_union_cylinders.csv` | union densities of the listed classes at depths 32 and 100, row by row | 44 s, 200 MB |
| `union_ledger_c44_only` | `UNION` | the earlier ledger with only the inverse-word catalogue added | 1 s, 180 MB |
| `union_sampling_depth32` | `UNION` | random sample of `4*10^7` integers at depth 32 | 14 s, 180 MB |
| `union_sampling_depth100` | `UNION` | random sample of `8*10^8` integers at depth 100 | 3 min, 180 MB |
| `carry_pruned_budget19` | `19` | filtered equal-count displacement set for even budget 19, dead states pruned | 7 s, 660 MB |
| `carry_reverse_pruned_control` | none | the pruned method against the unpruned counts for budgets 2 to 10 | 1 s, small |
| `carry_cylinder_test` | none | random test of the carry-cylinder identities | 1 s, small |

Data files: `finite_ledger_119.csv` and `projected181.csv` are the files of the same content from 25 November; `parents27.txt` lists the depth-27 parent residues; `previous_cylinders.csv` the cylinders of earlier equal-count transfer certificates; `pullbacks.txt` the pullback progressions as modulus, residue; `prefix5_families.csv`, `meetings22.csv` and `meetings22_union_cylinders.csv` the families; `ternary_classes.csv` sixteen test classes.

`union_ledger` cuts the all-length initial-run rule at the stated depth. At depth 32 this lowers its values by about `1.2*10^-8` percentage points, so its baseline reads `99.5965842902%` where the complete rule gives `99.5965843025%`; the seven printed decimals of the later rows are not affected at the values reported.

All exact comparisons are in integer or rational arithmetic; the two sampling programs are statistical checks. The densities are of integers covered by coefficient crossing within the stated depth or by a conditional induction rule. They depend on the depth and are not proportions of integers proved to converge, and nothing here proves the Collatz conjecture.
