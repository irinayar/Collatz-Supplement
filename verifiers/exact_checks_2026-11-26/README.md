# Exact checks added 26 November 2026

Environment: .NET SDK 9.0 (C#). Run from this folder with `dotnet run --project weighted_windows -c Release`.

| Program | Arguments | What it checks | Time, memory |
|---|---|---|---|
| `weighted_windows` | none | phase-localized weighted window capacity (44 odd inputs, charges 0/2/3, budget 28): reconstructs the 73 admissible (odd count, length) pairs below 10^12 and excludes 7 of them for a first coefficient crossing without descent, 8 when the odd inputs are distinct or for shortest direct ancestors (66, 65, 65 remain) | seconds, small memory |

All decisive comparisons are in exact integer or rational arithmetic. The program was run once from these files with the output above. It is a computer check of necessary conditions on a single trajectory: it uses crossing and suffix bounds proved elsewhere, does not show that any remaining pair occurs, says nothing about trajectories that never cross or about more than 10^12 odd steps, and does not prove the Collatz conjecture.
