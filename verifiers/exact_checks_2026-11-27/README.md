# Exact checks added 27 November 2026

Environment: .NET SDK 9.0 (C#). Run from this folder with `dotnet run --project <name> -c Release -- data`.

| Program | What it checks |
|---|---|
| `families_closure_and_census` | odd-count cap table at depth 41; closure on twenty-one source words and four target count profiles; five-even and six-even classifications; later-endpoint census at endpoints 6 to 18; delayed and fixed-base families; certified-base counts; local union fractions; logarithmic-strip constants; the 48 six-even and 21 complementary family rows |
| `offsets_activations_and_controls` | count-layer offsets and the split of the minimum-six cells; first activations; exclusion of listed progressions from 501 domains; local stage cell counts; continuation count controls |
| `fixed_base_recount` | fixed-base affordable starts at endpoint seven for even budgets 5 to 8, and the cumulative unions through endpoints 13 (budget 5) and 11 (budget 8) |

Each program runs in seconds with small memory and prints one line per check and a total number of failures.

Not covered here: the per-word numbers of integral offsets in the four target count profiles, and the earlier theorems on which the logarithmic-strip and cover arguments rely.

The Lean 4 module `lean/CollatzMeetings.lean` (core Lean 4.35.0, no Mathlib, no `sorry`) certifies the 151 listed smaller-origin meeting families for every parameter, the two families with unbounded source time, and several integer comparisons. Check it with `lean CollatzMeetings.lean`.

All comparisons are exact. These are finite computations and conditional smaller-origin statements; nothing here shows that every integer is covered, and nothing proves the Collatz conjecture.
