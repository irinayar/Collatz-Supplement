# Lean 4 formalization of elementary Collatz lemmas

`CollatzElementary.lean` (Lean 4.35.0 with Mathlib). Imports only `Mathlib.Tactic.Ring`, `Linarith`, `Positivity`, `RingTheory.Coprime.Basic` and `RingTheory.Coprime.Lemmas` (`import Mathlib.Tactic` is much slower). Check with `./check_lean.sh CollatzElementary.lean` after setting `LEAN` (path of the lean executable) and `MATHLIB_PACKAGES` (directory containing the compiled `mathlib`, `batteries`, `aesop`, `Qq`, `plausible`, `LeanSearchClient`, `importGraph`, `proofwidgets` packages). Result: exit code 0, no `sorry`, no warnings; each theorem depends only on `propext`, `Classical.choice`, `Quot.sound`.

| Lean theorem | Statement |
|---|---|
| `T_growth`, `Tit_growth` | `2 (T x + 1) <= 3 (x + 1)`; `2^j (T^j x + 1) <= 3^j (x + 1)` |
| `T_odd_mod3`, `T_odd`, `T_even` | an odd input maps to 2 mod 3; the two branches |
| `T_collision` | `T x = T y`, `x != y` implies `{x, y} = {odd x, 3x+1}` |
| `Tit_fibre_mult3` | `3 | y` and `T^j x = y` imply `x = 2^j y` |
| `Tit_allodd`, `allodd_barrier` | `T^j(2^j t - 1) + 1 = 3^j t`; every `m < 2^j t - 1` has `T^j m < T^j(2^j t - 1)` |
| `Tit_congr`, `Tit_gap` | equal parity bits of the first `L` steps imply `2^L | x - y`; distinct `x < y` differ by at least `2^L` |
| `product_factor` | `(3x+1)^6 (x-1) < 729 x^6 (x+1)` for `x >= 2` |
| `Tit_affine`, `Tit_lower` | `2^j T^j x = 3^a x + U`; `3^a x <= 2^j T^j x` |
| `allodd_run_dvd`, `allodd_run_le` | `j` consecutive odd steps from `n` force `2^j | n+1` and `2^j <= n+1` |
| `Tit_add` | `T^(m+n) x = T^n (T^m x)` |
| `defect_rec`, `defect_dvd`, `block_defect_collatz` | repeated-block defect: `B^k | D` for a repeated block |
| `lemma_E`, `lemma_E_pos` (`LemmaE.lean`) | arithmetic core of the successor-count inequality: from `2^(r+k) x = 3^r m + V`, `V <= 2^k (3^r - 2^r)`, `2^(r+1+k) x = 3^(r+1) m' + V'`, `V' >= 3^(r+1) - 2^(r+1)` and `m >= 3 * 2^k - 4` follows `m' < m` (integers; natural-number version without subtraction) |

Not formalized: the telescoping of the product bound over distinct odd states, the lower barrier on the odd-step count, the tradeoff theorem, the numerator dynamic programs, the numerator envelope for parity words, the finite enumerations behind the fixed-even-budget monotonicity statements and the density results.
