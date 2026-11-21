import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
Lemma E (arithmetic core). Let `x` be an endpoint, `m` an origin with `r` odd and `k` even steps
(affine identity `2^(r+k) x = 3^r m + V` with numerator `V ≤ 2^k (3^r - 2^r)`), and `m'` an origin
of the same endpoint with `r+1` odd and `k` even steps (numerator `V' ≥ 3^(r+1) - 2^(r+1)`).
If `m ≥ 3 * 2^k - 4` then `m' < m`.
All quantities are integers; the numerator bounds are the formal-word envelope.
-/

theorem lemma_E (x m m' V V' : Int) (r k : Nat) (hk : 1 ≤ k)
    (h1 : 2 ^ (r + k) * x = 3 ^ r * m + V)
    (hV : V ≤ 2 ^ k * (3 ^ r - 2 ^ r))
    (h2 : 2 ^ (r + 1 + k) * x = 3 ^ (r + 1) * m' + V')
    (hV' : 3 ^ (r + 1) - 2 ^ (r + 1) ≤ V')
    (hm : 3 * 2 ^ k - 4 ≤ m) : m' < m := by
  have ha : (2 : Int) ≤ 2 ^ k := by
    calc (2 : Int) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hb : (0 : Int) < 3 ^ r := by positivity
  have hc : (0 : Int) < 2 ^ r := by positivity
  have e1 : (2 : Int) ^ (r + k) = 2 ^ r * 2 ^ k := pow_add 2 r k
  have e2 : (2 : Int) ^ (r + 1 + k) = 2 ^ r * 2 * 2 ^ k := by
    rw [pow_add, pow_succ]
  have e3 : (3 : Int) ^ (r + 1) = 3 ^ r * 3 := pow_succ 3 r
  have e4 : (2 : Int) ^ (r + 1) = 2 ^ r * 2 := pow_succ 2 r
  rw [e1] at h1
  rw [e2, e3] at h2
  rw [e3, e4] at hV'
  have hbm : 3 ^ r * (3 * 2 ^ k - 4) ≤ 3 ^ r * m := mul_le_mul_of_nonneg_left hm hb.le
  have hprod : 0 < (2 ^ k - 1 : Int) * (3 ^ r + 2 * 2 ^ r) := by
    apply mul_pos
    · linarith
    · positivity
  have key : 3 * 3 ^ r * m' < 3 * 3 ^ r * m := by
    nlinarith [hbm, hprod, h1, h2, hV, hV']
  have h3 : 0 < 3 * (3 : Int) ^ r := by positivity
  exact lt_of_mul_lt_mul_left key h3.le

/-- Corollary used in the finite monotonicity argument: the successor-count origin `m'` is
below every origin `m ≥ 3 * 2^k - 4` of the previous count. -/
theorem lemma_E_pos (x m m' V V' : Nat) (r k : Nat) (hk : 1 ≤ k)
    (h1 : 2 ^ (r + k) * x = 3 ^ r * m + V)
    (hV : V + 2 ^ k * 2 ^ r ≤ 2 ^ k * 3 ^ r)
    (h2 : 2 ^ (r + 1 + k) * x = 3 ^ (r + 1) * m' + V')
    (hV' : 3 ^ (r + 1) ≤ V' + 2 ^ (r + 1))
    (hm : 3 * 2 ^ k ≤ m + 4) : m' < m := by
  have := lemma_E (x : Int) (m : Int) (m' : Int) (V : Int) (V' : Int) r k hk
    (by exact_mod_cast h1) (by
      have : ((V + 2 ^ k * 2 ^ r : Nat) : Int) ≤ ((2 ^ k * 3 ^ r : Nat) : Int) := by exact_mod_cast hV
      push_cast at this
      linarith)
    (by exact_mod_cast h2) (by
      have : ((3 ^ (r + 1) : Nat) : Int) ≤ ((V' + 2 ^ (r + 1) : Nat) : Int) := by exact_mod_cast hV'
      push_cast at this
      linarith)
    (by
      have : ((3 * 2 ^ k : Nat) : Int) ≤ ((m + 4 : Nat) : Int) := by exact_mod_cast hm
      push_cast at this
      linarith)
  exact_mod_cast this
