import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Coprime.Lemmas

/-!
Arithmetic cores of the 2026-11-21 separation/slope results (all elementary, no `sorry`).

Conventions: an origin `m` of an endpoint `z` with `k` even and `r` odd accelerated steps satisfies the
affine identity `2^(k+r) z = 3^r m + V` with numerator `V` (`V > 0` when `r ≥ 1`, and
`V ≤ 2^k (3^r - 2^r)` always).

* `origin_slope_lt`      (Lemma S)  any origin with `R ≥ 1` odd steps lies strictly below `2^(K+R) z / 3^R`.
* `origin_smaller_of_product`        `m < n` whenever the source product `G = 2^L z / (3^r n)` is below the
                                     profile threshold, in cross-multiplied form.
* `separation_of_product_lt`         the `G < 3/2` separation criterion (K100/K122 form).
* `separation_early_range`           separation for every `k` when `2^r (x+3) > 3^(r+1)`.
* `block_identity`, `block_absorb`   the block potential identity and absorption (K126/K129): for an expanding
                                     block `z = (a y + B)/d`, `G = (1 + c/y)/(1 + c/z)` and for `c ≤ C`,
                                     `G (1 + C/z) ≤ 1 + C/y` when `y ≤ z`.
* `periodic_word_dvd`                repeated-word divisibility `2^(e+1) ∣ D x - U` (Lemma P').
-/

/-- Lemma S: a positive numerator forces `3^R m < 2^(K+R) z`. -/
theorem origin_slope_lt (z m V : Nat) (K R : Nat)
    (h : 2 ^ (K + R) * z = 3 ^ R * m + V) (hV : 0 < V) :
    3 ^ R * m < 2 ^ (K + R) * z := by
  omega

/-- A source `n` (counts `k`, `r`, endpoint `z`) and a target origin `m` of the same endpoint with
profile `(k + dk, r + dr)`: if `2^(dk+dr) * 2^(k+r) z < 3^(r+dr) n` (i.e. `G < 3^dr / 2^(dk+dr)`),
then `m < n`. -/
theorem origin_smaller_of_product (z n m V : Nat) (k r dk dr : Nat)
    (h : 2 ^ (k + dk + (r + dr)) * z = 3 ^ (r + dr) * m + V) (hV : 0 < V)
    (hG : 2 ^ (dk + dr) * (2 ^ (k + r) * z) < 3 ^ (r + dr) * n) : m < n := by
  have e : 2 ^ (k + dk + (r + dr)) = 2 ^ (dk + dr) * 2 ^ (k + r) := by
    rw [← pow_add]; congr 1; omega
  have h1 : 3 ^ (r + dr) * m < 2 ^ (dk + dr) * (2 ^ (k + r) * z) := by
    rw [e] at h
    have : 2 ^ (dk + dr) * (2 ^ (k + r) * z) = 3 ^ (r + dr) * m + V := by
      rw [← h]; ring
    omega
  have h2 : 3 ^ (r + dr) * m < 3 ^ (r + dr) * n := lt_trans h1 hG
  exact Nat.lt_of_mul_lt_mul_left h2

/-- Separation from the product barrier: `G < 3/2` for the old origin `m` (written
`2 * 2^(k+r) z < 3 * 3^r m`) forces every successor origin `m'` (`r+1` odd steps, same `k`) below `m`. -/
theorem separation_of_product_lt (z m m' V' : Nat) (k r : Nat)
    (h2 : 2 ^ (k + (r + 1)) * z = 3 ^ (r + 1) * m' + V') (hV' : 0 < V')
    (hG : 2 * (2 ^ (k + r) * z) < 3 * (3 ^ r * m)) : m' < m := by
  have := origin_smaller_of_product z m m' V' k r 0 1 (by simpa using h2) hV'
    (by simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hG)
  exact this

/-- Early range: if `2^r (x+3) > 3^(r+1)` then, for every `k`, every origin `m'` with `r+1` odd steps
is below every origin `m` with `r` odd steps (numerator envelope `V ≤ 2^k (3^r - 2^r)`). -/
theorem separation_early_range (x m m' V V' : Nat) (k r : Nat)
    (h1 : 2 ^ (r + k) * x = 3 ^ r * m + V)
    (hV : V + 2 ^ k * 2 ^ r ≤ 2 ^ k * 3 ^ r)
    (h2 : 2 ^ (r + 1 + k) * x = 3 ^ (r + 1) * m' + V') (hV' : 0 < V')
    (hearly : 3 ^ (r + 1) < 2 ^ r * (x + 3)) : m' < m := by
  have hpos2 : 0 < 2 ^ k := by positivity
  -- 3^(r+1) m ≥ 3 (2^(r+k) x - 2^k (3^r - 2^r)) and this exceeds 2^(r+1+k) x
  have key : 2 ^ (r + 1 + k) * x < 3 ^ (r + 1) * m := by
    have e1 : (2 : Nat) ^ (r + k) = 2 ^ r * 2 ^ k := pow_add 2 r k
    have e2 : (2 : Nat) ^ (r + 1 + k) = 2 ^ r * 2 * 2 ^ k := by rw [pow_add, pow_succ]
    have e3 : (3 : Nat) ^ (r + 1) = 3 ^ r * 3 := pow_succ 3 r
    rw [e1] at h1
    rw [e2]; rw [e3] at hearly ⊢
    have hmul : 2 ^ k * (3 ^ r * 3) < 2 ^ k * (2 ^ r * (x + 3)) :=
      Nat.mul_lt_mul_of_pos_left hearly hpos2
    nlinarith [h1, hV, hmul]
  have : 3 ^ (r + 1) * m' < 3 ^ (r + 1) * m := by
    have : 2 ^ (r + 1 + k) * x = 3 ^ (r + 1) * m' + V' := h2
    omega
  exact Nat.lt_of_mul_lt_mul_left this

/-- Block identity: if `z d = a y + B`, `c (a - d) = B`, `0 < y`, `0 < z`, `0 < a`, `0 < c`
then `d z / (a y) = (1 + c/y) / (1 + c/z)` over `ℚ`. -/
theorem block_identity (a d B y z c : ℚ) (hy : 0 < y) (hz : 0 < z) (ha : 0 < a) (hc : 0 < c)
    (hz' : z * d = a * y + B) (hcB : c * (a - d) = B) :
    d * z / (a * y) = (1 + c / y) / (1 + c / z) := by
  have hzc : 0 < z + c := by linarith
  have hd : d * (z + c) = a * (y + c) := by nlinarith [hz', hcB]
  have hyc : 0 < y + c := by linarith
  have hd0 : 0 < d := by
    by_contra hneg
    have hneg : d ≤ 0 := not_lt.mp hneg
    have : d * (z + c) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hzc.le
    have : 0 < a * (y + c) := mul_pos ha hyc
    linarith
  field_simp
  nlinarith [hd]

/-- Absorption: for `0 < y ≤ z` and `0 < c ≤ C`, `(1 + c/y)/(1 + c/z) * (1 + C/z) ≤ 1 + C/y`. -/
theorem block_absorb (y z c C : ℚ) (hy : 0 < y) (hyz : y ≤ z) (hc : 0 < c) (hcC : c ≤ C) :
    (1 + c / y) / (1 + c / z) * (1 + C / z) ≤ 1 + C / y := by
  have hz : 0 < z := lt_of_lt_of_le hy hyz
  have hC : 0 < C := lt_of_lt_of_le hc hcC
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have e1 : (1 + c / y) * (1 + C / z) = (y + c) * (z + C) / (y * z) := by field_simp
  have e2 : (1 + C / y) * (1 + c / z) = (y + C) * (z + c) / (y * z) := by field_simp
  rw [e1, e2]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [mul_nonneg (sub_nonneg.mpr hcC) (sub_nonneg.mpr hyz)]

/-- Repeated-word divisibility (Lemma P'): if `2^e (D y - U) = p (D x - U)` with `p, D, U, y` odd
(`e = E N` for `N` repetitions of a word of total valuation `E`) then `2^(e+1) ∣ D x - U`. -/
theorem periodic_word_dvd (D U x y p : Int) (e : Nat)
    (h : (2 : Int) ^ e * (D * y - U) = p * (D * x - U))
    (hp : Odd p) (hD : Odd D) (hU : Odd U) (hy : Odd y) :
    (2 : Int) ^ (e + 1) ∣ D * x - U := by
  have hDy : Odd (D * y) := hD.mul hy
  have heven : (2 : Int) ∣ D * y - U := by
    obtain ⟨a, ha⟩ := hDy
    obtain ⟨b, hb⟩ := hU
    exact ⟨a - b, by omega⟩
  have h1 : (2 : Int) ^ (e + 1) ∣ p * (D * x - U) := by
    rw [← h, pow_succ]
    obtain ⟨t, ht⟩ := heven
    exact ⟨t, by rw [ht]; ring⟩
  have hcop : IsCoprime ((2 : Int) ^ (e + 1)) p := by
    obtain ⟨k, hk⟩ := hp
    have h2 : IsCoprime (2 : Int) p := ⟨-k, 1, by rw [hk]; ring⟩
    exact h2.pow_left
  exact hcop.dvd_of_dvd_mul_left h1
