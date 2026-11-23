import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Maximal runs: exact correction, output, signed budget and recovery coefficients (module `CollatzRuns`).

A maximal run starting at height `a` has `s ≥ 1` odd inputs: `s - 1` transitions of exponent one followed by a
transition of exponent `e ≥ 2`.  Writing `z = (2/3)^s` and `f = 1 - z`, the inputs are
`x_t = (3/2)^t (a+1) - 1` (`xr a t`), the complete multiplicative correction is `1 + f/a`, the output is
`b = (3^s (a+1) - 2^s)/2^(s+e-1) ≤ (a+f)/(2z)`, and for the signed charge
`psi = [kappa f/a + 1/a - 1/b]_+`, `kappa = 1 - 4/(3n+1)`, one has
`a * psi ≤ [2 - 3 z]_+` (zero for `s = 1`), while for expanding runs (`s ≥ 2`, `e = 2`)
`b/a ≥ 9/8` and `psi ≤ 6 (1/a - 1/b)`.  The recovery coefficient `K(ρ,t0) = 6 (t0-1)/(t0 - 1/ρ)` is monotone.
All statements are exact identities/inequalities over `ℚ` (sources: ChatGPT/Codex K158, K171, K174-K176).
-/

/-- The `t`-th input of a run started at height `a`: `x_t + 1 = (3/2)^t (a + 1)`. -/
def xr (a : ℚ) (t : ℕ) : ℚ := (3 / 2) ^ t * (a + 1) - 1

theorem xr_zero (a : ℚ) : xr a 0 = a := by unfold xr; ring

theorem xr_step (a : ℚ) (t : ℕ) : 3 * xr a t + 1 = 2 * xr a (t + 1) := by
  unfold xr; rw [pow_succ]; ring

theorem xr_ge (a : ℚ) (ha : 0 ≤ a) (t : ℕ) : a ≤ xr a t := by
  unfold xr
  have h1 : (1 : ℚ) ≤ (3 / 2) ^ t := one_le_pow₀ (by norm_num)
  nlinarith

theorem xr_pos (a : ℚ) (ha : 0 < a) (t : ℕ) : 0 < xr a t := lt_of_lt_of_le ha (xr_ge a ha.le t)

/-- Telescoping of the run correction: `∏_(t<s) (1 + 1/(3 x_t)) = (2/3)^s x_s / a`. -/
theorem run_prod_telescope (a : ℚ) (ha : 0 < a) (s : ℕ) :
    ∏ t ∈ Finset.range s, (1 + 1 / (3 * xr a t)) = (2 / 3) ^ s * xr a s / a := by
  induction s with
  | zero => simp [xr_zero, div_self ha.ne']
  | succ s ih =>
    rw [Finset.prod_range_succ, ih]
    have hx : xr a s ≠ 0 := (xr_pos a ha s).ne'
    have e := xr_step a s
    have : (1 : ℚ) + 1 / (3 * xr a s) = 2 * xr a (s + 1) / (3 * xr a s) := by
      field_simp; linarith
    rw [this, pow_succ]
    field_simp

/-- **Exact run correction**: `G_run = 1 + (1 - (2/3)^s)/a`. -/
theorem run_correction (a : ℚ) (ha : 0 < a) (s : ℕ) :
    ∏ t ∈ Finset.range s, (1 + 1 / (3 * xr a t)) = 1 + (1 - (2 / 3) ^ s) / a := by
  rw [run_prod_telescope a ha s]
  unfold xr
  have h : ((2 : ℚ) / 3) ^ s * (3 / 2) ^ s = 1 := by rw [← mul_pow]; norm_num
  have : (2 / 3 : ℚ) ^ s * ((3 / 2) ^ s * (a + 1) - 1) = (a + 1) - (2 / 3) ^ s := by
    have : (2 / 3 : ℚ) ^ s * ((3 / 2) ^ s * (a + 1) - 1)
        = ((2 / 3 : ℚ) ^ s * (3 / 2) ^ s) * (a + 1) - (2 / 3) ^ s := by ring
    rw [this, h]; ring
  rw [this]; field_simp; ring

/-- Output of the run: `2 x_s / 2^(e'+1)` equals `(3^s (a+1) - 2^s)/2^(s+e')`. -/
theorem run_output (a : ℚ) (s e' : ℕ) :
    2 * xr a s / 2 ^ (e' + 1) = (3 ^ s * (a + 1) - 2 ^ s) / 2 ^ (s + e') := by
  unfold xr
  rw [div_pow]
  have h2 : ((2 : ℚ) ^ s) ≠ 0 := by positivity
  field_simp
  ring

/-- For `e ≥ 2` the output satisfies `b ≤ (a + f)/(2 z)` with `z = (2/3)^s`, `f = 1 - z`. -/
theorem run_b_le (a : ℚ) (ha : 0 < a) (s e : ℕ) (he : 2 ≤ e) :
    2 * xr a s / 2 ^ e ≤ (a + (1 - (2 / 3 : ℚ) ^ s)) / (2 * (2 / 3 : ℚ) ^ s) := by
  have hz : (0 : ℚ) < (2 / 3 : ℚ) ^ s := by positivity
  have hxp : 0 < xr a s := xr_pos a ha s
  have h4 : (4 : ℚ) ≤ 2 ^ e := by
    have h22 : (2 : ℚ) ^ 2 ≤ 2 ^ e := pow_le_pow_right₀ (by norm_num) he
    calc (4 : ℚ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := h22
  have hxr : xr a s = (a + (1 - (2 / 3 : ℚ) ^ s)) / (2 / 3 : ℚ) ^ s := by
    unfold xr
    have h : ((2 : ℚ) / 3) ^ s * (3 / 2) ^ s = 1 := by rw [← mul_pow]; norm_num
    field_simp
    nlinarith [h]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (a + (1 - (2 / 3 : ℚ) ^ s)) = xr a s * (2 / 3 : ℚ) ^ s := by rw [hxr]; field_simp
  rw [this]
  have hxz : 0 < xr a s * (2 / 3 : ℚ) ^ s := by positivity
  nlinarith [mul_pos hxp hz, h4]

/-- **Signed budget bound** `a * psi ≤ [2 - 3z]_+`, for `1 ≤ n ≤ a`, `0 < z ≤ 2/3`, `0 < b ≤ (a+f)/(2z)`. -/
theorem psi_bound (n a z b : ℚ) (hn : 1 ≤ n) (hna : n ≤ a) (hz0 : 0 < z) (hz : z ≤ 2 / 3)
    (hb : 0 < b) (hbb : b ≤ (a + (1 - z)) / (2 * z)) :
    a * max 0 ((1 - 4 / (3 * n + 1)) * ((1 - z) / a) + 1 / a - 1 / b) ≤ max 0 (2 - 3 * z) := by
  have ha : 0 < a := by linarith
  have hab : 0 < a + (1 - z) := by linarith
  have key : (1 - 4 / (3 * n + 1)) * (1 - z) + 1 - a / b ≤ 2 - 3 * z := by
    have h1 : 2 * z * a / (a + (1 - z)) ≤ a / b := by
      rw [div_le_div_iff₀ (by positivity) hb]
      have := (le_div_iff₀ (by positivity : (0 : ℚ) < 2 * z)).mp hbb
      nlinarith [this]
    have h3 : 0 < 3 * n + 1 := by linarith
    have h2 : 2 * z / (a + (1 - z)) ≤ 4 / (3 * n + 1) := by
      rw [div_le_div_iff₀ hab h3]
      nlinarith
    have h4 : 2 * z * a / (a + (1 - z)) ≥ 2 * z - 2 * z * (1 - z) / (a + (1 - z)) := by
      have : 2 * z * a / (a + (1 - z)) = 2 * z - 2 * z * (1 - z) / (a + (1 - z)) := by field_simp; ring
      linarith
    have hf : 0 ≤ 1 - z := by linarith
    have h5 : (1 - 4 / (3 * n + 1)) * (1 - z) = (1 - z) - (4 / (3 * n + 1)) * (1 - z) := by ring
    -- (1-z)(1 + 4/(3n+1)... ) reorganize: use f * (2z/(a+f) - 4/(3n+1)) ≤ 0
    have h6 : (1 - z) * (2 * z / (a + (1 - z))) ≤ (1 - z) * (4 / (3 * n + 1)) := mul_le_mul_of_nonneg_left h2 hf
    have h7 : 2 * z * a / (a + (1 - z)) = 2 * z - (1 - z) * (2 * z / (a + (1 - z))) := by field_simp; ring
    nlinarith [h1, h6, h7, h5]
  by_cases hpos : 0 ≤ (1 - 4 / (3 * n + 1)) * ((1 - z) / a) + 1 / a - 1 / b
  · rw [max_eq_right hpos]
    have : a * ((1 - 4 / (3 * n + 1)) * ((1 - z) / a) + 1 / a - 1 / b) = (1 - 4 / (3 * n + 1)) * (1 - z) + 1 - a / b := by
      field_simp
    rw [this]
    exact le_trans key (le_max_right _ _)
  · rw [max_eq_left (by linarith)]
    simp

/-- For a single-input run (`s = 1`, `z = 2/3`) the signed budget vanishes. -/
theorem psi_single (n a b : ℚ) (hn : 1 ≤ n) (hna : n ≤ a) (hb : 0 < b) (hbb : b ≤ (a + 1 / 3) / (2 * (2 / 3))) :
    a * max 0 ((1 - 4 / (3 * n + 1)) * ((1 - 2 / 3) / a) + 1 / a - 1 / b) ≤ 0 := by
  have := psi_bound n a (2 / 3) b hn hna (by norm_num) (by norm_num) hb (by convert hbb using 2; norm_num)
  convert this using 1
  norm_num

/-- Expanding run (`s ≥ 2`, `e = 2`): `b = (a+f)/(2z)` gives `b/a ≥ 9/8`. -/
theorem expanding_growth (a z : ℚ) (ha : 0 < a) (hz0 : 0 < z) (hz : z ≤ 4 / 9) (_hf : z < 1) :
    9 / 8 * a ≤ (a + (1 - z)) / (2 * z) := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- Expanding run: `psi ≤ 6 (1/a - 1/b)` (K175), for `b = (a+f)/(2z)`, `0 < z ≤ 4/9`, `a ≥ n ≥ 1`. -/
theorem expanding_psi (n a z : ℚ) (hn : 1 ≤ n) (hna : n ≤ a) (hz0 : 0 < z) (hz : z ≤ 4 / 9) :
    max 0 ((1 - 4 / (3 * n + 1)) * ((1 - z) / a) + 1 / a - 1 / ((a + (1 - z)) / (2 * z)))
      ≤ 6 * (1 / a - 1 / ((a + (1 - z)) / (2 * z))) := by
  have ha : 0 < a := by linarith
  have hab : 0 < a + (1 - z) := by linarith
  have hk : 0 ≤ 4 / (3 * n + 1) := by positivity
  have hk1 : 4 / (3 * n + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hfz : 0 ≤ 1 - z := by linarith
  have e : 1 / ((a + (1 - z)) / (2 * z)) = 2 * z / (a + (1 - z)) := by field_simp
  rw [e]
  have h2 : 2 * z / (a + (1 - z)) ≤ 2 * z / a := by
    apply div_le_div_of_nonneg_left (by positivity) ha (by linarith)
  have hmain : (1 - 4 / (3 * n + 1)) * ((1 - z) / a) + 1 / a - 2 * z / (a + (1 - z)) ≤ 6 * (1 / a - 2 * z / (a + (1 - z))) := by
    have h3 : (1 - 4 / (3 * n + 1)) * ((1 - z) / a) ≤ (1 - z) / a := by
      have : (1 - z) / a ≥ 0 := by positivity
      nlinarith
    have h4 : (1 - z) / a ≤ 5 * (1 / a - 2 * z / (a + (1 - z))) := by
      have : 5 * (1 / a - 2 * z / (a + (1 - z))) - (1 - z) / a = (5 * (a + (1 - z)) - 10 * z * a - (1 - z) * (a + (1 - z))) / (a * (a + (1 - z))) := by
        field_simp
        ring
      have hnum : 0 ≤ (5 * (a + (1 - z)) - 10 * z * a - (1 - z) * (a + (1 - z))) := by nlinarith [mul_nonneg ha.le (by linarith : (0:ℚ) ≤ 4 - 9 * z), mul_nonneg hfz (by linarith : (0:ℚ) ≤ 4 + z)]
      have : 0 ≤ 5 * (1 / a - 2 * z / (a + (1 - z))) - (1 - z) / a := by
        rw [this]; positivity
      linarith
    nlinarith
  have hpos : 0 ≤ 6 * (1 / a - 2 * z / (a + (1 - z))) := by
    have : 2 * z / (a + (1 - z)) ≤ 1 / a := by
      rw [div_le_div_iff₀ hab ha]; nlinarith
    linarith
  exact max_le hpos hmain

/-- The recovery coefficient. -/
noncomputable def Kcoef (t0 ρ : ℚ) : ℚ := 6 * (t0 - 1) / (t0 - 1 / ρ)

/-- `t ↦ 6 (t-1)/(t - 1/ρ)` is nonincreasing for `t > 1/ρ`, `0 < ρ < 1`. -/
theorem Kcoef_antitone (ρ t1 t2 : ℚ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (h1 : 1 / ρ < t1) (h12 : t1 ≤ t2) :
    6 * (t2 - 1) / (t2 - 1 / ρ) ≤ 6 * (t1 - 1) / (t1 - 1 / ρ) := by
  have hu : 1 < 1 / ρ := by rw [lt_div_iff₀ hρ0]; linarith
  have hd1 : 0 < t1 - 1 / ρ := by linarith
  have hd2 : 0 < t2 - 1 / ρ := by linarith
  rw [div_le_div_iff₀ hd2 hd1]
  nlinarith [mul_nonneg (sub_nonneg.mpr h12) (sub_nonneg.mpr hu.le)]

/-- Block bound (K176): if `S ≤ 6 (1/a - 1/c)`, `c ≥ t0 a`, `b ≥ ρ c`, `0 < ρ < 1`, `ρ t0 > 1`, then
`S ≤ K(ρ,t0) (1/a - 1/b)`. -/
theorem block_bound (a c b S ρ t0 : ℚ) (ha : 0 < a) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ht0 : 1 / ρ < t0)
    (hc : t0 * a ≤ c) (hb : ρ * c ≤ b) (hS : S ≤ 6 * (1 / a - 1 / c)) :
    S ≤ Kcoef t0 ρ * (1 / a - 1 / b) := by
  have hρt : 1 < ρ * t0 := by rwa [div_lt_iff₀ hρ0, mul_comm] at ht0
  have hu : 1 < 1 / ρ := by rw [lt_div_iff₀ hρ0]; linarith
  have hc0 : 0 < c := by nlinarith
  have hb0 : 0 < b := by nlinarith
  set t := c / a with ht
  have htc : c = t * a := by rw [ht]; field_simp
  have ht0' : t0 ≤ t := by rw [ht, le_div_iff₀ ha]; linarith
  have h1t : 1 / ρ < t := lt_of_lt_of_le ht0 ht0'
  have htp : 0 < t := by nlinarith
  have hbt : ρ * t * a ≤ b := by rw [htc] at hb; nlinarith
  -- 1/a - 1/b ≥ (1/a) (1 - 1/(ρ t))
  have hden : 0 < t - 1 / ρ := by linarith
  have hKpos : 0 ≤ Kcoef t0 ρ := by
    unfold Kcoef; apply div_nonneg; nlinarith
    have : 0 < t0 - 1 / ρ := by linarith
    exact this.le
  have hlow : (1 / a) * (1 - 1 / (ρ * t)) ≤ 1 / a - 1 / b := by
    have : 1 / b ≤ 1 / (ρ * t * a) := one_div_le_one_div_of_le (by positivity) hbt
    have e : (1 / a) * (1 - 1 / (ρ * t)) = 1 / a - 1 / (ρ * t * a) := by field_simp
    linarith
  have hSbound : S ≤ (6 / a) * (1 - 1 / t) := by
    have : 1 / c = 1 / (t * a) := by rw [htc]
    have e : (6 / a) * (1 - 1 / t) = 6 * (1 / a - 1 / (t * a)) := by field_simp
    rw [e, ← this]; exact hS
  have hK : 6 * (t - 1) / (t - 1 / ρ) ≤ Kcoef t0 ρ := Kcoef_antitone ρ t0 t hρ0 hρ1 ht0 ht0'
  have hfac : (6 / a) * (1 - 1 / t) = (6 * (t - 1) / (t - 1 / ρ)) * ((1 / a) * (1 - 1 / (ρ * t))) := by
    have hρ' : ρ ≠ 0 := hρ0.ne'
    have ht' : t ≠ 0 := htp.ne'
    have hd : t - 1 / ρ ≠ 0 := hden.ne'
    have h7 : ∀ D X Y : ℚ, D ≠ 0 → X / D * (D / Y) = X / Y := by intro D X Y hD; field_simp
    have h6 : (1 / a) * (1 - 1 / (ρ * t)) = (t - 1 / ρ) / (a * t) := by field_simp
    have h8 : (6 / a) * (1 - 1 / t) = 6 * (t - 1) / (a * t) := by field_simp
    rw [h6, h8]
    exact (h7 _ _ _ hd).symm
  have hnn : 0 ≤ (1 / a) * (1 - 1 / (ρ * t)) := by
    have : 1 / (ρ * t) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    have : 0 ≤ 1 - 1 / (ρ * t) := by linarith
    positivity
  calc S ≤ (6 / a) * (1 - 1 / t) := hSbound
    _ = (6 * (t - 1) / (t - 1 / ρ)) * ((1 / a) * (1 - 1 / (ρ * t))) := hfac
    _ ≤ Kcoef t0 ρ * ((1 / a) * (1 - 1 / (ρ * t))) := mul_le_mul_of_nonneg_right hK hnn
    _ ≤ Kcoef t0 ρ * (1 / a - 1 / b) := mul_le_mul_of_nonneg_left hlow hKpos

#print axioms run_correction
#print axioms run_output
#print axioms psi_bound
#print axioms expanding_psi
#print axioms block_bound
