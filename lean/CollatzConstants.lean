import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Exact numerical comparisons used in the first-source reduction (module `CollatzConstants`).

Every statement is an exact comparison of integers or rationals proved by `norm_num` (no floating point),
except the logarithm certificate, which uses Mathlib's series for `log ((1+x)/(1-x))`.
Source: Codex K153, K159, K169, K172-K176, K179 and the ChatGPT audits of 2026-11-22.
-/

/-! ## Integer comparisons behind the high-input estimates -/
theorem three_pow_99_lt : (3 : ℕ) ^ 99 < 2 ^ 160 := by norm_num
theorem frac_193_200_pow_99_lt : ((193 : ℚ) / 200) ^ 99 < 1 / 32 := by norm_num
theorem three_pow_39_lt : (3 : ℕ) ^ 39 < 2 ^ 62 := by norm_num
theorem four_mul_193_pow_39_lt : 4 * (193 : ℕ) ^ 39 < 200 ^ 39 := by norm_num
theorem thousand3_pow_22_lt : (3000 : ℕ) ^ 22 < 2 ^ 256 := by norm_num
/-- `n^(-1/22) < 1/3000` for `n ≥ 2^256` in integer form. -/
theorem tail_ratio_const : (96 : ℚ) / (258 * 3000) = 2 / 16125 := by norm_num

/-! ## The allocation 21/125 and its sufficient targets -/
theorem alloc_unweighted : (47 : ℚ) / 30 * (51 / 4700) = 17 / 1000 := by norm_num
theorem alloc_unweighted' : (151 : ℚ) / 1000 + 17 / 1000 = 21 / 125 := by norm_num
theorem alloc_weighted : (488 : ℚ) / 375 * (327 / 3904) = 109 / 1000 := by norm_num
theorem alloc_weighted' : (59 : ℚ) / 1000 + 109 / 1000 = 21 / 125 := by norm_num
theorem absorb_coeff : (61 : ℚ) / 50 / (1 - 4 / 64) = 488 / 375 := by norm_num
theorem tail_const : (120 : ℚ) / 3000 + 488 / 375 * (1 / 1000 + 2 / 100000) = 32287 / 781250 := by norm_num
theorem tail_const_lt : (32287 : ℚ) / 781250 < 59 / 1000 := by norm_num
theorem old_tail_const : (400 : ℚ) / 3000 + 47 / 30 * (1 / 1000 + 6 / 100000) = 67497 / 500000 := by norm_num
theorem old_tail_const_lt : (67497 : ℚ) / 500000 < 151 / 1000 := by norm_num

/-! ## The count constants c, T and the 159-run / 56-budget thresholds (K172-K174) -/
def cK : ℚ := 620751769493359576 / 1180591620717411303425
def TK : ℚ := 327 / 3904

theorem c_den : (1180591620717411303425 : ℕ) = 2 ^ 70 + 1 := by norm_num
theorem c_lt_one_1500 : cK < 1 / 1500 := by unfold cK; norm_num
theorem runs_159_lt : 159 * cK < TK := by unfold cK TK; norm_num
theorem runs_160_gt : TK < 160 * cK := by unfold cK TK; norm_num
theorem gap_159 : TK - 159 * cK = 730489586363446452039 / 4609029687280773728571200 := by unfold cK TK; norm_num
theorem gap_16 : TK - 16 * cK = 347278821444960283664711 / 4609029687280773728571200 := by unfold cK TK; norm_num
theorem target_J : (TK - 159 * cK) / (3000 / 2797) = 681059791019519908784361 / 4609029687280773728571200000 := by
  unfold cK TK; norm_num
/-- Mixed-sector comparison: `56 b0 c + a0 < 159 c`, with `b0 = 3000/2797`, `a0 = 8850/170617`. -/
theorem mixed_sector : 56 * (3000 / 2797) * cK + 8850 / 170617 < 159 * cK := by unfold cK; norm_num
theorem mixed_sector_57 : 159 * cK < 57 * (3000 / 2797) * cK + 8850 / 170617 := by unfold cK; norm_num
theorem b0_def : (15 : ℚ) / (15 * (999 / 1000) - 1) = 3000 / 2797 := by norm_num
theorem a0_def : (750 : ℚ) / 61 * (59 / 1000) / (15 * (999 / 1000) - 1) = 8850 / 170617 := by norm_num

/-! ## Run-length weights: `(1-(2/3)^s)/(s+1) ≤ 5/27` -/
theorem run_weight_le (s : ℕ) (hs : 1 ≤ s) : 27 * (1 - (2 / 3 : ℚ) ^ s) ≤ 5 * ((s : ℚ) + 1) := by
  have hz : (0 : ℚ) < (2 / 3 : ℚ) ^ s := by positivity
  by_cases h : 5 ≤ s
  · have : (5 : ℚ) ≤ s := by exact_mod_cast h
    nlinarith
  · interval_cases s <;> norm_num

/-! ## K176 interruption constants: `K(ρ, t0) = 6 (t0 - 1)/(t0 - 1/ρ)` -/
def Kc (t0 ρ : ℚ) : ℚ := 6 * (t0 - 1) / (t0 - 1 / ρ)
theorem K3 : Kc ((9 / 8) ^ 3) (3 / 4) = 3906 / 139 := by unfold Kc; norm_num
theorem K4 : Kc ((9 / 8) ^ 4) (3 / 4) = 44370 / 3299 := by unfold Kc; norm_num
theorem K_e3 : Kc ((9 / 8) ^ 9) (3 / 8) = 4557649698 / 88519643 := by unfold Kc; norm_num
theorem K_two_shorts : Kc ((9 / 8) ^ 5) (9 / 16) = 1419174 / 7153 := by unfold Kc; norm_num
theorem K3_lt : (3906 : ℚ) / 139 < 56 := by norm_num
theorem K4_four : 4 * (44370 : ℚ) / 3299 < 56 := by norm_num
theorem K_e3_lt : (4557649698 : ℚ) / 88519643 < 56 := by norm_num
theorem K_two_shorts_gt : (56 : ℚ) < 1419174 / 7153 := by norm_num
theorem growth_two_shorts : 1 < (9 / 16 : ℚ) * (9 / 8) ^ 5 := by norm_num

/-! ## K179: the two mixed pairs -/
theorem pair_A : (3 : ℕ) ^ 12 = 531441 ∧ (2 : ℕ) ^ 19 = 524288 ∧ 524288 < 531441 := by norm_num
theorem pair_B_du : (2187 : ℕ) * 319 + 256 * 3767 = 1662005 := by norm_num
theorem pair_B_ud : (243 : ℕ) * 3767 + 2048 * 319 = 1568693 := by norm_num
theorem pair_compose_A : (243 : ℕ) * 2187 = 3 ^ 12 ∧ (256 : ℕ) * 2048 = 2 ^ 19 := by norm_num
def Kmax : ℚ := 1669158 / 7153
theorem K179_main : Kmax * (3000 / 2797) * (2 / 16125) + 8850 / 170617 = 4351172358 / 52478206243 := by
  unfold Kmax; norm_num
theorem K179_gap : TK - 4351172358 / 52478206243 = 2842566489 / 3358605199552 := by unfold TK; norm_num
theorem K179_gap_pos : (0 : ℚ) < 2842566489 / 3358605199552 := by norm_num
theorem pairs_budget : 5 * (2 / 3 : ℚ) = 10 / 3 ∧ 140 / 3 < (56 : ℚ) := by norm_num

/-! ## Exponential majorant constants (ChatGPT unfinished-tails note, 2026-11-22) -/
/-- Truncated exponential with a geometric tail: an upper bound for `exp x` when `0 ≤ x < 1`. -/
def E10 (x : ℚ) : ℚ :=
  x ^ 0 / 1 + x ^ 1 / 1 + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 + x ^ 6 / 720 + x ^ 7 / 5040
  + x ^ 8 / 40320 + x ^ 9 / 362880 + x ^ 10 / 3628800 + (x ^ 11 / 39916800) / (1 - x / 12)

theorem E10_Rstar : E10 (575597 / 1500000) * (1 + 10 / 2 ^ 71) < 367 / 250 := by unfold E10; norm_num

/-! ## The logarithm certificate behind `G - 1 < (61/50) W` -/
theorem rational_log_cert : (61 : ℚ) / 50 * (189480 / 493039) - 15 / 32 = 8571 / 78886240 := by norm_num
theorem rational_log_cert_pos : (0 : ℚ) < 8571 / 78886240 := by norm_num
theorem t_series_value : (2 : ℚ) * (15 / 79 + (15 / 79) ^ 3 / 3) = 189480 / 493039 := by norm_num

/-- `log (47/32) > 189480/493039`, from `log((1+x)/(1-x)) = 2 Σ x^(2k+1)/(2k+1)` with `x = 15/79`. -/
theorem log_47_32_lower : (189480 : ℝ) / 493039 < Real.log (47 / 32) := by
  have hx : |(15 / 79 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one hx
  have e : Real.log (1 + 15 / 79) - Real.log (1 - 15 / 79) = Real.log (47 / 32) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  rw [e] at hs
  have hnn : ∀ k : ℕ, 0 ≤ (2 * (1 / (2 * (k : ℝ) + 1)) * (15 / 79 : ℝ) ^ (2 * k + 1)) := fun k => by positivity
  have h2 := sum_le_hasSum (Finset.range 2) (fun k _ => hnn k) hs
  have : ∑ k ∈ Finset.range 2, (2 * (1 / (2 * (k : ℝ) + 1)) * (15 / 79 : ℝ) ^ (2 * k + 1)) = 189480 / 493039 := by
    simp [Finset.sum_range_succ]; norm_num
  rw [this] at h2
  -- strictness: the third term is positive
  have h3 := sum_le_hasSum (Finset.range 3) (fun k _ => hnn k) hs
  have : ∑ k ∈ Finset.range 3, (2 * (1 / (2 * (k : ℝ) + 1)) * (15 / 79 : ℝ) ^ (2 * k + 1)) > 189480 / 493039 := by
    simp [Finset.sum_range_succ]; norm_num
  linarith

#print axioms three_pow_99_lt
#print axioms mixed_sector
#print axioms K179_gap
#print axioms E10_Rstar
#print axioms log_47_32_lower
