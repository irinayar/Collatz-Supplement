import Mathlib.Tactic.NormNum
import CollatzElementary
import CollatzFirstReturn

/-!
# Explicit trajectories checked by kernel evaluation (module `CollatzExamples`).

All statements are decided by `decide +kernel` (exact big-integer evaluation of the iterates `Tit i u`; no `native_decide`).

1. The **80-bit nonempty-core return** (ChatGPT, 2026-11-22): source `u80`, 192 shortcut steps, 121 odd inputs, return to `w80`;
   a genuine first return for EVERY odd threshold `n ∈ [n0, n1]` (5.3 · 10^21 thresholds), with total phase `Q > 13`.
2. The **g = 46 high-phase word** (Sturmian-type exponents `⌊i log₂ 3⌋`): 73 shortcut steps, 46 odd inputs, phase `Q > 11`,
   a genuine first return at the threshold `n46 = 3(u46+1)/4`.
3. The **n = 55 control**: the source 63 returns to 61 after 54 shortcut steps (34 odd inputs).
-/

/-! ## 1. The 80-bit example -/
def u80 : Nat := 1194734292994222926486523
def w80 : Nat := 1026086522416072566002429
def z80 : Nat := 1211034369283948566961147   -- least proper state

theorem ex80_end : Tit 192 u80 = w80 := by decide +kernel
theorem ex80_proper : ∀ i < 192, 0 < i → z80 ≤ Tit i u80 := by decide +kernel
theorem ex80_oddc : oddc 192 u80 = 121 := by decide +kernel
theorem ex80_numr :
    numr 192 u80 = 74033533329214600835857505470186789172875818989501471223215 := by decide +kernel
theorem ex80_den : (3 : Nat) ^ 121 = 5391030899743293631239539488528815119194426882613553319203 := by norm_num
/-- Phase `Q = numr/3^121 > 13`. -/
theorem ex80_phase_gt13 : 13 * 3 ^ 121 < numr 192 u80 := by
  rw [ex80_numr]; norm_num
/-- Affine identity for the whole word (instance of `Tit_affine`). -/
theorem ex80_affine : 2 ^ 192 * w80 = 3 ^ 121 * u80 + numr 192 u80 := by
  have := Tit_affine 192 u80
  rw [ex80_end, ex80_oddc] at this
  exact this

def n80lo : Nat := 896050719745667194864893
def n80hi : Nat := 906694364710971881029631

theorem ex80_genuine (n : Nat) (h0 : n80lo ≤ n) (h1 : n ≤ n80hi) : Genuine n u80 192 := by
  apply genuine_of_bounds n u80 192 w80 z80 (by norm_num) ex80_end
    (fun i hi1 hi2 => ex80_proper i hi2 hi1)
  all_goals (simp only [Hband, n80lo, n80hi, u80, w80, z80] at *; omega)

theorem ex80_threshold_count : (n80hi - n80lo) / 2 + 1 = 5321822482652343082370 := by
  unfold n80hi n80lo; norm_num

/-! ## 2. The g = 46 high-phase witness -/
def u46 : Nat := 9420305793941977848827
def w46 : Nat := 8840015659815569560675
def z46 : Nat := 9548829520107877063675
def n46 : Nat := 7065229345456483386621

theorem ex46_end : Tit 73 u46 = w46 := by decide +kernel
theorem ex46_proper : ∀ i < 73, 0 < i → z46 ≤ Tit i u46 := by decide +kernel
theorem ex46_oddc : oddc 73 u46 = 46 := by decide +kernel
theorem ex46_numr : numr 73 u46 = 98878719971867038884317 := by decide +kernel
theorem ex46_den : (3 : Nat) ^ 46 = 8862938119652501095929 := by norm_num
/-- Phase `Q = numr/3^46 > 11`. -/
theorem ex46_phase_gt11 : 11 * 3 ^ 46 < numr 73 u46 := by rw [ex46_numr]; norm_num
theorem ex46_genuine : Genuine n46 u46 73 := by
  apply genuine_of_bounds n46 u46 73 w46 z46 (by norm_num) ex46_end
    (fun i hi1 hi2 => ex46_proper i hi2 hi1)
  all_goals (simp only [Hband, n46, u46, w46, z46]; omega)

/-! ## 3. The n = 55 control -/
theorem ex55_end : Tit 54 63 = 61 := by decide +kernel
theorem ex55_proper : ∀ i < 54, 0 < i → 73 ≤ Tit i 63 := by decide +kernel
theorem ex55_oddc : oddc 54 63 = 34 := by decide +kernel
theorem ex55_genuine : Genuine 55 63 54 := by
  apply genuine_of_bounds 55 63 54 61 73 (by norm_num) ex55_end
    (fun i hi1 hi2 => ex55_proper i hi2 hi1)
  all_goals (try simp only [Hband]); all_goals omega

#print axioms ex80_genuine
#print axioms ex80_phase_gt13
#print axioms ex46_genuine
#print axioms ex55_genuine
