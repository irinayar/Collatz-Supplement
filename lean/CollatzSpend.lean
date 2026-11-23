import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field

/-!
# "Spend each phase interval once" (module `CollatzSpend`): the finite combinatorics behind K161, K171-K176.

* `span_telescope`      : for a monotone phase `q` and disjoint run intervals `[s k, e k]` with `e k ≤ s (k+1)`,
  `Σ_(k<r) (q (e k) - q (s k)) ≤ q (s r) - q (s 0)`  (all selected runs except the last fit inside the span);
* `span_budget`         : if the first selected start has phase `> B` and the last has phase `< Q - B`, the spent phase is `< Q - 2B`;
* `weighted_sum_le`     : `ΔQ_k = (u + q_k) δ_k` with `q_k ≥ B` gives `Σ δ_k ≤ (Σ ΔQ_k)/(u+B)`;
* `split_identity`, `split_nonneg` : the splitting identity `c(i,j) - c(i,k) - c(k+1,j) ≥ 0` for `c(i,j) = (q_j - q_i)/(u + q_i)`;
* `window_count`        : if each of `m` items spends at least `d` of a budget `B`, then `m ≤ B/d`;
* `central_mass_bound`  : the profile-wise inequality `R_p ≤ 3 Z_p/(u_p + B) + A/(H+1) [Q_p > 2B]` sums to
  `R ≤ (3/n) Σ Z_p + (A/(H+1)) #{p : Q_p > 2B}`.
-/

theorem span_telescope (q : ℕ → ℚ) (hq : Monotone q) (s e : ℕ → ℕ)
    (hes : ∀ k, e k ≤ s (k + 1)) (r : ℕ) :
    ∑ k ∈ Finset.range r, (q (e k) - q (s k)) ≤ q (s r) - q (s 0) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ]
    have : q (e r) ≤ q (s (r + 1)) := hq (hes r)
    linarith

theorem span_budget (q : ℕ → ℚ) (hq : Monotone q) (s e : ℕ → ℕ)
    (hes : ∀ k, e k ≤ s (k + 1)) (r : ℕ) (B Q : ℚ)
    (hfirst : B < q (s 0)) (hlast : q (s r) < Q - B) :
    ∑ k ∈ Finset.range r, (q (e k) - q (s k)) < Q - 2 * B := by
  have := span_telescope q hq s e hes r
  linarith

theorem weighted_sum_le (u B : ℚ) (m : ℕ) (δ d q : ℕ → ℚ)
    (hd : ∀ k, d k = (u + q k) * δ k) (hδ : ∀ k, 0 ≤ δ k) (hq : ∀ k, B ≤ q k) (hpos : 0 < u + B) :
    ∑ k ∈ Finset.range m, δ k ≤ (∑ k ∈ Finset.range m, d k) / (u + B) := by
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro k _
  rw [hd k, le_div_iff₀ hpos]
  have : u + B ≤ u + q k := by linarith [hq k]
  nlinarith [hδ k]

theorem split_identity (u qi qk qk1 qj : ℚ) (h1 : 0 < u + qi) (h2 : 0 < u + qk1) :
    (qj - qi) / (u + qi) - (qk - qi) / (u + qi) - (qj - qk1) / (u + qk1)
      = (qk1 - qk) / (u + qi) + (qj - qk1) * (1 / (u + qi) - 1 / (u + qk1)) := by
  field_simp
  ring

theorem split_nonneg (u qi qk qk1 qj : ℚ) (h1 : 0 < u + qi) (h2 : 0 < u + qk1)
    (hik : qi ≤ qk) (hkk : qk ≤ qk1) (hkj : qk1 ≤ qj) :
    (qk - qi) / (u + qi) + (qj - qk1) / (u + qk1) ≤ (qj - qi) / (u + qi) := by
  have e := split_identity u qi qk qk1 qj h1 h2
  have hA : 0 ≤ (qk1 - qk) / (u + qi) := div_nonneg (by linarith) h1.le
  have hB : 1 / (u + qk1) ≤ 1 / (u + qi) := one_div_le_one_div_of_le h1 (by linarith)
  have hC : 0 ≤ (qj - qk1) * (1 / (u + qi) - 1 / (u + qk1)) :=
    mul_nonneg (by linarith) (by linarith)
  linarith

theorem window_count (m : ℕ) (d B : ℚ) (hd : 0 < d) (inc : ℕ → ℚ) (hinc : ∀ k, d ≤ inc k)
    (htot : ∑ k ∈ Finset.range m, inc k ≤ B) : (m : ℚ) ≤ B / d := by
  have h1 : (m : ℚ) * d ≤ ∑ k ∈ Finset.range m, inc k := by
    have := Finset.sum_le_sum (s := Finset.range m) (f := fun _ => d) (g := inc) (fun k _ => hinc k)
    simpa using this
  rw [le_div_iff₀ hd]
  linarith

/-- Profile-wise central occupation bound summed over a finite family. -/
theorem central_mass_bound {ι : Type*} (F : Finset ι) (R Z Q u : ι → ℚ) (n B A Hh : ℚ)
    (hn : 0 < n) (hB : 0 ≤ B) (_hA : 0 ≤ A) (_hH : 0 < Hh + 1)
    (hu : ∀ p ∈ F, n ≤ u p) (hZ : ∀ p ∈ F, 0 ≤ Z p)
    (hR : ∀ p ∈ F, R p ≤ 3 * Z p / (u p + B) + (if 2 * B < Q p then A / (Hh + 1) else 0)) :
    ∑ p ∈ F, R p ≤ 3 / n * ∑ p ∈ F, Z p + A / (Hh + 1) * ((F.filter (fun p => 2 * B < Q p)).card : ℚ) := by
  have h1 : ∀ p ∈ F, R p ≤ 3 / n * Z p + (if 2 * B < Q p then A / (Hh + 1) else 0) := by
    intro p hp
    have h := hR p hp
    have hup : n ≤ u p + B := by linarith [hu p hp]
    have : 3 * Z p / (u p + B) ≤ 3 / n * Z p := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) hn]
      have := hZ p hp
      nlinarith
    linarith
  calc ∑ p ∈ F, R p ≤ ∑ p ∈ F, (3 / n * Z p + (if 2 * B < Q p then A / (Hh + 1) else 0)) :=
        Finset.sum_le_sum h1
    _ = 3 / n * ∑ p ∈ F, Z p + ∑ p ∈ F, (if 2 * B < Q p then A / (Hh + 1) else 0) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = 3 / n * ∑ p ∈ F, Z p + A / (Hh + 1) * ((F.filter (fun p => 2 * B < Q p)).card : ℚ) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]; ring

#print axioms span_telescope
#print axioms weighted_sum_le
#print axioms split_nonneg
#print axioms window_count
#print axioms central_mass_bound
