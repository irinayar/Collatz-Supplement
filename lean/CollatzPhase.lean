import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import CollatzElementary

/-!
# Original-source phase, correction product, potential and reciprocal flux (module `CollatzPhase`).

For a start `n` (positive), `a_i = oddc i n` odd inputs and `U_i = numr i n` the affine numerator of the first `i`
steps (`2^i T^i n = 3^a n + U`, `Tit_affine`). The *phase* is the rational `Q_i = U_i / 3^(a_i)`.

Results (all over `ℚ`/`ℕ`, no `sorry`):
* `phase_affine`            : `n + Q_i = 2^i * T^i n / 3^(a_i)`  (so `n + Q_i = n * G_i`, `G = 2^i x_i/(3^a n)`);
* `phase_step_odd/even`     : increments `Q_(i+1) - Q_i = 2^i/3^(a_i+1) = (n+Q_i)/(3 x_i)` for an odd input, `0` for even;
* `phase_mono`              : `Q_i ≤ Q_(i+1)`;
* `phase_prod`              : `n + Q_i = n * ∏_(k<i, x_k odd) (1 + 1/(3 x_k))`  (correction product);
* `rho_formula`             : `(1+Q/u)(1+5/y)/(1+5/u) - 1 = (Q(y+5) - 5(y-u))/(y(u+5))`;
* `rho_nonpos_Q_lt_five`    : if the normalized charge is `≤ 1` and `y > u > 0` then `Q < 5`;
* `flux_step`, `flux_sum`   : signed reciprocal flux `1/T x - 1/x` and its telescoping over `i < j`;
* `numr_not_dvd_three`      : once an odd input occurred, `3 ∤ numr` (the numerator is a unit mod 3).
-/

/-- The original-source phase `Q_i = U_i / 3^(a_i)`. -/
noncomputable def Qph (i n : Nat) : ℚ := (numr i n : ℚ) / (3 : ℚ) ^ (oddc i n)

theorem T_pos (x : Nat) (hx : 0 < x) : 0 < T x := by
  unfold T; split <;> omega

theorem Tit_pos : ∀ (i x : Nat), 0 < x → 0 < Tit i x := by
  intro i
  induction i with
  | zero => intro x hx; simpa [Tit_zero] using hx
  | succ i ih => intro x hx; rw [Tit_succ']; exact T_pos _ (ih x hx)

/-- `n + Q_i = 2^i * T^i n / 3^(a_i)`. -/
theorem phase_affine (i n : Nat) :
    (n : ℚ) + Qph i n = (2 : ℚ) ^ i * (Tit i n : ℚ) / (3 : ℚ) ^ (oddc i n) := by
  have h := Tit_affine i n
  have h' : ((2 : ℚ) ^ i * (Tit i n : ℚ)) = (3 : ℚ) ^ (oddc i n) * n + numr i n := by exact_mod_cast h
  unfold Qph
  have h3 : ((3 : ℚ) ^ (oddc i n)) ≠ 0 := by positivity
  rw [h']; field_simp

/-- Odd input: `Q_(i+1) - Q_i = 2^i / 3^(a_i+1) = (n + Q_i) / (3 x_i)`. -/
theorem phase_step_odd (i n : Nat) (hn : 0 < n) (hx : Tit i n % 2 = 1) :
    Qph (i + 1) n - Qph i n = (2 : ℚ) ^ i / (3 : ℚ) ^ (oddc i n + 1)
    ∧ Qph (i + 1) n - Qph i n = ((n : ℚ) + Qph i n) / (3 * (Tit i n : ℚ)) := by
  have ha : oddc (i + 1) n = oddc i n + 1 := by simp [oddc, hx]
  have hu : numr (i + 1) n = 3 * numr i n + 2 ^ i := by simp [numr, hx]
  have hxpos : (0 : ℚ) < (Tit i n : ℚ) := by exact_mod_cast Tit_pos i n hn
  have h3 : ((3 : ℚ) ^ (oddc i n)) ≠ 0 := by positivity
  have first : Qph (i + 1) n - Qph i n = (2 : ℚ) ^ i / (3 : ℚ) ^ (oddc i n + 1) := by
    unfold Qph; rw [ha, hu]; push_cast; field_simp; ring
  refine ⟨first, ?_⟩
  rw [first]
  have key := phase_affine i n
  rw [key]
  field_simp; ring

/-- Even input: the phase does not change. -/
theorem phase_step_even (i n : Nat) (hx : Tit i n % 2 = 0) : Qph (i + 1) n = Qph i n := by
  have ha : oddc (i + 1) n = oddc i n := by simp [oddc, hx]
  have hu : numr (i + 1) n = numr i n := by simp [numr, show ¬ (Tit i n % 2 = 1) by omega]
  unfold Qph; rw [ha, hu]

theorem phase_mono (i n : Nat) : Qph i n ≤ Qph (i + 1) n := by
  by_cases hx : Tit i n % 2 = 1
  · by_cases hn : 0 < n
    · have := (phase_step_odd i n hn hx).1
      have hpos : (0 : ℚ) < (2 : ℚ) ^ i / (3 : ℚ) ^ (oddc i n + 1) := by positivity
      linarith
    · have hn0 : n = 0 := by omega
      subst hn0
      -- with start 0 every state is 0 (even), so this case cannot occur
      have : Tit i 0 = 0 := by
        clear hx
        induction i with
        | zero => rfl
        | succ i ih => rw [Tit_succ', ih]; rfl
      omega
  · have hx0 : Tit i n % 2 = 0 := by omega
    rw [phase_step_even i n hx0]

/-- The correction product `G_i = ∏_(k<i) (if x_k odd then 1 + 1/(3x_k) else 1)`. -/
noncomputable def Gprod (i n : Nat) : ℚ :=
  ∏ k ∈ Finset.range i, (if Tit k n % 2 = 1 then 1 + 1 / (3 * (Tit k n : ℚ)) else 1)

/-- `n + Q_i = n * G_i`, i.e. `Q_i = n (G_i - 1)`. -/
theorem phase_prod (i n : Nat) (hn : 0 < n) : (n : ℚ) + Qph i n = (n : ℚ) * Gprod i n := by
  induction i with
  | zero => simp [Qph, oddc, numr, Gprod]
  | succ i ih =>
    unfold Gprod at ih ⊢
    rw [Finset.prod_range_succ]
    by_cases hx : Tit i n % 2 = 1
    · have hs := (phase_step_odd i n hn hx).2
      have hxpos : (0 : ℚ) < (Tit i n : ℚ) := by exact_mod_cast Tit_pos i n hn
      simp only [hx, ite_true]
      have : (n : ℚ) + Qph (i + 1) n = ((n : ℚ) + Qph i n) * (1 + 1 / (3 * (Tit i n : ℚ))) := by
        have e : Qph (i + 1) n = Qph i n + ((n : ℚ) + Qph i n) / (3 * (Tit i n : ℚ)) := by linarith
        rw [e]; field_simp; ring
      rw [this, ih]; ring
    · have hx0 : Tit i n % 2 = 0 := by omega
      have e := phase_step_even i n hx0
      have hne : ¬ (Tit i n % 2 = 1) := by omega
      simp only [hne, ite_false, mul_one]
      rw [e, ih]

/-- Potential ratio: `(1 + Q/u)(1 + 5/y)/(1 + 5/u) - 1 = (Q (y+5) - 5 (y-u)) / (y (u+5))`. -/
theorem rho_formula (Q u y : ℚ) (hu : 0 < u) (hy : 0 < y) :
    (1 + Q / u) * (1 + 5 / y) / (1 + 5 / u) - 1 = (Q * (y + 5) - 5 * (y - u)) / (y * (u + 5)) := by
  have hu5 : u + 5 ≠ 0 := by positivity
  have hu' : u ≠ 0 := hu.ne'
  have hy' : y ≠ 0 := hy.ne'
  field_simp
  ring

/-- If the normalized charge is at most `1`, `y > u > 0` and `Q ≥ 0`, then `Q < 5`:
a nonpositive incoming prefix charge forces a small phase. -/
theorem rho_nonpos_Q_lt_five (Q u y : ℚ) (hu : 0 < u) (huy : u < y)
    (h : (1 + Q / u) * (1 + 5 / y) / (1 + 5 / u) ≤ 1) : Q < 5 := by
  have hy : 0 < y := hu.trans huy
  have e := rho_formula Q u y hu hy
  have hnum : Q * (y + 5) - 5 * (y - u) ≤ 0 := by
    have hd : 0 < y * (u + 5) := by positivity
    have : (Q * (y + 5) - 5 * (y - u)) / (y * (u + 5)) ≤ 0 := by linarith
    exact (div_nonpos_iff.mp this).elim (fun h => absurd h.2 (by nlinarith)) (fun h => h.1)
  have h5 : 0 < y - u := by linarith
  have : Q * (y + 5) ≤ 5 * (y - u) := by linarith
  by_contra hQ
  have hQ := not_lt.mp hQ
  nlinarith

/-- One-step reciprocal flux: `1/T x - 1/x = -(x+1)/(x(3x+1))` for odd `x`, and `= 1/x` for even `x`. -/
theorem flux_step (x : Nat) (hx : 0 < x) :
    (1 : ℚ) / (T x) - 1 / x =
      if x % 2 = 1 then -((x : ℚ) + 1) / ((x : ℚ) * (3 * x + 1)) else 1 / (x : ℚ) := by
  have hxq : (0 : ℚ) < x := by exact_mod_cast hx
  by_cases h : x % 2 = 1
  · simp only [h, ↓reduceIte]
    rw [T_odd x h]
    have h2 : (2 : ℚ) * (((3 * x + 1) / 2 : Nat) : ℚ) = 3 * x + 1 := by
      have : 2 * ((3 * x + 1) / 2) = 3 * x + 1 := by omega
      exact_mod_cast this
    have hpos : (0 : ℚ) < (((3 * x + 1) / 2 : Nat) : ℚ) := by
      have : 0 < (3 * x + 1) / 2 := by omega
      exact_mod_cast this
    have : (((3 * x + 1) / 2 : Nat) : ℚ) = (3 * x + 1) / 2 := by linarith
    rw [this]; field_simp; ring
  · simp only [h, ↓reduceIte]
    rw [T_even x (by omega)]
    have h2 : (2 : ℚ) * ((x / 2 : Nat) : ℚ) = x := by
      have : 2 * (x / 2) = x := by omega
      exact_mod_cast this
    have hpos : (0 : ℚ) < ((x / 2 : Nat) : ℚ) := by
      have : 0 < x / 2 := by omega
      exact_mod_cast this
    have : ((x / 2 : Nat) : ℚ) = (x : ℚ) / 2 := by linarith
    rw [this]; field_simp; ring

/-- Telescoping: `1/T^j n - 1/n = Σ_(i<j) (flux of the i-th step)`. -/
theorem flux_sum (j n : Nat) (hn : 0 < n) :
    (1 : ℚ) / (Tit j n) - 1 / n =
      ∑ i ∈ Finset.range j, (if Tit i n % 2 = 1 then -((Tit i n : ℚ) + 1) / ((Tit i n : ℚ) * (3 * Tit i n + 1))
        else 1 / (Tit i n : ℚ)) := by
  induction j with
  | zero => simp [Tit_zero]
  | succ j ih =>
    rw [Finset.sum_range_succ, ← ih, Tit_succ']
    have := flux_step (Tit j n) (Tit_pos j n hn)
    linarith

theorem two_pow_mod3 : ∀ j : Nat, 2 ^ j % 3 = 1 ∨ 2 ^ j % 3 = 2 := by
  intro j
  induction j with
  | zero => simp
  | succ j ih => rw [Nat.pow_succ]; omega

/-- Once an odd input has occurred the affine numerator is not divisible by `3`. -/
theorem numr_not_dvd_three (j n : Nat) (h : 1 ≤ oddc j n) : ¬ (3 ∣ numr j n) := by
  induction j with
  | zero => simp [oddc] at h
  | succ j ih =>
    by_cases hx : Tit j n % 2 = 1
    · have hu : numr (j + 1) n = 3 * numr j n + 2 ^ j := by simp [numr, hx]
      rw [hu]
      intro hd
      have h3 : 3 ∣ 2 ^ j := by
        have : 3 ∣ 3 * numr j n := dvd_mul_right 3 _
        exact (Nat.dvd_add_right this).mp hd
      have hm := two_pow_mod3 j
      have : 2 ^ j % 3 = 0 := Nat.mod_eq_zero_of_dvd h3
      omega
    · have hx0 : Tit j n % 2 = 0 := by omega
      have ha : oddc (j + 1) n = oddc j n := by simp [oddc, hx0]
      have hu : numr (j + 1) n = numr j n := by simp [numr, hx]
      rw [hu]; rw [ha] at h; exact ih h

#print axioms phase_affine
#print axioms phase_step_odd
#print axioms phase_mono
#print axioms phase_prod
#print axioms rho_formula
#print axioms rho_nonpos_Q_lt_five
#print axioms flux_sum
#print axioms numr_not_dvd_three
