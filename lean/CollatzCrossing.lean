import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CollatzElementary

/-!
# The first-crossing horizon lemma (K167 / K168), formalized.

Setting: the accelerated map `T` of `CollatzElementary`, a start `n ≥ 1`, and `j` steps with `a = oddc j n`
odd inputs and affine numerator `U = numr j n`, so that `2^j * T^j n = 3^a * n + U` (`Tit_affine`).

*Coefficient crossing* at step `j` means `3^a < 2^j` (the homogeneous multiplier `3^a/2^j` is below one);
*not yet crossed* at step `i` means `2^i ≤ 3^(oddc i n)`.

Main result `crossing_descent`: if the coefficient has not crossed before step `j`, crosses at step `j`, and
`n` is large in the sense `a * 2^j < 3 * n * (2^j - 3^a)` (equivalently `n > a 2^j / (3 (2^j - 3^a))`),
then `T^j n < n`, i.e. the first crossing is already a strict descent.

Proof ingredients, all in `ℕ`:
* before the first crossing every state is `≥ n` (`state_ge`);
* the relative correction obeys `(3n)^a * P ≤ (3n+1)^a * 3^a * n` with `P = 3^a n + U = 2^i x_i`
  (the integer form of `G ≤ (1+1/(3n))^a`, `correction_bound`);
* the Bernoulli-type inequality `(N+1)^a (N-a) ≤ N^(a+1)` (`bernoulli_nat`), which gives `G ≤ 1/(1 - a/(3n))`.
-/

/-- Bernoulli-type inequality in `ℕ` with `N = a + d`: `(N+1)^a * d ≤ N^(a+1)`. -/
theorem bernoulli_nat : ∀ (a d : Nat), (a + d + 1) ^ a * d ≤ (a + d) ^ (a + 1) := by
  intro a
  induction a with
  | zero => intro d; simp
  | succ a ih =>
    intro d
    have h := ih (d + 1)
    have e1 : a + (d + 1) + 1 = a + d + 2 := by omega
    have e2 : a + (d + 1) = a + d + 1 := by omega
    rw [e1, e2] at h
    have e3 : a + 1 + d + 1 = a + d + 2 := by omega
    have e4 : a + 1 + d = a + d + 1 := by omega
    rw [e3, e4]
    -- goal: (a+d+2)^(a+1) * d ≤ (a+d+1)^(a+1+1)
    have hmul : (a + d + 2) * d ≤ (a + d + 1) * (d + 1) := by nlinarith
    calc (a + d + 2) ^ (a + 1) * d = (a + d + 2) ^ a * ((a + d + 2) * d) := by ring
      _ ≤ (a + d + 2) ^ a * ((a + d + 1) * (d + 1)) := Nat.mul_le_mul_left _ hmul
      _ = (a + d + 1) * ((a + d + 2) ^ a * (d + 1)) := by ring
      _ ≤ (a + d + 1) * ((a + d + 1) ^ (a + 1)) := Nat.mul_le_mul_left _ h
      _ = (a + d + 1) ^ (a + 1 + 1) := by ring

/-- The same inequality in the form used below: `(N+1)^a * (N - a) ≤ N^(a+1)` for `a ≤ N`. -/
theorem bernoulli_nat' (a N : Nat) (h : a ≤ N) : (N + 1) ^ a * (N - a) ≤ N ^ (a + 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, N = a + d := ⟨N - a, by omega⟩
  have := bernoulli_nat a d
  have e : a + d - a = d := by omega
  rw [e]; exact this

/-- `P_i = 3^(a_i) n + U_i = 2^i * T^i n`. -/
theorem P_eq (i n : Nat) : 3 ^ (oddc i n) * n + numr i n = 2 ^ i * Tit i n := (Tit_affine i n).symm

/-- Before the first crossing every state is at least `n`. -/
theorem state_ge (n j : Nat) (_hn : 1 ≤ n) (hnc : ∀ i, i < j → 2 ^ i ≤ 3 ^ (oddc i n)) :
    ∀ i, i < j → n ≤ Tit i n := by
  intro i hi
  have h1 := hnc i hi
  have h2 := Tit_affine i n
  by_contra hlt
  replace hlt := Nat.lt_of_not_le hlt
  have : 2 ^ i * Tit i n < 2 ^ i * n := Nat.mul_lt_mul_of_pos_left hlt (by positivity)
  have h3 : 2 ^ i * n ≤ 3 ^ oddc i n * n := Nat.mul_le_mul_right n h1
  omega

/-- Integer form of `G ≤ (1 + 1/(3n))^a`: `(3n)^a * P_i ≤ (3n+1)^a * 3^a * n`, valid for `i ≤ j`
when all earlier states are `≥ n`. -/
theorem correction_bound (n j : Nat) (hn : 1 ≤ n) (hge : ∀ i, i < j → n ≤ Tit i n) :
    ∀ i, i ≤ j →
      (3 * n) ^ (oddc i n) * (3 ^ (oddc i n) * n + numr i n)
        ≤ (3 * n + 1) ^ (oddc i n) * 3 ^ (oddc i n) * n := by
  intro i
  induction i with
  | zero => intro _; simp [oddc, numr]
  | succ i ih =>
    intro hi
    have ih' := ih (by omega)
    have hxi : n ≤ Tit i n := hge i (by omega)
    have hP := Tit_affine i n
    by_cases hz : Tit i n % 2 = 1
    · -- odd step: a' = a + 1, U' = 3U + 2^i
      have ha : oddc (i + 1) n = oddc i n + 1 := by simp [oddc, hz]
      have hu : numr (i + 1) n = 3 * numr i n + 2 ^ i := by simp [numr, hz]
      rw [ha, hu]
      set a := oddc i n with ha0
      set U := numr i n with hU0
      set P := 3 ^ a * n + U with hPdef
      have hP2 : P = 2 ^ i * Tit i n := by rw [hPdef]; exact hP.symm
      have hn2 : n * 2 ^ i ≤ P := by
        rw [hP2]; calc n * 2 ^ i = 2 ^ i * n := by ring
          _ ≤ 2 ^ i * Tit i n := Nat.mul_le_mul_left _ hxi
      have hnew : 3 ^ (a + 1) * n + (3 * U + 2 ^ i) = 3 * P + 2 ^ i := by rw [hPdef]; ring
      rw [hnew]
      have hstep : n * (3 * P + 2 ^ i) ≤ (3 * n + 1) * P := by nlinarith
      have hnpos : 0 < n := hn
      -- multiply the goal by n
      have key : n * ((3 * n) ^ (a + 1) * (3 * P + 2 ^ i))
          ≤ n * ((3 * n + 1) ^ (a + 1) * 3 ^ (a + 1) * n) := by
        calc n * ((3 * n) ^ (a + 1) * (3 * P + 2 ^ i))
            = (3 * n) ^ (a + 1) * (n * (3 * P + 2 ^ i)) := by ring
          _ ≤ (3 * n) ^ (a + 1) * ((3 * n + 1) * P) := Nat.mul_le_mul_left _ hstep
          _ = (3 * n) * (3 * n + 1) * ((3 * n) ^ a * P) := by ring
          _ ≤ (3 * n) * (3 * n + 1) * ((3 * n + 1) ^ a * 3 ^ a * n) := Nat.mul_le_mul_left _ ih'
          _ = n * ((3 * n + 1) ^ (a + 1) * 3 ^ (a + 1) * n) := by ring
      exact Nat.le_of_mul_le_mul_left key hnpos
    · -- even step: nothing changes
      have hz0 : Tit i n % 2 = 0 := by omega
      have ha : oddc (i + 1) n = oddc i n := by simp [oddc, hz0]
      have hu : numr (i + 1) n = numr i n := by simp [numr, hz]
      rw [ha, hu]; exact ih'

/-- **K167/K168 horizon lemma.** If the coefficient has not crossed before `j`, crosses at `j`, and
`a * 2^j < 3 n (2^j - 3^a)` with `a = oddc j n`, then `T^j n < n`. -/
theorem crossing_descent (n j : Nat) (hn : 1 ≤ n)
    (hnc : ∀ i, i < j → 2 ^ i ≤ 3 ^ (oddc i n))
    (hc : 3 ^ (oddc j n) < 2 ^ j)
    (hbig : oddc j n * 2 ^ j < 3 * n * (2 ^ j - 3 ^ (oddc j n))) :
    Tit j n < n := by
  have hge := state_ge n j hn hnc
  have hcb := correction_bound n j hn hge j le_rfl
  set a := oddc j n with ha
  set P := 3 ^ a * n + numr j n with hP
  have hPeq : P = 2 ^ j * Tit j n := by rw [hP]; exact (Tit_affine j n).symm
  -- a < 3 n
  have han : a < 3 * n := by
    by_contra hge3
    replace hge3 := Nat.le_of_not_lt hge3
    have h1 : 3 * n * (2 ^ j - 3 ^ a) < 3 * n * 2 ^ j := by
      apply Nat.mul_lt_mul_of_pos_left _ (by omega)
      have : 0 < 3 ^ a := by positivity
      omega
    have h2 : 3 * n * 2 ^ j ≤ a * 2 ^ j := Nat.mul_le_mul_right _ hge3
    omega
  -- by contradiction: suppose P ≥ 2^j n
  by_contra hnot
  replace hnot := Nat.le_of_not_lt hnot
  have hP2 : 2 ^ j * n ≤ P := by rw [hPeq]; exact Nat.mul_le_mul_left _ hnot
  have h1 : (3 * n) ^ a * (2 ^ j * n) ≤ (3 * n + 1) ^ a * 3 ^ a * n := le_trans (Nat.mul_le_mul_left _ hP2) hcb
  have hnpos : 0 < n := hn
  have h2 : (3 * n) ^ a * 2 ^ j ≤ (3 * n + 1) ^ a * 3 ^ a := by
    have : n * ((3 * n) ^ a * 2 ^ j) ≤ n * ((3 * n + 1) ^ a * 3 ^ a) := by
      calc n * ((3 * n) ^ a * 2 ^ j) = (3 * n) ^ a * (2 ^ j * n) := by ring
        _ ≤ (3 * n + 1) ^ a * 3 ^ a * n := h1
        _ = n * ((3 * n + 1) ^ a * 3 ^ a) := by ring
    exact Nat.le_of_mul_le_mul_left this hnpos
  have hbern := bernoulli_nat' a (3 * n) (by omega)
  have h3 : (3 * n) ^ a * (2 ^ j * (3 * n - a)) ≤ (3 * n) ^ a * (3 * n * 3 ^ a) := by
    calc (3 * n) ^ a * (2 ^ j * (3 * n - a)) = ((3 * n) ^ a * 2 ^ j) * (3 * n - a) := by ring
      _ ≤ ((3 * n + 1) ^ a * 3 ^ a) * (3 * n - a) := Nat.mul_le_mul_right _ h2
      _ = ((3 * n + 1) ^ a * (3 * n - a)) * 3 ^ a := by ring
      _ ≤ (3 * n) ^ (a + 1) * 3 ^ a := Nat.mul_le_mul_right _ hbern
      _ = (3 * n) ^ a * (3 * n * 3 ^ a) := by ring
  have hpos : 0 < (3 * n) ^ a := by positivity
  have h4 : 2 ^ j * (3 * n - a) ≤ 3 * n * 3 ^ a := Nat.le_of_mul_le_mul_left h3 hpos
  -- contradiction with hbig
  have hsub : 3 * n * (2 ^ j - 3 ^ a) = 3 * n * 2 ^ j - 3 * n * 3 ^ a := Nat.mul_sub _ _ _
  have h5 : a * 2 ^ j < 3 * n * 2 ^ j - 3 * n * 3 ^ a := by rw [← hsub]; exact hbig
  have h6 : 2 ^ j * (3 * n - a) = 2 ^ j * (3 * n) - 2 ^ j * a := Nat.mul_sub _ _ _
  have h7 : 3 * n * 3 ^ a ≤ 3 * n * 2 ^ j := Nat.mul_le_mul_left _ hc.le
  have h8 : 2 ^ j * a ≤ 2 ^ j * (3 * n) := Nat.mul_le_mul_left _ han.le
  have e1 : a * 2 ^ j = 2 ^ j * a := by ring
  have e2 : 3 * n * 2 ^ j = 2 ^ j * (3 * n) := by ring
  omega

#print axioms bernoulli_nat
#print axioms state_ge
#print axioms correction_bound
#print axioms crossing_descent
