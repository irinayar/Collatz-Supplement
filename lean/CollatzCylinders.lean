import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.ModEq

/-!
# Source cylinders: residues, spacing, uniqueness of the total exponent, and explicit blocks (module `CollatzCylinders`).

* `unique_pow_two_in_window`  : an interval `[lo, hi)` with `hi ≤ 2 lo` contains at most one power of two
  (so the total exponent `E` of an incoming word at fixed depth and anchor is unique, K155);
* `residue_spacing`           : integers in one residue class mod `M` closer than `M` coincide;
* `cylinder_odd_arrival`      : `2^E w = 3^g u + D` with `w` odd forces `(3^g u + D) % 2^(E+1) = 2^E`;
* `cylinder_unique_mod`       : two sources with the same `(g, E, D)` and odd outputs agree mod `2^(E+1)`;
* `first_exponent_one`        : in a band `[n, H]`, `H = ⌊(4n-2)/3⌋`, a source with first exponent `≥ 2`
  has next state `< n` (hence every genuine return starts with exponent one, i.e. `u ≡ 3 mod 4`);
* explicit blocks of K177/K179: the cylinders `43 mod 64`, `379 mod 512`, their maps, the polynomial
  certificates, and the composed mixed pairs `W_du`, `W_ud`.
-/

theorem unique_pow_two_in_window (lo hi E E' : Nat) (hhi : hi ≤ 2 * lo)
    (h1 : lo ≤ 2 ^ E) (h2 : 2 ^ E < hi) (h3 : lo ≤ 2 ^ E') (h4 : 2 ^ E' < hi) : E = E' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have : 2 ^ (E + 1) ≤ 2 ^ E' := Nat.pow_le_pow_right (by norm_num) hlt
    rw [Nat.pow_succ] at this
    omega
  · have : 2 ^ (E' + 1) ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) hlt
    rw [Nat.pow_succ] at this
    omega

theorem residue_spacing (M x y : Nat) (hmod : x % M = y % M) (hxy : x ≤ y) (hlt : y < x + M) : x = y := by
  rcases Nat.eq_zero_or_pos M with h0 | hM
  · subst h0; omega
  · have hx := Nat.div_add_mod x M
    have hy := Nat.div_add_mod y M
    have hq : x / M ≤ y / M := Nat.div_le_div_right hxy
    by_contra hne
    have hlt' : x / M < y / M := by
      rcases Nat.lt_or_ge (x / M) (y / M) with h | h
      · exact h
      · exfalso; have : x / M = y / M := le_antisymm hq h
        apply hne; rw [← hx, ← hy, this, hmod]
    have hM2 : M * (x / M + 1) ≤ M * (y / M) := Nat.mul_le_mul_left _ hlt'
    have : M * (x / M + 1) = M * (x / M) + M := by ring
    omega

/-- For an odd output `w`, `3^g u + D ≡ 2^E (mod 2^(E+1))`. -/
theorem cylinder_odd_arrival (E g u D w : Nat) (hw : w % 2 = 1) (h : 2 ^ E * w = 3 ^ g * u + D) :
    (3 ^ g * u + D) % 2 ^ (E + 1) = 2 ^ E := by
  rw [← h]
  obtain ⟨m, hm⟩ : ∃ m, w = 2 * m + 1 := ⟨w / 2, by omega⟩
  have hP : 0 < 2 ^ E := by positivity
  have e : 2 ^ E * w = 2 ^ (E + 1) * m + 2 ^ E := by rw [hm, Nat.pow_succ]; ring
  rw [e, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (by rw [Nat.pow_succ]; omega)

/-- Two sources with the same word data and odd outputs agree modulo `2^(E+1)`. -/
theorem cylinder_unique_mod (E g u u' D w w' : Nat) (hw : w % 2 = 1) (hw' : w' % 2 = 1)
    (h : 2 ^ E * w = 3 ^ g * u + D) (h' : 2 ^ E * w' = 3 ^ g * u' + D) :
    (3 ^ g * u) % 2 ^ (E + 1) = (3 ^ g * u') % 2 ^ (E + 1) := by
  have a1 := cylinder_odd_arrival E g u D w hw h
  have a2 := cylinder_odd_arrival E g u' D w' hw' h'
  have : (3 ^ g * u + D) % 2 ^ (E + 1) = (3 ^ g * u' + D) % 2 ^ (E + 1) := by rw [a1, a2]
  exact Nat.ModEq.add_right_cancel' D this

/-- A source `u ≤ H = ⌊(4n-2)/3⌋` whose first exponent is at least two lands below `n`. -/
theorem first_exponent_one (n u : Nat) (hn : 1 ≤ n) (hu : u ≤ (4 * n - 2) / 3) (hd : 4 ∣ 3 * u + 1) :
    (3 * u + 1) / 4 < n := by
  have h3 : 3 * ((4 * n - 2) / 3) ≤ 4 * n - 2 := Nat.mul_div_le _ _
  obtain ⟨k, hk⟩ := hd
  omega

/-- Equivalent form: exponent `1` for an odd source means `u % 4 = 3`. -/
theorem exponent_one_iff (u : Nat) (hu : u % 2 = 1) : (3 * u + 1) % 4 = 2 ↔ u % 4 = 3 := by omega

/-! ## Explicit cylinders of K177 -/
/-- Cylinder `a = 43 mod 64`: valuations `(1,2,2)`, output `(27a+23)/32 = 37 + 54k`. -/
theorem blockA1 (k : Nat) :
    3 * (43 + 64 * k) + 1 = 2 * (65 + 96 * k) ∧ (65 + 96 * k) % 2 = 1 ∧
    3 * (65 + 96 * k) + 1 = 4 * (49 + 72 * k) ∧ (49 + 72 * k) % 2 = 1 ∧
    3 * (49 + 72 * k) + 1 = 4 * (37 + 54 * k) ∧ (37 + 54 * k) % 2 = 1 ∧
    32 * (37 + 54 * k) = 27 * (43 + 64 * k) + 23 := by
  refine ⟨by ring, by omega, by ring, by omega, by ring, by omega, by ring⟩

/-- Cylinder `a = 379 mod 512`: valuations `(1,2,1,2,2)`, output `(243a+319)/256 = 361 + 486k`. -/
theorem blockA2 (k : Nat) :
    3 * (379 + 512 * k) + 1 = 2 * (569 + 768 * k) ∧ (569 + 768 * k) % 2 = 1 ∧
    3 * (569 + 768 * k) + 1 = 4 * (427 + 576 * k) ∧ (427 + 576 * k) % 2 = 1 ∧
    3 * (427 + 576 * k) + 1 = 2 * (641 + 864 * k) ∧ (641 + 864 * k) % 2 = 1 ∧
    3 * (641 + 864 * k) + 1 = 4 * (481 + 648 * k) ∧ (481 + 648 * k) % 2 = 1 ∧
    3 * (481 + 648 * k) + 1 = 4 * (361 + 486 * k) ∧ (361 + 486 * k) % 2 = 1 ∧
    256 * (361 + 486 * k) = 243 * (379 + 512 * k) + 319 := by
  refine ⟨by ring, by omega, by ring, by omega, by ring, by omega, by ring, by omega, by ring, by omega, by ring⟩

/-- Polynomial certificates of K177 (exact shifted forms). -/
theorem poly_A1 (t : Int) : 18 * (107 + t) ^ 2 - 1676 * (107 + t) - 1150 = 18 * t ^ 2 + 2176 * t + 25600 := by ring
theorem poly_A2 (t : Int) :
    486 * (1915 + t) ^ 2 - 750084 * (1915 + t) - 813450 = 486 * t ^ 2 + 1111296 * t + 345047040 := by ring
theorem poly_A1_pos (t : Int) (ht : 0 ≤ t) : 0 < 18 * (107 + t) ^ 2 - 1676 * (107 + t) - 1150 := by
  rw [poly_A1]; nlinarith
theorem poly_A2_pos (t : Int) (ht : 0 ≤ t) : 0 < 486 * (1915 + t) ^ 2 - 750084 * (1915 + t) - 813450 := by
  rw [poly_A2]; nlinarith
theorem poly_A1_neg_at_43 : 18 * (43 : Int) ^ 2 - 1676 * 43 - 1150 < 0 := by norm_num
theorem poly_A2_neg_at_1403 : 486 * (1403 : Int) ^ 2 - 750084 * 1403 - 813450 < 0 := by norm_num

/-! ## The mixed pairs of K179 -/
/-- `W_du = A2 A3`: `(243 a + 319)/256` then `(2187 b + 3767)/2048` compose to `(3^12 a + 1662005)/2^19`. -/
theorem pair_du (a x1 x2 : Nat) (h1 : 256 * x1 = 243 * a + 319) (h2 : 2048 * x2 = 2187 * x1 + 3767) :
    524288 * x2 = 531441 * a + 1662005 := by
  calc 524288 * x2 = 256 * (2048 * x2) := by ring
    _ = 256 * (2187 * x1 + 3767) := by rw [h2]
    _ = 2187 * (256 * x1) + 256 * 3767 := by ring
    _ = 2187 * (243 * a + 319) + 256 * 3767 := by rw [h1]
    _ = 531441 * a + 1662005 := by ring

/-- `W_ud = A3 A2`: `(2187 a + 3767)/2048` then `(243 b + 319)/256` compose to `(3^12 a + 1568693)/2^19`. -/
theorem pair_ud (a x1 x2 : Nat) (h1 : 2048 * x1 = 2187 * a + 3767) (h2 : 256 * x2 = 243 * x1 + 319) :
    524288 * x2 = 531441 * a + 1568693 := by
  calc 524288 * x2 = 2048 * (256 * x2) := by ring
    _ = 2048 * (243 * x1 + 319) := by rw [h2]
    _ = 243 * (2048 * x1) + 2048 * 319 := by ring
    _ = 243 * (2187 * a + 3767) + 2048 * 319 := by rw [h1]
    _ = 531441 * a + 1568693 := by ring

/-- Each pair expands: `A = 3^12 > D = 2^19`, hence `b > a` for positive offsets. -/
theorem pair_expands (a x : Nat) (B : Nat) (hB : 0 < B) (h : 524288 * x = 531441 * a + B) : a < x := by
  by_contra hle
  have hle' : x ≤ a := Nat.le_of_not_lt hle
  have : 524288 * x ≤ 524288 * a := Nat.mul_le_mul_left _ hle'
  have h2 : 524288 * a ≤ 531441 * a := Nat.mul_le_mul_right _ (by norm_num)
  omega

#print axioms unique_pow_two_in_window
#print axioms residue_spacing
#print axioms cylinder_unique_mod
#print axioms first_exponent_one
#print axioms blockA2
#print axioms pair_du
