import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
/-! Elementary lemmas for the accelerated Collatz map T(x) = x/2 (x even), (3x+1)/2 (x odd), on ℕ.
    Part 1 (core Lean only): growth bound, iterated growth bound, odd-step residue, collision matching,
    singleton fibres above multiples of 3, the all-odd run identity and its smaller-origin barrier. -/

def T (x : Nat) : Nat := if x % 2 = 0 then x / 2 else (3 * x + 1) / 2

/-- `Tit j x = T^[j] x`, applying `T` first. -/
def Tit : Nat → Nat → Nat
  | 0, x => x
  | (j + 1), x => Tit j (T x)

theorem Tit_succ (j x : Nat) : Tit (j + 1) x = Tit j (T x) := rfl
theorem Tit_zero (x : Nat) : Tit 0 x = x := rfl

/-- L1: `T x + 1 ≤ (3/2)(x+1)`, with equality for odd `x`. -/
theorem T_growth (x : Nat) : 2 * (T x + 1) ≤ 3 * (x + 1) := by
  unfold T; split <;> omega

theorem T_growth_odd (x : Nat) (h : x % 2 = 1) : 2 * (T x + 1) = 3 * (x + 1) := by
  unfold T; have : ¬ (x % 2 = 0) := by omega
  simp [this]; omega

/-- L1': iterated growth bound `2^j (T^j x + 1) ≤ 3^j (x + 1)`. -/
theorem Tit_growth : ∀ (j x : Nat), 2 ^ j * (Tit j x + 1) ≤ 3 ^ j * (x + 1) := by
  intro j
  induction j with
  | zero => intro x; simp [Tit_zero]
  | succ j ih =>
    intro x
    rw [Tit_succ]
    have h1 := ih (T x)
    have h2 := T_growth x
    calc 2 ^ (j + 1) * (Tit j (T x) + 1) = 2 * (2 ^ j * (Tit j (T x) + 1)) := by rw [Nat.pow_succ]; ring_nf
      _ ≤ 2 * (3 ^ j * (T x + 1)) := Nat.mul_le_mul_left 2 h1
      _ = 3 ^ j * (2 * (T x + 1)) := by ring_nf
      _ ≤ 3 ^ j * (3 * (x + 1)) := Nat.mul_le_mul_left _ h2
      _ = 3 ^ (j + 1) * (x + 1) := by rw [Nat.pow_succ]; ring_nf

/-- An odd input maps to a value that is 2 modulo 3. -/
theorem T_odd_mod3 (x : Nat) (h : x % 2 = 1) : T x % 3 = 2 := by
  unfold T
  have : ¬ (x % 2 = 0) := by omega
  simp [this]; omega

/-- L5: collision matching. Two distinct integers with the same image are `x` odd and `3x+1`. -/
theorem T_collision (x y : Nat) (h : T x = T y) (hne : x ≠ y) :
    (x % 2 = 1 ∧ y = 3 * x + 1) ∨ (y % 2 = 1 ∧ x = 3 * y + 1) := by
  unfold T at h
  by_cases hx : x % 2 = 0 <;> by_cases hy : y % 2 = 0 <;> simp [hx, hy] at h <;> omega

/-- Theorem A (arbitrary depth): the fibre of a multiple of 3 is the singleton `{2^j y}`. -/
theorem Tit_fibre_mult3 : ∀ (j y x : Nat), 3 ∣ y → Tit j x = y → x = 2 ^ j * y := by
  intro j
  induction j with
  | zero => intro y x _ h; simpa [Tit_zero] using h
  | succ j ih =>
    intro y x h3 h
    rw [Tit_succ] at h
    have hx := ih y (T x) h3 h
    have h3' : 3 ∣ T x := by rw [hx]; exact Dvd.dvd.mul_left h3 _
    by_cases hodd : x % 2 = 1
    · have := T_odd_mod3 x hodd; omega
    · have hev : x % 2 = 0 := by omega
      have : T x = x / 2 := by unfold T; simp [hev]
      rw [Nat.pow_succ]
      have : x = 2 * T x := by omega
      rw [this, hx]; ring

/-- L6: all-odd run identity `T^j(2^j t - 1) + 1 = 3^j t` (for `t ≥ 1`). -/
theorem Tit_allodd : ∀ (j t : Nat), 1 ≤ t → Tit j (2 ^ j * t - 1) + 1 = 3 ^ j * t := by
  intro j
  induction j with
  | zero => intro t ht; simp [Tit_zero]; omega
  | succ j ih =>
    intro t ht
    have hm : 1 ≤ 2 ^ j * t := Nat.mul_le_mul (Nat.one_le_two_pow) ht
    have hx : (2 ^ (j + 1) * t - 1) = 2 * (2 ^ j * t) - 1 := by rw [Nat.pow_succ]; ring_nf
    have hT : T (2 ^ (j + 1) * t - 1) = 2 ^ j * (3 * t) - 1 := by
      rw [hx]; unfold T
      have h1 : (2 * (2 ^ j * t) - 1) % 2 = 1 := by omega
      have h2 : ¬ ((2 * (2 ^ j * t) - 1) % 2 = 0) := by omega
      simp [h2]
      have : 2 ^ j * (3 * t) = 3 * (2 ^ j * t) := by ring
      omega
    rw [Tit_succ, hT]
    have := ih (3 * t) (by omega)
    rw [this]; rw [Nat.pow_succ]; ring

/-- Smaller-origin barrier for the all-odd source: for `m < 2^j t - 1`, `T^j m < T^j (2^j t - 1)`. -/
theorem allodd_barrier (j t m : Nat) (ht : 1 ≤ t) (hm : m < 2 ^ j * t - 1) :
    Tit j m < Tit j (2 ^ j * t - 1) := by
  have h1 := Tit_growth j m
  have h2 := Tit_allodd j t ht
  have hp : 0 < 2 ^ j := Nat.pow_pos (by decide)
  have hpm : m + 1 < 2 ^ j * t := by omega
  have h3 : 3 ^ j * (m + 1) < 3 ^ j * (2 ^ j * t) := by
    exact Nat.mul_lt_mul_of_pos_left hpm (Nat.pow_pos (by decide))
  -- 2^j (T^j m + 1) ≤ 3^j (m+1) < 3^j 2^j t = 2^j (T^j n + 1)
  have h4 : 2 ^ j * (Tit j m + 1) < 2 ^ j * (Tit j (2 ^ j * t - 1) + 1) := by
    rw [h2]
    calc 2 ^ j * (Tit j m + 1) ≤ 3 ^ j * (m + 1) := h1
      _ < 3 ^ j * (2 ^ j * t) := h3
      _ = 2 ^ j * (3 ^ j * t) := by ring
  have := Nat.lt_of_mul_lt_mul_left h4
  omega

/-! Part 2: repeat rigidity (equal parity futures force congruence modulo 2^L) and its size consequence,
    and the one-factor inequality behind the distinct-odd product bound. -/

theorem T_even (x : Nat) (h : x % 2 = 0) : T x = x / 2 := by unfold T; simp [h]
theorem T_odd (x : Nat) (h : x % 2 = 1) : T x = (3 * x + 1) / 2 := by
  unfold T; have : ¬ (x % 2 = 0) := by omega
  simp [this]

/-- L2 (Fact P): if the first `L` parity bits of the orbits of `x` and `y` agree, then `2^L ∣ x - y`. -/
theorem Tit_congr : ∀ (L x y : Nat), (∀ i, i < L → Tit i x % 2 = Tit i y % 2) →
    ((2 : Int) ^ L ∣ (x : Int) - (y : Int)) := by
  intro L
  induction L with
  | zero => intro x y _; simp
  | succ L ih =>
    intro x y h
    have hpar : x % 2 = y % 2 := by simpa [Tit_zero] using h 0 (Nat.succ_pos L)
    have hih : (2 : Int) ^ L ∣ ((T x : Nat) : Int) - ((T y : Nat) : Int) :=
      ih (T x) (T y) (fun i hi => by simpa [Tit_succ] using h (i + 1) (by omega))
    by_cases hx : x % 2 = 0
    · have hy : y % 2 = 0 := by omega
      obtain ⟨a, ha⟩ : ∃ a, x = 2 * a := ⟨x / 2, by omega⟩
      obtain ⟨b, hb⟩ : ∃ b, y = 2 * b := ⟨y / 2, by omega⟩
      have hTx : T x = a := by rw [T_even x hx]; omega
      have hTy : T y = b := by rw [T_even y hy]; omega
      rw [hTx, hTy] at hih
      obtain ⟨k, hk⟩ := hih
      refine ⟨k, ?_⟩
      rw [ha, hb, pow_succ]; push_cast
      linarith [hk]
    · have hx1 : x % 2 = 1 := by omega
      have hy1 : y % 2 = 1 := by omega
      obtain ⟨a, ha⟩ : ∃ a, x = 2 * a + 1 := ⟨x / 2, by omega⟩
      obtain ⟨b, hb⟩ : ∃ b, y = 2 * b + 1 := ⟨y / 2, by omega⟩
      have hTx : T x = 3 * a + 2 := by rw [T_odd x hx1]; omega
      have hTy : T y = 3 * b + 2 := by rw [T_odd y hy1]; omega
      rw [hTx, hTy] at hih
      have h3 : (2 : Int) ^ L ∣ 3 * ((a : Int) - (b : Int)) := by
        have : (((3 * a + 2 : Nat) : Int)) - (((3 * b + 2 : Nat) : Int)) = 3 * ((a : Int) - (b : Int)) := by
          push_cast; ring
        rw [this] at hih; exact hih
      have hcop : IsCoprime ((2 : Int) ^ L) 3 := IsCoprime.pow_left (show IsCoprime (2 : Int) 3 from ⟨-1, 1, by norm_num⟩)
      have hab : (2 : Int) ^ L ∣ (a : Int) - (b : Int) := hcop.dvd_of_dvd_mul_left h3
      obtain ⟨k, hk⟩ := hab
      refine ⟨k, ?_⟩
      rw [ha, hb, pow_succ]; push_cast
      linarith [hk]

/-- L3 (Lemma R): two distinct integers with equal `L`-step parity futures differ by at least `2^L`. -/
theorem Tit_gap (L x y : Nat) (hxy : x < y) (h : ∀ i, i < L → Tit i x % 2 = Tit i y % 2) :
    2 ^ L ≤ y - x := by
  have hd := Tit_congr L x y h
  have hd' : (2 : Int) ^ L ∣ (y : Int) - (x : Int) := by
    have := dvd_neg.mpr hd
    simpa using this
  have hpos : (0 : Int) < (y : Int) - (x : Int) := by omega
  have hle := Int.le_of_dvd hpos hd'
  have : ((2 ^ L : Nat) : Int) ≤ ((y - x : Nat) : Int) := by
    push_cast; rw [Nat.cast_sub hxy.le]; exact_mod_cast hle
  exact_mod_cast this

/-- One-factor inequality behind the distinct-odd product bound: `(1 + 1/(3x))^6 < (x+1)/(x-1)` for `x ≥ 2`,
    in the integer form `(3x+1)^6 (x-1) < 729 x^6 (x+1)`. -/
theorem product_factor (x : Nat) (hx : 2 ≤ x) : (3 * x + 1) ^ 6 * (x - 1) < 729 * x ^ 6 * (x + 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, x = t + 2 := ⟨x - 2, by omega⟩
  have h1 : t + 2 - 1 = t + 1 := by omega
  rw [h1]
  have key : 729 * (t + 2) ^ 6 * (t + 2 + 1) = (3 * (t + 2) + 1) ^ 6 * (t + 1) +
      (22319 + 46385 * t + 38187 * t ^ 2 + 15525 * t ^ 3 + 3105 * t ^ 4 + 243 * t ^ 5) := by ring
  rw [key]
  exact Nat.lt_add_of_pos_right (by positivity)

/-! Part 3: the affine parity identity `2^j T^j(x) = 3^a x + U`, with `a` the number of odd inputs among the
    first `j` steps and `U` the affine numerator (all later affine statements are built on it). -/

theorem Tit_succ' : ∀ (j x : Nat), Tit (j + 1) x = T (Tit j x) := by
  intro j
  induction j with
  | zero => intro x; rfl
  | succ j ih => intro x; rw [Tit_succ, ih (T x), Tit_succ]

/-- number of odd inputs among the first `j` steps -/
def oddc : Nat → Nat → Nat
  | 0, _ => 0
  | (j + 1), x => oddc j x + Tit j x % 2

/-- affine numerator `U` of the first `j` steps -/
def numr : Nat → Nat → Nat
  | 0, _ => 0
  | (j + 1), x => if Tit j x % 2 = 1 then 3 * numr j x + 2 ^ j else numr j x

theorem Tit_affine : ∀ (j x : Nat), 2 ^ j * Tit j x = 3 ^ (oddc j x) * x + numr j x := by
  intro j x
  induction j with
  | zero => simp [Tit_zero, oddc, numr]
  | succ j ih =>
    rw [Tit_succ', oddc, numr]
    by_cases hz : Tit j x % 2 = 1
    · have h2 : 2 * T (Tit j x) = 3 * Tit j x + 1 := by rw [T_odd _ hz]; omega
      simp only [hz, ite_true, Nat.pow_succ]
      calc 2 ^ j * 2 * T (Tit j x) = 2 ^ j * (2 * T (Tit j x)) := by ring
        _ = 2 ^ j * (3 * Tit j x + 1) := by rw [h2]
        _ = 3 * (2 ^ j * Tit j x) + 2 ^ j := by ring
        _ = 3 * (3 ^ oddc j x * x + numr j x) + 2 ^ j := by rw [ih]
        _ = 3 ^ (oddc j x + 1) * x + (3 * numr j x + 2 ^ j) := by rw [Nat.pow_succ]; ring
    · have hz0 : Tit j x % 2 = 0 := by omega
      have h2 : 2 * T (Tit j x) = Tit j x := by rw [T_even _ hz0]; omega
      simp only [hz0, Nat.add_zero, Nat.pow_succ]
      calc 2 ^ j * 2 * T (Tit j x) = 2 ^ j * (2 * T (Tit j x)) := by ring
        _ = 2 ^ j * Tit j x := by rw [h2]
        _ = 3 ^ oddc j x * x + numr j x := ih

/-- Consequence: with `a` odd inputs, `3^a x ≤ 2^j T^j(x)` (the numerator is nonnegative). -/
theorem Tit_lower (j x : Nat) : 3 ^ (oddc j x) * x ≤ 2 ^ j * Tit j x := by
  have := Tit_affine j x; omega


/-- An initial run of `j` odd inputs forces `2^j ∣ n + 1`: the maximal all-odd run of a fixed `n` is `v_2(n+1)`. -/
theorem allodd_run_dvd : ∀ (j n : Nat), (∀ i, i < j → Tit i n % 2 = 1) → 2 ^ j ∣ n + 1 := by
  intro j
  induction j with
  | zero => intro n _; simp
  | succ j ih =>
    intro n h
    have hn : n % 2 = 1 := by simpa [Tit_zero] using h 0 (Nat.succ_pos j)
    have h' : ∀ i, i < j → Tit i (T n) % 2 = 1 := fun i hi => by
      simpa [Tit_succ] using h (i + 1) (by omega)
    have hd := ih (T n) h'
    obtain ⟨k, hk⟩ : ∃ k, n + 1 = 2 * k := ⟨(n + 1) / 2, by omega⟩
    have hT : T n + 1 = 3 * k := by rw [T_odd n hn]; omega
    rw [hT] at hd
    have hcop : Nat.Coprime (2 ^ j) 3 := Nat.Coprime.pow_left _ (by decide)
    have hk' : 2 ^ j ∣ k := hcop.dvd_of_dvd_mul_left hd
    obtain ⟨c, hc⟩ := hk'
    rw [hk, Nat.pow_succ]
    exact ⟨c, by rw [hc]; ring⟩

/-- Corollary: an all-odd run of length `j` from `n` needs `2^j ≤ n + 1`. -/
theorem allodd_run_le (j n : Nat) (h : ∀ i, i < j → Tit i n % 2 = 1) : 2 ^ j ≤ n + 1 :=
  Nat.le_of_dvd (by omega) (allodd_run_dvd j n h)


/-! Part 4: repeated-block defect divisibility. If the first `k` blocks of length `L` of the orbit of `x` all have the
    same odd count `a` and numerator `U`, then `2^(L k) ∣ (2^L - 3^a) x - U` (the defect `D`). -/

theorem Tit_add : ∀ (m n x : Nat), Tit (m + n) x = Tit n (Tit m x) := by
  intro m
  induction m with
  | zero => intro n x; simp [Tit_zero]
  | succ m ih => intro n x; rw [Nat.succ_add, Tit_succ, ih, Tit_succ]

/-- pure recurrence form: `B y(i+1) = A y(i) + U` for `i < k` gives `B^k D_k = A^k D_0`, `D_i = (B-A) y(i) - U`. -/
theorem defect_rec (A B U : Int) (y : Nat → Int) :
    ∀ k : Nat, (∀ i, i < k → B * y (i + 1) = A * y i + U) →
      B ^ k * ((B - A) * y k - U) = A ^ k * ((B - A) * y 0 - U) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro h
    have hk := ih (fun i hi => h i (by omega))
    have hstep := h k (Nat.lt_succ_self k)
    have hD : B * ((B - A) * y (k + 1) - U) = A * ((B - A) * y k - U) := by
      calc B * ((B - A) * y (k + 1) - U) = (B - A) * (B * y (k + 1)) - B * U := by ring
        _ = (B - A) * (A * y k + U) - B * U := by rw [hstep]
        _ = A * ((B - A) * y k - U) := by ring
    calc B ^ (k + 1) * ((B - A) * y (k + 1) - U) = B ^ k * (B * ((B - A) * y (k + 1) - U)) := by ring
      _ = B ^ k * (A * ((B - A) * y k - U)) := by rw [hD]
      _ = A * (B ^ k * ((B - A) * y k - U)) := by ring
      _ = A * (A ^ k * ((B - A) * y 0 - U)) := by rw [hk]
      _ = A ^ (k + 1) * ((B - A) * y 0 - U) := by ring

/-- Repeated-block defect divisibility (pure form): with `B = 2^L` and `A = 3^a` odd. -/
theorem defect_dvd (L a : Nat) (U : Int) (y : Nat → Int) (k : Nat)
    (h : ∀ i, i < k → (2 : Int) ^ L * y (i + 1) = 3 ^ a * y i + U) :
    ((2 : Int) ^ L) ^ k ∣ ((2 : Int) ^ L - 3 ^ a) * y 0 - U := by
  have hk := defect_rec (3 ^ a) (2 ^ L) U y k h
  have h1 : ((2 : Int) ^ L) ^ k ∣ ((3 : Int) ^ a) ^ k * (((2 : Int) ^ L - 3 ^ a) * y 0 - U) := by
    rw [← hk]; exact Dvd.intro _ rfl
  have hc : IsCoprime (((2 : Int) ^ L) ^ k) (((3 : Int) ^ a) ^ k) :=
    IsCoprime.pow (IsCoprime.pow (show IsCoprime (2 : Int) 3 from ⟨-1, 1, by norm_num⟩))
  exact hc.dvd_of_dvd_mul_left h1

/-- Collatz form: if each of the first `k` length-`L` blocks of the orbit of `x` has odd count `a` and numerator `U`,
    then `(2^L)^k ∣ (2^L - 3^a) x - U`. -/
theorem block_defect_collatz (L a U k x : Nat)
    (h : ∀ i, i < k → oddc L (Tit (i * L) x) = a ∧ numr L (Tit (i * L) x) = U) :
    ((2 : Int) ^ L) ^ k ∣ ((2 : Int) ^ L - 3 ^ a) * (x : Int) - (U : Int) := by
  have hy : ∀ i, i < k → (2 : Int) ^ L * ((Tit ((i + 1) * L) x : Nat) : Int)
      = 3 ^ a * ((Tit (i * L) x : Nat) : Int) + (U : Int) := by
    intro i hi
    obtain ⟨ha, hu⟩ := h i hi
    have hadd : Tit ((i + 1) * L) x = Tit L (Tit (i * L) x) := by
      rw [Nat.succ_mul, Tit_add]
    have := Tit_affine L (Tit (i * L) x)
    rw [ha, hu] at this
    rw [hadd]
    exact_mod_cast this
  have := defect_dvd L a (U : Int) (fun i => ((Tit (i * L) x : Nat) : Int)) k hy
  simpa [Tit_zero] using this

#print axioms Tit_add
#print axioms defect_rec
#print axioms defect_dvd
#print axioms block_defect_collatz
#print axioms T_growth
#print axioms Tit_growth
#print axioms T_collision
#print axioms Tit_fibre_mult3
#print axioms Tit_allodd
#print axioms allodd_barrier
#print axioms Tit_congr
#print axioms Tit_gap
#print axioms product_factor
#print axioms Tit_affine
#print axioms allodd_run_dvd
