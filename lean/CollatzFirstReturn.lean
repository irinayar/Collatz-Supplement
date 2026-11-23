import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CollatzElementary
import CollatzPhase

/-!
# Genuine first returns to the low band (module `CollatzFirstReturn`).

For an odd threshold `n` put `H n = ⌊(4n-2)/3⌋` and call the shortcut path of `u` (`Tit i u`) a *genuine first return of length `j`*
when `u ∈ [n, H]`, `0 < j`, every proper state `Tit i u` (`0 < i < j`) is above `H`, and the endpoint `Tit j u ∈ [n, H]`.
(The final output may equal the source.)

* `genuine_unique_length` : a source has at most one return length (the earlier endpoint would be a forbidden proper state);
* `genuine_states_distinct`: the states `Tit i u`, `0 ≤ i < j`, are pairwise distinct (no repeated input before the return);
* `genuine_source_odd`, `genuine_source_mod4` : a genuine return starts at an odd `u` with `u ≡ 3 (mod 4)`;
* `genuine_of_bounds`     : a sufficient criterion used for explicit examples (a family of thresholds from one trajectory).
-/

def Hband (n : Nat) : Nat := (4 * n - 2) / 3

/-- A genuine first return of length `j` from the source `u` to the band `[n, Hband n]`. -/
def Genuine (n u j : Nat) : Prop :=
  n ≤ u ∧ u ≤ Hband n ∧ 0 < j ∧ (∀ i, 0 < i → i < j → Hband n < Tit i u) ∧ n ≤ Tit j u ∧ Tit j u ≤ Hband n

theorem genuine_unique_length (n u j j' : Nat) (h : Genuine n u j) (h' : Genuine n u j') : j = j' := by
  obtain ⟨_, _, hj, hp, hn1, hn2⟩ := h
  obtain ⟨_, _, hj', hp', hn1', hn2'⟩ := h'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := hp' j hj hlt; omega
  · have := hp j' hj' hlt; omega

theorem genuine_states_distinct (n u j : Nat) (h : Genuine n u j) :
    ∀ i k, i < k → k < j → Tit i u ≠ Tit k u := by
  obtain ⟨_, _, hj, hp, hn1, hn2⟩ := h
  intro i k hik hkj heq
  -- Tit j u = Tit (j - k) (Tit k u) = Tit (j - k) (Tit i u) = Tit (j - (k - i)) u, a proper state in the band
  have e1 : Tit j u = Tit (j - k) (Tit k u) := by
    have := Tit_add k (j - k) u
    rw [show k + (j - k) = j by omega] at this
    exact this
  have e2 : Tit (i + (j - k)) u = Tit (j - k) (Tit i u) := Tit_add i (j - k) u
  have e3 : Tit (i + (j - k)) u = Tit j u := by rw [e2, heq, ← e1]
  have hpos : 0 < i + (j - k) := by omega
  have hlt : i + (j - k) < j := by omega
  have := hp _ hpos hlt
  omega

theorem genuine_source_odd (n u j : Nat) (hn : 1 ≤ n) (h : Genuine n u j) : u % 2 = 1 := by
  obtain ⟨hnu, huH, hj, hp, hn1, hn2⟩ := h
  by_contra hev
  have hev' : u % 2 = 0 := by omega
  have hT : T u = u / 2 := T_even u hev'
  have hH : u / 2 < n := by unfold Hband at huH; omega
  by_cases hj1 : j = 1
  · subst hj1
    have : Tit 1 u = T u := rfl
    omega
  · have hj2 : 1 < j := by omega
    have := hp 1 (by omega) hj2
    have e : Tit 1 u = T u := rfl
    unfold Hband at this huH
    omega

theorem genuine_source_mod4 (n u j : Nat) (hn : 1 ≤ n) (h : Genuine n u j) : u % 4 = 3 := by
  have hodd := genuine_source_odd n u j hn h
  obtain ⟨hnu, huH, hj, hp, hn1, hn2⟩ := h
  by_contra hne
  have h1 : u % 4 = 1 := by omega
  -- u ≡ 1 mod 4: T u = (3u+1)/2 is even and T (T u) = (3u+1)/4 < n
  have hT1 : T u = (3 * u + 1) / 2 := T_odd u hodd
  have hev : (T u) % 2 = 0 := by rw [hT1]; omega
  have hT2 : T (T u) = (3 * u + 1) / 4 := by rw [T_even _ hev, hT1]; omega
  have hlt : (3 * u + 1) / 4 < n := by unfold Hband at huH; omega
  by_cases hj2 : j = 2
  · subst hj2
    have e : Tit 2 u = T (T u) := rfl
    omega
  · by_cases hj1 : j = 1
    · subst hj1
      have e : Tit 1 u = T u := rfl
      -- T u = (3u+1)/2 > H when u ≥ n ... then not in band
      unfold Hband at huH hn2
      omega
    · have hj3 : 2 < j := by omega
      have := hp 2 (by omega) hj3
      have e : Tit 2 u = T (T u) := rfl
      omega

/-- A criterion for explicit examples: a trajectory with `Tit j u = w`, all proper states at least `z`, and
`n ≤ w ≤ Hband n`, `n ≤ u ≤ Hband n`, `Hband n < z` gives a genuine return of length `j`. -/
theorem genuine_of_bounds (n u j w z : Nat) (hj : 0 < j) (hw : Tit j u = w)
    (hprop : ∀ i, 0 < i → i < j → z ≤ Tit i u) (hz : Hband n < z)
    (hu1 : n ≤ u) (hu2 : u ≤ Hband n) (hw1 : n ≤ w) (hw2 : w ≤ Hband n) : Genuine n u j := by
  refine ⟨hu1, hu2, hj, fun i hi1 hi2 => lt_of_lt_of_le hz (hprop i hi1 hi2), ?_, ?_⟩
  · rw [hw]; exact hw1
  · rw [hw]; exact hw2

#print axioms genuine_unique_length
#print axioms genuine_states_distinct
#print axioms genuine_source_odd
#print axioms genuine_source_mod4
#print axioms genuine_of_bounds
