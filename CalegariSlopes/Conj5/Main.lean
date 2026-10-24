/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.ADB.Main
public import CalegariSlopes.Conj5.Lemmas

@[expose] public section

/-!
# Lemma 8.1 and Theorem 8.2: Loeffler's conjecture at p = 3 on its exact intervals

Every theorem of `CalegariSlopes/ChallengeConj5.lean`, with the same name and statement, proved from
`CalegariSlopes.ADB.adb` (Theorem 2.3) and the lemmas of `Conj5/Lemmas.lean`, as in the proofs of Lemma 8.1 and
Theorem 8.2 of the paper; the challenge is not imported. Comparator checks the pair (`config-conj5.json`).
-/

namespace CalegariSlopes.Conj5

open CalegariSlopes CalegariSlopes.ADB

/-- (F) `U^(r) = A^(r) D B^(r)`: for all `i, j ≥ 1`,
`Σ_{1 ≤ p ≤ min(i, j)} (γ^(p-i) A_ip) D_p (γ^(j-p) B_pj) = γ^(j-i) u_ij`, in any field of characteristic `0`. -/
theorem factorization {K : Type*} [Field K] [CharZero K] (γ : K) (hγ : γ ≠ 0) (i j : ℕ) (hi : 1 ≤ i)
    (hj : 1 ≤ j) :
    ∑ p ∈ Finset.Icc 1 (min i j),
        (γ ^ ((p : ℤ) - i) * (A i p : K)) * (D p : K) * (γ ^ ((j : ℤ) - p) * (B p j : K)) =
      γ ^ ((j : ℤ) - i) * (u i j : K) := by
  have h := congrArg (fun x : ℚ => (x : K)) (adb i j hi hj)
  simp only [Rat.cast_sum, Rat.cast_mul] at h
  rw [← h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have e : γ ^ ((j : ℤ) - i) = γ ^ ((p : ℤ) - i) * γ ^ ((j : ℤ) - p) := by
    rw [← zpow_add₀ hγ]
    congr 1
    ring
  rw [e]
  ring

/-- The scaled factors are unit triangular: `A` lower, `B` upper, on the indices `i, j ≥ 1`. -/
theorem factors_unitTriangular (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    (i < j → A i j = 0) ∧ (j < i → B i j = 0) ∧ A i i = 1 ∧ B i i = 1 := by
  have _ := hj
  exact ⟨Newton.A_eq_zero_of_lt i j, Newton.B_eq_zero_of_lt i j, Newton.A_self i hi, Newton.B_self i hi⟩

/-- (U) Uniqueness: a factorization `U^(r) = A' D' B'` with `A'` unit lower triangular, `B'` unit upper triangular
and `D'` diagonal (indices `≥ 1`) is `A' = A^(r)`, `B' = B^(r)`, `D' = D`. -/
theorem factorization_unique {K : Type*} [Field K] [CharZero K] (γ : K) (hγ : γ ≠ 0)
    (A' B' : ℕ → ℕ → K) (D' : ℕ → K)
    (hA'0 : ∀ i p, 1 ≤ i → i < p → A' i p = 0) (hA'1 : ∀ i, 1 ≤ i → A' i i = 1)
    (hB'0 : ∀ p j, 1 ≤ j → j < p → B' p j = 0) (hB'1 : ∀ p, 1 ≤ p → B' p p = 1)
    (h : ∀ i j, 1 ≤ i → 1 ≤ j →
      ∑ p ∈ Finset.Icc 1 (min i j), A' i p * D' p * B' p j = γ ^ ((j : ℤ) - i) * (u i j : K))
    (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    A' i j = γ ^ ((j : ℤ) - i) * (A i j : K) ∧ B' i j = γ ^ ((j : ℤ) - i) * (B i j : K) ∧
      D' i = (D i : K) := by
  have key := ldu_unique (fun i p => γ ^ ((p : ℤ) - i) * (A i p : K))
    (fun p j => γ ^ ((j : ℤ) - p) * (B p j : K)) A' B' (fun p => (D p : K)) D'
    (fun i hi => by simp [Newton.A_self i hi]) (fun i hi => by simp [Newton.B_self i hi]) hA'1 hB'1
    (fun p _ => by exact_mod_cast (Newton.D_pos p).ne')
    (fun i j hi hj => by rw [factorization γ hγ i j hi hj, h i j hi hj])
  refine ⟨?_, ?_, ((key i hi).1).symm⟩
  · rcases lt_or_ge i j with hij | hij
    · rw [hA'0 i j hi hij, Newton.A_eq_zero_of_lt i j hij, Rat.cast_zero, mul_zero]
    · exact ((key j hj).2.2 i hij).symm
  · rcases lt_or_ge j i with hij | hij
    · rw [hB'0 i j hj hij, Newton.B_eq_zero_of_lt i j hij, Rat.cast_zero, mul_zero]
    · exact ((key i hi).2.1 j hij).symm

/-- (M), first bound: `v_3(B^(r)_ij) ≥ (6r - 2)(j - i)` above the diagonal, for every `r`. -/
theorem valuation_B_ge (r : ℚ) (i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (h : B i j ≠ 0) :
    (6 * r - 2) * ((j : ℚ) - i) ≤ (padicValRat 3 (B i j) : ℚ) + (6 * r - 3) * ((j : ℚ) - i) := by
  have h1 : ((j : ℤ) - i : ℤ) ≤ padicValRat 3 (B i j) := padicValRat_B_ge i j hi hij h
  have h2 : (j : ℚ) - i ≤ (padicValRat 3 (B i j) : ℚ) := by exact_mod_cast h1
  have e : (padicValRat 3 (B i j) : ℚ) + (6 * r - 3) * ((j : ℚ) - i) - (6 * r - 2) * ((j : ℚ) - i) =
      (padicValRat 3 (B i j) : ℚ) - ((j : ℚ) - i) := by ring
  linarith

/-- (M), second bound: `v_3(A^(r)_ij) ≥ (4 - 6r)(i - j)` below the diagonal, for every `r`. -/
theorem valuation_A_ge (r : ℚ) (i j : ℕ) (hj : 1 ≤ j) (hij : j < i) (h : A i j ≠ 0) :
    (4 - 6 * r) * ((i : ℚ) - j) ≤ (padicValRat 3 (A i j) : ℚ) + (6 * r - 3) * ((j : ℚ) - i) := by
  have h1 : ((i : ℤ) - j : ℤ) ≤ padicValRat 3 (A i j) := padicValRat_A_ge i j hj hij h
  have h2 : (i : ℚ) - j ≤ (padicValRat 3 (A i j) : ℚ) := by exact_mod_cast h1
  have e : (padicValRat 3 (A i j) : ℚ) + (6 * r - 3) * ((j : ℚ) - i) - (4 - 6 * r) * ((i : ℚ) - j) =
      (padicValRat 3 (A i j) : ℚ) - ((i : ℚ) - j) := by ring
  linarith

/-- Off the support or on the diagonal: the entry of `B` is `0` or the weighted valuation is `0`. -/
theorem B_cases (r : ℚ) (i j : ℕ) (hi : 1 ≤ i) (hij : ¬ i < j) :
    B i j = 0 ∨ (padicValRat 3 (B i j) : ℚ) + (6 * r - 3) * ((j : ℚ) - i) = 0 := by
  rcases lt_or_eq_of_le (not_lt.mp hij) with h | rfl
  · exact Or.inl (Newton.B_eq_zero_of_lt i j h)
  · right
    rw [Newton.B_self j hi]
    simp

/-- Off the support or on the diagonal: the entry of `A` is `0` or the weighted valuation is `0`. -/
theorem A_cases (r : ℚ) (i j : ℕ) (hi : 1 ≤ i) (hij : ¬ j < i) :
    A i j = 0 ∨ (padicValRat 3 (A i j) : ℚ) + (6 * r - 3) * ((j : ℚ) - i) = 0 := by
  rcases lt_or_eq_of_le (not_lt.mp hij) with h | rfl
  · exact Or.inl (Newton.A_eq_zero_of_lt i j h)
  · right
    rw [Newton.A_self i hi]
    simp

/-- The weighted valuation of `B_24` is `12r - 4`. -/
theorem wval_B_24 (r : ℚ) :
    (padicValRat 3 (B 2 4) : ℚ) + (6 * r - 3) * (((4 : ℕ) : ℚ) - ((2 : ℕ) : ℚ)) = 12 * r - 4 := by
  rw [padicValRat_B_24]
  push_cast
  ring

/-- The weighted valuation of `A_42` is `8 - 12r`. -/
theorem wval_A_42 (r : ℚ) :
    (padicValRat 3 (A 4 2) : ℚ) + (6 * r - 3) * (((2 : ℕ) : ℚ) - ((4 : ℕ) : ℚ)) = 8 - 12 * r := by
  rw [padicValRat_A_42]
  push_cast
  ring

theorem B_24_ne_zero : B 2 4 ≠ 0 := by
  rw [B_24]
  norm_num

theorem A_42_ne_zero : A 4 2 ≠ 0 := by
  rw [A_42]
  norm_num

/-- (I) `A^(r)` and `B^(r)` have all their entries in `O_{C_3}` iff `1/3 ≤ r ≤ 2/3`. -/
theorem integral_iff (r : ℚ) :
    (∀ i j : ℕ, 1 ≤ i → 1 ≤ j →
      (B i j = 0 ∨ 0 ≤ (padicValRat 3 (B i j) : ℚ) + (6 * r - 3) * ((j : ℚ) - i)) ∧
      (A i j = 0 ∨ 0 ≤ (padicValRat 3 (A i j) : ℚ) + (6 * r - 3) * ((j : ℚ) - i))) ↔
      1 / 3 ≤ r ∧ r ≤ 2 / 3 := by
  constructor
  · intro H
    have hB := ((H 2 4 (by norm_num) (by norm_num)).1.resolve_left B_24_ne_zero)
    have hA := ((H 4 2 (by norm_num) (by norm_num)).2.resolve_left A_42_ne_zero)
    rw [wval_B_24] at hB
    rw [wval_A_42] at hA
    constructor <;> linarith
  · rintro ⟨h1, h2⟩ i j hi hj
    constructor
    · by_cases hij : i < j
      · by_cases hB : B i j = 0
        · exact Or.inl hB
        · right
          have := valuation_B_ge r i j hi hij hB
          have hd : (0 : ℚ) ≤ (j : ℚ) - i := by
            have : (i : ℚ) < j := by exact_mod_cast hij
            linarith
          nlinarith
      · rcases B_cases r i j hi hij with h | h
        · exact Or.inl h
        · exact Or.inr h.ge
    · by_cases hij : j < i
      · by_cases hA : A i j = 0
        · exact Or.inl hA
        · right
          have := valuation_A_ge r i j hj hij hA
          have hd : (0 : ℚ) ≤ (i : ℚ) - j := by
            have : (j : ℚ) < i := by exact_mod_cast hij
            linarith
          nlinarith
      · rcases A_cases r i j hi hij with h | h
        · exact Or.inl h
        · exact Or.inr h.ge

/-- (M) `A^(r)` and `B^(r)` are congruent to the identity modulo the maximal ideal of `O_{C_3}` (every entry off the
diagonal has positive valuation; the diagonal is `1`) iff `1/3 < r < 2/3`. -/
theorem congr_maximal_iff (r : ℚ) :
    (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → i ≠ j →
      (B i j = 0 ∨ 0 < (padicValRat 3 (B i j) : ℚ) + (6 * r - 3) * ((j : ℚ) - i)) ∧
      (A i j = 0 ∨ 0 < (padicValRat 3 (A i j) : ℚ) + (6 * r - 3) * ((j : ℚ) - i))) ↔
      1 / 3 < r ∧ r < 2 / 3 := by
  constructor
  · intro H
    have hB := ((H 2 4 (by norm_num) (by norm_num) (by norm_num)).1.resolve_left B_24_ne_zero)
    have hA := ((H 4 2 (by norm_num) (by norm_num) (by norm_num)).2.resolve_left A_42_ne_zero)
    rw [wval_B_24] at hB
    rw [wval_A_42] at hA
    constructor <;> linarith
  · rintro ⟨h1, h2⟩ i j hi hj hne
    constructor
    · by_cases hij : i < j
      · by_cases hB : B i j = 0
        · exact Or.inl hB
        · right
          have := valuation_B_ge r i j hi hij hB
          have hd : (1 : ℚ) ≤ (j : ℚ) - i := by
            have : (i : ℚ) + 1 ≤ j := by exact_mod_cast hij
            linarith
          nlinarith
      · exact Or.inl (Newton.B_eq_zero_of_lt i j (by omega))
    · by_cases hij : j < i
      · by_cases hA : A i j = 0
        · exact Or.inl hA
        · right
          have := valuation_A_ge r i j hj hij hA
          have hd : (1 : ℚ) ≤ (i : ℚ) - j := by
            have : (j : ℚ) + 1 ≤ i := by exact_mod_cast hij
            linarith
          nlinarith
      · exact Or.inl (Newton.A_eq_zero_of_lt i j (by omega))

/-- (M), uniform bound: for `1/3 ≤ r ≤ 2/3` every entry of `A^(r)`, `B^(r)` off the diagonal has valuation
`≥ 1 - |6r - 3|`, so `sup |A^(r) - I|, sup |B^(r) - I| ≤ 3^(-(1 - |6r - 3|))`. -/
theorem valuation_uniform (r : ℚ) (h1 : 1 / 3 ≤ r) (h2 : r ≤ 2 / 3) (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hij : i ≠ j) :
    (B i j = 0 ∨ 1 - |6 * r - 3| ≤ (padicValRat 3 (B i j) : ℚ) + (6 * r - 3) * ((j : ℚ) - i)) ∧
      (A i j = 0 ∨ 1 - |6 * r - 3| ≤ (padicValRat 3 (A i j) : ℚ) + (6 * r - 3) * ((j : ℚ) - i)) := by
  have habs1 := neg_abs_le (6 * r - 3)
  have habs2 := le_abs_self (6 * r - 3)
  constructor
  · by_cases hlt : i < j
    · by_cases hB : B i j = 0
      · exact Or.inl hB
      · right
        have := valuation_B_ge r i j hi hlt hB
        have hd : (1 : ℚ) ≤ (j : ℚ) - i := by
          have : (i : ℚ) + 1 ≤ j := by exact_mod_cast hlt
          linarith
        nlinarith
    · exact Or.inl (Newton.B_eq_zero_of_lt i j (by omega))
  · by_cases hlt : j < i
    · by_cases hA : A i j = 0
      · exact Or.inl hA
      · right
        have := valuation_A_ge r i j hj hlt hA
        have hd : (1 : ℚ) ≤ (i : ℚ) - j := by
          have : (j : ℚ) + 1 ≤ i := by exact_mod_cast hlt
          linarith
        nlinarith
    · exact Or.inl (Newton.A_eq_zero_of_lt i j (by omega))

/-- (P) `A^(r)` and `B^(r)` are congruent to the identity modulo `3` (every entry off the diagonal has valuation
`≥ 1`; the diagonal is `1`) iff `5/12 ≤ r ≤ 7/12`. -/
theorem congr_three_iff (r : ℚ) :
    (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → i ≠ j →
      (B i j = 0 ∨ 1 ≤ (padicValRat 3 (B i j) : ℚ) + (6 * r - 3) * ((j : ℚ) - i)) ∧
      (A i j = 0 ∨ 1 ≤ (padicValRat 3 (A i j) : ℚ) + (6 * r - 3) * ((j : ℚ) - i))) ↔
      5 / 12 ≤ r ∧ r ≤ 7 / 12 := by
  constructor
  · intro H
    have hB := ((H 2 4 (by norm_num) (by norm_num) (by norm_num)).1.resolve_left B_24_ne_zero)
    have hA := ((H 4 2 (by norm_num) (by norm_num) (by norm_num)).2.resolve_left A_42_ne_zero)
    rw [wval_B_24] at hB
    rw [wval_A_42] at hA
    constructor <;> linarith
  · rintro ⟨h1, h2⟩ i j hi hj hne
    constructor
    · by_cases hlt : i < j
      · by_cases hB : B i j = 0
        · exact Or.inl hB
        · right
          rcases (show j = i + 1 ∨ i + 2 ≤ j by omega) with rfl | h2j
          · have hv := padicValRat_B_succ i hi
            have hz : (2 : ℤ) ≤ padicValRat 3 (B i (i + 1)) := by rw [hv]; omega
            have hv' : (2 : ℚ) ≤ (padicValRat 3 (B i (i + 1)) : ℚ) := by exact_mod_cast hz
            push_cast
            linarith
          · have := valuation_B_ge r i j hi hlt hB
            have hd : (2 : ℚ) ≤ (j : ℚ) - i := by
              have : (i : ℚ) + 2 ≤ j := by exact_mod_cast h2j
              linarith
            nlinarith
      · exact Or.inl (Newton.B_eq_zero_of_lt i j (by omega))
    · by_cases hlt : j < i
      · by_cases hA : A i j = 0
        · exact Or.inl hA
        · right
          rcases (show i = j + 1 ∨ j + 2 ≤ i by omega) with rfl | h2i
          · have hv := padicValRat_A_succ j hj
            have hz : (2 : ℤ) ≤ padicValRat 3 (A (j + 1) j) := by rw [hv]; omega
            have hv' : (2 : ℚ) ≤ (padicValRat 3 (A (j + 1) j) : ℚ) := by exact_mod_cast hz
            push_cast
            linarith
          · have := valuation_A_ge r i j hj hlt hA
            have hd : (2 : ℚ) ≤ (i : ℚ) - j := by
              have : (j : ℚ) + 2 ≤ i := by exact_mod_cast h2i
              linarith
            nlinarith
      · exact Or.inl (Newton.A_eq_zero_of_lt i j (by omega))

/-- The witness of optimality above the diagonal: `B_24 = 3060/77`. -/
theorem B_two_four : B 2 4 = 3060 / 77 := B_24

/-- The witness of optimality below the diagonal: `A_42 = 1530/77`. -/
theorem A_four_two : A 4 2 = 1530 / 77 := A_42

/-- `v_3(B_24) = 2`, so `v_3(B^(r)_24) = 12r - 4`. -/
theorem padicValRat_B_two_four : padicValRat 3 (B 2 4) = 2 := padicValRat_B_24

/-- `v_3(A_42) = 2`, so `v_3(A^(r)_42) = 8 - 12r`. -/
theorem padicValRat_A_four_two : padicValRat 3 (A 4 2) = 2 := padicValRat_A_42

end CalegariSlopes.Conj5
