/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.ADB.Defs

@[expose] public section

/-!
# Loeffler's conjecture at p = 3, weight 0, on its exact intervals (statement)

The statements of Lemma 8.1 and Theorem 8.2 of the paper, with `sorry` proofs: the challenge of Comparator
(`config-conj5.json`), which nothing imports, so its warnings `declaration uses sorry` are expected;
`CalegariSlopes/Conj5/Main.lean` proves them under the same names. `(F)` and `(U)` below are Lemma 8.1 (a), `(I)`,
`(M)` and `(P)` are Theorem 8.2 (a), (b) and (c), and the witnesses are Lemma 8.1 (c).

`u` is the matrix of `U_3` in the basis `g, g ^ 2, ...` of `CalegariSlopes/Target.lean`; `A`, `B`, `D` are Loeffler's
factors of `CalegariSlopes/ADB/Defs.lean` (`A` unit lower triangular, `B` unit upper triangular, `D` diagonal,
`ADB = U` is `CalegariSlopes.ADB.adb`). For a rational `r` let `γ` have `v_3(γ) = 6r - 3`, and let
`U^(r)_ij = γ^(j-i) u_ij`, `A^(r)_ij = γ^(j-i) A_ij`, `B^(r)_ij = γ^(j-i) B_ij` (Section 8 of the paper).

* `factorization`, `factorization_unique`, `factors_unitTriangular`: `U^(r) = A^(r) D B^(r)` over any field of
  characteristic `0` containing `γ ≠ 0`, the unique factorization with unit triangular outer factors and a diagonal
  middle factor; so `D` does not depend on `r`.
* `integral_iff` (I), `congr_maximal_iff` (M), `congr_three_iff` (P): for an entry `x` of `A` or `B` at `(i, j)`,
  `v_3(γ^(j-i) x) = v_3(x) + (6r - 3)(j - i)`, written `padicValRat 3 x + (6 * r - 3) * (j - i)`; an entry `x = 0`
  has valuation `+∞` and is exempted by the disjunct `x = 0` (`padicValRat 3 0 = 0`).
* `valuation_B_ge`, `valuation_A_ge`, `valuation_uniform`: the bounds of (M).
* `B_two_four`, `A_four_two`, `padicValRat_B_two_four`, `padicValRat_A_four_two`: the witnesses of optimality.
-/

namespace CalegariSlopes.Conj5

open CalegariSlopes.ADB

/-- (F) `U^(r) = A^(r) D B^(r)`: for all `i, j ≥ 1`,
`Σ_{1 ≤ p ≤ min(i, j)} (γ^(p-i) A_ip) D_p (γ^(j-p) B_pj) = γ^(j-i) u_ij`, in any field of characteristic `0`. -/
theorem factorization {K : Type*} [Field K] [CharZero K] (γ : K) (hγ : γ ≠ 0) (i j : ℕ) (hi : 1 ≤ i)
    (hj : 1 ≤ j) :
    ∑ p ∈ Finset.Icc 1 (min i j),
        (γ ^ ((p : ℤ) - i) * (A i p : K)) * (D p : K) * (γ ^ ((j : ℤ) - p) * (B p j : K)) =
      γ ^ ((j : ℤ) - i) * (u i j : K) := by
  sorry

/-- The scaled factors are unit triangular: `A` lower, `B` upper, on the indices `i, j ≥ 1`. -/
theorem factors_unitTriangular (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    (i < j → A i j = 0) ∧ (j < i → B i j = 0) ∧ A i i = 1 ∧ B i i = 1 := by
  sorry

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
  sorry

/-- (I) `A^(r)` and `B^(r)` have all their entries in `O_{C_3}` iff `1/3 ≤ r ≤ 2/3`. -/
theorem integral_iff (r : ℚ) :
    (∀ i j : ℕ, 1 ≤ i → 1 ≤ j →
      (B i j = 0 ∨ 0 ≤ (padicValRat 3 (B i j) : ℚ) + (6 * r - 3) * ((j : ℚ) - i)) ∧
      (A i j = 0 ∨ 0 ≤ (padicValRat 3 (A i j) : ℚ) + (6 * r - 3) * ((j : ℚ) - i))) ↔
      1 / 3 ≤ r ∧ r ≤ 2 / 3 := by
  sorry

/-- (M) `A^(r)` and `B^(r)` are congruent to the identity modulo the maximal ideal of `O_{C_3}` (every entry off the
diagonal has positive valuation; the diagonal is `1`) iff `1/3 < r < 2/3`. -/
theorem congr_maximal_iff (r : ℚ) :
    (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → i ≠ j →
      (B i j = 0 ∨ 0 < (padicValRat 3 (B i j) : ℚ) + (6 * r - 3) * ((j : ℚ) - i)) ∧
      (A i j = 0 ∨ 0 < (padicValRat 3 (A i j) : ℚ) + (6 * r - 3) * ((j : ℚ) - i))) ↔
      1 / 3 < r ∧ r < 2 / 3 := by
  sorry

/-- (M), first bound: `v_3(B^(r)_ij) ≥ (6r - 2)(j - i)` above the diagonal, for every `r`. -/
theorem valuation_B_ge (r : ℚ) (i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (h : B i j ≠ 0) :
    (6 * r - 2) * ((j : ℚ) - i) ≤ (padicValRat 3 (B i j) : ℚ) + (6 * r - 3) * ((j : ℚ) - i) := by
  sorry

/-- (M), second bound: `v_3(A^(r)_ij) ≥ (4 - 6r)(i - j)` below the diagonal, for every `r`. -/
theorem valuation_A_ge (r : ℚ) (i j : ℕ) (hj : 1 ≤ j) (hij : j < i) (h : A i j ≠ 0) :
    (4 - 6 * r) * ((i : ℚ) - j) ≤ (padicValRat 3 (A i j) : ℚ) + (6 * r - 3) * ((j : ℚ) - i) := by
  sorry

/-- (M), uniform bound: for `1/3 ≤ r ≤ 2/3` every entry of `A^(r)`, `B^(r)` off the diagonal has valuation
`≥ 1 - |6r - 3|`, so `sup |A^(r) - I|, sup |B^(r) - I| ≤ 3^(-(1 - |6r - 3|))`. -/
theorem valuation_uniform (r : ℚ) (h1 : 1 / 3 ≤ r) (h2 : r ≤ 2 / 3) (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hij : i ≠ j) :
    (B i j = 0 ∨ 1 - |6 * r - 3| ≤ (padicValRat 3 (B i j) : ℚ) + (6 * r - 3) * ((j : ℚ) - i)) ∧
      (A i j = 0 ∨ 1 - |6 * r - 3| ≤ (padicValRat 3 (A i j) : ℚ) + (6 * r - 3) * ((j : ℚ) - i)) := by
  sorry

/-- (P) `A^(r)` and `B^(r)` are congruent to the identity modulo `3` (every entry off the diagonal has valuation
`≥ 1`; the diagonal is `1`) iff `5/12 ≤ r ≤ 7/12`. -/
theorem congr_three_iff (r : ℚ) :
    (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → i ≠ j →
      (B i j = 0 ∨ 1 ≤ (padicValRat 3 (B i j) : ℚ) + (6 * r - 3) * ((j : ℚ) - i)) ∧
      (A i j = 0 ∨ 1 ≤ (padicValRat 3 (A i j) : ℚ) + (6 * r - 3) * ((j : ℚ) - i))) ↔
      5 / 12 ≤ r ∧ r ≤ 7 / 12 := by
  sorry

/-- The witness of optimality above the diagonal: `B_24 = 3060/77`. -/
theorem B_two_four : B 2 4 = 3060 / 77 := by
  sorry

/-- The witness of optimality below the diagonal: `A_42 = 1530/77`. -/
theorem A_four_two : A 4 2 = 1530 / 77 := by
  sorry

/-- `v_3(B_24) = 2`, so `v_3(B^(r)_24) = 12r - 4`. -/
theorem padicValRat_B_two_four : padicValRat 3 (B 2 4) = 2 := by
  sorry

/-- `v_3(A_42) = 2`, so `v_3(A^(r)_42) = 8 - 12r`. -/
theorem padicValRat_A_four_two : padicValRat 3 (A 4 2) = 2 := by
  sorry

end CalegariSlopes.Conj5
