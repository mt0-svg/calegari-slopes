/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.ADB.P1
public import CalegariSlopes.ADB.P2
public import CalegariSlopes.ADB.Corners

@[expose] public section

/-!
# Loeffler's identity `ADB = U` (Theorem 2.3)

The proof of Section 5: the lemmas proved in `P1.lean`, `P2.lean` and `Corners.lean` (namespace
`CalegariSlopes.ADB.Proof`), then Lemma 5.2 (`RV_zero`), the pivot and the descent of Section 5.4 (`S_eq_V`, `adb`).

- `P1`: Lemma 5.1, Loeffler's column recurrence `(M + p^2 N) B_{p,.} = 0` at every `k ≥ 1`, for every `p ≥ 1`.
- `RS_zero`: Lemma 5.3, `(R S)(i, j) = 0` for `i, j ≥ 1`, `S_ij = i u_ij`.
- `B_eq_zero_of_lt`, `B_eq_zero_of_gt`, `B_self`, `D_mul_B_corner`, `u_eq_zero_of_gt`, `u_corner`: supports and
  corners (Lemmas 3.1 and 3.2); `V_eq_sum`, `V_eq_zero_of_gt`, `V_corner`: the same for `V_ij = Σ_p λ_p B_pi B_pj`
  (Lemma 5.4 (a), (b)).
- `S_col_one`, `S_col_two`: the columns `j = 1, 2` (Lemma 5.4 (c)).
-/

namespace CalegariSlopes.ADB

/-! ## Lemmas 5.1 and 5.3 -/

/-- Lemma 5.1: Loeffler's recurrence for the row `B_{p,.}`, for every `p ≥ 1` and `k ≥ 1`. -/
theorem P1 (p k : ℕ) (hp : 1 ≤ p) (hk : 1 ≤ k) : mOp (B p) k + (p : ℚ) ^ 2 * nOp (B p) k = 0 := by
  exact Proof.P1 p k hp hk

/-- Lemma 5.3: `R` kills `S_ij = i u_ij` at every `i, j ≥ 1`. -/
theorem RS_zero (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) : R S i j = 0 := by
  exact Proof.RS_zero i j hi hj

/-! ## Supports and corners -/

/-- `B_pk = 0` for `k < p`. -/
theorem B_eq_zero_of_lt (p k : ℕ) (h : k < p) : B p k = 0 := by
  exact Proof.B_eq_zero_of_lt p k h

/-- `B_pk = 0` for `k > 3p`. -/
theorem B_eq_zero_of_gt (p k : ℕ) (h : 3 * p < k) : B p k = 0 := by
  exact Proof.B_eq_zero_of_gt p k h

/-- `B_pp = 1`. -/
theorem B_self (p : ℕ) (hp : 1 ≤ p) : B p p = 1 := by
  exact Proof.B_self p hp

/-- `D_p B_{p,3p} = 3^{6p}`. -/
theorem D_mul_B_corner (p : ℕ) (hp : 1 ≤ p) : D p * B p (3 * p) = 3 ^ (6 * p) := by
  exact Proof.D_mul_B_corner p hp

/-- `u_ij = 0` for `i > 3j` (weights). -/
theorem u_eq_zero_of_gt (i j : ℕ) (h : 3 * j < i) : u i j = 0 := by
  exact Proof.u_eq_zero_of_gt i j h

/-- `u_{3j,j} = 3^{6j - 1}`, written without subtraction. -/
theorem u_corner (j : ℕ) (hj : 1 ≤ j) : 3 * u (3 * j) j = 3 ^ (6 * j) := by
  exact Proof.u_corner j hj

/-- The sum defining `V_ij` may run over any `1 ≤ p ≤ K` with `K ≥ min(i, j)`. -/
theorem V_eq_sum (i j K : ℕ) (hK : min i j ≤ K) :
    V i j = ∑ p ∈ Finset.Icc 1 K, lam p * B p i * B p j := by
  exact Proof.V_eq_sum i j K hK

/-- `V_ij = 0` for `i > 3j`. -/
theorem V_eq_zero_of_gt (i j : ℕ) (h : 3 * j < i) : V i j = 0 := by
  exact Proof.V_eq_zero_of_gt i j h

/-- `V_{3j,j} = j 3^{6j}`. -/
theorem V_corner (j : ℕ) (hj : 1 ≤ j) : V (3 * j) j = j * 3 ^ (6 * j) := by
  exact Proof.V_corner j hj

/-! ## The columns `j = 1, 2` -/

/-- `S_{i1} = V_{i1}`. -/
theorem S_col_one (i : ℕ) (hi : 1 ≤ i) : S i 1 = V i 1 := by
  exact Proof.S_col_one i hi

/-- `S_{i2} = V_{i2}`. -/
theorem S_col_two (i : ℕ) (hi : 1 ≤ i) : S i 2 = V i 2 := by
  exact Proof.S_col_two i hi

/-! ## The closing argument, from the lemmas above -/

/-- Lemma 5.2: `R` kills every term `λ_p B_pi B_pj`, so `(R V)(i, j) = 0`. -/
theorem RV_zero (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) : R V i j = 0 := by
  have hexp : R V i j = ∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3,
      ∑ p ∈ Finset.Icc 1 (i + 2), (mC a i * nC b j - nC a i * mC b j) *
        (lam p * B p (i + a) * B p (j + b)) := by
    unfold R
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b _ => ?_
    rw [V_eq_sum (i + a) (j + b) (i + 2) (by simp only [Finset.mem_range] at ha; omega),
      Finset.mul_sum]
  have hswap : R V i j = ∑ p ∈ Finset.Icc 1 (i + 2), lam p *
      (mOp (B p) i * nOp (B p) j - nOp (B p) i * mOp (B p) j) := by
    rw [hexp]
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [mOp, nOp, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    ring
  rw [hswap]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp1 : 1 ≤ p := (Finset.mem_Icc.mp hp).1
  have hMi : mOp (B p) i = -(p : ℚ) ^ 2 * nOp (B p) i := by linear_combination P1 p i hp1 hi
  have hMj : mOp (B p) j = -(p : ℚ) ^ 2 * nOp (B p) j := by linear_combination P1 p j hp1 hj
  rw [hMi, hMj]
  ring

/-- `R` is linear. -/
theorem R_sub (i j : ℕ) : R (fun a b => S a b - V a b) i j = R S i j - R V i j := by
  simp only [R, mul_sub, Finset.sum_sub_distrib]

/-- The pivot of Section 5.4: the coefficient of `W(i, k + 2)` in `(R W)(i, k)`, with `j = k + 2`. -/
theorem pivot (i k : ℚ) :
    mC 0 i * nC 2 k - nC 0 i * mC 2 k =
      9 * (i + 1) ^ 2 * (i + 2) ^ 2 * k * (k + 1) * (3 * k + 4) * (3 * k + 5) *
        ((3 * (k + 2) - i) * (3 * (k + 2) + i)) := by
  simp only [mC, nC]
  ring

/-- `S = V` on `i, j ≥ 1`: base columns, then for each column `j ≥ 3` a descent in `i` from `3j` (Section 5.4). -/
theorem S_eq_V (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) : S i j = V i j := by
  induction j using Nat.strong_induction_on generalizing i with
  | _ j ih =>
  obtain rfl | rfl | ⟨k, rfl⟩ : j = 1 ∨ j = 2 ∨ ∃ k, j = k + 3 :=
    by rcases j with _ | _ | _ | k <;> simp_all
  · exact S_col_one i hi
  · exact S_col_two i hi
  · have desc : ∀ n i, 3 * (k + 3) ≤ i + n → 1 ≤ i → S i (k + 3) = V i (k + 3) := by
      intro n
      induction n with
      | zero =>
        intro i hin hi
        rcases (show 3 * (k + 3) < i ∨ i = 3 * (k + 3) by omega) with h | rfl
        · rw [S, u_eq_zero_of_gt i (k + 3) h, V_eq_zero_of_gt i (k + 3) h, mul_zero]
        · rw [V_corner (k + 3) (by omega), S]
          have hc := u_corner (k + 3) (by omega)
          push_cast
          linear_combination ((k : ℚ) + 3) * hc
      | succ n ihn =>
        intro i hin hi
        by_cases h : 3 * (k + 3) ≤ i + n
        · exact ihn i h hi
        · have hR := R_sub i (k + 1)
          rw [RS_zero i (k + 1) hi (by omega), RV_zero i (k + 1) hi (by omega), sub_zero] at hR
          have c1 : ∀ a, S (i + a) (k + 1) - V (i + a) (k + 1) = 0 := fun a => by
            rw [ih (k + 1) (by omega) (i + a) (by omega) (by omega), sub_self]
          have c2 : ∀ a, S (i + a) (k + 2) - V (i + a) (k + 2) = 0 := fun a => by
            rw [ih (k + 2) (by omega) (i + a) (by omega) (by omega), sub_self]
          have c3 : ∀ a, 1 ≤ a → S (i + a) (k + 3) - V (i + a) (k + 3) = 0 := fun a ha => by
            rw [ihn (i + a) (by omega) (by omega), sub_self]
          simp only [R, Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hR
          rw [show k + 1 + 1 = k + 2 by omega, show k + 1 + 2 = k + 3 by omega] at hR
          rw [show S (i + 0) (k + 1) - V (i + 0) (k + 1) = 0 from c1 0,
            show S (i + 1) (k + 1) - V (i + 1) (k + 1) = 0 from c1 1,
            show S (i + 2) (k + 1) - V (i + 2) (k + 1) = 0 from c1 2,
            show S (i + 0) (k + 2) - V (i + 0) (k + 2) = 0 from c2 0,
            show S (i + 1) (k + 2) - V (i + 1) (k + 2) = 0 from c2 1,
            show S (i + 2) (k + 2) - V (i + 2) (k + 2) = 0 from c2 2,
            show S (i + 1) (k + 3) - V (i + 1) (k + 3) = 0 from c3 1 le_rfl,
            show S (i + 2) (k + 3) - V (i + 2) (k + 3) = 0 from c3 2 (by norm_num)] at hR
          simp only [mul_zero, add_zero, zero_add] at hR
          have hpiv : mC 0 (i : ℚ) * nC 2 ((k + 1 : ℕ) : ℚ) - nC 0 (i : ℚ) * mC 2 ((k + 1 : ℕ) : ℚ) ≠ 0 := by
            rw [pivot]
            have h3 : (i : ℚ) < 3 * (((k + 1 : ℕ) : ℚ) + 2) := by
              have : i < 3 * (k + 3) := by omega
              have : (i : ℚ) < 3 * ((k : ℚ) + 3) := by exact_mod_cast this
              push_cast
              linarith
            have hk1 : (0 : ℚ) < ((k + 1 : ℕ) : ℚ) := by positivity
            have hi0 : (0 : ℚ) ≤ (i : ℚ) := by positivity
            apply ne_of_gt
            have e1 : (0 : ℚ) < 3 * (((k + 1 : ℕ) : ℚ) + 2) - i := by linarith
            positivity
          have := (mul_eq_zero.mp hR).resolve_left hpiv
          linear_combination this
    exact desc (3 * (k + 3)) i (by omega) hi

/-- **Loeffler's identity** `ADB = U` (Theorem 2.3): for all `i, j ≥ 1`,
`Σ_{p ≤ min(i, j)} A_ip D_p B_pj = u_ij`, with `u` the coefficients of `F` (`CalegariSlopes.u`). -/
theorem adb : ∀ i j, 1 ≤ i → 1 ≤ j →
    ∑ p ∈ Finset.Icc 1 (min i j), A i p * D p * B p j = u i j := by
  intro i j hi hj
  have hSV := S_eq_V i j hi hj
  have hi0 : (i : ℚ) ≠ 0 := by positivity
  have hsum : (i : ℚ) * ∑ p ∈ Finset.Icc 1 (min i j), A i p * D p * B p j = V i j := by
    rw [V, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [A, lam]
    field_simp
  rw [S] at hSV
  exact mul_left_cancel₀ hi0 (hsum.trans hSV.symm)

end CalegariSlopes.ADB
