/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Bridge.C4Defs
public import CalegariSlopes.ADB.URec
public import CalegariSlopes.ADB.Corners

@[expose] public section

/-!
# The recurrence of the columns of `u` (Lemma 4.7)

The column polynomials
`col j` satisfy `IsColRec X col` (`CalegariSlopes.ADB.u_rec` coefficientwise), hence `S_j = Σ_{1 ≤ i ≤ 3j} u_ij gⁱ`
satisfies `IsColRec g` for every `g`; the recurrence has at most one solution.
-/

namespace CalegariSlopes.Bridge.Level9

theorem coeff_col (i j : ℕ) : (col j).coeff i = u i j := by
  unfold col
  simp
  intro h
  rw [CalegariSlopes.ADB.Proof.u_eq_zero_of_gt i j h]

theorem isColRec_col : IsColRec (Polynomial.X : Polynomial ℚ) col := by
  have hT : ∀ (a : ℚ) (k t i j : ℕ), ((Polynomial.C a * Polynomial.X ^ k) * col (j - t)).coeff i =
      if k ≤ i ∧ t ≤ j then a * u (i - k) (j - t) else 0 := by
    intro a k t i j
    rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    by_cases hk : k ≤ i <;> by_cases ht : t ≤ j <;> simp only [hk, ht, coeff_col, and_self, and_true,
      and_false, ↓reduceIte, mul_zero]
    rw [show j - t = 0 by omega, CalegariSlopes.ADB.u_zero_right, mul_zero]
  have hF : ∀ i j : ℕ, 1 ≤ j → (fnRec j (Polynomial.X : Polynomial ℚ)).coeff i =
      (if 1 = i ∧ 1 = j then 90 else 0) + (if 2 = i ∧ 1 = j then 324 else 0) +
      (if 1 = i ∧ 2 = j then 648 else 0) + (if 3 = i ∧ 1 = j then 243 else 0) +
      (if 2 = i ∧ 2 = j then 486 else 0) + (if 1 = i ∧ 3 = j then 729 else 0) := by
    intro i j hj
    unfold fnRec
    rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ 4 ≤ j by omega) with rfl | rfl | rfl | h4
    · simp only [↓reduceIte, Polynomial.coeff_add, Polynomial.coeff_ofNat_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_X]
      rcases (show i = 1 ∨ i = 2 ∨ i = 3 ∨ (i ≠ 1 ∧ i ≠ 2 ∧ i ≠ 3) by omega) with rfl | rfl | rfl | ⟨h1, h2, h3⟩
      · norm_num
      · norm_num
      · norm_num
      · simp [h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3]
    · simp only [show (2 : ℕ) ≠ 1 by decide, ↓reduceIte, Polynomial.coeff_add, Polynomial.coeff_ofNat_mul,
        Polynomial.coeff_X_pow, Polynomial.coeff_X]
      rcases (show i = 1 ∨ i = 2 ∨ (i ≠ 1 ∧ i ≠ 2) by omega) with rfl | rfl | ⟨h1, h2⟩
      · norm_num
      · norm_num
      · simp [h2, Ne.symm h1, Ne.symm h2]
    · simp only [show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, ↓reduceIte,
        Polynomial.coeff_ofNat_mul, Polynomial.coeff_X]
      rcases (show i = 1 ∨ i ≠ 1 by omega) with rfl | h1
      · norm_num
      · simp [Ne.symm h1]
    · simp only [show j ≠ 1 by omega, show j ≠ 2 by omega, show j ≠ 3 by omega, ↓reduceIte,
        Polynomial.coeff_zero, show 1 ≠ j by omega, show 2 ≠ j by omega, show 3 ≠ j by omega, and_false]
      norm_num
  refine ⟨?_, fun j hj => ?_⟩
  · ext i
    rw [coeff_col, CalegariSlopes.ADB.u_zero_right, Polynomial.coeff_zero]
  · have e : fnRec j (Polynomial.X : Polynomial ℚ)
        + (270 * Polynomial.X + 972 * Polynomial.X ^ 2 + 729 * Polynomial.X ^ 3) * col (j - 1)
        + (972 * Polynomial.X + 729 * Polynomial.X ^ 2) * col (j - 2) + 729 * Polynomial.X * col (j - 3)
        = fnRec j Polynomial.X
          + (Polynomial.C 270 * Polynomial.X ^ 1 * col (j - 1) + Polynomial.C 972 * Polynomial.X ^ 2 * col (j - 1)
          + Polynomial.C 972 * Polynomial.X ^ 1 * col (j - 2) + Polynomial.C 729 * Polynomial.X ^ 3 * col (j - 1)
          + Polynomial.C 729 * Polynomial.X ^ 2 * col (j - 2)
          + Polynomial.C 729 * Polynomial.X ^ 1 * col (j - 3)) := by
      simp only [map_ofNat]
      ring
    rw [e]
    ext i
    rw [coeff_col, CalegariSlopes.ADB.u_rec i j]
    simp only [Polynomial.coeff_add, hT, hF i j hj, show 1 ≤ j from hj, and_true]

theorem IsColRec.map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {g : R}
    {Z : ℕ → R} (h : IsColRec g Z) : IsColRec (f g) (fun j => f (Z j)) := by
  rcases h with ⟨h0, hrec⟩
  have hfnRec : ∀ j : ℕ, f (fnRec j g) = fnRec j (f g) := by
    intro j
    unfold fnRec
    split_ifs with h1 h2 h3
    · simp [map_add, map_mul, map_pow, map_ofNat]
    · simp [map_add, map_mul, map_pow, map_ofNat]
    · simp [map_mul, map_ofNat]
    · simp
  constructor
  · simp [h0]
  · intro j hj
    have hrecj := hrec j hj
    calc
      f (Z j) = f (fnRec j g + (270 * g + 972 * g ^ 2 + 729 * g ^ 3) * Z (j - 1) +
        (972 * g + 729 * g ^ 2) * Z (j - 2) + 729 * g * Z (j - 3)) := by rw [hrecj]
      _ = f (fnRec j g) + f ((270 * g + 972 * g ^ 2 + 729 * g ^ 3) * Z (j - 1)) +
        f ((972 * g + 729 * g ^ 2) * Z (j - 2)) + f (729 * g * Z (j - 3)) := by
        simp [map_add]
      _ = f (fnRec j g) + f (270 * g + 972 * g ^ 2 + 729 * g ^ 3) * f (Z (j - 1)) +
        f (972 * g + 729 * g ^ 2) * f (Z (j - 2)) + f (729 * g) * f (Z (j - 3)) := by
        simp [map_mul]
      _ = f (fnRec j g) + (270 * f g + 972 * (f g) ^ 2 + 729 * (f g) ^ 3) * f (Z (j - 1)) +
        (972 * f g + 729 * (f g) ^ 2) * f (Z (j - 2)) + 729 * f g * f (Z (j - 3)) := by
        simp [map_add, map_mul, map_pow, map_ofNat]
      _ = fnRec j (f g) + (270 * f g + 972 * (f g) ^ 2 + 729 * (f g) ^ 3) * f (Z (j - 1)) +
        (972 * f g + 729 * (f g) ^ 2) * f (Z (j - 2)) + 729 * f g * f (Z (j - 3)) := by
        rw [hfnRec j]

theorem aeval_col {R : Type*} [CommRing R] [Algebra ℚ R] (g : R) (j : ℕ) :
    Polynomial.aeval g (col j) = ∑ i ∈ Finset.Icc 1 (3 * j), u i j • g ^ i := by
  have hpos : 0 < 3 * j + 1 := by omega
  calc
    Polynomial.aeval g (col j) = Polynomial.aeval g
      (∑ i ∈ Finset.range (3 * j + 1), Polynomial.C (u i j) * Polynomial.X ^ i) := rfl
    _ = ∑ i ∈ Finset.range (3 * j + 1),
      Polynomial.aeval g (Polynomial.C (u i j) * Polynomial.X ^ i) := by rw [map_sum]
    _ = ∑ i ∈ Finset.range (3 * j + 1),
      (Polynomial.aeval g (Polynomial.C (u i j)) * Polynomial.aeval g (Polynomial.X ^ i)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Polynomial.aeval_mul]
    _ = ∑ i ∈ Finset.range (3 * j + 1), (algebraMap ℚ R (u i j) * g ^ i) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Polynomial.aeval_C, Polynomial.aeval_X_pow]
    _ = ∑ i ∈ Finset.range (3 * j + 1), ((u i j) • g ^ i) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Algebra.smul_def]
    _ = ((u 0 j) • g ^ 0) + ∑ i ∈ Finset.Ico 1 (3 * j + 1), ((u i j) • g ^ i) :=
      Finset.sum_range_eq_add_Ico (f := fun i => (u i j) • g ^ i) hpos
    _ = (algebraMap ℚ R (u 0 j)) + ∑ i ∈ Finset.Ico 1 (3 * j + 1), ((u i j) • g ^ i) := by
      simp [Algebra.smul_def]
    _ = (algebraMap ℚ R 0) + ∑ i ∈ Finset.Ico 1 (3 * j + 1), ((u i j) • g ^ i) := by
      rw [CalegariSlopes.ADB.u_zero_left j]
    _ = 0 + ∑ i ∈ Finset.Ico 1 (3 * j + 1), ((u i j) • g ^ i) := by simp
    _ = ∑ i ∈ Finset.Ico 1 (3 * j + 1), ((u i j) • g ^ i) := by simp
    _ = ∑ i ∈ Finset.Icc 1 (3 * j), ((u i j) • g ^ i) := by
      rw [Finset.Ico_add_one_right_eq_Icc 1 (3*j)]

/-- Lemma 4.7: `S_j = Σ_{1 ≤ i ≤ 3j} u_ij gⁱ` satisfies the recurrence. -/
theorem isColRec_S {R : Type*} [CommRing R] [Algebra ℚ R] (g : R) :
    IsColRec g (fun j => ∑ i ∈ Finset.Icc 1 (3 * j), u i j • g ^ i) := by
  have h := isColRec_col.map (Polynomial.aeval g).toRingHom
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X, aeval_col] at h
  exact h

theorem IsColRec.unique {R : Type*} [CommRing R] {g : R} {Z Z' : ℕ → R}
    (h : IsColRec g Z) (h' : IsColRec g Z') : Z = Z' := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with (rfl | n)
    · rw [h.1, h'.1]
    · have hn : 1 ≤ n.succ := by omega
      have hrec := h.2 n.succ hn
      have hrec' := h'.2 n.succ hn
      rw [hrec, hrec']
      have h1 : Z (n.succ - 1) = Z' (n.succ - 1) := ih (n.succ - 1) (by omega)
      have h2 : Z (n.succ - 2) = Z' (n.succ - 2) := ih (n.succ - 2) (by omega)
      have h3 : Z (n.succ - 3) = Z' (n.succ - 3) := ih (n.succ - 3) (by omega)
      rw [h1, h2, h3]

end CalegariSlopes.Bridge.Level9
