/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Target

@[expose] public section

/-!
# The recurrence of `u` (`Q F = N`, coefficientwise)

The helpers live in the namespace `CalegariSlopes.ADB.URec`.
-/

open MvPowerSeries

namespace CalegariSlopes.ADB.URec

open CalegariSlopes

/-- Exponent `x ^ i * y ^ j`. -/
noncomputable abbrev e (i j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j

theorem e_apply_zero (i j : ℕ) : e i j 0 = i := by simp [e]

theorem e_apply_one (i j : ℕ) : e i j 1 = j := by simp [e]

theorem e_le_e (a b i j : ℕ) : e a b ≤ e i j ↔ a ≤ i ∧ b ≤ j := by
  rw [Finsupp.le_def, Fin.forall_fin_two]
  simp [e_apply_zero, e_apply_one]

theorem e_sub_e (a b i j : ℕ) : e i j - e a b = e (i - a) (j - b) := by
  ext k
  fin_cases k <;> simp [e_apply_zero, e_apply_one]

theorem e_eq_zero (i j : ℕ) : e i j = 0 ↔ i = 0 ∧ j = 0 := by
  constructor
  · intro h
    have h0 := congrArg (· 0) h
    have h1 := congrArg (· 1) h
    simp only [e_apply_zero, e_apply_one, Finsupp.coe_zero, Pi.zero_apply] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩
    simp [e]

theorem u_eq (i j : ℕ) : u i j = coeff (e i j) F := rfl

theorem x_pow_mul_y_pow (a b : ℕ) :
    (x ^ a * y ^ b : MvPowerSeries (Fin 2) ℚ) = monomial (e a b) 1 := by
  simp only [x, y, X_pow_eq, monomial_mul_monomial, mul_one, e]

theorem coeff_e_mul (a b i j : ℕ) (φ : MvPowerSeries (Fin 2) ℚ) :
    coeff (e i j) (x ^ a * (y ^ b * φ)) =
      if a ≤ i ∧ b ≤ j then coeff (e (i - a) (j - b)) φ else 0 := by
  rw [← mul_assoc, x_pow_mul_y_pow, coeff_monomial_mul]
  simp only [e_le_e, e_sub_e, one_mul]

theorem coeff_e (a b i j : ℕ) :
    coeff (e i j) (x ^ a * y ^ b : MvPowerSeries (Fin 2) ℚ) = if a = i ∧ b = j then 1 else 0 := by
  have h := coeff_e_mul a b i j 1
  rw [mul_one] at h
  rw [h, coeff_one]
  by_cases hab : a ≤ i ∧ b ≤ j
  · simp only [hab, and_self, ite_true, e_eq_zero]
    by_cases hij : a = i ∧ b = j
    · simp [hij]
    · rw [ite_eq_right_iff.mpr (fun h => absurd ⟨by omega, by omega⟩ hij), ite_eq_right_iff.mpr]
      exact fun h => absurd h hij
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hab), ite_eq_right_iff.mpr]
    exact fun h => absurd ⟨h.1.le, h.2.le⟩ hab

/-- `N` as a sum of monomials. -/
theorem N_eq : N = C 90 * (x ^ 1 * y ^ 1) + C 324 * (x ^ 2 * y ^ 1) + C 648 * (x ^ 1 * y ^ 2) +
    C 243 * (x ^ 3 * y ^ 1) + C 486 * (x ^ 2 * y ^ 2) + C 729 * (x ^ 1 * y ^ 3) := by
  simp only [N, map_ofNat]
  ring

/-- `1 - Q` as a sum of monomials. -/
theorem one_sub_Q_eq : 1 - Q = C 270 * (x ^ 1 * y ^ 1) + C 972 * (x ^ 2 * y ^ 1) +
    C 972 * (x ^ 1 * y ^ 2) + C 729 * (x ^ 3 * y ^ 1) + C 729 * (x ^ 2 * y ^ 2) +
    C 729 * (x ^ 1 * y ^ 3) := by
  simp only [Q, map_ofNat]
  ring

theorem constantCoeff_Q : constantCoeff Q = 1 := by
  simp [Q, x, y]

/-- `Q⁻¹` is a two-sided inverse of `Q`, so `F` is the power series of `N / Q`. -/
theorem Q_mul_F : Q * F = N := by
  rw [F, mul_comm N, ← mul_assoc, MvPowerSeries.mul_inv_cancel Q (by rw [constantCoeff_Q]; norm_num),
    one_mul]

end CalegariSlopes.ADB.URec

namespace CalegariSlopes.ADB

open URec in
/-- The recurrence `F = N + (1 - Q) F`, coefficientwise; the truncated subtractions are harmless since
`u 0 j = u i 0 = 0`. -/
theorem u_rec (i j : ℕ) :
    u i j =
      (if 1 = i ∧ 1 = j then 90 else 0) + (if 2 = i ∧ 1 = j then 324 else 0) +
      (if 1 = i ∧ 2 = j then 648 else 0) + (if 3 = i ∧ 1 = j then 243 else 0) +
      (if 2 = i ∧ 2 = j then 486 else 0) + (if 1 = i ∧ 3 = j then 729 else 0) +
      ((if 1 ≤ i ∧ 1 ≤ j then 270 * u (i - 1) (j - 1) else 0) +
      (if 2 ≤ i ∧ 1 ≤ j then 972 * u (i - 2) (j - 1) else 0) +
      (if 1 ≤ i ∧ 2 ≤ j then 972 * u (i - 1) (j - 2) else 0) +
      (if 3 ≤ i ∧ 1 ≤ j then 729 * u (i - 3) (j - 1) else 0) +
      (if 2 ≤ i ∧ 2 ≤ j then 729 * u (i - 2) (j - 2) else 0) +
      (if 1 ≤ i ∧ 3 ≤ j then 729 * u (i - 1) (j - 3) else 0)) := by
  have hF : F = N + (1 - Q) * F := by rw [sub_mul, one_mul, Q_mul_F]; ring
  have h := congrArg (coeff (e i j)) hF
  rw [N_eq, one_sub_Q_eq] at h
  simp only [map_add, add_mul, mul_assoc, coeff_C_mul, coeff_e_mul, coeff_e, ← u_eq, mul_ite,
    mul_one, mul_zero] at h
  exact h

theorem u_zero_left (j : ℕ) : u 0 j = 0 := by
  rw [u_rec]; simp

theorem u_zero_right (i : ℕ) : u i 0 = 0 := by
  rw [u_rec]; simp

end CalegariSlopes.ADB
