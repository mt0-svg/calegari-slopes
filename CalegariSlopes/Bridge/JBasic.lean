/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Bridge.JDefs

@[expose] public section

/-! # θ, V3, the series `Sol` (Lemma 4.3), small coefficients -/

open PowerSeries
open CalegariSlopes.Overconvergent (E4q E6q Dq jinv)
open CalegariSlopes.Spectral (JHyp)

namespace CalegariSlopes.Bridge

/-! ## θ and V3 -/

theorem theta_apply (f : ℚ⟦X⟧) : theta f = X * derivative f := rfl

theorem coeff_theta (f : ℚ⟦X⟧) (n : ℕ) : coeff n (theta f) = n * coeff n f := by
  rw [theta_apply]
  rcases n with _ | m
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

theorem theta_V3 (f : ℚ⟦X⟧) : theta (V3 f) = 3 * V3 (theta f) := by
  ext n
  simp only [coeff_theta, V3, coeff_expand, PowerSeries.coeff_ofNat_mul]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [Nat.mul_div_cancel_left m (by norm_num)]
    push_cast
    ring
  · simp
/-! ## The series `Sol b c` -/

theorem coeff_Sol_zero (b : ℚ⟦X⟧) (c : ℚ) : coeff 0 (Sol b c) = 0 := by
  simp [Sol, solCoeff]

theorem coeff_Sol_one (b : ℚ⟦X⟧) (c : ℚ) : coeff 1 (Sol b c) = c := by
  simp [Sol, solCoeff]

theorem coeff_Sol_add_two (b : ℚ⟦X⟧) (c : ℚ) (n : ℕ) :
    coeff (n + 2) (Sol b c) =
      ((n : ℚ) + 1)⁻¹ * ∑ k : Fin (n + 1), coeff ((k : ℕ) + 1) b * coeff (n + 1 - k) (Sol b c) := by
  simp only [Sol, coeff_mk]
  rw [solCoeff]

theorem theta_Sol (b : ℚ⟦X⟧) (c : ℚ) (hb : constantCoeff b = 1) : theta (Sol b c) = b * Sol b c := by
  have hb0 : coeff 0 b = 1 := by rw [coeff_zero_eq_constantCoeff_apply, hb]
  ext n
  rw [coeff_theta, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i b * coeff j (Sol b c))]
  rcases n with _ | _ | m
  · simp [coeff_Sol_zero]
  · simp [Finset.sum_range_succ, coeff_Sol_zero, coeff_Sol_one, hb0]
  · have key := coeff_Sol_add_two b c m
    rw [Fin.sum_univ_eq_sum_range (fun k => coeff (k + 1) b * coeff (m + 1 - k) (Sol b c))] at key
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    have hmid : ∑ i ∈ Finset.range (m + 1), coeff (i + 1) b * coeff (m + 2 - (i + 1)) (Sol b c) =
        ∑ i ∈ Finset.range (m + 1), coeff (i + 1) b * coeff (m + 1 - i) (Sol b c) :=
      Finset.sum_congr rfl fun i _ => by rw [show m + 2 - (i + 1) = m + 1 - i by omega]
    rw [hmid, Nat.sub_self, coeff_Sol_zero, Nat.sub_zero, hb0]
    set S := ∑ i ∈ Finset.range (m + 1), coeff (i + 1) b * coeff (m + 1 - i) (Sol b c)
    rw [key]
    have : (m : ℚ) + 1 ≠ 0 := by positivity
    field_simp
    push_cast
    ring

/-! ## Small coefficients -/

theorem coeff_E2q_small :
    coeff 0 E2q = 1 ∧ coeff 1 E2q = -24 ∧ coeff 2 E2q = -72 ∧ coeff 3 E2q = -96 := by
  have hs : ArithmeticFunction.sigma 1 1 = 1 ∧ ArithmeticFunction.sigma 1 2 = 3 ∧
      ArithmeticFunction.sigma 1 3 = 4 := by
    simp only [ArithmeticFunction.sigma_apply]
    decide
  obtain ⟨h1, h2, h3⟩ := hs
  simp only [E2q, coeff_mk, h1, h2, h3]
  norm_num

theorem coeff_E4q_small :
    coeff 0 E4q = 1 ∧ coeff 1 E4q = 240 ∧ coeff 2 E4q = 2160 ∧ coeff 3 E4q = 6720 := by
  have hs : ArithmeticFunction.sigma 3 1 = 1 ∧ ArithmeticFunction.sigma 3 2 = 9 ∧
      ArithmeticFunction.sigma 3 3 = 28 := by
    simp only [ArithmeticFunction.sigma_apply]
    decide
  obtain ⟨h1, h2, h3⟩ := hs
  simp only [CalegariSlopes.Overconvergent.E4q, coeff_mk, h1, h2, h3]
  norm_num

theorem coeff_E6q_small :
    coeff 0 E6q = 1 ∧ coeff 1 E6q = -504 ∧ coeff 2 E6q = -16632 ∧ coeff 3 E6q = -122976 := by
  have hs : ArithmeticFunction.sigma 5 1 = 1 ∧ ArithmeticFunction.sigma 5 2 = 33 ∧
      ArithmeticFunction.sigma 5 3 = 244 := by
    simp only [ArithmeticFunction.sigma_apply]
    decide
  obtain ⟨h1, h2, h3⟩ := hs
  simp only [CalegariSlopes.Overconvergent.E6q, coeff_mk, h1, h2, h3]
  norm_num

theorem coeff_V3_small (f : ℚ⟦X⟧) :
    coeff 0 (V3 f) = coeff 0 f ∧ coeff 1 (V3 f) = 0 ∧ coeff 2 (V3 f) = 0 ∧ coeff 3 (V3 f) = coeff 1 f := by
  simp only [V3, coeff_expand]
  norm_num

theorem two_mul_a2 : 2 * a2 = 3 * V3 E2q - E2q := by
  ext n
  simp only [a2, PowerSeries.coeff_ofNat_mul, coeff_smul, smul_eq_mul]
  ring

theorem coeff_a2_small : coeff 0 a2 = 1 ∧ coeff 1 a2 = 12 ∧ coeff 2 a2 = 36 ∧ coeff 3 a2 = 12 := by
  obtain ⟨p0, p1, p2, p3⟩ := coeff_E2q_small
  obtain ⟨v0, v1, v2, v3⟩ := coeff_V3_small E2q
  simp only [a2, coeff_smul, map_sub, PowerSeries.coeff_ofNat_mul, v0, v1, v2, v3, p0, p1, p2, p3, smul_eq_mul]
  norm_num

theorem coeff_G_small :
    coeff 0 (Sol a2 27) = 0 ∧ coeff 1 (Sol a2 27) = 27 ∧ coeff 2 (Sol a2 27) = 324 ∧
      coeff 3 (Sol a2 27) = 2430 := by
  obtain ⟨-, a1, a2', -⟩ := coeff_a2_small
  have g1 := coeff_Sol_one a2 27
  have g2 : coeff 2 (Sol a2 27) = 324 := by
    rw [show (2 : ℕ) = 0 + 2 from rfl, coeff_Sol_add_two]
    simp [a1, g1]
    norm_num
  have g3 : coeff 3 (Sol a2 27) = 2430 := by
    rw [show (3 : ℕ) = 1 + 2 from rfl, coeff_Sol_add_two]
    simp [Fin.sum_univ_two, a1, a2', g1, g2]
    norm_num
  exact ⟨coeff_Sol_zero a2 27, g1, g2, g3⟩

theorem constantCoeff_a2 : constantCoeff a2 = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact coeff_a2_small.1

theorem theta_G : theta (Sol a2 27) = a2 * Sol a2 27 :=
  theta_Sol a2 27 constantCoeff_a2
end CalegariSlopes.Bridge
