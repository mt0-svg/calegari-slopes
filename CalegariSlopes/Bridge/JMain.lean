/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Bridge.TheoremA

@[expose] public section

/-! # Theorem 2.1 (a) for `G = Sol a2 27` -/

open PowerSeries
open CalegariSlopes.Overconvergent (E4q E6q Dq jinv)
open CalegariSlopes.Spectral (JHyp)

namespace CalegariSlopes.Bridge

/-! ## Theorem 2.1 (a) -/

/-- The first and third identities of Theorem 4.4 give Theorem 2.1 (a), through
`(1 + 9G)³ (1 + G) - (1 - 18G - 27G²)² = 64 G` (Section 4.2). -/
theorem jhyp_of (G a : ℚ⟦X⟧) (hG : constantCoeff G = 0)
    (h1 : (1 + G) * E4q = a ^ 2 * (1 + 9 * G))
    (h3 : (1 + G) ^ 2 * E6q = a ^ 3 * (1 - 18 * G - 27 * G ^ 2)) : JHyp G := by
  have hD : 1728 * Dq = E4q ^ 3 - E6q ^ 2 := by
    rw [CalegariSlopes.Overconvergent.Dq, mul_smul_comm, show (1728 : ℚ⟦X⟧) * (E4q ^ 3 - E6q ^ 2) =
      (1728 : ℚ) • (E4q ^ 3 - E6q ^ 2) by rw [Algebra.smul_def]; rfl, smul_smul]
    norm_num
  have e1 : (1 + G) ^ 4 * E4q ^ 3 = (1 + G) * (a ^ 2 * (1 + 9 * G)) ^ 3 := by rw [← h1]; ring
  have e3 : (1 + G) ^ 4 * E6q ^ 2 = (a ^ 3 * (1 - 18 * G - 27 * G ^ 2)) ^ 2 := by rw [← h3]; ring
  have hc : (1 + G) ^ 4 ≠ 0 := pow_ne_zero 4 fun h => by simpa [hG] using congrArg constantCoeff h
  have h64 : (64 : ℚ⟦X⟧) ≠ 0 := fun h => by
    have := congrArg (coeff 0) (show C (64 : ℚ) = 0 from h)
    simp at this
  have key : Dq * (27 * (1 + G) * (1 + 9 * G) ^ 3) = G * E4q ^ 3 := by
    refine mul_right_cancel₀ hc (mul_left_cancel₀ h64 ?_)
    linear_combination (1 + G) ^ 5 * (1 + 9 * G) ^ 3 * hD
      + ((1 + G) * (1 + 9 * G) ^ 3 - 64 * G) * e1 - (1 + G) * (1 + 9 * G) ^ 3 * e3
  have hQ : constantCoeff (E4q ^ 3) ≠ 0 := by
    rw [map_pow, ← coeff_zero_eq_constantCoeff_apply, coeff_E4q_small.1]; norm_num
  show CalegariSlopes.Overconvergent.jinv * (27 * (1 + G) * (1 + 9 * G) ^ 3) = G
  rw [CalegariSlopes.Overconvergent.jinv, mul_comm Dq, mul_assoc, key, mul_comm G, ← mul_assoc,
    PowerSeries.inv_mul_cancel _ hQ, one_mul]

/-- **Theorem 2.1 (a)** for `G = Sol a2 27`: `jinv * 27 (1 + G) (1 + 9 G) ^ 3 = G` in `ℚ⟦q⟧`. -/
theorem jhyp_Sol : JHyp (Sol a2 27) := by
  refine jhyp_of (Sol a2 27) a2 ?_ theoremA.1 theoremA.2.2.1
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact coeff_G_small.1

end CalegariSlopes.Bridge
