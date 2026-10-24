/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Bridge.RamanujanPort
public import CalegariSlopes.Bridge.JBasic

@[expose] public section

/-!
# Theorem 4.1, Ramanujan's equations, in `ℚ⟦q⟧`

From the port `CalegariSlopes.RamanujanPort.ramanujan_system_int` (Ramanujan's system in `ℤ⟦q⟧` with divisor sums)
by `PowerSeries.map (Int.castRingHom ℚ)`.
-/

open PowerSeries
open CalegariSlopes.Overconvergent (E4q E6q Dq jinv)
open CalegariSlopes.Spectral (JHyp)

namespace CalegariSlopes.Bridge

theorem map_derivative_int (f : PowerSeries ℤ) :
    PowerSeries.map (Int.castRingHom ℚ) (derivative (R := ℤ) f) =
      derivative (R := ℚ) (PowerSeries.map (Int.castRingHom ℚ) f) := by
  ext n
  simp [coeff_derivative]

theorem map_P_int :
    PowerSeries.map (Int.castRingHom ℚ)
      (PowerSeries.mk fun n => if n = 0 then 1 else -24 * ∑ d ∈ n.divisors, (d : ℤ)) = E2q := by
  ext n
  simp only [coeff_map, coeff_mk, Int.coe_castRingHom, E2q, ArithmeticFunction.sigma_one_apply]
  split_ifs <;> push_cast <;> ring

theorem map_Q_int :
    PowerSeries.map (Int.castRingHom ℚ)
      (PowerSeries.mk fun n => if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3) = E4q := by
  ext n
  simp only [coeff_map, coeff_mk, Int.coe_castRingHom, CalegariSlopes.Overconvergent.E4q,
    ArithmeticFunction.sigma_apply]
  split_ifs <;> push_cast <;> ring

theorem map_R_int :
    PowerSeries.map (Int.castRingHom ℚ)
      (PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5) = E6q := by
  ext n
  simp only [coeff_map, coeff_mk, Int.coe_castRingHom, CalegariSlopes.Overconvergent.E6q,
    ArithmeticFunction.sigma_apply]
  split_ifs <;> push_cast <;> ring

/-- Theorem 4.1 over ℚ, with `X * derivative` for `θ`. -/
theorem ramq :
    12 * (X * derivative (R := ℚ) E2q) = E2q ^ 2 - E4q ∧
      3 * (X * derivative (R := ℚ) E4q) = E2q * E4q - E6q ∧
        2 * (X * derivative (R := ℚ) E6q) = E2q * E6q - E4q ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := CalegariSlopes.RamanujanPort.ramanujan_system_int _ _ _ rfl rfl rfl
  have h1' := congrArg (PowerSeries.map (Int.castRingHom ℚ)) h1
  have h2' := congrArg (PowerSeries.map (Int.castRingHom ℚ)) h2
  have h3' := congrArg (PowerSeries.map (Int.castRingHom ℚ)) h3
  simp only [map_mul, map_sub, map_pow, map_ofNat, PowerSeries.map_X, map_derivative_int, map_P_int,
    map_Q_int, map_R_int] at h1' h2' h3'
  exact ⟨h1', h2', h3'⟩

/-! ## Theorem 4.1: Ramanujan's system on q-expansions -/

theorem ram_E2 : 12 * theta E2q = E2q ^ 2 - E4q := by
  rw [theta_apply]
  exact ramq.1

theorem ram_E4 : 3 * theta E4q = E2q * E4q - E6q := by
  rw [theta_apply]
  exact ramq.2.1

theorem ram_E6 : 2 * theta E6q = E2q * E6q - E4q ^ 2 := by
  rw [theta_apply]
  exact ramq.2.2

end CalegariSlopes.Bridge
