/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Spectral.Defs
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Expand

@[expose] public section

/-!
# Definitions for Theorem 2.1 (a)

For Sections 4.1 and 4.2, which prove Theorem 2.1 (a), `CalegariSlopes.Spectral.JHyp (Sol a2 27)`
(`CalegariSlopes/Spectral/Defs.lean`), with `jinv`, `E4q`, `E6q` of `CalegariSlopes/Statement.lean`.

* `theta = q d/dq` on `ℚ⟦q⟧`, as a derivation (`θ (Σ aₙ qⁿ) = Σ n aₙ qⁿ`).
* `E2q = 1 - 24 Σ σ₁(n) qⁿ`, the q-expansion of `E₂` (`E4q`, `E6q` are those of Statement.lean).
* `V3 f = f(q³)`.
* `a2 = (3 E₂(q³) - E₂(q)) / 2 = 1 + 12 q + 36 q² + 12 q³ + ...`, the paper's `𝓔`.
* `Sol b c`: the series `y` with `y₀ = 0`, `y₁ = c` and `(n - 1) yₙ = Σ_{k=1}^{n-1} b_k y_{n-k}` for `n ≥ 2`, so that
  `θ y = b y` when `b₀ = 1` (Lemma 4.3). The series `g` of the paper is `G = Sol a2 27`
  `= 27 q + 324 q² + 2430 q³ + ...` (the eta quotient `27 q Π (1 - q³ⁿ)¹² / (1 - qⁿ)¹²`, never used as such).
-/

open PowerSeries
open CalegariSlopes.Overconvergent (E4q E6q Dq jinv)

namespace CalegariSlopes.Bridge

/-- `θ = q d/dq` on `ℚ⟦q⟧`, as a derivation. -/
noncomputable def theta : Derivation ℚ ℚ⟦X⟧ ℚ⟦X⟧ := (X : ℚ⟦X⟧) • PowerSeries.derivative

/-- The q-expansion of the Eisenstein series `E₂ = 1 - 24 Σ σ₁(n) qⁿ`. -/
noncomputable def E2q : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n = 0 then 1 else -24 * (ArithmeticFunction.sigma 1 n : ℚ)

/-- `V3 f = f(q³)`. -/
noncomputable def V3 : ℚ⟦X⟧ →ₐ[ℚ] ℚ⟦X⟧ := PowerSeries.expand 3 three_ne_zero

/-- `a2 = (3 E₂(q³) - E₂(q)) / 2`. -/
noncomputable def a2 : PowerSeries ℚ := (2 : ℚ)⁻¹ • (3 * V3 E2q - E2q)

/-- The coefficients of `Sol b c`: `y₀ = 0`, `y₁ = c`, `y_{n+2} = (n + 1)⁻¹ Σ_{k=0}^{n} b_{k+1} y_{n+1-k}`. -/
noncomputable def solCoeff (b : PowerSeries ℚ) (c : ℚ) : ℕ → ℚ
  | 0 => 0
  | 1 => c
  | n + 2 => ((n : ℚ) + 1)⁻¹ * ∑ k : Fin (n + 1), coeff ((k : ℕ) + 1) b * solCoeff b c (n + 1 - k)
decreasing_by omega

/-- `Sol b c`: the solution of `θ y = b y` with `y = c q + O(q²)` (for `b₀ = 1`). -/
noncomputable def Sol (b : PowerSeries ℚ) (c : ℚ) : PowerSeries ℚ := PowerSeries.mk (solCoeff b c)

/-- The first four coefficients of `f` are `c0 c1 c2 c3`. -/
def Coeffs4 (f : ℚ⟦X⟧) (c0 c1 c2 c3 : ℚ) : Prop :=
  coeff 0 f = c0 ∧ coeff 1 f = c1 ∧ coeff 2 f = c2 ∧ coeff 3 f = c3

end CalegariSlopes.Bridge
