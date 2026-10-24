/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Bridge.JDefs

@[expose] public section

/-!
# Definitions of the level 9 step and of Theorem 2.1 (b)

For Theorem 4.5 and Section 4.4, which prove Theorem 2.1 (b), `CalegariSlopes.Spectral.C4 (Sol a2 27)`
(`CalegariSlopes/Spectral/Defs.lean`), with `Sol`, `a2`, `V3`, `theta` of `CalegariSlopes.Bridge.JDefs` and `u` of
`CalegariSlopes/Target.lean`.

* `bW = V3 (a2 (1 + G)⁻¹)` with `G = Sol a2 27`: the series `b` of Section 4.3, a series in `q³` with
  constant coefficient `1`.
* `W = Sol bW 3 = 3 q - 15 q⁴ + ...` (the level 9 series `3 X / (1 + 3 X)`, `X = (η(9τ)/η(τ))³`, never used as such).
* `col j = Σ_{i ≤ 3j} u_ij xⁱ ∈ ℚ[x]`, the column `j` of `u`.
* `fnRec j g`: `fn₁ = 90 g + 324 g² + 243 g³`, `fn₂ = 648 g + 486 g²`, `fn₃ = 729 g`, `fn_j = 0` otherwise (the
  coefficients of `yʲ` in `N` of Target.lean, at `x = g`).
* `IsColRec g Z`: `Z₀ = 0` and `Z_j = fn_j(g) + q₁(g) Z_{j-1} + q₂(g) Z_{j-2} + 729 g Z_{j-3}` for `j ≥ 1` (truncated
  subtraction), `q₁ = 270 g + 972 g² + 729 g³`, `q₂ = 972 g + 729 g²`: the recurrence `CalegariSlopes.ADB.u_rec`
  (`F = N + (1 - Q) F`) read at `x = g` (Lemma 4.7).
-/

open PowerSeries

namespace CalegariSlopes.Bridge.Level9

/-- `b = V3 (a2 (1 + G)⁻¹)`, `G = Sol a2 27`. -/
noncomputable def bW : ℚ⟦X⟧ := V3 (a2 * (1 + Sol a2 27)⁻¹)

/-- `W = Sol b 3`: the solution of `θ W = b W` with `W = 3 q + O(q²)`. -/
noncomputable def W : ℚ⟦X⟧ := Sol bW 3

/-- The column `j` of `u` as a polynomial, `Σ_{i ≤ 3j} u_ij xⁱ`. -/
noncomputable def col (j : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (3 * j + 1), Polynomial.C (u i j) * Polynomial.X ^ i

/-- `fn_j(g)`, the coefficient of `yʲ` in `N(g, y)`, for `j ≥ 1`. -/
def fnRec {R : Type*} [CommRing R] (j : ℕ) (g : R) : R :=
  if j = 1 then 90 * g + 324 * g ^ 2 + 243 * g ^ 3
  else if j = 2 then 648 * g + 486 * g ^ 2
  else if j = 3 then 729 * g
  else 0

/-- The recurrence of the columns of `u` at `x = g`. -/
def IsColRec {R : Type*} [CommRing R] (g : R) (Z : ℕ → R) : Prop :=
  Z 0 = 0 ∧ ∀ j : ℕ, 1 ≤ j →
    Z j = fnRec j g + (270 * g + 972 * g ^ 2 + 729 * g ^ 3) * Z (j - 1) + (972 * g + 729 * g ^ 2) * Z (j - 2)
      + 729 * g * Z (j - 3)

end CalegariSlopes.Bridge.Level9
