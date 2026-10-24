/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# Calegari's conjecture at p = 3, tame level 1, weight 0, through the characteristic series (statement)

The statement of Corollary 7.1, with a `sorry` proof: the challenge of Comparator (`config-matrix.json`), which
nothing imports, so its warning `declaration uses sorry` is expected; `CalegariSlopes/SolutionMatrix.lean` proves it.
`CalegariSlopes/Target.lean` holds the same definitions without the theorem.

`u i j` is the coefficient of `x ^ i * y ^ j` in Loeffler's rational function
`F x y = N x y / Q x y`, a two variable power series over `ℚ` (`Q` has constant term `1`).
By Smithline (thesis, 2000) and Loeffler (IMRN 2007; note of May 2008, section 2), `(u i j)` is the
matrix of `U_3` on the `1/2`-overconvergent 3-adic cusp forms of tame level 1 and weight 0 in the
orthonormal basis `g, g ^ 2, g ^ 3, ...`, `g = 3 ^ 3 * (Δ(3z) / Δ(z)) ^ (1/2)`. By Serre (Publ. IHES 12,
1962, Prop. 7 a)), `det (1 - T U) = Σ n, (-1) ^ n * c n * T ^ n`, where `c n` is the sum of the principal
minors of order `n` of `(u i j)`. The conjectured slopes `slope i` increase strictly, so "the Newton
polygon of `det (1 - T U)` has slopes `slope 1, slope 2, ...`, each once" is equivalent to
`v_3 (c n) = slope 1 + ... + slope n` for every `n`, which is the statement below.
-/

open MvPowerSeries

namespace CalegariSlopes

/-- The first variable `x`. -/
noncomputable abbrev x : MvPowerSeries (Fin 2) ℚ := X 0

/-- The second variable `y`. -/
noncomputable abbrev y : MvPowerSeries (Fin 2) ℚ := X 1

/-- The numerator `N` of `F`. -/
noncomputable def N : MvPowerSeries (Fin 2) ℚ :=
  90 * x * y + 324 * x ^ 2 * y + 648 * x * y ^ 2 + 243 * x ^ 3 * y + 486 * x ^ 2 * y ^ 2
    + 729 * x * y ^ 3

/-- The denominator `Q` of `F`; its constant coefficient is `1`. -/
noncomputable def Q : MvPowerSeries (Fin 2) ℚ :=
  1 - 270 * x * y - 972 * x * y * (x + y) - 729 * x * y * (x ^ 2 + x * y + y ^ 2)

/-- Loeffler's rational function `F = N / Q`, expanded as a power series (`Q⁻¹` is the inverse in
`MvPowerSeries (Fin 2) ℚ`, which exists since the constant coefficient of `Q` is `1`). -/
noncomputable def F : MvPowerSeries (Fin 2) ℚ := N * Q⁻¹

/-- `u i j` is the coefficient of `x ^ i * y ^ j` in `F`. -/
noncomputable def u (i j : ℕ) : ℚ := coeff (Finsupp.single 0 i + Finsupp.single 1 j) F

/-- The principal minor of the matrix `(u i j)` on a finite set `S` of positive integers, in `ℚ_[3]`. -/
noncomputable def principalMinor (S : Finset ℕ+) : ℚ_[3] :=
  (Matrix.of fun a b : S => (u (a : ℕ+) (b : ℕ+) : ℚ_[3])).det

/-- `c n` is the sum, over the sets `S` of `n` positive integers, of the principal minors of `(u i j)`
on `S`: `det (1 - T U) = Σ n, (-1) ^ n * c n * T ^ n`. -/
noncomputable def c (n : ℕ) : ℚ_[3] :=
  ∑' S : {S : Finset ℕ+ // S.card = n}, principalMinor S.1

/-- The conjectured `i`-th slope, `2 i + 2 v_3 ((2 i)! / i!)` (the division is exact). -/
def slope (i : ℕ) : ℕ := 2 * i + 2 * padicValNat 3 ((2 * i).factorial / i.factorial)

/-- **Corollary 7.1**: for every `n` the principal minors of order `n` are summable in `ℚ_[3]`, their sum `c n` is
nonzero, and `v_3 (c n) = slope 1 + ... + slope n` (at `n = 0`, `c 0 = 1` and both sides are `0`). With the inputs
of Smithline, Loeffler and Serre recalled above, this is Calegari's conjecture at p = 3 (recorded by Smithline,
CRM Proc. 2004). -/
theorem calegari_conjecture (n : ℕ) :
    Summable (fun S : {S : Finset ℕ+ // S.card = n} => principalMinor S.1) ∧ c n ≠ 0 ∧
      Padic.valuation (c n) = ∑ i ∈ Finset.Icc 1 n, (slope i : ℤ) := by
  sorry

end CalegariSlopes
