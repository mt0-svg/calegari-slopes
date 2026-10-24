/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Spectral.Defs

@[expose] public section

/-!
# The matrix `u^(r)` (definition)

The definition that the statement file `CalegariSlopes/ChallengeConj5Spectral.lean` adds to those of
`CalegariSlopes.Spectral.Defs`. For a rational `r` and `γ` with `v_3(γ) = 6r - 3`
(`‖γ‖ = 3 ^ (3 - 6r)`), `u^(r)_ij = γ ^ (j - i) u_ij` is the matrix of Section 8 of the paper.

`Ur γ` is `u^(r)` acting on sequences `ℕ → K` (`K = ℂ_[3]`) with the conventions of `CalegariSlopes.Spectral.Defs`:
the coordinates are indexed from `1`, the coordinate `0` is a spectator (ignored, and
`(Ur γ a) 0 = 0`), and `(u^(r) a)_i = Σ_{1 ≤ j ≤ 3i} γ ^ (j - i) u_ij a_j`, the whole row since `u_ij = 0` for
`j > 3 i` (`CalegariSlopes.Spectral.u_eq_zero_of_lt`). For `γ ≠ 0` it is `Λ⁻¹ ∘ Uop ∘ Λ` with `Λ a = (γ ^ j a_j)_j`.
-/

open CalegariSlopes.Overconvergent (K)

namespace CalegariSlopes.Conj5

/-- `u^(r) = (γ ^ (j - i) u_ij)` acting on sequences: `(Ur γ a)_i = Σ_{1 ≤ j ≤ 3i} γ ^ (j - i) u_ij a_j`
(integer powers; zero at `i = 0`). -/
noncomputable def Ur (γ : K) : Module.End K (ℕ → K) where
  toFun a i := ∑ j ∈ Finset.Icc 1 (3 * i), γ ^ ((j : ℤ) - i) * (u i j : K) * a j
  map_add' a b := by
    funext i
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    funext i
    simp [Finset.mul_sum, mul_left_comm]

end CalegariSlopes.Conj5
