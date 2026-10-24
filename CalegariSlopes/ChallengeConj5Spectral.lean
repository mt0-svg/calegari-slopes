/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Conj5.SpectralDefs

@[expose] public section

/-!
# The spectral expansion at radius `r` and the grading of the eigenvectors (statement)

The statements of Corollaries 8.3 and 8.4 of the paper, with `sorry` proofs: the challenge of Comparator
(`config-conj5-spectral.json`), which nothing imports, so its warnings `declaration uses sorry` are expected;
`CalegariSlopes/Conj5/SpectralMain.lean` proves them under the same names.

The objects are those of `CalegariSlopes.Spectral.Defs`: sequences `ℕ → K` (`K = ℂ_[3]`) with the spectator
coordinate `0`, `c₀` (`IsC0`), `L_s` (`InS s`: `v_3(a_j) + s j → +∞`), the unit sequences `e_n` (`unitSeq`),
`Σ_n b_n y_n` (`expand y b`), and the eigen-family of Theorem 2.4 (a) of the paper (`EigenFamily`: `x_n ∈ c₀` with
`‖x_n - e_n‖ ≤ 1/3`, `u x_n = λ_n x_n`, `‖λ_n‖ = 3 ^ (-σ_n)`, completed at `n = 0` by `λ_0 = 0`); and
`u^(r) = Ur γ` of `CalegariSlopes.Conj5.SpectralDefs`. Here `r` is rational, `s = 3 - 6r`, `ε = 1 - |s|`, and
`γ = c_r / 27` is any element of `K` with `v_3(γ) = -s`, that is `‖γ‖ = 3 ^ s`; such a `γ` exists (`exists_gamma`).

* `spectral_expansion`: Corollary 8.3 for `y_n`, `n ≥ 1`, completed at `n = 0` by `y_0 = e_0` (the coordinate `0`
  carried along, as for `x_0`, `λ_0`).
* `x_mem_L`: the last sentence of Corollary 8.3, `x_n ∈ L_s`.
* `norm_x_le`: Corollary 8.4, `v_3(x_{n,i}) ≥ |i - n|`.
-/

open CalegariSlopes.Overconvergent (K)
open CalegariSlopes.Spectral

namespace CalegariSlopes.Conj5

/-- Loeffler's `γ = c_r / 27` exists for every rational `r`: some `γ ∈ ℂ_[3]` has `v_3(γ) = 6r - 3`. -/
theorem exists_gamma (r : ℚ) : ∃ γ : K, ‖γ‖ = (3 : ℝ) ^ (3 - 6 * (r : ℝ)) := by
  sorry

/-- Corollary 8.3: for rational `1/3 < r < 2/3`, `s = 3 - 6r`, `ε = 1 - |s|` and `‖γ‖ = 3 ^ s`,
there are `y_n ∈ c₀` with `‖y_n - e_n‖ ≤ 3 ^ (-ε)` and `u^(r) y_n = λ_n y_n`; every `a ∈ c₀` is `Σ_n b_n y_n` for
exactly one `b ∈ c₀`, and `‖a‖ = ‖b‖` (sup norms); for `μ ≠ 0` the generalized eigenvectors of `u^(r)` in `c₀`
are the multiples of `y_n` if `μ = λ_n`, and `0` if `μ` is none of the `λ_n`. -/
theorem spectral_expansion (E : EigenFamily) (r : ℚ) (hr1 : 1 / 3 < r) (hr2 : r < 2 / 3) (γ : K)
    (hγ : ‖γ‖ = (3 : ℝ) ^ (3 - 6 * (r : ℝ))) :
    ∃ y : ℕ → ℕ → K,
      y 0 = unitSeq 0 ∧ (∀ n, 1 ≤ n → y n 0 = 0) ∧
      (∀ n, IsC0 (y n)) ∧
      (∀ n i, ‖y n i - unitSeq n i‖ ≤ (3 : ℝ) ^ (-(1 - |3 - 6 * (r : ℝ)|))) ∧
      (∀ n, 1 ≤ n → Ur γ (y n) = E.lam n • y n) ∧
      (∀ a, IsC0 a → ∃! b, IsC0 b ∧ expand y b = a) ∧
      (∀ b, IsC0 b → ⨆ i, ‖expand y b i‖ = ⨆ n, ‖b n‖) ∧
      (∀ n, 1 ≤ n → ∀ a, IsC0 a →
        ((∃ k : ℕ, ((Ur γ - E.lam n • (1 : Module.End K (ℕ → K))) ^ k) a = 0) ↔ ∃ c : K, a = c • y n)) ∧
      (∀ μ : K, μ ≠ 0 → (∀ n, 1 ≤ n → E.lam n ≠ μ) → ∀ a, IsC0 a →
        (∃ k : ℕ, ((Ur γ - μ • (1 : Module.End K (ℕ → K))) ^ k) a = 0) → a = 0) := by
  sorry

/-- Corollary 8.3, last sentence: `x_n ∈ L_s` for `s = 3 - 6r`, `1/3 < r < 2/3` rational. -/
theorem x_mem_L (E : EigenFamily) (r : ℚ) (hr1 : 1 / 3 < r) (hr2 : r < 2 / 3) (n : ℕ) (hn : 1 ≤ n) :
    InS (3 - 6 * (r : ℝ)) (E.x n) := by
  sorry

/-- Corollary 8.4: `v_3(x_{n,i}) ≥ |i - n|` for all `n, i ≥ 1`. -/
theorem norm_x_le (E : EigenFamily) (n i : ℕ) (hn : 1 ≤ n) (hi : 1 ≤ i) :
    ‖E.x n i‖ ≤ (3 : ℝ) ^ (-|(i : ℤ) - n|) := by
  sorry

end CalegariSlopes.Conj5
