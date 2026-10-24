/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Calegari's conjecture at p = 3, tame level 1, weight 0, on overconvergent forms (statement)

The statement of Theorem 1.2, described in Section 9.1 of the paper, with a `sorry` proof: the challenge of
Comparator (`config.json`), which nothing imports, so its warning `declaration uses sorry` is expected;
`CalegariSlopes/Solution.lean` proves it. `CalegariSlopes/Statement.lean` holds the same definitions without the
theorem. No literature input is left named: the statement is about the 3-adic overconvergent cusp forms themselves,
written through their q-expansions.

* `jinv` is the q-expansion of `1 / j = Δ / E₄ ^ 3`, with `E₄ = 1 + 240 Σ σ₃(n) qⁿ`,
  `E₆ = 1 - 504 Σ σ₅(n) qⁿ` and `Δ = (E₄ ^ 3 - E₆ ^ 2) / 1728`.
* `K = ℂ_[3]`. At p = 3 the supersingular locus of the j-line is the disc `|j| < 1` (`j = 0 ≡ 1728`), so
  the ordinary locus is the disc `|w| ≤ 1` in the coordinate `w = 1 / j`. For `0 < r < 1/2` the
  `r`-overconvergent region (`|E₆| ≥ 3 ^ (-3 r)`, and `E₆ ^ 2 / Δ = j - 1728`) is the disc
  `|w| ≤ 3 ^ (6 r)`. An overconvergent cusp form of tame level 1 and weight 0 is therefore a rigid
  function `Σ c m * w ^ m` on a disc `|w| ≤ 3 ^ t`, `t > 0`, vanishing at the cusp `w = 0`: `c 0 = 0` and
  `‖c m‖ * 3 ^ (t * m) → 0`. Its q-expansion is `Σ c m * jinv ^ m` (`jinv = q + O(q ^ 2)`, so the
  coefficient of `q ^ n` is the finite sum over `m ≤ n`). `S0dag` is the space of these q-expansions.
* `U3` acts on q-expansions by `Σ aₙ qⁿ ↦ Σ a₃ₙ qⁿ`.
* `genEig μ` is the generalized eigenspace of `U3` on `S0dag` for the eigenvalue `μ`.

The theorem says that the nonzero eigenvalues of `U3` on `S0dag`, counted with algebraic multiplicity,
are the values of a family `ev i`, `i ≥ 1`, with `v_3 (ev i) = slope i`: the slopes are exactly
`slope i = 2 i + 2 v_3 ((2 i)! / i!)`, each once.
-/

open PowerSeries Filter Topology

namespace CalegariSlopes.Overconvergent

/-- The coefficient field, the completion `ℂ_[3]` of an algebraic closure of `ℚ_[3]`. -/
abbrev K : Type := ℂ_[3]

/-- The q-expansion of the Eisenstein series `E₄ = 1 + 240 Σ σ₃(n) qⁿ`. -/
noncomputable def E4q : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 n : ℚ)

/-- The q-expansion of the Eisenstein series `E₆ = 1 - 504 Σ σ₅(n) qⁿ`. -/
noncomputable def E6q : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n = 0 then 1 else -504 * (ArithmeticFunction.sigma 5 n : ℚ)

/-- The q-expansion of the discriminant `Δ = (E₄ ^ 3 - E₆ ^ 2) / 1728 = q ∏ (1 - qⁿ) ^ 24`. -/
noncomputable def Dq : PowerSeries ℚ := (1728 : ℚ)⁻¹ • (E4q ^ 3 - E6q ^ 2)

/-- The q-expansion of `1 / j = Δ / E₄ ^ 3` (`E₄ ^ 3` has constant coefficient `1`, so `⁻¹` is the
power series inverse). -/
noncomputable def jinv : PowerSeries ℚ := Dq * (E4q ^ 3)⁻¹

/-- `jinv` with coefficients in `K`. -/
noncomputable def jinvK : PowerSeries K := PowerSeries.map (algebraMap ℚ K) jinv

/-- `Σ c m * w ^ m` converges on a closed disc `|w| ≤ 3 ^ t` with `t > 0`, strictly larger than the
ordinary locus `|w| ≤ 1`. -/
def IsOverconvergent (c : ℕ → K) : Prop :=
  ∃ t : ℝ, 0 < t ∧ Tendsto (fun m : ℕ => ‖c m‖ * (3 : ℝ) ^ (t * m)) atTop (𝓝 0)

lemma IsOverconvergent.zero : IsOverconvergent 0 :=
  ⟨1, one_pos, by simp⟩

lemma IsOverconvergent.add {c d : ℕ → K} (hc : IsOverconvergent c) (hd : IsOverconvergent d) :
    IsOverconvergent (c + d) := by
  obtain ⟨t, ht, htc⟩ := hc
  obtain ⟨s, hs, hsd⟩ := hd
  refine ⟨min t s, lt_min ht hs, squeeze_zero (fun m => by positivity) (fun m => ?_)
    (by simpa using htc.add hsd)⟩
  have h3t : (3 : ℝ) ^ (min t s * m) ≤ 3 ^ (t * m) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right (min_le_left t s) (Nat.cast_nonneg m))
  have h3s : (3 : ℝ) ^ (min t s * m) ≤ 3 ^ (s * m) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right (min_le_right t s) (Nat.cast_nonneg m))
  calc ‖(c + d) m‖ * (3 : ℝ) ^ (min t s * m)
      ≤ (‖c m‖ + ‖d m‖) * (3 : ℝ) ^ (min t s * m) := by
        gcongr
        exact norm_add_le _ _
    _ = ‖c m‖ * (3 : ℝ) ^ (min t s * m) + ‖d m‖ * (3 : ℝ) ^ (min t s * m) := add_mul _ _ _
    _ ≤ ‖c m‖ * 3 ^ (t * m) + ‖d m‖ * 3 ^ (s * m) := by gcongr

lemma IsOverconvergent.const_mul {c : ℕ → K} (a : K) (hc : IsOverconvergent c) :
    IsOverconvergent fun m => a * c m := by
  obtain ⟨t, ht, htc⟩ := hc
  refine ⟨t, ht, ?_⟩
  simpa [norm_mul, mul_assoc] using htc.const_mul ‖a‖

/-- The 3-adic overconvergent cusp forms of tame level 1 and weight 0, as q-expansions: the series
`Σ c m * jinv ^ m` with `c 0 = 0` and `c` overconvergent. -/
noncomputable def S0dag : Submodule K (PowerSeries K) where
  carrier := {F | ∃ c : ℕ → K, c 0 = 0 ∧ IsOverconvergent c ∧
    ∀ n, coeff n F = ∑ m ∈ Finset.range (n + 1), c m * coeff n (jinvK ^ m)}
  zero_mem' := ⟨0, rfl, IsOverconvergent.zero, fun n => by simp⟩
  add_mem' := by
    rintro F G ⟨c, hc0, hc, hF⟩ ⟨d, hd0, hd, hG⟩
    refine ⟨c + d, by simp [hc0, hd0], hc.add hd, fun n => ?_⟩
    simp [hF, hG, add_mul, Finset.sum_add_distrib]
  smul_mem' := by
    rintro a F ⟨c, hc0, hc, hF⟩
    refine ⟨fun m => a * c m, by simp [hc0], hc.const_mul a, fun n => ?_⟩
    simp [hF, Finset.mul_sum, mul_assoc]

/-- The Hecke operator `U_3` on q-expansions: `Σ aₙ qⁿ ↦ Σ a₃ₙ qⁿ`. -/
noncomputable def U3 : Module.End K (PowerSeries K) where
  toFun F := PowerSeries.mk fun n => coeff (3 * n) F
  map_add' F G := by ext n; simp
  map_smul' a F := by ext n; simp

/-- The generalized eigenspace of `U3` on `S0dag` for the eigenvalue `μ`: the `F ∈ S0dag` with
`(U3 - μ) ^ k F = 0` for some `k` (`Module.End.mem_maxGenEigenspace`). -/
noncomputable def genEig (μ : K) : Submodule K (PowerSeries K) :=
  S0dag ⊓ Module.End.maxGenEigenspace U3 μ

/-- The conjectured `i`-th slope, `2 i + 2 v_3 ((2 i)! / i!)` (the division is exact). -/
def slope (i : ℕ) : ℕ := 2 * i + 2 * padicValNat 3 ((2 * i).factorial / i.factorial)

/-- **Calegari's conjecture at p = 3** (Theorem 1.2; Calegari, recorded by Smithline, CRM Proc. 2004): the nonzero
eigenvalues of `U_3` on the 3-adic overconvergent cusp forms of tame level 1 and weight 0, counted with
algebraic multiplicity, are `ev 1, ev 2, ...` with `‖ev i‖ = 3 ^ (-slope i)`. -/
theorem calegari_conjecture_overconvergent :
    ∃ ev : ℕ+ → K, (∀ i, ‖ev i‖ = (3 : ℝ) ^ (-(slope i : ℤ))) ∧
      ∀ μ : K, μ ≠ 0 → FiniteDimensional K (genEig μ) ∧
        Module.finrank K (genEig μ) = Nat.card {i : ℕ+ // ev i = μ} := by
  sorry

end CalegariSlopes.Overconvergent
