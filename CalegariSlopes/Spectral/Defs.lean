/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Statement
public import CalegariSlopes.ADB.Defs

@[expose] public section

/-!
# Definitions of the spectral step

The objects of Sections 2 and 6: the two properties of Theorem 2.1 as predicates on a power series `G ∈ ℚ⟦q⟧`
((C4) `C4 G` for part (b), (J) `JHyp G` for part (a)), sequences `ℕ → K` (`K = ℂ_[3]`), the spaces `c₀` (`IsC0`,
the paper's null sequences) and `S_s` (`InS s`, the paper's `𝓛_s`), banded rational matrices acting by finite sums
(`bact`), `U` (`Uop`, the action of `u`), `C = B A` (`Cm`), the radius map `φ` (`phiS`, the paper's `ψ`),
`Φ(a) = Σ_{j ≥ 1} a_j G ^ j` (`Phi`), the hypotheses of Lemma 6.1 (`NearBasis`) and the eigen-family of
Theorem 2.4 (`EigenFamily`).

The coordinate `j` of a sequence `a` is the coefficient of `G ^ j`; the coordinate `0` is a spectator (`Φ` and every
matrix action ignore it, and `(U a) 0 = 0`). Every matrix of the proof is banded (`M i j = 0` for `j > 3 i`), so
`bact` acts by the whole row.
-/

open PowerSeries Filter Topology
open CalegariSlopes.Overconvergent (K S0dag U3 genEig jinv jinvK)

namespace CalegariSlopes.Spectral

/-! ## The two inputs from the q-series side -/

/-- `U_3` on `ℚ⟦q⟧`: `Σ aₙ qⁿ ↦ Σ a₃ₙ qⁿ`. -/
noncomputable def U3Q (F : PowerSeries ℚ) : PowerSeries ℚ := PowerSeries.mk fun n => coeff (3 * n) F

/-- (C4), the property of Theorem 2.1 (b): `U_3 (G ^ j) = Σ_i u_ij G ^ i` in `ℚ⟦q⟧` for every
`j ≥ 1`; the sum is over `1 ≤ i ≤ 3 j`, which holds every nonzero `u_ij` (`u_0j = 0`, and `u_ij = 0` for
`i > 3 j`). -/
def C4 (G : PowerSeries ℚ) : Prop :=
  ∀ j : ℕ, 1 ≤ j → U3Q (G ^ j) = ∑ i ∈ Finset.Icc 1 (3 * j), u i j • G ^ i

/-- (J), the property of Theorem 2.1 (a): `jinv * 27 (1 + G) (1 + 9 G) ^ 3 = G` in `ℚ⟦q⟧`, that is
`j = 27 (1 + G) (1 + 9 G) ^ 3 / G` (the relation between `j` and the hauptmodul of `X_0(3)`). -/
def JHyp (G : PowerSeries ℚ) : Prop :=
  jinv * (27 * (1 + G) * (1 + 9 * G) ^ 3) = G

/-- `G` with coefficients in `K`. -/
noncomputable def GK (G : PowerSeries ℚ) : PowerSeries K := PowerSeries.map (algebraMap ℚ K) G

/-! ## Sequences and banded matrices -/

/-- `c₀`: the sequence tends to `0`. -/
def IsC0 (a : ℕ → K) : Prop := Tendsto a atTop (𝓝 0)

/-- `a ∈ S_s`: `v_3(a_j) + s j → +∞`, that is `‖a_j‖ 3 ^ (-s j) → 0`. `S_0 = c₀`. -/
def InS (s : ℝ) (a : ℕ → K) : Prop :=
  Tendsto (fun j : ℕ => ‖a j‖ * (3 : ℝ) ^ (-(s * j))) atTop (𝓝 0)

/-- The unit sequence `e_n`. -/
noncomputable def unitSeq (n i : ℕ) : K := if i = n then 1 else 0

/-- The action of a rational matrix supported on `1 ≤ j ≤ 3 i`: `(M a)_i = Σ_{1 ≤ j ≤ 3i} M_ij a_j` (zero at
`i = 0`). -/
noncomputable def bact (M : ℕ → ℕ → ℚ) (a : ℕ → K) (i : ℕ) : K :=
  ∑ j ∈ Finset.Icc 1 (3 * i), (M i j : K) * a j

/-- `U = (u_ij)` acting on sequences (`u_ij = 0` for `j > 3 i`, so the finite sums of `bact` are the whole
sums). -/
noncomputable def Uop : Module.End K (ℕ → K) where
  toFun a := bact u a
  map_add' a b := by
    funext i
    simp [bact, mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    funext i
    simp [bact, Finset.mul_sum, mul_left_comm]

/-- `Σ_n b_n x_n`, coordinatewise (a convergent series for `b ∈ c₀` and bounded `x`). -/
noncomputable def expand (x : ℕ → ℕ → K) (b : ℕ → K) (i : ℕ) : K := ∑' n, b n * x n i

/-- `C = B A`: `C_ij = Σ_{1 ≤ k ≤ 3i} B_ik A_kj` (`B_ik = 0` for `k > 3 i`). -/
def Cm (i j : ℕ) : ℚ := ∑ k ∈ Finset.Icc 1 (3 * i), ADB.B i k * ADB.A k j

/-- `w = e_n + y`. -/
noncomputable def wv (n : ℕ) (y : ℕ → K) (j : ℕ) : K := unitSeq n j + y j

/-- `φ(s) = max(3 s - 6, s / 3 - 2)`, the radius map of Lemma 6.5 (the paper's `ψ`). -/
noncomputable def phiS (s : ℝ) : ℝ := max (3 * s - 6) (s / 3 - 2)

/-- `Φ(a) = Σ_{j ≥ 1} a_j G ^ j` in `K⟦q⟧`: the coefficient of `q ^ N` is the finite sum over `j ≤ N`
(the whole sum when `G = O(q)`). -/
noncomputable def Phi (G : PowerSeries ℚ) : (ℕ → K) →ₗ[K] PowerSeries K where
  toFun a := PowerSeries.mk fun N => ∑ j ∈ Finset.Icc 1 N, a j * coeff N (GK G ^ j)
  map_add' a b := by
    ext N
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    ext N
    simp [Finset.mul_sum, mul_assoc]

/-! ## The hypotheses of Lemma 6.1 and the eigen-family of Theorem 2.4 -/

/-- The hypotheses of Lemma 6.1: every `x n` is in `c₀` and `‖x n - e n‖ ≤ c` coordinatewise, `0 ≤ c < 1`. -/
structure NearBasis (x : ℕ → ℕ → K) (c : ℝ) : Prop where
  nonneg : 0 ≤ c
  lt_one : c < 1
  isC0 : ∀ n, IsC0 (x n)
  near : ∀ n i, ‖x n i - unitSeq n i‖ ≤ c

/-- The eigenvectors `x_n = A w_n` and eigenvalues `λ_n = D_n μ_n` of Theorem 2.4 (a), `n ≥ 1`, completed at
`n = 0` by `x_0 = e_0`, `λ_0 = 0` (the spectator coordinate). -/
structure EigenFamily where
  x : ℕ → ℕ → K
  lam : ℕ → K
  near : NearBasis x (1 / 3)
  eig : ∀ n, Uop (x n) = lam n • x n
  lam_zero : lam 0 = 0
  norm_lam : ∀ n, 1 ≤ n → ‖lam n‖ = (3 : ℝ) ^ (-(slope n : ℤ))

end CalegariSlopes.Spectral
