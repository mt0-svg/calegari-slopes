/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Spectral.Basic
public import CalegariSlopes.Spectral.Seq

@[expose] public section

/-!
# The contraction: one eigenvector for each `n` (Section 6.3)

`exists_eigen_DC` (Proposition 6.4) and `exists_eigenFamily` (Theorem 2.4 (a)).

For `n ≥ 1` and `y` in the ball `Y = {y ∈ c₀ : y_0 = y_n = 0, ‖y‖ ≤ 1/3}`, with `w = e_n + y`:
`μ(y) = (C w)_n` (the paper's `ξ(y)`), `s_i(y) = (C° w)_i` (`C°` the off-diagonal part of `C`; the paper's
`η_i(y)`), `δ_i(y) = D_n μ(y) - D_i C_ii` (the paper's `Δ_i(y)`), and
`T(y)_i = D_i s_i(y) / δ_i(y)` for `i ∉ {0, n}`, `T(y)_0 = T(y)_n = 0`. The estimates (V1) to (V3) put `T(Y)` in
`Y`; (L1) to (L3) make `T` a contraction of factor `1/3`; its fixed point gives `D (C w) = D_n μ w`.
-/

open PowerSeries Filter Topology
open CalegariSlopes.Overconvergent (K S0dag U3 genEig jinv jinvK)

namespace CalegariSlopes.Spectral

/-! ## The map `T` -/

/-- `C°`, the off-diagonal part of `C`. -/
def Coff (i j : ℕ) : ℚ := if i = j then 0 else Cm i j

/-- `μ(y) = (C w)_n`, `w = e_n + y`. -/
noncomputable def muY (n : ℕ) (y : ℕ → K) : K := bact Cm (wv n y) n

/-- `s_i(y) = (C° w)_i`. -/
noncomputable def sY (n : ℕ) (y : ℕ → K) (i : ℕ) : K := bact Coff (wv n y) i

/-- `δ_i(y) = D_n μ(y) - D_i C_ii`. -/
noncomputable def deltaY (n : ℕ) (y : ℕ → K) (i : ℕ) : K :=
  (ADB.D n : K) * muY n y - (ADB.D i : K) * (Cm i i : K)

/-- `T(y)_i = D_i s_i(y) / δ_i(y)` for `i ∉ {0, n}`, and `0` at `i = 0` and `i = n`. -/
noncomputable def Tmap (n : ℕ) (y : ℕ → K) (i : ℕ) : K :=
  if i = 0 ∨ i = n then 0 else (ADB.D i : K) * sY n y i / deltaY n y i

/-! ## Elementary facts -/

/-- `‖w_j‖ ≤ 1` for `w = e_n + y`, `‖y‖ ≤ 1/3`. -/
theorem norm_wv_le_one {n : ℕ} {y : ℕ → K} (hy : ∀ j, ‖y j‖ ≤ 1 / 3) (j : ℕ) : ‖wv n y j‖ ≤ 1 := by
  dsimp [wv]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
  refine max_le ?_ ?_
  · unfold unitSeq; split_ifs <;> simp
  · have h := hy j
    linarith

/-- `‖C°_ij‖ ≤ 1/3`. -/
theorem norm_Coff_le (i j : ℕ) : ‖(Coff i j : ℚ_[3])‖ ≤ 1 / 3 := by
  dsimp [Coff]
  split_ifs with h
  · simp
  · exact norm_Cm_le_third h

/-- `(C w)_i = C_ii w_i + (C° w)_i` for `i ≥ 1`. -/
theorem bact_Cm_eq (w : ℕ → K) (i : ℕ) (hi : 1 ≤ i) :
    bact Cm w i = (Cm i i : K) * w i + bact Coff w i := by
  have hi_mem : i ∈ Finset.Icc 1 (3 * i) := by
    refine Finset.mem_Icc.mpr ⟨hi, ?_⟩
    nlinarith
  have hcoff_sum : bact Coff w i = ∑ j ∈ (Finset.Icc 1 (3 * i)).erase i, (Coff i j : K) * w j := by
    rw [bact, ← Finset.add_sum_erase _ _ hi_mem]
    simp [Coff]
  calc
    bact Cm w i = ∑ j ∈ Finset.Icc 1 (3 * i), (Cm i j : K) * w j := rfl
    _ = (Cm i i : K) * w i + ∑ j ∈ (Finset.Icc 1 (3 * i)).erase i, (Cm i j : K) * w j := by
      rw [← Finset.add_sum_erase _ _ hi_mem]
    _ = (Cm i i : K) * w i + ∑ j ∈ (Finset.Icc 1 (3 * i)).erase i, (Coff i j : K) * w j := by
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj_ne : j ≠ i := (Finset.mem_erase.mp hj).left
      have h_eq : (Coff i j : K) = (Cm i j : K) := by
        dsimp [Coff]
        by_cases h : i = j
        · exfalso; exact hj_ne h.symm
        · simp [h]
      rw [h_eq]
    _ = (Cm i i : K) * w i + bact Coff w i := by rw [hcoff_sum]

/-- `|slope i - slope n| ≥ 1` for `i ≠ n`, as norms: `‖D_i‖ ≠ ‖D_n‖`. -/
theorem norm_D_ne {i n : ℕ} (h : i ≠ n) : ‖(ADB.D i : K)‖ ≠ ‖(ADB.D n : K)‖ := by
  have h_slope_ne : slope i ≠ slope n := slope_strictMono.injective.ne h
  have h_exp_ne : -(slope i : ℤ) ≠ -(slope n : ℤ) := by
    intro h_eq
    apply h_slope_ne
    have := neg_inj.mp h_eq
    exact Nat.cast_inj.mp this
  have h_norm_i : ‖(ADB.D i : K)‖ = (3 : ℝ) ^ (-(slope i : ℤ)) := by
    rw [norm_ratCast_K (ADB.D i), CalegariSlopes.Newton.norm_D i]
  have h_norm_n : ‖(ADB.D n : K)‖ = (3 : ℝ) ^ (-(slope n : ℤ)) := by
    rw [norm_ratCast_K (ADB.D n), CalegariSlopes.Newton.norm_D n]
  rw [h_norm_i, h_norm_n]
  exact (zpow_right_injective₀ (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≠ 1)).ne h_exp_ne

/-- `‖D_i‖ / ‖D_n‖ ≤ 1/3` or `‖D_n‖ / ‖D_i‖ ≤ 1/3` for `i ≠ n`: `‖D_i‖ ‖D_n‖ ≤ (1/3) max(‖D_i‖, ‖D_n‖) ^ 2`. -/
theorem norm_D_mul_le {i n : ℕ} (h : i ≠ n) :
    ‖(ADB.D i : K)‖ * ‖(ADB.D n : K)‖ ≤ 1 / 3 * max ‖(ADB.D i : K)‖ ‖(ADB.D n : K)‖ ^ 2 := by
  have h_lt_or : i < n ∨ n < i := Nat.lt_or_gt_of_ne h
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have h3one : (1 : ℝ) ≤ 3 := by norm_num
  have h3ne0 : (3 : ℝ) ≠ 0 := by norm_num
  have hpos_i : 0 ≤ ‖(ADB.D i : K)‖ := norm_nonneg _
  have hpos_n : 0 ≤ ‖(ADB.D n : K)‖ := norm_nonneg _
  have norm_D_i : ‖(ADB.D i : K)‖ = (3 : ℝ) ^ (-(slope i : ℤ)) := by
    rw [norm_ratCast_K, CalegariSlopes.Newton.norm_D]
  have norm_D_n : ‖(ADB.D n : K)‖ = (3 : ℝ) ^ (-(slope n : ℤ)) := by
    rw [norm_ratCast_K, CalegariSlopes.Newton.norm_D]
  rcases h_lt_or with (h_lt | h_lt)
  · -- case i < n
    have h_slope_lt : slope i < slope n := slope_strictMono h_lt
    have h_slope_le : (slope i : ℤ) + 1 ≤ (slope n : ℤ) := by
      have : slope i + 1 ≤ slope n := Nat.succ_le_of_lt h_slope_lt
      exact mod_cast this
    have h_neg_le : -(slope n : ℤ) ≤ -(slope i : ℤ) - 1 := by
      linarith
    have h_pow_le : (3 : ℝ) ^ (-(slope n : ℤ)) ≤ (3 : ℝ) ^ (-(slope i : ℤ) - 1) :=
      zpow_le_zpow_right₀ h3one h_neg_le
    have h_pow_sub : (3 : ℝ) ^ (-(slope i : ℤ) - 1) = (3 : ℝ) ^ (-(slope i : ℤ)) * ((3 : ℝ) ^ (-1 : ℤ)) := by
      rw [zpow_sub₀ h3ne0 (-(slope i : ℤ)) (1 : ℤ), div_eq_mul_inv, zpow_one, zpow_neg_one]
    have h_pow_neg_one : (3 : ℝ) ^ (-1 : ℤ) = (1 / 3 : ℝ) := by
      norm_num
    rw [h_pow_sub, h_pow_neg_one] at h_pow_le
    have h_le : ‖(ADB.D n : K)‖ ≤ (1/3 : ℝ) * ‖(ADB.D i : K)‖ := by
      rw [norm_D_i, norm_D_n]
      linarith
    have h_max_eq : max ‖(ADB.D i : K)‖ ‖(ADB.D n : K)‖ = ‖(ADB.D i : K)‖ := by
      apply max_eq_left
      calc
        ‖(ADB.D n : K)‖ ≤ (1/3 : ℝ) * ‖(ADB.D i : K)‖ := h_le
        _ ≤ ‖(ADB.D i : K)‖ := by
          nlinarith [hpos_i]
    calc
      ‖(ADB.D i : K)‖ * ‖(ADB.D n : K)‖ ≤ ‖(ADB.D i : K)‖ * ((1/3 : ℝ) * ‖(ADB.D i : K)‖) := by
        gcongr
      _ = (1/3 : ℝ) * (‖(ADB.D i : K)‖ * ‖(ADB.D i : K)‖) := by ring
      _ = (1/3 : ℝ) * max ‖(ADB.D i : K)‖ ‖(ADB.D n : K)‖ ^ 2 := by
        rw [h_max_eq]
        ring
  · -- case n < i, symmetric
    have h_slope_lt : slope n < slope i := slope_strictMono h_lt
    have h_slope_le : (slope n : ℤ) + 1 ≤ (slope i : ℤ) := by
      have : slope n + 1 ≤ slope i := Nat.succ_le_of_lt h_slope_lt
      exact mod_cast this
    have h_neg_le : -(slope i : ℤ) ≤ -(slope n : ℤ) - 1 := by
      linarith
    have h_pow_le : (3 : ℝ) ^ (-(slope i : ℤ)) ≤ (3 : ℝ) ^ (-(slope n : ℤ) - 1) :=
      zpow_le_zpow_right₀ h3one h_neg_le
    have h_pow_sub : (3 : ℝ) ^ (-(slope n : ℤ) - 1) = (3 : ℝ) ^ (-(slope n : ℤ)) * ((3 : ℝ) ^ (-1 : ℤ)) := by
      rw [zpow_sub₀ h3ne0 (-(slope n : ℤ)) (1 : ℤ), div_eq_mul_inv, zpow_one, zpow_neg_one]
    have h_pow_neg_one : (3 : ℝ) ^ (-1 : ℤ) = (1 / 3 : ℝ) := by
      norm_num
    rw [h_pow_sub, h_pow_neg_one] at h_pow_le
    have h_le : ‖(ADB.D i : K)‖ ≤ (1/3 : ℝ) * ‖(ADB.D n : K)‖ := by
      rw [norm_D_i, norm_D_n]
      linarith
    have h_max_eq : max ‖(ADB.D i : K)‖ ‖(ADB.D n : K)‖ = ‖(ADB.D n : K)‖ := by
      apply max_eq_right
      calc
        ‖(ADB.D i : K)‖ ≤ (1/3 : ℝ) * ‖(ADB.D n : K)‖ := h_le
        _ ≤ ‖(ADB.D n : K)‖ := by
          nlinarith [hpos_n]
    calc
      ‖(ADB.D i : K)‖ * ‖(ADB.D n : K)‖ ≤ ((1/3 : ℝ) * ‖(ADB.D n : K)‖) * ‖(ADB.D n : K)‖ := by
        gcongr
      _ = (1/3 : ℝ) * (‖(ADB.D n : K)‖ * ‖(ADB.D n : K)‖) := by ring
      _ = (1/3 : ℝ) * max ‖(ADB.D i : K)‖ ‖(ADB.D n : K)‖ ^ 2 := by
        rw [h_max_eq]
        ring

/-! ## (V1) to (V3) -/

/-- (V1) `v_3(μ(y) - 1) ≥ 2`. -/
theorem norm_muY_sub_one_le {n : ℕ} (hn : 1 ≤ n) {y : ℕ → K} (hy : ∀ j, ‖y j‖ ≤ 1 / 3) (hyn : y n = 0) :
    ‖muY n y - 1‖ ≤ 1 / 9 := by
  have hnpos : 1 ≤ n := hn
  -- Decompose muY n y = (Cm n n : K) + bact Coff (wv n y) n
  have hmuY_eq : muY n y = (Cm n n : K) + bact Coff (wv n y) n := by
    calc
      muY n y = bact Cm (wv n y) n := rfl
      _ = (Cm n n : K) * wv n y n + bact Coff (wv n y) n := bact_Cm_eq (wv n y) n hn
      _ = (Cm n n : K) * 1 + bact Coff (wv n y) n := by
        simp [wv, unitSeq, hyn]
      _ = (Cm n n : K) + bact Coff (wv n y) n := by simp
  have hsub : muY n y - 1 = ((Cm n n : K) - 1) + bact Coff (wv n y) n := by
    rw [hmuY_eq]
    abel
  rw [hsub]
  -- Bound the first term: ‖(Cm n n : K) - 1‖ ≤ 1/9
  have hCm : ‖(Cm n n : K) - 1‖ ≤ 1 / 9 := by
    calc
      ‖(Cm n n : K) - 1‖ = ‖((Cm n n - 1 : ℚ) : K)‖ := by norm_num
      _ = ‖((Cm n n - 1 : ℚ) : ℚ_[3])‖ := norm_ratCast_K _
      _ ≤ (3 : ℝ) ^ (-2 : ℤ) := norm_Cm_self_sub_one_le n hn
      _ = 1 / 9 := by norm_num
  -- Bound the second term: ‖bact Coff (wv n y) n‖ ≤ 1/9
  have hCoff : ‖bact Coff (wv n y) n‖ ≤ 1 / 9 := by
    have h_nonempty : (Finset.Icc 1 (3 * n)).Nonempty := by
      refine ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, ?_⟩⟩
      have : 1 ≤ 3 * n := by
        have h3n : 1 ≤ 3 * n := by
          nlinarith
        exact h3n
      exact this
    have h_each : ∀ j ∈ Finset.Icc 1 (3 * n), ‖(Coff n j : K) * wv n y j‖ ≤ 1 / 9 := by
      intro j hj
      rcases Finset.mem_Icc.mp hj with ⟨hj1, hj2⟩
      by_cases hjn : j = n
      · subst hjn
        simp [Coff]
      · have hwv : wv n y j = y j := by
          dsimp [wv, unitSeq]
          simp [hjn]
        rw [hwv, norm_mul]
        have hCoff_norm : ‖(Coff n j : K)‖ ≤ 1 / 3 := by
          rw [norm_ratCast_K]
          exact norm_Coff_le n j
        have hy_norm : ‖y j‖ ≤ 1 / 3 := hy j
        have h_nonneg_Coff : 0 ≤ ‖(Coff n j : K)‖ := norm_nonneg _
        have h_nonneg_y : 0 ≤ ‖y j‖ := norm_nonneg _
        have h_third_nonneg : 0 ≤ (1 : ℝ) / 3 := by norm_num
        calc
          ‖(Coff n j : K)‖ * ‖y j‖ ≤ (1 / 3) * (1 / 3) :=
            mul_le_mul hCoff_norm hy_norm h_nonneg_y h_third_nonneg
          _ = 1 / 9 := by norm_num
    have hsum := IsUltrametricDist.norm_sum_le_of_forall_le_of_nonempty h_nonempty h_each
    simpa [bact] using hsum
  -- Apply ultrametric inequality for addition
  have h_add : ‖((Cm n n : K) - 1) + bact Coff (wv n y) n‖ ≤
      max (‖(Cm n n : K) - 1‖) (‖bact Coff (wv n y) n‖) :=
    IsUltrametricDist.norm_add_le_max _ _
  have h_max : max (‖(Cm n n : K) - 1‖) (‖bact Coff (wv n y) n‖) ≤ 1 / 9 :=
    max_le hCm hCoff
  exact le_trans h_add h_max

/-- (V2) `‖δ_i(y)‖ = max(‖D_n‖, ‖D_i‖)` for `i ≠ n` (`μ(y)` and `C_ii` are units, `slope i ≠ slope n`). -/
theorem norm_deltaY {n i : ℕ} (hn : 1 ≤ n) (hi : 1 ≤ i) (hin : i ≠ n) {y : ℕ → K}
    (hmu : ‖muY n y - 1‖ ≤ 1 / 9) : ‖deltaY n y i‖ = max ‖(ADB.D n : K)‖ ‖(ADB.D i : K)‖ := by
  have hmu_norm : ‖muY n y‖ = 1 := by
    have hlt : ‖muY n y - 1‖ < ‖(1 : K)‖ := by
      calc
        ‖muY n y - 1‖ ≤ 1/9 := hmu
        _ < 1 := by norm_num
        _ = ‖(1 : K)‖ := by simp
    have h_ne : ‖muY n y - 1‖ ≠ ‖(1 : K)‖ := by linarith
    have h_eq : ‖(muY n y - 1) + 1‖ = max ‖muY n y - 1‖ ‖(1 : K)‖ :=
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_ne
    have h_max : max ‖muY n y - 1‖ ‖(1 : K)‖ = ‖(1 : K)‖ :=
      max_eq_right (by linarith)
    calc
      ‖muY n y‖ = ‖(muY n y - 1) + 1‖ := by simp
      _ = max ‖muY n y - 1‖ ‖(1 : K)‖ := h_eq
      _ = ‖(1 : K)‖ := h_max
      _ = 1 := by simp
  have h_Cm_self : ‖(Cm i i : K)‖ = 1 := by
    calc
      ‖(Cm i i : K)‖ = ‖(Cm i i : ℚ_[3])‖ := by simpa using norm_ratCast_K (Cm i i)
      _ = 1 := norm_Cm_self i hi
  have h_Dn_muY : ‖(ADB.D n : K) * muY n y‖ = ‖(ADB.D n : K)‖ := by
    calc
      ‖(ADB.D n : K) * muY n y‖ = ‖(ADB.D n : K)‖ * ‖muY n y‖ := norm_mul _ _
      _ = ‖(ADB.D n : K)‖ * 1 := by rw [hmu_norm]
      _ = ‖(ADB.D n : K)‖ := by simp
  have h_Di_Cm : ‖(ADB.D i : K) * (Cm i i : K)‖ = ‖(ADB.D i : K)‖ := by
    calc
      ‖(ADB.D i : K) * (Cm i i : K)‖ = ‖(ADB.D i : K)‖ * ‖(Cm i i : K)‖ := norm_mul _ _
      _ = ‖(ADB.D i : K)‖ * 1 := by rw [h_Cm_self]
      _ = ‖(ADB.D i : K)‖ := by simp
  have h_D_ne : ‖(ADB.D n : K)‖ ≠ ‖(ADB.D i : K)‖ := Ne.symm (norm_D_ne hin)
  have h_Dn_muY_ne_neg_Di_Cm : ‖(ADB.D n : K) * muY n y‖ ≠ ‖-((ADB.D i : K) * (Cm i i : K))‖ := by
    rw [norm_neg, h_Dn_muY, h_Di_Cm]
    exact h_D_ne
  calc
    ‖deltaY n y i‖ = ‖(ADB.D n : K) * muY n y - (ADB.D i : K) * (Cm i i : K)‖ := rfl
    _ = ‖(ADB.D n : K) * muY n y + (-((ADB.D i : K) * (Cm i i : K)))‖ := by rw [sub_eq_add_neg]
    _ = max ‖(ADB.D n : K) * muY n y‖ ‖(-((ADB.D i : K) * (Cm i i : K)))‖ :=
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_Dn_muY_ne_neg_Di_Cm
    _ = max ‖(ADB.D n : K) * muY n y‖ ‖(ADB.D i : K) * (Cm i i : K)‖ := by simp
    _ = max ‖(ADB.D n : K)‖ ‖(ADB.D i : K)‖ := by rw [h_Dn_muY, h_Di_Cm]

/-- (V2) `δ_i(y) ≠ 0` and `‖D_i / δ_i(y)‖ ≤ 1`. -/
theorem norm_D_div_deltaY_le {n i : ℕ} (hn : 1 ≤ n) (hi : 1 ≤ i) (hin : i ≠ n) {y : ℕ → K}
    (hmu : ‖muY n y - 1‖ ≤ 1 / 9) : deltaY n y i ≠ 0 ∧ ‖(ADB.D i : K) / deltaY n y i‖ ≤ 1 := by
  have hδ := norm_deltaY hn hi hin hmu
  have hD : 0 < ‖(ADB.D i : K)‖ := by
    rw [norm_pos_iff, Rat.cast_ne_zero]
    exact (CalegariSlopes.Newton.D_pos i).ne'
  have hpos : 0 < ‖deltaY n y i‖ := by
    rw [hδ]
    exact lt_of_lt_of_le hD (le_max_right _ _)
  refine ⟨norm_pos_iff.1 hpos, ?_⟩
  rw [norm_div, div_le_one hpos, hδ]
  exact le_max_right _ _

/-- (V3) `v_3(s_i(y)) ≥ 1`. -/
theorem norm_sY_le (n : ℕ) {y : ℕ → K} (hy : ∀ j, ‖y j‖ ≤ 1 / 3) (i : ℕ) : ‖sY n y i‖ ≤ 1 / 3 := by
  have hpos : (0 : ℝ) ≤ 1 / 3 := by norm_num
  have hterm : ∀ j ∈ Finset.Icc 1 (3 * i), ‖((Coff i j : K) * wv n y j : K)‖ ≤ 1 / 3 := by
    intro j hj
    calc
      ‖((Coff i j : K) * wv n y j : K)‖ = ‖(Coff i j : K)‖ * ‖wv n y j‖ := norm_mul _ _
      _ = ‖(Coff i j : ℚ_[3])‖ * ‖wv n y j‖ := by rw [norm_ratCast_K (Coff i j)]
      _ ≤ (1 / 3) * ‖wv n y j‖ := by
        gcongr
        exact norm_Coff_le i j
      _ ≤ (1 / 3) * 1 := by
        gcongr
        exact norm_wv_le_one hy j
      _ = 1 / 3 := by ring
  simpa [sY, bact, wv] using norm_sum_le_of_le (Finset.Icc 1 (3 * i)) hpos hterm

/-- `s(y) ∈ c₀`. -/
theorem isC0_sY (n : ℕ) {y : ℕ → K} (hy : IsC0 y) : IsC0 (sY n y) := by
  have h_eq : sY n y = bact Coff (wv n y) := by
    funext i; rfl
  rw [h_eq]
  refine isC0_bact Coff (fun i j h => ?_) (fun i j => ?_) (isC0_wv hy)
  · dsimp [Coff]
    split
    · rfl
    · exact Cm_eq_zero_of_gt h
  · have hle := norm_Coff_le i j
    have : (1 / 3 : ℝ) ≤ 1 := by norm_num
    linarith

/-! ## (L1) to (L3) -/

/-- (L1) `v_3(μ(y) - μ(y')) ≥ 1 + d`. -/
theorem norm_muY_sub_le {n : ℕ} {y y' : ℕ → K} (hyn : y n = 0) (hy'n : y' n = 0) {d : ℝ} (hd0 : 0 ≤ d)
    (hd : ∀ j, ‖y j - y' j‖ ≤ d) : ‖muY n y - muY n y'‖ ≤ d / 3 := by
  have hd3 : 0 ≤ d / 3 := by nlinarith
  have hwv_sub (j : ℕ) : wv n y j - wv n y' j = y j - y' j := by
    dsimp [wv]
    abel
  have hnormCm (j : ℕ) (hj : j ≠ n) : ‖(Cm n j : K)‖ ≤ (1 : ℝ) / 3 := by
    have h := norm_Cm_le_third (Ne.symm hj)
    calc
      ‖(Cm n j : K)‖ = ‖(Cm n j : ℚ_[3])‖ := by
        simpa using norm_ratCast_K (Cm n j)
      _ ≤ (1 : ℝ) / 3 := h
  calc
    ‖muY n y - muY n y'‖ = ‖(∑ j ∈ Finset.Icc 1 (3 * n), (Cm n j : K) * wv n y j) -
                            (∑ j ∈ Finset.Icc 1 (3 * n), (Cm n j : K) * wv n y' j)‖ := by
      simp [muY, bact]
    _ = ‖∑ j ∈ Finset.Icc 1 (3 * n), ((Cm n j : K) * wv n y j - (Cm n j : K) * wv n y' j)‖ := by
      simp [Finset.sum_sub_distrib]
    _ = ‖∑ j ∈ Finset.Icc 1 (3 * n), (Cm n j : K) * (wv n y j - wv n y' j)‖ := by
      simp [mul_sub]
    _ = ‖∑ j ∈ Finset.Icc 1 (3 * n), (Cm n j : K) * (y j - y' j)‖ := by
      simp [hwv_sub]
    _ ≤ d / 3 := by
      refine norm_sum_le_of_le (Finset.Icc 1 (3 * n)) hd3 ?_
      intro j hj
      by_cases hjn : j = n
      · subst hjn
        simp [hyn, hy'n, hd3]
      · calc
          ‖(Cm n j : K) * (y j - y' j)‖ = ‖(Cm n j : K)‖ * ‖y j - y' j‖ := by
            exact norm_mul (Cm n j : K) (y j - y' j)
          _ ≤ ((1 : ℝ) / 3) * d := by
            have h1 : 0 ≤ ‖(Cm n j : K)‖ := norm_nonneg _
            have h2 : 0 ≤ ‖y j - y' j‖ := norm_nonneg _
            gcongr
            · exact hnormCm j hjn
            · exact hd j
          _ = d / 3 := by ring

/-- (L2) `v_3(s_i(y) - s_i(y')) ≥ 1 + d`. -/
theorem norm_sY_sub_le (n : ℕ) {y y' : ℕ → K} {d : ℝ} (hd0 : 0 ≤ d) (hd : ∀ j, ‖y j - y' j‖ ≤ d) (i : ℕ) :
    ‖sY n y i - sY n y' i‖ ≤ d / 3 := by
  have hsub : sY n y i - sY n y' i = ∑ j ∈ Finset.Icc 1 (3 * i), (Coff i j : K) * (y j - y' j) := by
    calc
      sY n y i - sY n y' i = bact Coff (wv n y) i - bact Coff (wv n y') i := rfl
      _ = (∑ j ∈ Finset.Icc 1 (3 * i), (Coff i j : K) * wv n y j) -
          (∑ j ∈ Finset.Icc 1 (3 * i), (Coff i j : K) * wv n y' j) := rfl
      _ = ∑ j ∈ Finset.Icc 1 (3 * i), ((Coff i j : K) * wv n y j - (Coff i j : K) * wv n y' j) := by
        rw [Finset.sum_sub_distrib]
      _ = ∑ j ∈ Finset.Icc 1 (3 * i), (Coff i j : K) * (wv n y j - wv n y' j) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [mul_sub]
      _ = ∑ j ∈ Finset.Icc 1 (3 * i), (Coff i j : K) * (y j - y' j) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        simp [wv, unitSeq]
  rw [hsub]
  have hnorm : ∀ j, ‖(Coff i j : K)‖ ≤ 1/3 := by
    intro j
    calc
      ‖(Coff i j : K)‖ = ‖(Coff i j : ℚ_[3])‖ := norm_ratCast_K (Coff i j)
      _ ≤ 1/3 := norm_Coff_le i j
  have hbound : ∀ j, ‖(Coff i j : K) * (y j - y' j)‖ ≤ d / 3 := by
    intro j
    calc
      ‖(Coff i j : K) * (y j - y' j)‖ = ‖(Coff i j : K)‖ * ‖y j - y' j‖ := norm_mul _ _
      _ ≤ (1/3 : ℝ) * ‖y j - y' j‖ := mul_le_mul_of_nonneg_right (hnorm j) (norm_nonneg _)
      _ ≤ (1/3 : ℝ) * d := mul_le_mul_of_nonneg_left (hd j) (by norm_num)
      _ = d / 3 := by ring
  have hd3 : 0 ≤ d / 3 := by nlinarith
  apply norm_sum_le_of_le (Finset.Icc 1 (3 * i)) hd3 (fun j hj => hbound j)

/-- (L3) `v_3(D_i / δ_i(y) - D_i / δ_i(y')) ≥ |slope i - slope n| + v_3(μ(y) - μ(y'))`, used with the gap `≥ 1`. -/
theorem norm_D_div_deltaY_sub_le {n i : ℕ} (hn : 1 ≤ n) (hi : 1 ≤ i) (hin : i ≠ n) {y y' : ℕ → K}
    (hmu : ‖muY n y - 1‖ ≤ 1 / 9) (hmu' : ‖muY n y' - 1‖ ≤ 1 / 9) :
    ‖(ADB.D i : K) / deltaY n y i - (ADB.D i : K) / deltaY n y' i‖ ≤ 1 / 3 * ‖muY n y - muY n y'‖ := by
  rcases norm_D_div_deltaY_le hn hi hin hmu with ⟨hδ_ne, hδ_le⟩
  rcases norm_D_div_deltaY_le hn hi hin hmu' with ⟨hδ'_ne, hδ'_le⟩
  have hδ_norm : ‖deltaY n y i‖ = max ‖(ADB.D n : K)‖ ‖(ADB.D i : K)‖ := norm_deltaY hn hi hin hmu
  have hδ'_norm : ‖deltaY n y' i‖ = max ‖(ADB.D n : K)‖ ‖(ADB.D i : K)‖ := norm_deltaY hn hi hin hmu'
  set M := max ‖(ADB.D n : K)‖ ‖(ADB.D i : K)‖ with hM_def
  have hM_pos : 0 < M := by
    rw [← hδ_norm]
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm (mt norm_eq_zero.mp hδ_ne))
  have h_diff : deltaY n y' i - deltaY n y i = (ADB.D n : K) * (muY n y' - muY n y) := by
    dsimp [deltaY]
    ring
  have h_sub_eq : (ADB.D i : K) / deltaY n y i - (ADB.D i : K) / deltaY n y' i =
      (ADB.D i : K) * (ADB.D n : K) * (muY n y' - muY n y) / (deltaY n y i * deltaY n y' i) := by
    field_simp [hδ_ne, hδ'_ne]
    rw [h_diff]
    ring
  rw [h_sub_eq]
  rw [norm_div, norm_mul, norm_mul, norm_mul]
  rw [hδ_norm, hδ'_norm]
  rw [← pow_two]
  rw [norm_sub_rev (muY n y') (muY n y)]
  have hM_sq_pos : 0 < M ^ 2 := pow_pos hM_pos 2
  have h_mul : ‖(ADB.D i : K)‖ * ‖(ADB.D n : K)‖ ≤ 1 / 3 * M ^ 2 := by
    have := norm_D_mul_le hin
    simpa [max_comm, hM_def] using this
  calc
    ‖(ADB.D i : K)‖ * ‖(ADB.D n : K)‖ * ‖muY n y - muY n y'‖ / (M ^ 2)
        = (‖(ADB.D i : K)‖ * ‖(ADB.D n : K)‖ / (M ^ 2)) * ‖muY n y - muY n y'‖ := by ring
    _ ≤ ((1 / 3 * M ^ 2) / (M ^ 2)) * ‖muY n y - muY n y'‖ := by
      have h_div : ‖(ADB.D i : K)‖ * ‖(ADB.D n : K)‖ / (M ^ 2) ≤ (1 / 3 * M ^ 2) / (M ^ 2) :=
        div_le_div_of_nonneg_right h_mul hM_sq_pos.le
      exact mul_le_mul_of_nonneg_right h_div (norm_nonneg _)
    _ = 1 / 3 * ‖muY n y - muY n y'‖ := by
      field_simp [hM_sq_pos.ne']

/-! ## `T` maps `Y` into `Y` and contracts -/

/-- `T(Y) ⊆ Y`. -/
theorem Tmap_maps {n : ℕ} (hn : 1 ≤ n) {y : ℕ → K} (hy : ∀ j, ‖y j‖ ≤ 1 / 3) (hyn : y n = 0)
    (hyc : IsC0 y) :
    (∀ i, ‖Tmap n y i‖ ≤ 1 / 3) ∧ (∀ i ∈ ({0, n} : Set ℕ), Tmap n y i = 0) ∧ IsC0 (Tmap n y) := by
  have hmu := norm_muY_sub_one_le hn hy hyn
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hi0 : i = 0
    · subst hi0; unfold Tmap; simp
    · by_cases hin : i = n
      · subst hin; unfold Tmap; simp
      · have hi1 : 1 ≤ i := by omega
        unfold Tmap
        simp [hi0, hin]
        have hdiv := norm_D_div_deltaY_le hn hi1 hin hmu
        rcases hdiv with ⟨hden_ne_zero, hdiv_le⟩
        have hdiv_le' : ‖(ADB.D i : K)‖ / ‖deltaY n y i‖ ≤ 1 := by
          rw [← norm_div]
          exact hdiv_le
        have h : ‖(ADB.D i : K)‖ * ‖sY n y i‖ / ‖deltaY n y i‖ ≤ ‖sY n y i‖ := by
          calc
            ‖(ADB.D i : K)‖ * ‖sY n y i‖ / ‖deltaY n y i‖ = (‖(ADB.D i : K)‖ / ‖deltaY n y i‖) * ‖sY n y i‖ := by
              rw [← div_mul_eq_mul_div]
            _ ≤ 1 * ‖sY n y i‖ := by gcongr
            _ = ‖sY n y i‖ := by simp
        apply le_trans h
        simpa [one_div] using norm_sY_le n hy i
  · intro i hi
    simp_rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with (rfl | rfl)
    · unfold Tmap; simp
    · unfold Tmap; simp
  · refine IsC0.of_norm_le (isC0_sY n hyc) ?_
    intro i
    by_cases hi0 : i = 0
    · subst hi0; unfold Tmap; simp
    · by_cases hin : i = n
      · subst hin; unfold Tmap; simp
      · have hi1 : 1 ≤ i := by omega
        unfold Tmap
        simp [hi0, hin]
        have hdiv := norm_D_div_deltaY_le hn hi1 hin hmu
        rcases hdiv with ⟨hden_ne_zero, hdiv_le⟩
        have hdiv_le' : ‖(ADB.D i : K)‖ / ‖deltaY n y i‖ ≤ 1 := by
          rw [← norm_div]
          exact hdiv_le
        calc
          ‖(ADB.D i : K)‖ * ‖sY n y i‖ / ‖deltaY n y i‖ = (‖(ADB.D i : K)‖ / ‖deltaY n y i‖) * ‖sY n y i‖ := by
            rw [← div_mul_eq_mul_div]
          _ ≤ 1 * ‖sY n y i‖ := by gcongr
          _ = ‖sY n y i‖ := by simp

/-- `T` contracts by `1/3` on `Y`. -/
theorem Tmap_lip {n : ℕ} (hn : 1 ≤ n) {y y' : ℕ → K} (hy : ∀ j, ‖y j‖ ≤ 1 / 3) (hyn : y n = 0)
    (hy' : ∀ j, ‖y' j‖ ≤ 1 / 3) (hy'n : y' n = 0) {d : ℝ} (hd0 : 0 ≤ d) (hd : ∀ j, ‖y j - y' j‖ ≤ d)
    (i : ℕ) : ‖Tmap n y i - Tmap n y' i‖ ≤ 1 / 3 * d := by
  by_cases hi0 : i = 0
  · subst hi0; simp [Tmap, hd0]
  · by_cases hin : i = n
    · subst hin; simp [Tmap, hd0]
    · have hi : 1 ≤ i := Nat.one_le_of_lt (Nat.pos_of_ne_zero hi0)
      have hmu : ‖muY n y - 1‖ ≤ 1 / 9 := norm_muY_sub_one_le hn hy hyn
      have hmu' : ‖muY n y' - 1‖ ≤ 1 / 9 := norm_muY_sub_one_le hn hy' hy'n
      have hq := norm_D_div_deltaY_le hn hi hin hmu
      have hq_bound : ‖(ADB.D i : K) / deltaY n y i‖ ≤ 1 := hq.2
      have hq_ne_zero : deltaY n y i ≠ 0 := hq.1
      have hq' := norm_D_div_deltaY_le hn hi hin hmu'
      have hq'_ne_zero : deltaY n y' i ≠ 0 := hq'.1
      have hs_sub : ‖sY n y i - sY n y' i‖ ≤ d / 3 := norm_sY_sub_le n hd0 hd i
      have hq_sub : ‖(ADB.D i : K) / deltaY n y i - (ADB.D i : K) / deltaY n y' i‖ ≤
          1 / 3 * ‖muY n y - muY n y'‖ :=
        norm_D_div_deltaY_sub_le hn hi hin hmu hmu'
      have hmu_sub : ‖muY n y - muY n y'‖ ≤ d / 3 := norm_muY_sub_le hyn hy'n hd0 hd
      have hs_le : ‖sY n y' i‖ ≤ 1 / 3 := norm_sY_le n hy' i
      have h_eq : (ADB.D i : K) * sY n y i / deltaY n y i - (ADB.D i : K) * sY n y' i / deltaY n y' i =
          ((ADB.D i : K) / deltaY n y i) * (sY n y i - sY n y' i) +
          (((ADB.D i : K) / deltaY n y i) - ((ADB.D i : K) / deltaY n y' i)) * sY n y' i := by
        field_simp [hq_ne_zero, hq'_ne_zero]
        ring
      unfold Tmap
      simp [hi0, hin]
      rw [h_eq]
      have h1 : ‖((ADB.D i : K) / deltaY n y i) * (sY n y i - sY n y' i)‖ ≤ d / 3 := by
        calc
          ‖((ADB.D i : K) / deltaY n y i) * (sY n y i - sY n y' i)‖ ≤
              ‖(ADB.D i : K) / deltaY n y i‖ * ‖sY n y i - sY n y' i‖ := norm_mul_le _ _
          _ ≤ 1 * (d / 3) := by gcongr
          _ = d / 3 := by simp
      have h2 : ‖(((ADB.D i : K) / deltaY n y i) - ((ADB.D i : K) / deltaY n y' i)) * sY n y' i‖ ≤ d / 3 := by
        calc
          ‖(((ADB.D i : K) / deltaY n y i) - ((ADB.D i : K) / deltaY n y' i)) * sY n y' i‖ ≤
              ‖((ADB.D i : K) / deltaY n y i) - ((ADB.D i : K) / deltaY n y' i)‖ * ‖sY n y' i‖ := norm_mul_le _ _
          _ ≤ (1 / 3 * ‖muY n y - muY n y'‖) * (1 / 3) := by gcongr
          _ ≤ (1 / 3 * (d / 3)) * (1 / 3) := by gcongr
          _ = d / 27 := by ring
          _ ≤ d / 3 := by
            have : 0 ≤ d := hd0
            nlinarith
      have hmax : ‖((ADB.D i : K) / deltaY n y i) * (sY n y i - sY n y' i) +
          (((ADB.D i : K) / deltaY n y i) - ((ADB.D i : K) / deltaY n y' i)) * sY n y' i‖ ≤ d / 3 := by
        apply le_trans (IsUltrametricDist.norm_add_le_max _ _)
        apply max_le h1 h2
      simpa [div_eq_mul_inv, mul_comm] using hmax

/-- The equations at a fixed point: `D_i (C w)_i = D_n μ(y) w_i` for `i ≥ 1`. -/
theorem eq_of_Tmap_eq {n : ℕ} (hn : 1 ≤ n) {y : ℕ → K} (hy : ∀ j, ‖y j‖ ≤ 1 / 3) (hyn : y n = 0)
    (hT : Tmap n y = y) (i : ℕ) (hi : 1 ≤ i) :
    (ADB.D i : K) * bact Cm (wv n y) i = (ADB.D n : K) * muY n y * wv n y i := by
  by_cases hin : i = n
  · -- case i = n
    rw [hin]
    have hwvn : wv n y n = 1 := by
      dsimp [wv, unitSeq]
      simp [hyn]
    have hbact : bact Cm (wv n y) n = muY n y := rfl
    rw [hwvn, hbact]
    ring
  · -- case i ≠ n
    have hi0 : i ≠ 0 := by omega
    have hwvi : wv n y i = y i := by
      dsimp [wv, unitSeq]
      simp [hin]
    have hbact_eq : bact Cm (wv n y) i = (Cm i i : K) * wv n y i + bact Coff (wv n y) i :=
      bact_Cm_eq (wv n y) i hi
    rw [hwvi] at hbact_eq
    have hT_i : Tmap n y i = y i := by rw [hT]
    have hT_i_eq : Tmap n y i = (ADB.D i : K) * sY n y i / deltaY n y i := by
      dsimp [Tmap]
      simp [hi0, hin]
    rw [hT_i_eq] at hT_i
    have h_delta_ne_zero : deltaY n y i ≠ 0 :=
      (norm_D_div_deltaY_le hn hi hin (norm_muY_sub_one_le hn hy hyn)).1
    have h_eq : deltaY n y i * y i = (ADB.D i : K) * sY n y i := by
      have := (div_eq_iff h_delta_ne_zero).mp hT_i
      -- this: (ADB.D i : K) * sY n y i = y i * deltaY n y i
      calc
        deltaY n y i * y i = y i * deltaY n y i := mul_comm _ _
        _ = (ADB.D i : K) * sY n y i := by rw [← this]
    have h_delta_def : deltaY n y i = (ADB.D n : K) * muY n y - (ADB.D i : K) * (Cm i i : K) := rfl
    rw [h_delta_def] at h_eq
    rw [hbact_eq]
    have h_sY_def : sY n y i = bact Coff (wv n y) i := rfl
    rw [h_sY_def] at h_eq
    -- h_eq: ((ADB.D n : K) * muY n y - (ADB.D i : K) * (Cm i i : K)) * y i = (ADB.D i : K) * bact Coff (wv n y) i
    -- Goal: (ADB.D i : K) * ((Cm i i : K) * y i + bact Coff (wv n y) i) = (ADB.D n : K) * muY n y * wv n y i
    rw [hwvi]
    -- Goal: (ADB.D i : K) * ((Cm i i : K) * y i + bact Coff (wv n y) i) = (ADB.D n : K) * muY n y * y i
    calc
      (ADB.D i : K) * ((Cm i i : K) * y i + bact Coff (wv n y) i)
          = (ADB.D i : K) * ((Cm i i : K) * y i) + (ADB.D i : K) * bact Coff (wv n y) i := by ring
      _ = (ADB.D i : K) * (Cm i i : K) * y i + (ADB.D i : K) * bact Coff (wv n y) i := by ring
      _ = (ADB.D i : K) * (Cm i i : K) * y i + (((ADB.D n : K) * muY n y - (ADB.D i : K) * (Cm i i : K)) * y i) := by rw [← h_eq]
      _ = ((ADB.D i : K) * (Cm i i : K) + ((ADB.D n : K) * muY n y - (ADB.D i : K) * (Cm i i : K))) * y i := by ring
      _ = (ADB.D n : K) * muY n y * y i := by ring

/-! ## Proposition 6.4 and Theorem 2.4 (a) -/

/-- Proposition 6.4. -/
theorem exists_eigen_DC (n : ℕ) (hn : 1 ≤ n) :
    ∃ (y : ℕ → K) (μ : K), y 0 = 0 ∧ y n = 0 ∧ (∀ j, ‖y j‖ ≤ 1 / 3) ∧ IsC0 y ∧ ‖μ - 1‖ ≤ 1 / 9 ∧
      ∀ i, 1 ≤ i → (ADB.D i : K) * bact Cm (wv n y) i = (ADB.D n : K) * μ * wv n y i := by
  have hr : 0 ≤ (1/3 : ℝ) := by norm_num
  have hc0 : 0 ≤ (1/3 : ℝ) := by norm_num
  have hc1 : (1/3 : ℝ) < 1 := by norm_num
  have hmaps : ∀ y : ℕ → K, (∀ i, ‖y i‖ ≤ (1/3 : ℝ)) → (∀ i ∈ ({0, n} : Set ℕ), y i = 0) → IsC0 y →
    (∀ i, ‖Tmap n y i‖ ≤ (1/3 : ℝ)) ∧ (∀ i ∈ ({0, n} : Set ℕ), Tmap n y i = 0) ∧ IsC0 (Tmap n y) := by
    intro y hy hZ hyc
    have hyn : y n = 0 := hZ n (by simp)
    exact Tmap_maps hn hy hyn hyc
  have hlip : ∀ y y' : ℕ → K, (∀ i, ‖y i‖ ≤ (1/3 : ℝ)) → (∀ i ∈ ({0, n} : Set ℕ), y i = 0) → IsC0 y →
    (∀ i, ‖y' i‖ ≤ (1/3 : ℝ)) → (∀ i ∈ ({0, n} : Set ℕ), y' i = 0) → IsC0 y' →
    ∀ d : ℝ, 0 ≤ d → (∀ i, ‖y i - y' i‖ ≤ d) → ∀ i, ‖Tmap n y i - Tmap n y' i‖ ≤ (1/3 : ℝ) * d := by
    intro y y' hy hZ hyc hy' hZ' hyc' d hd0 hd i
    have hyn : y n = 0 := hZ n (by simp)
    have hy'n : y' n = 0 := hZ' n (by simp)
    exact Tmap_lip hn hy hyn hy' hy'n hd0 hd i
  obtain ⟨y, hy_bound, hy_zero, hy_c0, hT_eq⟩ := exists_fixed_seq (Tmap n) (1/3) (1/3) ({0, n} : Set ℕ)
    hr hc0 hc1 hmaps hlip
  have hy0 : y 0 = 0 := hy_zero 0 (by simp)
  have hyn : y n = 0 := hy_zero n (by simp)
  refine ⟨y, muY n y, hy0, hyn, hy_bound, hy_c0, ?_, ?_⟩
  · exact norm_muY_sub_one_le hn hy_bound hyn
  · intro i hi
    exact eq_of_Tmap_eq hn hy_bound hyn hT_eq i hi

/-- `U e_0 = 0`: the spectator coordinate. -/
theorem Uop_unitSeq_zero : Uop (unitSeq 0) = 0 := by
  funext i
  dsimp [Uop, bact, unitSeq]
  refine Finset.sum_eq_zero ?_
  intro j hj
  have hj0 : j ≠ 0 := by
    rcases Finset.mem_Icc.1 hj with ⟨h1, h2⟩
    omega
  simp [hj0]

/-- Theorem 2.4 (a) for one `n ≥ 1`: `x = A w`, `λ = D_n μ`. -/
theorem exists_eigvec (n : ℕ) (hn : 1 ≤ n) :
    ∃ (x : ℕ → K) (lam : K), IsC0 x ∧ (∀ i, ‖x i - unitSeq n i‖ ≤ 1 / 3) ∧ Uop x = lam • x ∧
      ‖lam‖ = (3 : ℝ) ^ (-(slope n : ℤ)) := by
  obtain ⟨y, μ, -, -, hy, hyc, hμ, heq⟩ := exists_eigen_DC n hn
  refine ⟨bact ADB.A (wv n y), (ADB.D n : K) * μ, ?_, ?_, ?_, ?_⟩
  · exact isC0_bact ADB.A (fun i j h => A_eq_zero_of_gt h) norm_A_le_one (isC0_wv hyc)
  · intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · have h1 : bact ADB.A (wv n y) 0 = 0 := by simp [bact]
      have h2 : unitSeq n 0 = 0 := by simp only [unitSeq, ite_eq_right_iff]; omega
      rw [h1, h2, sub_zero, norm_zero]
      norm_num
    · have h1 := norm_bact_A_sub_le (wv n y) 1 (norm_wv_le_one hy) i hi
      have h3 : bact ADB.A (wv n y) i - unitSeq n i = (bact ADB.A (wv n y) i - wv n y i) + y i := by
        simp only [wv]
        ring
      rw [h3]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hy i))
      simpa using h1
  · show bact u (bact ADB.A (wv n y)) = _
    rw [bact_u_bact_A]
    funext i
    show ∑ j ∈ Finset.Icc 1 (3 * i), (ADB.A i j : K) * ((ADB.D j : K) * bact Cm (wv n y) j) =
      ((ADB.D n : K) * μ) * ∑ j ∈ Finset.Icc 1 (3 * i), (ADB.A i j : K) * wv n y j
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [heq j (Finset.mem_Icc.1 hj).1]
    ring
  · have hμ1 : ‖μ‖ = 1 := by
      have h1 : ‖(1 : K)‖ ≠ ‖μ - 1‖ := by
        rw [norm_one]
        exact (by linarith : ‖μ - 1‖ < 1).ne'
      calc ‖μ‖ = ‖1 + (μ - 1)‖ := by ring_nf
        _ = max ‖(1 : K)‖ ‖μ - 1‖ := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1
        _ = 1 := by rw [norm_one]; exact max_eq_left (by linarith)
    rw [norm_mul, norm_ratCast_K, CalegariSlopes.Newton.norm_D, hμ1, mul_one]

/-- Theorem 2.4 (a). -/
theorem exists_eigenFamily : Nonempty EigenFamily := by
  choose x lam hxc hxn hxe hxl using exists_eigvec
  classical
  refine ⟨{ x := fun n => if h : 1 ≤ n then x n h else unitSeq 0,
            lam := fun n => if h : 1 ≤ n then lam n h else 0,
            near := ⟨by norm_num, by norm_num, fun n => ?_, fun n i => ?_⟩,
            eig := fun n => ?_, lam_zero := by simp, norm_lam := fun n hn => ?_ }⟩
  · by_cases h : 1 ≤ n
    · simp only [h, ↓reduceDIte]
      exact hxc n h
    · simp only [h, ↓reduceDIte]
      exact isC0_unitSeq 0
  · by_cases h : 1 ≤ n
    · simp only [h, ↓reduceDIte]
      exact hxn n h i
    · have h0 : n = 0 := by omega
      subst h0
      simp only [h, ↓reduceDIte, sub_self, norm_zero]
      norm_num
  · by_cases h : 1 ≤ n
    · simp only [h, ↓reduceDIte]
      exact hxe n h
    · simp only [h, ↓reduceDIte, zero_smul]
      exact Uop_unitSeq_zero
  · simp only [hn, ↓reduceDIte]
    exact hxl n hn

end CalegariSlopes.Spectral
