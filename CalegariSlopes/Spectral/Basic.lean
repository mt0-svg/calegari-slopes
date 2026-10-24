/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Spectral.Defs
public import CalegariSlopes.ADB.Main
public import CalegariSlopes.Newton.Proofs

@[expose] public section

/-!
# The matrices `A`, `B`, `C = B A`, `D`, `u` on sequences (Sections 3 and 6.2)

`slope_strictMono` (Lemma 3.4), Lemma 6.2 (`Cm_eq_zero_of_lt`, `Cm_eq_zero_of_gt`, `norm_Cm_le`,
`norm_Cm_self_sub_one_le`) and Lemma 6.3 (`isC0_bact`, `norm_bact_A_sub_le`, `bact_u_bact_A`), with their helpers.
The inputs are Theorem 2.3 and the supports of Lemmas 3.1 and 3.2 (`CalegariSlopes.ADB.adb`, `B_eq_zero_of_gt`,
`u_eq_zero_of_gt`) and the bounds of Section 3 (`CalegariSlopes.Newton`).
-/

open PowerSeries Filter Topology
open CalegariSlopes.Overconvergent (K S0dag U3 genEig jinv jinvK)

namespace CalegariSlopes.Spectral

/-! ## Norms of rationals in `K` -/

/-- The norm of a rational in `K = ℂ_[3]` is its `3`-adic norm. -/
theorem norm_ratCast_K (q : ℚ) : ‖(q : K)‖ = ‖(q : ℚ_[3])‖ := by
  simpa using norm_algebraMap' K (q : ℚ_[3])

/-! ## Lemma 3.4 -/

/-- `slope (k + 1) ≥ slope k + 2`; used through strict monotonicity (`slope k = 2 k + wslope k`). -/
theorem slope_strictMono : StrictMono slope := by
  refine strictMono_nat_of_lt_succ ?_
  intro k
  have h_wslope_le : CalegariSlopes.Newton.wslope k ≤ CalegariSlopes.Newton.wslope (k + 1) :=
    CalegariSlopes.Newton.wslope_mono (Nat.le_succ k)
  calc
    slope k = 2 * k + CalegariSlopes.Newton.wslope k := rfl
    _ ≤ 2 * k + CalegariSlopes.Newton.wslope (k + 1) := by omega
    _ < 2 * k + 2 + CalegariSlopes.Newton.wslope (k + 1) := by omega
    _ = 2 * (k + 1) + CalegariSlopes.Newton.wslope (k + 1) := by ring
    _ = slope (k + 1) := rfl

/-! ## Supports and bounds of `A` and `u` -/

/-- `A_ij = 0` for `i > 3 j` (`A_ij = (j / i) B_ji`, `B_ji = 0` for `i > 3 j`). -/
theorem A_eq_zero_of_gt {i j : ℕ} (h : 3 * j < i) : ADB.A i j = 0 := by
  simp [ADB.A, ADB.B_eq_zero_of_gt j i h]

/-- `‖A_ij‖ ≤ 1` for all `i, j` (`A` is lower triangular with `v_3(A_ij) ≥ i - j`; `A_0j = A_i0 = 0`). -/
theorem norm_A_le_one (i j : ℕ) : ‖(ADB.A i j : ℚ_[3])‖ ≤ 1 := by
  by_cases hi : i = 0
  · subst hi
    have hA : ADB.A 0 j = (0 : ℚ) := by
      simp [ADB.A]
    simp [hA]
  · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi
    by_cases hj : j = 0
    · subst hj
      have hA : ADB.A i 0 = (0 : ℚ) := by
        simp [ADB.A]
      simp [hA]
    · have hj_pos : 0 < j := Nat.pos_of_ne_zero hj
      by_cases hlt : i < j
      · have hA : ADB.A i j = 0 := Newton.A_eq_zero_of_lt i j hlt
        simp [hA]
      · have hle : j ≤ i := Nat.le_of_not_gt hlt
        have hnorm := Newton.norm_A_le i j (Nat.one_le_of_lt hi_pos) (Nat.one_le_of_lt hj_pos)
        have hpos : (1 : ℝ) ≤ (3 : ℝ) := by norm_num
        have hnonpos : -((i : ℤ) - (j : ℤ)) ≤ (0 : ℤ) := by
          have hsub_nonneg : (0 : ℤ) ≤ (i : ℤ) - (j : ℤ) := sub_nonneg.mpr (by exact mod_cast hle)
          linarith
        have hzpow : (3 : ℝ) ^ (-((i : ℤ) - (j : ℤ))) ≤ (1 : ℝ) :=
          zpow_le_one_of_nonpos₀ hpos hnonpos
        linarith

/-- `‖A_ij‖ ≤ 1/3` for `j < i`. -/
theorem norm_A_le_third {i j : ℕ} (h : j < i) : ‖(ADB.A i j : ℚ_[3])‖ ≤ 1 / 3 := by
  by_cases hj0 : j = 0
  · -- j = 0 case: A i 0 = 0
    subst hj0
    have hA : ADB.A i 0 = 0 := by
      simp [ADB.A]
    simp [hA]
  · -- 1 ≤ j case
    have hj1 : 1 ≤ j := Nat.one_le_of_lt (Nat.pos_of_ne_zero hj0)
    have hi1 : 1 ≤ i := Nat.le_trans hj1 (Nat.le_of_lt h)
    have hle := CalegariSlopes.Newton.norm_A_le i j hi1 hj1
    -- hle : ‖(A i j : ℚ_[3])‖ ≤ (3 : ℝ) ^ (-((i : ℤ) - j))
    have h_exp : (-((i : ℤ) - j) : ℤ) ≤ (-1 : ℤ) := by
      have : (1 : ℤ) ≤ (i : ℤ) - (j : ℤ) := by
        have h' : (j : ℤ) < (i : ℤ) := by exact_mod_cast h
        omega
      omega
    have h_pow : (3 : ℝ) ^ (-((i : ℤ) - j)) ≤ (3 : ℝ) ^ (-1 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) h_exp
    calc
      ‖(ADB.A i j : ℚ_[3])‖ ≤ (3 : ℝ) ^ (-((i : ℤ) - j)) := hle
      _ ≤ (3 : ℝ) ^ (-1 : ℤ) := h_pow
      _ = 1 / 3 := by norm_num

/-- `u_ij = 0` for `j > 3 i`, `i ≥ 1`, from Theorem 2.3: `B_pj = 0` for `j > 3 p`, `p ≤ i`. -/
theorem u_eq_zero_of_lt {i j : ℕ} (hi : 1 ≤ i) (h : 3 * i < j) : u i j = 0 := by
  have hj : 1 ≤ j := by
    have h3i : 3 ≤ 3 * i := by
      nlinarith
    omega
  have hadb := ADB.adb i j hi hj
  have hsum : ∑ p ∈ Finset.Icc 1 (min i j), ADB.A i p * ADB.D p * ADB.B p j = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    rcases Finset.mem_Icc.mp hp with ⟨hp1, hp2⟩
    have hp_le_i : p ≤ i := by
      have : min i j ≤ i := min_le_left i j
      omega
    have h3p_lt_j : 3 * p < j := by
      omega
    have hB : ADB.B p j = 0 := ADB.B_eq_zero_of_gt p j h3p_lt_j
    simp [hB]
  rw [← hadb, hsum]

/-- `‖u_ij‖ ≤ 1`. -/
theorem norm_u_le_one (i j : ℕ) : ‖(u i j : ℚ_[3])‖ ≤ 1 := by
  have h := CalegariSlopes.Newton.norm_u_le i j
  have h_exp : -(((i : ℤ) + (j : ℤ))) ≤ (0 : ℤ) := by
    have hi : (0 : ℤ) ≤ i := Nat.cast_nonneg _
    have hj : (0 : ℤ) ≤ j := Nat.cast_nonneg _
    have hsum : (0 : ℤ) ≤ (i : ℤ) + (j : ℤ) := by nlinarith
    linarith
  have h_pow : (3 : ℝ) ^ (-(((i : ℤ) + (j : ℤ)) : ℤ)) ≤ (3 : ℝ) ^ (0 : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ (3 : ℝ)) h_exp
  have h_one : (3 : ℝ) ^ (0 : ℤ) = (1 : ℝ) := by norm_num
  rw [h_one] at h_pow
  exact le_trans h h_pow

/-! ## Lemma 6.2: the matrix `C = B A` -/

/-- `C_ij = 0` for `j > 3 i`. -/
theorem Cm_eq_zero_of_lt {i j : ℕ} (h : 3 * i < j) : Cm i j = 0 := by
  dsimp [Cm]
  refine Finset.sum_eq_zero ?_
  intro k hk
  have hk_le : k ≤ 3 * i := (Finset.mem_Icc.mp hk).right
  have hk_lt_j : k < j := by omega
  rw [CalegariSlopes.Newton.A_eq_zero_of_lt k j hk_lt_j]
  simp

/-- `C_ij = 0` for `i > 3 j`. -/
theorem Cm_eq_zero_of_gt {i j : ℕ} (h : 3 * j < i) : Cm i j = 0 := by
  dsimp [Cm]
  refine Finset.sum_eq_zero ?_
  intro k hk
  rcases Finset.mem_Icc.mp hk with ⟨hk1, hk2⟩
  by_cases hki : k < i
  · have hB : ADB.B i k = 0 := CalegariSlopes.Newton.B_eq_zero_of_lt i k hki
    simp [hB]
  · have hik : i ≤ k := Nat.le_of_not_lt hki
    have h3jk : 3 * j < k := lt_of_lt_of_le h hik
    have hA : ADB.A k j = 0 := A_eq_zero_of_gt h3jk
    simp [hA]

/-- `v_3(B_ik A_kj) ≥ 2 k - i - j` for `k ≥ max(i, j)`, `i, j ≥ 1`. -/
theorem norm_B_mul_A_le (i j k : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hik : i ≤ k) (hjk : j ≤ k) :
    ‖((ADB.B i k * ADB.A k j : ℚ) : ℚ_[3])‖ ≤ (3 : ℝ) ^ (-((2 * k : ℤ) - i - j)) := by
  have hk : 1 ≤ k := Nat.le_trans hj hjk
  calc
    ‖((ADB.B i k * ADB.A k j : ℚ) : ℚ_[3])‖ = ‖(ADB.B i k : ℚ_[3]) * (ADB.A k j : ℚ_[3])‖ := by simp
    _ = ‖(ADB.B i k : ℚ_[3])‖ * ‖(ADB.A k j : ℚ_[3])‖ := by rw [norm_mul]
    _ ≤ (3 : ℝ) ^ (-((k : ℤ) - i)) * (3 : ℝ) ^ (-((k : ℤ) - j)) := by
      have hB := Newton.norm_B_le i k hi
      have hA := Newton.norm_A_le k j hk hj
      have hnonnegA : 0 ≤ ‖(ADB.A k j : ℚ_[3])‖ := norm_nonneg _
      have hnonneg3B : 0 ≤ (3 : ℝ) ^ (-((k : ℤ) - i)) := zpow_nonneg (by norm_num) _
      exact mul_le_mul hB hA hnonnegA hnonneg3B
    _ = (3 : ℝ) ^ ((-((k : ℤ) - i)) + (-((k : ℤ) - j))) := by
      rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0) (-((k : ℤ) - i)) (-((k : ℤ) - j))]
    _ = (3 : ℝ) ^ (-((2 * k : ℤ) - i - j)) := by ring_nf

/-- `v_3(C_ij) ≥ |i - j|`. -/
theorem norm_Cm_le (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    ‖(Cm i j : ℚ_[3])‖ ≤ (3 : ℝ) ^ (-|(i : ℤ) - j|) := by
  -- Push the cast inside the sum
  have hsum : (Cm i j : ℚ_[3]) = ∑ k ∈ Finset.Icc 1 (3 * i), ((ADB.B i k * ADB.A k j : ℚ) : ℚ_[3]) := by
    simp [Cm]
  rw [hsum]
  -- Use the ultrametric property: the norm of a sum is bounded by the max of the norms
  have h_nonneg : 0 ≤ (3 : ℝ) ^ (-|(i : ℤ) - j|) :=
    zpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h_nonneg ?_
  intro k hk
  rcases Finset.mem_Icc.mp hk with ⟨hk1, hk2⟩
  by_cases hki : k < i
  · -- If k < i, then B i k = 0
    have hB : ADB.B i k = 0 := CalegariSlopes.Newton.B_eq_zero_of_lt i k hki
    rw [hB, zero_mul]
    have hleft : ‖((0 : ℚ) : ℚ_[3])‖ = (0 : ℝ) := by simp
    rw [hleft]
    exact h_nonneg
  · -- Otherwise i ≤ k
    have hik : i ≤ k := Nat.le_of_not_lt hki
    by_cases hkj : k < j
    · -- If k < j, then A k j = 0
      have hA : ADB.A k j = 0 := CalegariSlopes.Newton.A_eq_zero_of_lt k j hkj
      rw [hA, mul_zero]
      have hleft : ‖((0 : ℚ) : ℚ_[3])‖ = (0 : ℝ) := by simp
      rw [hleft]
      exact h_nonneg
    · -- Otherwise j ≤ k
      have hjk : j ≤ k := Nat.le_of_not_lt hkj
      -- Use the bound for B * A
      have hbound := norm_B_mul_A_le i j k hi hj hik hjk
      -- hbound : ‖((ADB.B i k * ADB.A k j : ℚ) : ℚ_[3])‖ ≤ (3 : ℝ) ^ (-((2 * k : ℤ) - i - j))
      -- Now we need to relate this to (3 : ℝ) ^ (-|(i : ℤ) - j|)
      -- Since 1 ≤ 3, zpow is monotone in the exponent
      have h3pos : (1 : ℝ) ≤ (3 : ℝ) := by norm_num
      have hexp : -((2 * (k : ℤ)) - (i : ℤ) - (j : ℤ)) ≤ -|(i : ℤ) - (j : ℤ)| := by
        have h_abs : |(i : ℤ) - (j : ℤ)| ≤ 2 * (k : ℤ) - (i : ℤ) - (j : ℤ) := by
          have hik' : (i : ℤ) ≤ (k : ℤ) := by exact_mod_cast hik
          have hjk' : (j : ℤ) ≤ (k : ℤ) := by exact_mod_cast hjk
          by_cases hij : (i : ℤ) ≤ (j : ℤ)
          · -- Then |i - j| = -(i - j) = j - i
            have habs : |(i : ℤ) - (j : ℤ)| = -((i : ℤ) - (j : ℤ)) := abs_of_nonpos (sub_nonpos.mpr hij)
            rw [habs]
            omega
          · -- Then j < i, so |i - j| = i - j
            have hji : (j : ℤ) ≤ (i : ℤ) := by omega
            have habs : |(i : ℤ) - (j : ℤ)| = (i : ℤ) - (j : ℤ) := abs_of_nonneg (sub_nonneg.mpr hji)
            rw [habs]
            omega
        omega
      have h_pow : (3 : ℝ) ^ (-((2 * (k : ℤ)) - (i : ℤ) - (j : ℤ))) ≤ (3 : ℝ) ^ (-|(i : ℤ) - (j : ℤ)|) :=
        zpow_le_zpow_right₀ h3pos hexp
      exact le_trans hbound h_pow

/-- `v_3(C_ii - 1) ≥ 2`. -/
theorem norm_Cm_self_sub_one_le (i : ℕ) (hi : 1 ≤ i) :
    ‖((Cm i i - 1 : ℚ) : ℚ_[3])‖ ≤ (3 : ℝ) ^ (-2 : ℤ) := by
  have hi3 : i ≤ 3 * i := by
    nlinarith
  have mem : i ∈ Finset.Icc 1 (3 * i) :=
    Finset.mem_Icc.mpr ⟨hi, hi3⟩
  have hCm_eq : (Cm i i : ℚ) = (ADB.B i i * ADB.A i i : ℚ) +
      ∑ k ∈ (Finset.Icc 1 (3 * i)).erase i, (ADB.B i k * ADB.A k i : ℚ) := by
    dsimp [Cm]
    rw [Finset.add_sum_erase (Finset.Icc 1 (3 * i))
      (fun k => (ADB.B i k * ADB.A k i : ℚ)) mem]
  have hBself : ADB.B i i = 1 :=
    CalegariSlopes.Newton.B_self i hi
  have hAself : ADB.A i i = 1 :=
    CalegariSlopes.Newton.A_self i hi
  have hBA_one : (ADB.B i i * ADB.A i i : ℚ) = 1 := by
    rw [hBself, hAself]
    norm_num
  have hCm_sub_one : ((Cm i i - 1 : ℚ) : ℚ_[3]) =
      (∑ k ∈ (Finset.Icc 1 (3 * i)).erase i, ((ADB.B i k * ADB.A k i : ℚ) : ℚ_[3])) := by
    push_cast
    rw [hCm_eq, hBA_one]
    simp
  rw [hCm_sub_one]
  -- Now bound the sum using the ultrametric property
  have h_nonneg : 0 ≤ (3 : ℝ) ^ (-2 : ℤ) := by
    positivity
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h_nonneg ?_
  intro k hk
  have hk_mem : k ∈ Finset.Icc 1 (3 * i) :=
    Finset.mem_of_mem_erase hk
  rcases Finset.mem_Icc.mp hk_mem with ⟨hk1, hk2⟩
  by_cases hki : k < i
  · -- k < i: B i k = 0
    have hBzero : ADB.B i k = 0 :=
      CalegariSlopes.Newton.B_eq_zero_of_lt i k hki
    simp [hBzero]
  · -- k ≥ i, and since k ≠ i (from erase), we have i < k
    have hik : i ≤ k := by omega
    have hki_ne : k ≠ i := Finset.ne_of_mem_erase hk
    have hik_lt : i < k := by
      by_contra! H
      have : k ≤ i := H
      have : k = i := by omega
      exact hki_ne this
    have hbound : ‖((ADB.B i k * ADB.A k i : ℚ) : ℚ_[3])‖ ≤ (3 : ℝ) ^ (-((2 * k : ℤ) - i - i)) :=
      CalegariSlopes.Spectral.norm_B_mul_A_le i i k hi hi hik hik
    -- Need to show: (3 : ℝ) ^ (-((2 * k : ℤ) - i - i)) ≤ (3 : ℝ) ^ (-2 : ℤ)
    -- Since k > i, we have k - i ≥ 1, so 2k - 2i ≥ 2, so -(2k-2i) ≤ -2
    have h_exp_le : (-((2 * k : ℤ) - i - i) : ℤ) ≤ (-2 : ℤ) := by
      have : (i : ℤ) + i ≤ 2 * (k : ℤ) := by
        have hk' : (i : ℤ) ≤ k := by exact_mod_cast hik
        linarith
      omega
    have h_rpow_le : (3 : ℝ) ^ (-((2 * k : ℤ) - i - i)) ≤ (3 : ℝ) ^ (-2 : ℤ) := by
      have h_base : 1 ≤ (3 : ℝ) := by norm_num
      exact zpow_le_zpow_right₀ h_base h_exp_le
    exact le_trans hbound h_rpow_le

/-- `‖C_ij‖ ≤ 1` for all `i, j`. -/
theorem norm_Cm_le_one (i j : ℕ) : ‖(Cm i j : ℚ_[3])‖ ≤ 1 := by
  by_cases hi0 : i = 0
  · subst hi0
    have : Cm 0 j = 0 := by
      dsimp [Cm]
      simp
    simp [this]
  · by_cases hj0 : j = 0
    · subst hj0
      have : Cm i 0 = 0 := by
        dsimp [Cm, ADB.A]
        simp
      simp [this]
    · have hi : 1 ≤ i := Nat.one_le_of_lt (Nat.pos_of_ne_zero hi0)
      have hj : 1 ≤ j := Nat.one_le_of_lt (Nat.pos_of_ne_zero hj0)
      have hle := norm_Cm_le i j hi hj
      refine le_trans hle ?_
      have h_abs_nonneg : 0 ≤ |(i : ℤ) - j| := abs_nonneg _
      have h_exp_nonpos : (-|(i : ℤ) - j| : ℤ) ≤ (0 : ℤ) := by
        linarith
      have h_pow_le_one : (3 : ℝ) ^ (-|(i : ℤ) - j|) ≤ 1 :=
        zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ (3 : ℝ)) h_exp_nonpos
      exact h_pow_le_one

/-- `‖C_ij‖ ≤ 1/3` for `i ≠ j`. -/
theorem norm_Cm_le_third {i j : ℕ} (h : i ≠ j) : ‖(Cm i j : ℚ_[3])‖ ≤ 1 / 3 := by
  by_cases hi : i = 0
  · subst hi
    have hCm : Cm 0 j = 0 := by
      simp [Cm]
    simp [hCm]
  · by_cases hj : j = 0
    · subst hj
      have hCm : Cm i 0 = 0 := by
        simp [Cm, ADB.A]
      simp [hCm]
    · have hi' : 1 ≤ i := Nat.one_le_of_lt (Nat.pos_of_ne_zero hi)
      have hj' : 1 ≤ j := Nat.one_le_of_lt (Nat.pos_of_ne_zero hj)
      have hle := norm_Cm_le i j hi' hj'
      have habs : (1 : ℤ) ≤ |(i : ℤ) - (j : ℤ)| :=
        Int.one_le_abs (sub_ne_zero.mpr (by exact_mod_cast h))
      have hpow : (3 : ℝ) ^ (-|(i : ℤ) - (j : ℤ)|) ≤ (3 : ℝ) ^ (-1 : ℤ) := by
        have h_exp : (-(|(i : ℤ) - (j : ℤ)| : ℤ)) ≤ (-1 : ℤ) := by
          omega
        have h3 : (1 : ℝ) < (3 : ℝ) := by norm_num
        exact ((zpow_le_zpow_iff_right₀ h3).mpr h_exp)
      calc
        ‖(Cm i j : ℚ_[3])‖ ≤ (3 : ℝ) ^ (-|(i : ℤ) - (j : ℤ)|) := hle
        _ ≤ (3 : ℝ) ^ (-1 : ℤ) := hpow
        _ = 1/3 := by norm_num

/-- `C_ii` is a unit: `‖C_ii‖ = 1` for `i ≥ 1`. -/
theorem norm_Cm_self (i : ℕ) (hi : 1 ≤ i) : ‖(Cm i i : ℚ_[3])‖ = 1 := by
  have hsub := norm_Cm_self_sub_one_le i hi
  -- hsub : ‖((Cm i i - 1 : ℚ) : ℚ_[3])‖ ≤ (3 : ℝ) ^ (-2 : ℤ)
  have hlt : (3 : ℝ) ^ (-2 : ℤ) < 1 := by
    norm_num
  have h_norm_sub_lt_one : ‖((Cm i i - 1 : ℚ) : ℚ_[3])‖ < 1 :=
    lt_of_le_of_lt hsub hlt
  have h_norm_one : ‖(1 : ℚ_[3])‖ = 1 := by simp
  have h_ne : ‖(1 : ℚ_[3])‖ ≠ ‖((Cm i i - 1 : ℚ) : ℚ_[3])‖ := by
    rw [h_norm_one]
    exact ne_of_gt h_norm_sub_lt_one
  have h_add : ‖(1 : ℚ_[3]) + ((Cm i i - 1 : ℚ) : ℚ_[3])‖ = max ‖(1 : ℚ_[3])‖ ‖((Cm i i - 1 : ℚ) : ℚ_[3])‖ :=
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_ne
  have h_sum_eq : (1 : ℚ_[3]) + ((Cm i i - 1 : ℚ) : ℚ_[3]) = (Cm i i : ℚ_[3]) := by
    push_cast
    ring
  rw [h_sum_eq] at h_add
  rw [h_add, h_norm_one]
  have h_max : max (1 : ℝ) ‖((Cm i i - 1 : ℚ) : ℚ_[3])‖ = 1 :=
    max_eq_left (by linarith)
  rw [h_max]

/-! ## Lemma 6.3 -/

/-- A matrix with `M_ij = 0` for `i > 3 j` and entries of norm `≤ 1` maps `c₀` into `c₀` (`A`, `C`, `u`). -/
theorem isC0_bact (M : ℕ → ℕ → ℚ) (hband : ∀ i j, 3 * j < i → M i j = 0)
    (hM : ∀ i j, ‖(M i j : ℚ_[3])‖ ≤ 1) {a : ℕ → K} (ha : IsC0 a) : IsC0 (bact M a) := by
  have ha_norm : Tendsto (fun n => ‖a n‖) atTop (𝓝 (0 : ℝ)) :=
    ((tendsto_zero_iff_norm_tendsto_zero (f := a) (a := atTop)).mp ha)
  rcases (Metric.tendsto_atTop (a := 0)).mp ha_norm with ha_metric
  -- Goal: IsC0 (bact M a), i.e., Tendsto (bact M a) atTop (𝓝 0)
  -- Use Metric.tendsto_atTop.mpr
  apply (Metric.tendsto_atTop (a := 0)).mpr
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  rcases ha_metric (ε / 2) hε2 with ⟨J, hJ⟩
  refine ⟨3 * J, ?_⟩
  intro i hi
  have hbound : ∀ j, j ∈ Finset.Icc 1 (3 * i) → ‖(M i j : K) * a j‖ ≤ ε / 2 := by
    intro j hj
    rcases Finset.mem_Icc.mp hj with ⟨hj1, hj2⟩
    by_cases h : 3 * j < i
    · -- M i j = 0 by hband
      have hMzero : M i j = 0 := hband i j h
      simp [hMzero, hε2.le]
    · -- then i ≤ 3*j, so j ≥ J
      have hji : i ≤ 3 * j := by omega
      have hJj : J ≤ j := by
        have : 3 * J ≤ 3 * j := by omega
        omega
      have ha_j : ‖a j‖ < ε / 2 := by
        have := hJ j hJj
        simpa [dist_eq_norm, Real.norm_of_nonneg (norm_nonneg _)] using this
      have hnormM : ‖(M i j : K)‖ ≤ 1 := by
        have h := hM i j
        have hnorm : ‖(M i j : K)‖ = ‖(M i j : ℚ_[3])‖ := by
          calc
            ‖(M i j : K)‖ = ‖(((M i j : ℚ_[3]) : PadicAlgCl 3) : K)‖ := by
              have h_eq : (M i j : K) = (((M i j : ℚ_[3]) : PadicAlgCl 3) : K) := by
                calc
                  (M i j : K) = (algebraMap ℚ K) (M i j) := rfl
                  _ = (algebraMap (PadicAlgCl 3) K) ((algebraMap ℚ (PadicAlgCl 3)) (M i j)) := by
                    simpa [K] using (IsScalarTower.algebraMap_apply ℚ (PadicAlgCl 3) K (M i j))
                  _ = (algebraMap (PadicAlgCl 3) K) ((algebraMap ℚ_[3] (PadicAlgCl 3)) ((algebraMap ℚ ℚ_[3]) (M i j))) := by
                    simp
                  _ = (((M i j : ℚ_[3]) : PadicAlgCl 3) : K) := rfl
              rw [h_eq]
            _ = ‖((M i j : ℚ_[3]) : PadicAlgCl 3)‖ := by
              simpa [K] using (PadicComplex.norm_extends (3 : ℕ) ((M i j : ℚ_[3]) : PadicAlgCl 3))
            _ = ‖(M i j : ℚ_[3])‖ := by
              simpa using (PadicComplex.norm_extends' (3 : ℕ) (M i j : ℚ_[3]))
        rw [hnorm]
        exact h
      calc
        ‖(M i j : K) * a j‖ = ‖(M i j : K)‖ * ‖a j‖ := norm_mul _ _
        _ ≤ 1 * (ε / 2) := mul_le_mul hnormM (le_of_lt ha_j) (norm_nonneg _) (by linarith)
        _ = ε / 2 := by simp
  -- Now use the ultrametric inequality
  rw [bact]
  have hsum : ‖∑ j ∈ Finset.Icc 1 (3 * i), (M i j : K) * a j‖ ≤ ε / 2 :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by linarith) hbound
  -- Goal is: dist (∑ j ∈ Finset.Icc 1 (3 * i), (M i j : K) * a j) 0 < ε
  -- We have ‖sum‖ ≤ ε/2 < ε, and dist x 0 = ‖x‖
  simpa [dist_eq_norm] using (hsum.trans_lt (by linarith))

/-- Lemma 6.3, first part: `‖A w - w‖ ≤ ‖w‖ / 3` (coordinates `k ≥ 1`). -/
theorem norm_bact_A_sub_le (w : ℕ → K) (r : ℝ) (hw : ∀ j, ‖w j‖ ≤ r) (k : ℕ) (hk : 1 ≤ k) :
    ‖bact ADB.A w k - w k‖ ≤ r / 3 := by
  have hr_nonneg : 0 ≤ r := by
    have h0 := hw 0
    have hnorm0 : 0 ≤ ‖w 0‖ := norm_nonneg _
    linarith
  have hk_mem : k ∈ Finset.Icc 1 (3 * k) := by
    refine Finset.mem_Icc.mpr ?_
    have hk_le : k ≤ 3 * k := by
      nlinarith
    exact ⟨hk, hk_le⟩
  have hsum_erase : bact ADB.A w k - w k =
      ∑ j ∈ (Finset.Icc 1 (3 * k)).erase k, (ADB.A k j : K) * w j := by
    have hAkk : (ADB.A k k : K) = 1 := by
      exact_mod_cast Newton.A_self k hk
    calc
      bact ADB.A w k - w k = (∑ j ∈ Finset.Icc 1 (3 * k), (ADB.A k j : K) * w j) - w k := rfl
      _ = (∑ j ∈ Finset.Icc 1 (3 * k), (ADB.A k j : K) * w j) - ((1 : K) * w k) := by
        simp
      _ = (∑ j ∈ Finset.Icc 1 (3 * k), (ADB.A k j : K) * w j) - (ADB.A k k : K) * w k := by
        simp [hAkk]
      _ = ∑ j ∈ (Finset.Icc 1 (3 * k)).erase k, (ADB.A k j : K) * w j := by
        have h := Finset.add_sum_erase (Finset.Icc 1 (3 * k))
          (fun j => (ADB.A k j : K) * w j) hk_mem
        calc
          (∑ j ∈ Finset.Icc 1 (3 * k), (ADB.A k j : K) * w j) - (ADB.A k k : K) * w k =
              ((ADB.A k k : K) * w k + ∑ j ∈ (Finset.Icc 1 (3 * k)).erase k, (ADB.A k j : K) * w j) -
                (ADB.A k k : K) * w k := by rw [h]
          _ = ∑ j ∈ (Finset.Icc 1 (3 * k)).erase k, (ADB.A k j : K) * w j := by ring
  rw [hsum_erase]
  have h_nonneg : 0 ≤ r / 3 := by
    nlinarith
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h_nonneg ?_
  intro j hj
  have hj_mem : j ∈ Finset.Icc 1 (3 * k) := Finset.mem_of_mem_erase hj
  rcases Finset.mem_Icc.mp hj_mem with ⟨hj1, hj2⟩
  by_cases hjk : j < k
  · -- j < k case
    have hA_norm : ‖(ADB.A k j : K)‖ ≤ (1 : ℝ) / 3 := by
      have := norm_A_le_third hjk
      have h_eq : ‖(ADB.A k j : K)‖ = ‖(ADB.A k j : ℚ_[3])‖ := norm_ratCast_K _
      rw [h_eq]
      exact this
    have hw_norm : ‖w j‖ ≤ r := hw j
    calc
      ‖(ADB.A k j : K) * w j‖ = ‖(ADB.A k j : K)‖ * ‖w j‖ := norm_mul _ _
      _ ≤ (1 / 3) * r := by gcongr
      _ = r / 3 := by ring
  · -- j ≥ k case, but j ≠ k since j ∈ erase
    have hkj : k ≤ j := by
      omega
    have hkj_ne : j ≠ k := (Finset.mem_erase.mp hj).1
    -- k < j case: A k j = 0
    have hkj_lt : k < j := by
      omega
    have hA_zero : ADB.A k j = 0 := Newton.A_eq_zero_of_lt k j hkj_lt
    have : ‖(ADB.A k j : K) * w j‖ = 0 := by
      simp [hA_zero]
    rw [this]
    exact h_nonneg

/-- `U A = A D C` entrywise, from Theorem 2.3: for `i, m ≥ 1`,
`Σ_{1 ≤ j ≤ 3i} u_ij A_jm = Σ_{1 ≤ p ≤ 3i} A_ip D_p C_pm`. -/
theorem UA_entry (i m : ℕ) (hi : 1 ≤ i) (hm : 1 ≤ m) :
    ∑ j ∈ Finset.Icc 1 (3 * i), u i j * ADB.A j m =
      ∑ p ∈ Finset.Icc 1 (3 * i), ADB.A i p * ADB.D p * Cm p m := by
  have hL : ∀ j ∈ Finset.Icc 1 (3 * i), u i j * ADB.A j m =
      ∑ p ∈ Finset.Icc 1 (3 * i), ADB.A i p * ADB.D p * ADB.B p j * ADB.A j m := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
    rw [← ADB.adb i j hi hj1, Finset.sum_mul]
    apply Finset.sum_subset
    · intro p hp
      simp only [Finset.mem_Icc] at hp ⊢
      have := min_le_left i j
      omega
    · intro p hp hp'
      simp only [Finset.mem_Icc, not_and, not_le] at hp hp'
      rcases lt_or_ge i p with h | h
      · rw [Newton.A_eq_zero_of_lt i p h]; ring
      · have h2 := hp' hp.1
        have : j < p := by
          rcases le_total i j with hij | hij
          · rw [min_eq_left hij] at h2; omega
          · rw [min_eq_right hij] at h2; omega
        rw [Newton.B_eq_zero_of_lt p j this]; ring
  rw [Finset.sum_congr rfl hL, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  rcases lt_or_ge i p with h | h
  · simp [Newton.A_eq_zero_of_lt i p h]
  · rw [Cm, Finset.mul_sum]
    symm
    rw [Finset.sum_subset (s₁ := Finset.Icc 1 (3 * p)) (s₂ := Finset.Icc 1 (3 * i))]
    · exact Finset.sum_congr rfl fun k _ => by ring
    · intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    · intro k hk hk'
      simp only [Finset.mem_Icc, not_and, not_le] at hk hk'
      rw [ADB.B_eq_zero_of_gt p k (hk' hk.1)]; ring

/-- Lemma 6.3, second part: `U (A w) = A (D (C w))` for every sequence `w`, from Theorem 2.3. -/
theorem bact_u_bact_A (w : ℕ → K) :
    bact u (bact ADB.A w) = bact ADB.A (fun p => (ADB.D p : K) * bact Cm w p) := by
  funext i
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [bact]
  have hL : bact u (bact ADB.A w) i = ∑ j ∈ Finset.Icc 1 (3 * i), ∑ m ∈ Finset.Icc 1 (9 * i),
      (u i j : K) * (ADB.A j m : K) * w m := by
    simp only [bact, Finset.mul_sum, ← mul_assoc]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_Icc] at hj
    apply Finset.sum_subset
    · intro m hm
      simp only [Finset.mem_Icc] at hm ⊢
      omega
    · intro m hm hm'
      simp only [Finset.mem_Icc, not_and, not_le] at hm hm'
      rw [Newton.A_eq_zero_of_lt j m (by have := hm' hm.1; omega)]
      simp
  have hR : bact ADB.A (fun p => (ADB.D p : K) * bact Cm w p) i =
      ∑ p ∈ Finset.Icc 1 (3 * i), ∑ m ∈ Finset.Icc 1 (9 * i),
        (ADB.A i p : K) * (ADB.D p : K) * (Cm p m : K) * w m := by
    simp only [bact, Finset.mul_sum, ← mul_assoc]
    refine Finset.sum_congr rfl fun p hp => ?_
    simp only [Finset.mem_Icc] at hp
    apply Finset.sum_subset
    · intro m hm
      simp only [Finset.mem_Icc] at hm ⊢
      omega
    · intro m hm hm'
      simp only [Finset.mem_Icc, not_and, not_le] at hm hm'
      rw [Cm_eq_zero_of_lt (hm' hm.1)]
      simp
  rw [hL, hR]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  congr 1
  have h := congrArg (fun q : ℚ => (q : K)) (UA_entry i m hi (Finset.mem_Icc.1 hm).1)
  push_cast at h
  exact h

end CalegariSlopes.Spectral
