/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Conj5.SeqK

@[expose] public section

/-!
# The contraction for a `K`-matrix close to the identity

Proposition 6.4, proved for `C = B A` and the factor `1/3` in `CalegariSlopes.Spectral.Contraction`, here for any
`K`-matrix `M` with off-diagonal entries of norm `≤ c < 1` and unit diagonal entries congruent to `1` (`CHyp M c`):
the paper's proof of Corollary 8.3 runs it for `C^(r)_ij = γ ^ (j - i) C_ij` with `c = 3 ^ (-ε)`.

For `n ≥ 1` and `y` in the ball `Y = {y ∈ c₀ : y_0 = y_n = 0, ‖y‖ ≤ c}`, with `w = e_n + y`: `μ(y) = (M w)_n` (the
paper's `ξ(y)`), `s_i(y) = (M° w)_i` (`M°` the off-diagonal part of `M`; the paper's `η_i(y)`),
`δ_i(y) = D_n μ(y) - D_i M_ii` (the paper's `Δ_i(y)`), and `T(y)_i = D_i s_i(y) / δ_i(y)` for `i ∉ {0, n}`,
`T(y)_0 = T(y)_n = 0`. Then `T(Y) ⊆ Y` and `T` contracts by `c`; its fixed point gives `D (M w) = D_n μ w`.
-/

open Filter Topology
open CalegariSlopes.Overconvergent (K)
open CalegariSlopes.Spectral

namespace CalegariSlopes.Conj5

/-- The hypotheses on the matrix of the contraction: off-diagonal entries of norm `≤ c` with `0 ≤ c < 1`, diagonal
entries with `‖M_ii - 1‖ < 1`, on the rows `i ≥ 1`, and `M_ij = 0` for `i > 3 j`. -/
structure CHyp (M : ℕ → ℕ → K) (c : ℝ) : Prop where
  nonneg : 0 ≤ c
  lt_one : c < 1
  off : ∀ i j, 1 ≤ i → i ≠ j → ‖M i j‖ ≤ c
  diag : ∀ i, 1 ≤ i → ‖M i i - 1‖ < 1
  band : ∀ i j, 3 * j < i → M i j = 0

/-- `M°`, the off-diagonal part of `M`. -/
noncomputable def offd (M : ℕ → ℕ → K) (i j : ℕ) : K := if i = j then 0 else M i j

/-- `μ(y) = (M w)_n`, `w = e_n + y`. -/
noncomputable def gmu (M : ℕ → ℕ → K) (n : ℕ) (y : ℕ → K) : K := kact M (wv n y) n

/-- `s_i(y) = (M° w)_i`. -/
noncomputable def gs (M : ℕ → ℕ → K) (n : ℕ) (y : ℕ → K) (i : ℕ) : K := kact (offd M) (wv n y) i

/-- `δ_i(y) = D_n μ(y) - D_i M_ii`. -/
noncomputable def gdelta (M : ℕ → ℕ → K) (n : ℕ) (y : ℕ → K) (i : ℕ) : K :=
  (ADB.D n : K) * gmu M n y - (ADB.D i : K) * M i i

/-- `T(y)_i = D_i s_i(y) / δ_i(y)` for `i ∉ {0, n}`, and `0` at `i = 0` and `i = n`. -/
noncomputable def gT (M : ℕ → ℕ → K) (n : ℕ) (y : ℕ → K) (i : ℕ) : K :=
  if i = 0 ∨ i = n then 0 else (ADB.D i : K) * gs M n y i / gdelta M n y i

/-! ## Elementary facts -/

/-- `‖w_j‖ ≤ 1` for `w = e_n + y`, `‖y‖ ≤ c ≤ 1`. -/
theorem norm_wv_le_one_of {c : ℝ} (hc : c ≤ 1) {n : ℕ} {y : ℕ → K} (hy : ∀ j, ‖y j‖ ≤ c) (j : ℕ) :
    ‖wv n y j‖ ≤ 1 := by
  dsimp [wv]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
  refine max_le ?_ ?_
  · unfold unitSeq; split_ifs <;> simp
  · have h := hy j
    linarith

/-- `‖M_ii‖ = 1` on the rows `i ≥ 1`. -/
theorem CHyp.norm_diag {M : ℕ → ℕ → K} {c : ℝ} (h : CHyp M c) {i : ℕ} (hi : 1 ≤ i) : ‖M i i‖ = 1 := by
  have hd := h.diag i hi
  have hneq : ‖M i i - 1‖ ≠ ‖(1 : K)‖ := by
    rw [norm_one]
    linarith
  have hsum : M i i = (M i i - 1) + 1 := by ring
  rw [hsum]
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hneq]
  rw [norm_one]
  rw [max_eq_right (le_of_lt hd)]

/-- `‖M_ij‖ ≤ 1` on the rows `i ≥ 1`. -/
theorem CHyp.norm_le_one {M : ℕ → ℕ → K} {c : ℝ} (h : CHyp M c) {i : ℕ} (hi : 1 ≤ i) (j : ℕ) :
    ‖M i j‖ ≤ 1 := by
  by_cases hji : j = i
  · rw [hji]
    have h_eq : ‖M i i‖ = 1 := h.norm_diag hi
    linarith
  · have h_le_c : ‖M i j‖ ≤ c := h.off i j hi (Ne.symm hji)
    have hc_le_one : c ≤ 1 := h.lt_one.le
    linarith

/-- `‖M°_ij‖ ≤ c` for every `i, j` (the row `0` does not enter `kact`). -/
theorem CHyp.norm_offd_le {M : ℕ → ℕ → K} {c : ℝ} (h : CHyp M c) {i : ℕ} (hi : 1 ≤ i) (j : ℕ) :
    ‖offd M i j‖ ≤ c := by
  unfold offd
  by_cases h_eq : i = j
  · -- i = j: offd M i j = 0, and ‖0‖ = 0 ≤ c
    simp [h_eq, h.nonneg]
  · -- i ≠ j: offd M i j = M i j, and h.off i j hi h_eq gives ‖M i j‖ ≤ c
    simpa [h_eq] using h.off i j hi h_eq

/-- `(M w)_i = M_ii w_i + (M° w)_i` for `i ≥ 1`. -/
theorem kact_eq_diag_add_offd (M : ℕ → ℕ → K) (w : ℕ → K) {i : ℕ} (hi : 1 ≤ i) :
    kact M w i = M i i * w i + kact (offd M) w i := by
  have hi_mem : i ∈ Finset.Icc 1 (3 * i) := by
    refine Finset.mem_Icc.mpr ⟨hi, ?_⟩
    nlinarith
  have hcoff_sum : kact (offd M) w i = ∑ j ∈ (Finset.Icc 1 (3 * i)).erase i, (offd M i j) * w j := by
    rw [kact, ← Finset.add_sum_erase _ _ hi_mem]
    simp [offd]
  calc
    kact M w i = ∑ j ∈ Finset.Icc 1 (3 * i), M i j * w j := rfl
    _ = (M i i) * w i + ∑ j ∈ (Finset.Icc 1 (3 * i)).erase i, M i j * w j := by
      rw [← Finset.add_sum_erase _ _ hi_mem]
    _ = (M i i) * w i + ∑ j ∈ (Finset.Icc 1 (3 * i)).erase i, (offd M i j) * w j := by
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj_ne : j ≠ i := (Finset.mem_erase.mp hj).left
      by_cases h : i = j
      · exfalso; exact hj_ne h.symm
      · simp [offd, h]
    _ = (M i i) * w i + kact (offd M) w i := by rw [hcoff_sum]

/-! ## (V1) to (V3) -/

/-- (V1) `‖μ(y) - 1‖ < 1`. -/
theorem CHyp.norm_gmu_sub_one_lt {M : ℕ → ℕ → K} {c : ℝ} (h : CHyp M c) {n : ℕ} (hn : 1 ≤ n) {y : ℕ → K}
    (hy : ∀ j, ‖y j‖ ≤ c) (hyn : y n = 0) : ‖gmu M n y - 1‖ < 1 := by
  have hc_nonneg : 0 ≤ c := h.nonneg
  have hc_lt_one : c < 1 := h.lt_one
  have h_c_sq_lt_one : c * c < 1 := by
    nlinarith
  have hwv_n : wv n y n = 1 := by
    dsimp [wv, unitSeq]
    simp [hyn]
  have h_gmu_eq : gmu M n y = M n n + kact (offd M) (wv n y) n := by
    rw [gmu, kact_eq_diag_add_offd M (wv n y) hn, hwv_n, mul_one]
  have h_sub : gmu M n y - 1 = (M n n - 1) + kact (offd M) (wv n y) n := by
    rw [h_gmu_eq]
    abel
  rw [h_sub]
  have h_diag_lt : ‖M n n - 1‖ < 1 := h.diag n hn
  have h_nonneg_cc : 0 ≤ c * c := mul_nonneg hc_nonneg hc_nonneg
  have h_sum_bound : ‖kact (offd M) (wv n y) n‖ ≤ c * c := by
    rw [kact]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h_nonneg_cc ?_
    intro j hj
    rcases Finset.mem_Icc.mp hj with ⟨hj1, hj2⟩
    by_cases hjn : n = j
    · subst hjn
      simp [offd, hwv_n, h_nonneg_cc]
    · have hjn' : j ≠ n := fun h => hjn (h.symm)
      have h_offd : offd M n j = M n j := by
        dsimp [offd]
        simp [hjn]
      have hwv_j : wv n y j = y j := by
        dsimp [wv, unitSeq]
        simp [hjn']
      rw [h_offd, hwv_j, norm_mul]
      have hM : ‖M n j‖ ≤ c := h.off n j hn hjn
      have hy_j : ‖y j‖ ≤ c := hy j
      calc
        ‖M n j‖ * ‖y j‖ ≤ c * c := mul_le_mul hM hy_j (norm_nonneg _) hc_nonneg
        _ = c * c := rfl
  have h_sum_bound_lt_one : ‖kact (offd M) (wv n y) n‖ < 1 :=
    lt_of_le_of_lt h_sum_bound h_c_sq_lt_one
  have h_add : ‖(M n n - 1) + kact (offd M) (wv n y) n‖ ≤
      max (‖M n n - 1‖) (‖kact (offd M) (wv n y) n‖) :=
    IsUltrametricDist.norm_add_le_max _ _
  exact lt_of_le_of_lt h_add (max_lt h_diag_lt h_sum_bound_lt_one)

/-- (V2) `‖δ_i(y)‖ = max(‖D_n‖, ‖D_i‖)` for `i ≠ n` (`μ(y)` and `M_ii` are units, `slope i ≠ slope n`). -/
theorem CHyp.norm_gdelta {M : ℕ → ℕ → K} {c : ℝ} (h : CHyp M c) {n i : ℕ} (hi : 1 ≤ i) (hin : i ≠ n)
    {y : ℕ → K} (hmu : ‖gmu M n y - 1‖ < 1) :
    ‖gdelta M n y i‖ = max ‖(ADB.D n : K)‖ ‖(ADB.D i : K)‖ := by
  have hmu_norm : ‖gmu M n y‖ = 1 := by
    have hlt : ‖gmu M n y - 1‖ < ‖(1 : K)‖ := by
      simpa using hmu
    have h_ne : ‖gmu M n y - 1‖ ≠ ‖(1 : K)‖ := by linarith
    have h_eq : ‖(gmu M n y - 1) + 1‖ = max ‖gmu M n y - 1‖ ‖(1 : K)‖ :=
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_ne
    have h_max : max ‖gmu M n y - 1‖ ‖(1 : K)‖ = ‖(1 : K)‖ :=
      max_eq_right (by linarith)
    calc
      ‖gmu M n y‖ = ‖(gmu M n y - 1) + 1‖ := by simp
      _ = max ‖gmu M n y - 1‖ ‖(1 : K)‖ := h_eq
      _ = ‖(1 : K)‖ := h_max
      _ = 1 := by simp
  have h_Mii_norm : ‖M i i‖ = 1 := by
    have h_diag := h.diag i hi
    have hlt : ‖M i i - 1‖ < ‖(1 : K)‖ := by
      simpa using h_diag
    have h_ne : ‖M i i - 1‖ ≠ ‖(1 : K)‖ := by linarith
    have h_eq : ‖(M i i - 1) + 1‖ = max ‖M i i - 1‖ ‖(1 : K)‖ :=
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_ne
    have h_max : max ‖M i i - 1‖ ‖(1 : K)‖ = ‖(1 : K)‖ :=
      max_eq_right (by linarith)
    calc
      ‖M i i‖ = ‖(M i i - 1) + 1‖ := by simp
      _ = max ‖M i i - 1‖ ‖(1 : K)‖ := h_eq
      _ = ‖(1 : K)‖ := h_max
      _ = 1 := by simp
  have h_Dn_muY : ‖(ADB.D n : K) * gmu M n y‖ = ‖(ADB.D n : K)‖ := by
    calc
      ‖(ADB.D n : K) * gmu M n y‖ = ‖(ADB.D n : K)‖ * ‖gmu M n y‖ := norm_mul _ _
      _ = ‖(ADB.D n : K)‖ * 1 := by rw [hmu_norm]
      _ = ‖(ADB.D n : K)‖ := by simp
  have h_Di_Mii : ‖(ADB.D i : K) * M i i‖ = ‖(ADB.D i : K)‖ := by
    calc
      ‖(ADB.D i : K) * M i i‖ = ‖(ADB.D i : K)‖ * ‖M i i‖ := norm_mul _ _
      _ = ‖(ADB.D i : K)‖ * 1 := by rw [h_Mii_norm]
      _ = ‖(ADB.D i : K)‖ := by simp
  have h_D_ne : ‖(ADB.D n : K)‖ ≠ ‖(ADB.D i : K)‖ := (norm_D_ne hin).symm
  have h_Dn_muY_ne_neg_Di_Mii : ‖(ADB.D n : K) * gmu M n y‖ ≠ ‖-((ADB.D i : K) * M i i)‖ := by
    rw [norm_neg, h_Dn_muY, h_Di_Mii]
    exact h_D_ne
  calc
    ‖gdelta M n y i‖ = ‖(ADB.D n : K) * gmu M n y - (ADB.D i : K) * M i i‖ := rfl
    _ = ‖(ADB.D n : K) * gmu M n y + (-((ADB.D i : K) * M i i))‖ := by rw [sub_eq_add_neg]
    _ = max ‖(ADB.D n : K) * gmu M n y‖ ‖(-((ADB.D i : K) * M i i))‖ :=
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_Dn_muY_ne_neg_Di_Mii
    _ = max ‖(ADB.D n : K) * gmu M n y‖ ‖(ADB.D i : K) * M i i‖ := by simp
    _ = max ‖(ADB.D n : K)‖ ‖(ADB.D i : K)‖ := by rw [h_Dn_muY, h_Di_Mii]

/-- (V2) `δ_i(y) ≠ 0` and `‖D_i / δ_i(y)‖ ≤ 1`. -/
theorem CHyp.norm_D_div_gdelta_le {M : ℕ → ℕ → K} {c : ℝ} (h : CHyp M c) {n i : ℕ} (hi : 1 ≤ i) (hin : i ≠ n)
    {y : ℕ → K} (hmu : ‖gmu M n y - 1‖ < 1) :
    gdelta M n y i ≠ 0 ∧ ‖(ADB.D i : K) / gdelta M n y i‖ ≤ 1 := by
  have hδ := h.norm_gdelta hi hin hmu
  have hDpos' : 0 < ADB.D i := CalegariSlopes.Newton.D_pos i
  have hDne : (ADB.D i : K) ≠ 0 := by
    exact_mod_cast hDpos'.ne'
  have hDpos : 0 < ‖(ADB.D i : K)‖ := norm_pos_iff.mpr hDne
  have hpos : 0 < ‖gdelta M n y i‖ := by
    rw [hδ]
    exact lt_of_lt_of_le hDpos (le_max_right _ _)
  refine ⟨norm_pos_iff.mp hpos, ?_⟩
  rw [norm_div, div_le_one hpos, hδ]
  exact le_max_right _ _

/-- (V3) `‖s_i(y)‖ ≤ c`. -/
theorem CHyp.norm_gs_le {M : ℕ → ℕ → K} {c : ℝ} (h : CHyp M c) (n : ℕ) {y : ℕ → K} (hy : ∀ j, ‖y j‖ ≤ c)
    (i : ℕ) : ‖gs M n y i‖ ≤ c := by
  have hc_nonneg : 0 ≤ c := h.nonneg
  rcases em (i = 0) with (rfl | hi)
  · -- i = 0 case: gs M n y 0 = 0
    simp [gs, kact_apply_zero, hc_nonneg]
  · -- i ≥ 1 case
    have hi' : 1 ≤ i := Nat.one_le_of_lt (Nat.pos_of_ne_zero hi)
    have hc_le_one : c ≤ 1 := h.lt_one.le
    have hterm : ∀ j ∈ Finset.Icc 1 (3 * i), ‖(offd M i j) * (wv n y j)‖ ≤ c := by
      intro j hj
      rw [norm_mul]
      have h_offd : ‖offd M i j‖ ≤ c := h.norm_offd_le hi' j
      have h_wv : ‖wv n y j‖ ≤ 1 := norm_wv_le_one_of hc_le_one hy j
      have : ‖offd M i j‖ * ‖wv n y j‖ ≤ c * 1 := mul_le_mul h_offd h_wv (norm_nonneg _) hc_nonneg
      simpa [mul_one] using this
    unfold gs kact
    exact norm_sum_le_of_le (Finset.Icc 1 (3 * i)) hc_nonneg hterm

/-- `s(y) ∈ c₀`. -/
theorem CHyp.isC0_gs {M : ℕ → ℕ → K} {c : ℝ} (h : CHyp M c) (n : ℕ) {y : ℕ → K} (hy : IsC0 y) :
    IsC0 (gs M n y) := by
  have h_eq : gs M n y = kact (offd M) (wv n y) := by
    funext i; rfl
  rw [h_eq]
  refine isC0_kact (offd M) (fun i j hlt => ?_) (fun i j hi => ?_) (isC0_wv hy)
  · dsimp [offd]
    split
    · rfl
    · exact h.band i j hlt
  · have hle := h.norm_offd_le hi j
    have hc1 : c ≤ 1 := h.lt_one.le
    linarith

/-! ## (L1) to (L3) -/

/-- (L1) `‖μ(y) - μ(y')‖ ≤ c d`. -/
theorem CHyp.norm_gmu_sub_le {M : ℕ → ℕ → K} {c : ℝ} (h : CHyp M c) {n : ℕ} (hn : 1 ≤ n) {y y' : ℕ → K}
    (hyn : y n = 0) (hy'n : y' n = 0) {d : ℝ} (hd0 : 0 ≤ d) (hd : ∀ j, ‖y j - y' j‖ ≤ d) :
    ‖gmu M n y - gmu M n y'‖ ≤ c * d := by
  have hcd : 0 ≤ c * d := mul_nonneg h.nonneg hd0
  have hwv_sub (j : ℕ) : wv n y j - wv n y' j = y j - y' j := by
    dsimp [wv]
    abel
  calc
    ‖gmu M n y - gmu M n y'‖ = ‖(∑ j ∈ Finset.Icc 1 (3 * n), M n j * wv n y j) -
                                (∑ j ∈ Finset.Icc 1 (3 * n), M n j * wv n y' j)‖ := by
      simp [gmu, kact]
    _ = ‖∑ j ∈ Finset.Icc 1 (3 * n), (M n j * wv n y j - M n j * wv n y' j)‖ := by
      simp [Finset.sum_sub_distrib]
    _ = ‖∑ j ∈ Finset.Icc 1 (3 * n), M n j * (wv n y j - wv n y' j)‖ := by
      simp [mul_sub]
    _ = ‖∑ j ∈ Finset.Icc 1 (3 * n), M n j * (y j - y' j)‖ := by
      simp [hwv_sub]
    _ ≤ c * d := by
      refine norm_sum_le_of_le (Finset.Icc 1 (3 * n)) hcd ?_
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).left
      by_cases hjn : j = n
      · subst hjn
        simp [hyn, hy'n, hcd]
      · calc
          ‖M n j * (y j - y' j)‖ = ‖M n j‖ * ‖y j - y' j‖ := norm_mul _ _
          _ ≤ c * d :=
            mul_le_mul (h.off n j hn (Ne.symm hjn)) (hd j) (norm_nonneg _) h.nonneg

/-- (L2) `‖s_i(y) - s_i(y')‖ ≤ c d`. -/
theorem CHyp.norm_gs_sub_le {M : ℕ → ℕ → K} {c : ℝ} (h : CHyp M c) (n : ℕ) {y y' : ℕ → K} {d : ℝ}
    (hd0 : 0 ≤ d) (hd : ∀ j, ‖y j - y' j‖ ≤ d) (i : ℕ) : ‖gs M n y i - gs M n y' i‖ ≤ c * d := by
  have hsub : gs M n y i - gs M n y' i = ∑ j ∈ Finset.Icc 1 (3 * i), offd M i j * (y j - y' j) := by
    calc
      gs M n y i - gs M n y' i = kact (offd M) (wv n y) i - kact (offd M) (wv n y') i := rfl
      _ = (∑ j ∈ Finset.Icc 1 (3 * i), offd M i j * wv n y j) -
          (∑ j ∈ Finset.Icc 1 (3 * i), offd M i j * wv n y' j) := rfl
      _ = ∑ j ∈ Finset.Icc 1 (3 * i), (offd M i j * wv n y j - offd M i j * wv n y' j) := by
        rw [Finset.sum_sub_distrib]
      _ = ∑ j ∈ Finset.Icc 1 (3 * i), offd M i j * (wv n y j - wv n y' j) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [mul_sub]
      _ = ∑ j ∈ Finset.Icc 1 (3 * i), offd M i j * (y j - y' j) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        dsimp [wv, unitSeq]
        ring
  rw [hsub]
  by_cases hi0 : i = 0
  · subst hi0
    simp [mul_nonneg h.nonneg hd0]
  · have hi1 : 1 ≤ i := by omega
    have hnorm : ∀ j, ‖offd M i j‖ ≤ c := by
      intro j
      by_cases hij : i = j
      · subst hij
        simp [offd, h.nonneg]
      · have hle := h.off i j hi1 hij
        simpa [offd, hij] using hle
    have hbound : ∀ j, ‖offd M i j * (y j - y' j)‖ ≤ c * d := by
      intro j
      calc
        ‖offd M i j * (y j - y' j)‖ = ‖offd M i j‖ * ‖y j - y' j‖ := norm_mul _ _
        _ ≤ c * ‖y j - y' j‖ := mul_le_mul_of_nonneg_right (hnorm j) (norm_nonneg _)
        _ ≤ c * d := mul_le_mul_of_nonneg_left (hd j) h.nonneg
    have hcd : 0 ≤ c * d := mul_nonneg h.nonneg hd0
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hcd (fun j hj => hbound j)

/-- (L3) `‖D_i / δ_i(y) - D_i / δ_i(y')‖ ≤ ‖μ(y) - μ(y')‖ / 3` (the gap `|slope i - slope n| ≥ 1`). -/
theorem CHyp.norm_D_div_gdelta_sub_le {M : ℕ → ℕ → K} {c : ℝ} (h : CHyp M c) {n i : ℕ} (hi : 1 ≤ i)
    (hin : i ≠ n) {y y' : ℕ → K} (hmu : ‖gmu M n y - 1‖ < 1) (hmu' : ‖gmu M n y' - 1‖ < 1) :
    ‖(ADB.D i : K) / gdelta M n y i - (ADB.D i : K) / gdelta M n y' i‖ ≤ 1 / 3 * ‖gmu M n y - gmu M n y'‖ := by
  have hgdelta_ne_y : gdelta M n y i ≠ 0 := (CHyp.norm_D_div_gdelta_le h hi hin hmu).1
  have hgdelta_ne_y' : gdelta M n y' i ≠ 0 := (CHyp.norm_D_div_gdelta_le h hi hin hmu').1
  have hgdelta_norm_val : ‖gdelta M n y i‖ = max ‖(ADB.D n : K)‖ ‖(ADB.D i : K)‖ :=
    CHyp.norm_gdelta h hi hin hmu
  have hgdelta_norm_eq : ‖gdelta M n y i‖ = ‖gdelta M n y' i‖ := by
    rw [CHyp.norm_gdelta h hi hin hmu, CHyp.norm_gdelta h hi hin hmu']
  have hdelta_sub : gdelta M n y i - gdelta M n y' i = (ADB.D n : K) * (gmu M n y - gmu M n y') := by
    dsimp [gdelta, gmu]
    ring
  have hnorm_sub : ‖gdelta M n y i - gdelta M n y' i‖ = ‖(ADB.D n : K)‖ * ‖gmu M n y - gmu M n y'‖ := by
    rw [hdelta_sub, norm_mul]
  have hkey : ‖(ADB.D i : K) / gdelta M n y i - (ADB.D i : K) / gdelta M n y' i‖ =
      ‖(ADB.D i : K)‖ * ‖(ADB.D n : K)‖ * ‖gmu M n y - gmu M n y'‖ /
        (‖gdelta M n y i‖ * ‖gdelta M n y' i‖) := by
    calc
      ‖(ADB.D i : K) / gdelta M n y i - (ADB.D i : K) / gdelta M n y' i‖
          = ‖((ADB.D i : K) * gdelta M n y' i - gdelta M n y i * (ADB.D i : K)) /
              (gdelta M n y i * gdelta M n y' i)‖ := by
        rw [div_sub_div _ _ hgdelta_ne_y hgdelta_ne_y']
      _ = ‖(ADB.D i : K) * (gdelta M n y' i - gdelta M n y i) / (gdelta M n y i * gdelta M n y' i)‖ := by ring_nf
      _ = ‖(ADB.D i : K)‖ * ‖gdelta M n y' i - gdelta M n y i‖ / (‖gdelta M n y i‖ * ‖gdelta M n y' i‖) := by
        simp [norm_div, norm_mul]
      _ = ‖(ADB.D i : K)‖ * ‖gdelta M n y i - gdelta M n y' i‖ / (‖gdelta M n y i‖ * ‖gdelta M n y' i‖) := by
        rw [norm_sub_rev]
      _ = ‖(ADB.D i : K)‖ * (‖(ADB.D n : K)‖ * ‖gmu M n y - gmu M n y'‖) /
          (‖gdelta M n y i‖ * ‖gdelta M n y' i‖) := by rw [hnorm_sub]
      _ = ‖(ADB.D i : K)‖ * ‖(ADB.D n : K)‖ * ‖gmu M n y - gmu M n y'‖ /
          (‖gdelta M n y i‖ * ‖gdelta M n y' i‖) := by ring
  rw [hkey]
  have hdenom : ‖gdelta M n y i‖ * ‖gdelta M n y' i‖ = max ‖(ADB.D n : K)‖ ‖(ADB.D i : K)‖ ^ 2 := by
    rw [hgdelta_norm_val, ← hgdelta_norm_eq, hgdelta_norm_val]
    ring
  rw [hdenom]
  have hM_pos : 0 < max ‖(ADB.D n : K)‖ ‖(ADB.D i : K)‖ := by
    have hne := norm_D_ne hin
    have hn_nonneg : 0 ≤ ‖(ADB.D n : K)‖ := norm_nonneg _
    have hi_nonneg : 0 ≤ ‖(ADB.D i : K)‖ := norm_nonneg _
    by_contra! hle
    have hmax0 : max ‖(ADB.D n : K)‖ ‖(ADB.D i : K)‖ ≤ 0 := hle
    have hn0 : ‖(ADB.D n : K)‖ ≤ 0 := le_trans (le_max_left _ _) hmax0
    have hi0 : ‖(ADB.D i : K)‖ ≤ 0 := le_trans (le_max_right _ _) hmax0
    have hn0' : ‖(ADB.D n : K)‖ = 0 := by linarith
    have hi0' : ‖(ADB.D i : K)‖ = 0 := by linarith
    have heq : ‖(ADB.D n : K)‖ = ‖(ADB.D i : K)‖ := by rw [hn0', hi0']
    exact hne heq.symm
  have hM_sq_pos : 0 < max ‖(ADB.D n : K)‖ ‖(ADB.D i : K)‖ ^ 2 := pow_pos hM_pos 2
  have ha_le : ‖(ADB.D i : K)‖ * ‖(ADB.D n : K)‖ ≤ 1 / 3 * (max ‖(ADB.D n : K)‖ ‖(ADB.D i : K)‖ ^ 2) := by
    have h := norm_D_mul_le hin
    simpa [max_comm] using h
  have ha_div_M_le : ‖(ADB.D i : K)‖ * ‖(ADB.D n : K)‖ / (max ‖(ADB.D n : K)‖ ‖(ADB.D i : K)‖ ^ 2) ≤ 1/3 := by
    have htemp : ‖(ADB.D i : K)‖ * ‖(ADB.D n : K)‖ / (max ‖(ADB.D n : K)‖ ‖(ADB.D i : K)‖ ^ 2) ≤
        (1 / 3 * (max ‖(ADB.D n : K)‖ ‖(ADB.D i : K)‖ ^ 2)) / (max ‖(ADB.D n : K)‖ ‖(ADB.D i : K)‖ ^ 2) :=
      div_le_div_of_nonneg_right ha_le (by positivity)
    have hsimpl : (1 / 3 * (max ‖(ADB.D n : K)‖ ‖(ADB.D i : K)‖ ^ 2)) /
        (max ‖(ADB.D n : K)‖ ‖(ADB.D i : K)‖ ^ 2) = 1/3 := by
      field_simp [ne_of_gt hM_sq_pos]
    rwa [hsimpl] at htemp
  calc
    ‖(ADB.D i : K)‖ * ‖(ADB.D n : K)‖ * ‖gmu M n y - gmu M n y'‖ / (max ‖(ADB.D n : K)‖ ‖(ADB.D i : K)‖ ^ 2)
        = (‖(ADB.D i : K)‖ * ‖(ADB.D n : K)‖ / (max ‖(ADB.D n : K)‖ ‖(ADB.D i : K)‖ ^ 2)) *
          ‖gmu M n y - gmu M n y'‖ := by ring
    _ ≤ (1/3) * ‖gmu M n y - gmu M n y'‖ :=
      mul_le_mul_of_nonneg_right ha_div_M_le (norm_nonneg _)

/-! ## `T` maps `Y` into `Y` and contracts -/

/-- `T(Y) ⊆ Y`. -/
theorem CHyp.gT_maps {M : ℕ → ℕ → K} {c : ℝ} (h : CHyp M c) {n : ℕ} (hn : 1 ≤ n) {y : ℕ → K}
    (hy : ∀ j, ‖y j‖ ≤ c) (hyn : y n = 0) (hyc : IsC0 y) :
    (∀ i, ‖gT M n y i‖ ≤ c) ∧ (∀ i ∈ ({0, n} : Set ℕ), gT M n y i = 0) ∧ IsC0 (gT M n y) := by
  have hmu : ‖gmu M n y - 1‖ < 1 := h.norm_gmu_sub_one_lt hn hy hyn
  have h_gs_le : ∀ i, ‖gs M n y i‖ ≤ c := h.norm_gs_le n hy
  have h_isC0_gs : IsC0 (gs M n y) := h.isC0_gs n hyc
  have h_bound : ∀ i, ‖gT M n y i‖ ≤ ‖gs M n y i‖ := by
    intro i
    by_cases hi0 : i = 0
    · subst hi0; simp [gT]
    · by_cases hin : i = n
      · subst hin; simp [gT]
      · have hi1 : 1 ≤ i := by omega
        have hdiv := h.norm_D_div_gdelta_le hi1 hin hmu
        rcases hdiv with ⟨hden_ne_zero, hdiv_le⟩
        unfold gT
        simp [hi0, hin]
        have hdiv_le' : ‖(ADB.D i : K)‖ / ‖gdelta M n y i‖ ≤ 1 := by
          simpa [norm_div] using hdiv_le
        calc
          ‖(ADB.D i : K)‖ * ‖gs M n y i‖ / ‖gdelta M n y i‖ = (‖(ADB.D i : K)‖ / ‖gdelta M n y i‖) * ‖gs M n y i‖ := by
            ring
          _ ≤ 1 * ‖gs M n y i‖ := by gcongr
          _ = ‖gs M n y i‖ := by simp
  refine ⟨?_, ?_, ?_⟩
  · intro i
    calc
      ‖gT M n y i‖ ≤ ‖gs M n y i‖ := h_bound i
      _ ≤ c := h_gs_le i
  · intro i hi
    simp_rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with (rfl | rfl)
    · simp [gT]
    · simp [gT]
  · refine IsC0.of_norm_le h_isC0_gs ?_
    intro i
    exact h_bound i

/-- `T` contracts by `c` on `Y`. -/
theorem CHyp.gT_lip {M : ℕ → ℕ → K} {c : ℝ} (h : CHyp M c) {n : ℕ} (hn : 1 ≤ n) {y y' : ℕ → K}
    (hy : ∀ j, ‖y j‖ ≤ c) (hyn : y n = 0) (hy' : ∀ j, ‖y' j‖ ≤ c) (hy'n : y' n = 0) {d : ℝ} (hd0 : 0 ≤ d)
    (hd : ∀ j, ‖y j - y' j‖ ≤ d) (i : ℕ) : ‖gT M n y i - gT M n y' i‖ ≤ c * d := by
  by_cases hi0 : i = 0
  · subst hi0; simp [gT]; exact mul_nonneg h.nonneg hd0
  · by_cases hin : i = n
    · subst hin; simp [gT]; exact mul_nonneg h.nonneg hd0
    · have hi : 1 ≤ i := Nat.one_le_of_lt (Nat.pos_of_ne_zero hi0)
      have hmu : ‖gmu M n y - 1‖ < 1 := h.norm_gmu_sub_one_lt hn hy hyn
      have hmu' : ‖gmu M n y' - 1‖ < 1 := h.norm_gmu_sub_one_lt hn hy' hy'n
      have hq := h.norm_D_div_gdelta_le hi hin hmu
      have hq_bound : ‖(ADB.D i : K) / gdelta M n y i‖ ≤ 1 := hq.2
      have hq_ne_zero : gdelta M n y i ≠ 0 := hq.1
      have hq' := h.norm_D_div_gdelta_le hi hin hmu'
      have hq'_ne_zero : gdelta M n y' i ≠ 0 := hq'.1
      have hs_sub : ‖gs M n y i - gs M n y' i‖ ≤ c * d := h.norm_gs_sub_le n hd0 hd i
      have hq_sub : ‖(ADB.D i : K) / gdelta M n y i - (ADB.D i : K) / gdelta M n y' i‖ ≤
          1 / 3 * ‖gmu M n y - gmu M n y'‖ :=
        h.norm_D_div_gdelta_sub_le hi hin hmu hmu'
      have hmu_sub : ‖gmu M n y - gmu M n y'‖ ≤ c * d :=
        h.norm_gmu_sub_le hn hyn hy'n hd0 hd
      have hs_le : ‖gs M n y' i‖ ≤ c := h.norm_gs_le n hy' i
      have hc_nonneg : 0 ≤ c := h.nonneg
      have h_eq : (ADB.D i : K) * gs M n y i / gdelta M n y i - (ADB.D i : K) * gs M n y' i / gdelta M n y' i =
          ((ADB.D i : K) / gdelta M n y i) * (gs M n y i - gs M n y' i) +
          (((ADB.D i : K) / gdelta M n y i) - ((ADB.D i : K) / gdelta M n y' i)) * gs M n y' i := by
        field_simp [hq_ne_zero, hq'_ne_zero]
        ring
      unfold gT
      simp [hi0, hin]
      rw [h_eq]
      have h1 : ‖((ADB.D i : K) / gdelta M n y i) * (gs M n y i - gs M n y' i)‖ ≤ c * d := by
        calc
          ‖((ADB.D i : K) / gdelta M n y i) * (gs M n y i - gs M n y' i)‖ ≤
              ‖(ADB.D i : K) / gdelta M n y i‖ * ‖gs M n y i - gs M n y' i‖ := norm_mul_le _ _
          _ ≤ 1 * (c * d) := by gcongr
          _ = c * d := by simp
      have h2 : ‖(((ADB.D i : K) / gdelta M n y i) - ((ADB.D i : K) / gdelta M n y' i)) * gs M n y' i‖ ≤ c * d := by
        calc
          ‖(((ADB.D i : K) / gdelta M n y i) - ((ADB.D i : K) / gdelta M n y' i)) * gs M n y' i‖ ≤
              ‖((ADB.D i : K) / gdelta M n y i) - ((ADB.D i : K) / gdelta M n y' i)‖ * ‖gs M n y' i‖ := norm_mul_le _ _
          _ ≤ (1 / 3 * ‖gmu M n y - gmu M n y'‖) * c := by
            have hpos : 0 ≤ 1 / 3 * ‖gmu M n y - gmu M n y'‖ := by
              positivity
            exact mul_le_mul hq_sub hs_le (norm_nonneg _) hpos
          _ ≤ (1 / 3 * (c * d)) * c := by
            apply mul_le_mul_of_nonneg_right
            · apply mul_le_mul_of_nonneg_left hmu_sub
              norm_num
            · exact hc_nonneg
          _ = c ^ 2 * d / 3 := by ring
          _ ≤ c * d := by
            have hc : c ≤ 1 := le_of_lt h.lt_one
            have h_mul : c ^ 2 * d ≤ 3 * (c * d) := by
              have h_nonpos : c * d * (c - 3) ≤ 0 := by
                have h1 : c - 3 ≤ 0 := by linarith
                have h2 : c * d ≥ 0 := mul_nonneg hc_nonneg hd0
                nlinarith
              nlinarith
            calc
              c ^ 2 * d / 3 ≤ (3 * (c * d)) / 3 :=
                div_le_div_of_nonneg_right h_mul (by norm_num)
              _ = c * d := by field_simp
      have hmax : ‖((ADB.D i : K) / gdelta M n y i) * (gs M n y i - gs M n y' i) +
          (((ADB.D i : K) / gdelta M n y i) - ((ADB.D i : K) / gdelta M n y' i)) * gs M n y' i‖ ≤ c * d := by
        apply le_trans (IsUltrametricDist.norm_add_le_max _ _)
        apply max_le h1 h2
      exact hmax

/-- The equations at a fixed point: `D_i (M w)_i = D_n μ(y) w_i` for `i ≥ 1`. -/
theorem CHyp.eq_of_gT_eq {M : ℕ → ℕ → K} {c : ℝ} (h : CHyp M c) {n : ℕ} (hn : 1 ≤ n) {y : ℕ → K}
    (hy : ∀ j, ‖y j‖ ≤ c) (hyn : y n = 0) (hT : gT M n y = y) (i : ℕ) (hi : 1 ≤ i) :
    (ADB.D i : K) * kact M (wv n y) i = (ADB.D n : K) * gmu M n y * wv n y i := by
  by_cases hin : i = n
  · -- case i = n
    rw [hin]
    have hwvn : wv n y n = 1 := by
      dsimp [wv, unitSeq]
      simp [hyn]
    have hbact : kact M (wv n y) n = gmu M n y := rfl
    rw [hwvn, hbact]
    ring
  · -- case i ≠ n
    have hi0 : i ≠ 0 := by omega
    have hwvi : wv n y i = y i := by
      dsimp [wv, unitSeq]
      simp [hin]
    have hbact_eq : kact M (wv n y) i = M i i * wv n y i + kact (offd M) (wv n y) i :=
      kact_eq_diag_add_offd M (wv n y) hi
    rw [hwvi] at hbact_eq
    have hT_i : gT M n y i = y i := by rw [hT]
    have hT_i_eq : gT M n y i = (ADB.D i : K) * gs M n y i / gdelta M n y i := by
      dsimp [gT]
      simp [hi0, hin]
    rw [hT_i_eq] at hT_i
    have h_delta_ne_zero : gdelta M n y i ≠ 0 :=
      ((h.norm_D_div_gdelta_le hi hin (h.norm_gmu_sub_one_lt hn hy hyn)).1)
    have h_eq : gdelta M n y i * y i = (ADB.D i : K) * gs M n y i := by
      have := (div_eq_iff h_delta_ne_zero).mp hT_i
      calc
        gdelta M n y i * y i = y i * gdelta M n y i := mul_comm _ _
        _ = (ADB.D i : K) * gs M n y i := by rw [← this]
    have h_delta_def : gdelta M n y i = (ADB.D n : K) * gmu M n y - (ADB.D i : K) * M i i := rfl
    rw [h_delta_def] at h_eq
    rw [hbact_eq]
    have h_gs_def : gs M n y i = kact (offd M) (wv n y) i := rfl
    rw [h_gs_def] at h_eq
    rw [hwvi]
    calc
      (ADB.D i : K) * (M i i * y i + kact (offd M) (wv n y) i)
          = (ADB.D i : K) * (M i i * y i) + (ADB.D i : K) * kact (offd M) (wv n y) i := by ring
      _ = (ADB.D i : K) * M i i * y i + (ADB.D i : K) * kact (offd M) (wv n y) i := by ring
      _ = (ADB.D i : K) * M i i * y i + (((ADB.D n : K) * gmu M n y - (ADB.D i : K) * M i i) * y i) := by rw [← h_eq]
      _ = ((ADB.D i : K) * M i i + ((ADB.D n : K) * gmu M n y - (ADB.D i : K) * M i i)) * y i := by ring
      _ = (ADB.D n : K) * gmu M n y * y i := by ring

/-- Proposition 6.4 for `M`: for `n ≥ 1` there are `y ∈ c₀` with `y_0 = y_n = 0`, `‖y‖ ≤ c`, and `μ` with
`‖μ - 1‖ < 1`, such that `w = e_n + y` satisfies `D_i (M w)_i = D_n μ w_i` for every `i ≥ 1`. -/
theorem CHyp.exists_eigen {M : ℕ → ℕ → K} {c : ℝ} (h : CHyp M c) {n : ℕ} (hn : 1 ≤ n) :
    ∃ (y : ℕ → K) (μ : K), y 0 = 0 ∧ y n = 0 ∧ (∀ j, ‖y j‖ ≤ c) ∧ IsC0 y ∧ ‖μ - 1‖ < 1 ∧
      ∀ i, 1 ≤ i → (ADB.D i : K) * kact M (wv n y) i = (ADB.D n : K) * μ * wv n y i := by
  have hmaps' : ∀ y : ℕ → K, (∀ i, ‖y i‖ ≤ c) → (∀ i ∈ ({0, n} : Set ℕ), y i = 0) → IsC0 y →
      (∀ i, ‖gT M n y i‖ ≤ c) ∧ (∀ i ∈ ({0, n} : Set ℕ), gT M n y i = 0) ∧ IsC0 (gT M n y) := by
    intro y hy hZ hyc
    have hyn : y n = 0 := hZ n (by simp)
    exact h.gT_maps hn hy hyn hyc
  have hlip' : ∀ y y' : ℕ → K, (∀ i, ‖y i‖ ≤ c) → (∀ i ∈ ({0, n} : Set ℕ), y i = 0) → IsC0 y →
      (∀ i, ‖y' i‖ ≤ c) → (∀ i ∈ ({0, n} : Set ℕ), y' i = 0) → IsC0 y' →
      ∀ d : ℝ, 0 ≤ d → (∀ i, ‖y i - y' i‖ ≤ d) → ∀ i, ‖gT M n y i - gT M n y' i‖ ≤ c * d := by
    intro y y' hy hZ hyc hy' hZ' hyc' d hd0 hd i
    have hyn : y n = 0 := hZ n (by simp)
    have hy'n : y' n = 0 := hZ' n (by simp)
    exact h.gT_lip hn hy hyn hy' hy'n hd0 hd i
  obtain ⟨y, hy_bound, hy_zero, hy_c0, hT_eq⟩ := exists_fixed_seq (gT M n) c c ({0, n} : Set ℕ)
    h.nonneg h.nonneg h.lt_one hmaps' hlip'
  have hy0 : y 0 = 0 := hy_zero 0 (by simp)
  have hyn : y n = 0 := hy_zero n (by simp)
  refine ⟨y, gmu M n y, hy0, hyn, hy_bound, hy_c0, h.norm_gmu_sub_one_lt hn hy_bound hyn, ?_⟩
  intro i hi
  simpa using h.eq_of_gT_eq hn hy_bound hyn hT_eq i hi

end CalegariSlopes.Conj5
