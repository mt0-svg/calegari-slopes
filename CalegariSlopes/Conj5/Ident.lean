/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Conj5.Scaled

@[expose] public section

/-!
# The identification of the eigenvectors at radius `r` with those of `U`

The lemmas of the proof of Corollaries 8.3 and 8.4 of the paper that `CalegariSlopes.Conj5.SpectralMain` assembles:
`γ` of any rational valuation exists (`exists_norm_eq_rpow`); `Λ y_n = (γ ^ j y_{n,j})_j` lies in `L_s` with
`U Λ y_n = λ Λ y_n`, so it is in `c₀` (`isC0_of_InS`) and a nonzero multiple of `x_n` with `λ = λ_n`
(`EigenFamily.diag`, the injectivity of `σ`) (`identify`); the coordinates of `x_n = κ⁻¹ Λ y_n` give
`v(x_{n,i}) ≥ 1 - |s| + s (n - i)` (`norm_x_le_of_norm`), and the limit `s → ±1` (`le_zpow_of_forall_rat`).
-/

open Filter Topology
open CalegariSlopes.Overconvergent (K)
open CalegariSlopes.Spectral

namespace CalegariSlopes.Conj5

/-! ## `γ` -/

/-- For every rational `q` some `γ ∈ ℂ_[3]` has `‖γ‖ = 3 ^ q` (a root of `X ^ m = 3 ^ (-k)`, `q = k / m`). -/
theorem exists_norm_eq_rpow (q : ℚ) : ∃ γ : K, ‖γ‖ = (3 : ℝ) ^ (q : ℝ) := by
  have h3 : ‖(3 : K)‖ = 3⁻¹ := by
    rw [← map_ofNat (algebraMap ℚ_[3] K) 3, norm_algebraMap',
      show (3 : ℚ_[3]) = ((3 : ℕ) : ℚ_[3]) by norm_cast, Padic.norm_p]
    norm_num
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (3 : PadicAlgCl 3) q.den_pos
  set β : K := algebraMap (PadicAlgCl 3) K α with hβdef
  have hβ : β ^ q.den = 3 := by
    rw [hβdef, ← map_pow, hα, map_ofNat]
  have hβn : ‖β‖ = (3 : ℝ) ^ (-(1 / (q.den : ℝ))) := by
    have h1 : ‖β‖ ^ q.den = 3⁻¹ := by
      rw [← norm_pow, hβ, h3]
    calc ‖β‖ = (‖β‖ ^ q.den) ^ ((q.den : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast (norm_nonneg _) q.den_ne_zero).symm
      _ = ((3 : ℝ)⁻¹) ^ ((q.den : ℝ)⁻¹) := by rw [h1]
      _ = (3 : ℝ) ^ (-(1 / (q.den : ℝ))) := by
        rw [Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), one_div]
  refine ⟨β ^ (-q.num), ?_⟩
  rw [norm_zpow, hβn, ← Real.rpow_intCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  rw [Rat.cast_def]
  push_cast
  have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  field_simp

/-! ## The identification with `x_n` -/

/-- `Λ y ∈ L_s` for `y ∈ c₀` and `‖γ‖ = 3 ^ s`. -/
theorem InS_scal {γ : K} {s : ℝ} (hγ : ‖γ‖ = (3 : ℝ) ^ s) {y : ℕ → K} (hy : IsC0 y) : InS s (scal γ y) := by
  have hpos3 : (0 : ℝ) < 3 := by norm_num
  have h_nonneg3 : (0 : ℝ) ≤ 3 := by norm_num
  have h_eq : (fun j : ℕ => ‖scal γ y j‖ * (3 : ℝ) ^ (-(s * j))) = (fun j : ℕ => ‖y j‖) := by
    ext j
    calc
      ‖scal γ y j‖ * (3 : ℝ) ^ (-(s * j)) = ‖γ ^ (j : ℤ) * y j‖ * (3 : ℝ) ^ (-(s * j)) := rfl
      _ = (‖γ ^ (j : ℤ)‖ * ‖y j‖) * (3 : ℝ) ^ (-(s * j)) := by rw [norm_mul]
      _ = ((3 : ℝ) ^ (s * (j : ℤ)) * ‖y j‖) * (3 : ℝ) ^ (-(s * j)) := by rw [norm_zpow_of_norm hγ (j : ℤ)]
      _ = ‖y j‖ * ((3 : ℝ) ^ (s * (j : ℤ)) * (3 : ℝ) ^ (-(s * j))) := by ring
      _ = ‖y j‖ * ((3 : ℝ) ^ (s * (j : ℝ)) * (3 : ℝ) ^ (-(s * (j : ℝ)))) := by simp
      _ = ‖y j‖ * ((3 : ℝ) ^ (s * (j : ℝ)) * ((3 : ℝ) ^ (s * (j : ℝ)))⁻¹) := by
        rw [Real.rpow_neg h_nonneg3 (s * (j : ℝ))]
      _ = ‖y j‖ * 1 := by
        have hpos : (3 : ℝ) ^ (s * (j : ℝ)) > 0 :=
          Real.rpow_pos_of_pos hpos3 (s * (j : ℝ))
        field_simp [hpos.ne']
      _ = ‖y j‖ := by simp
  rw [InS, h_eq]
  simpa using hy.norm

/-- `Λ y_n` is a nonzero multiple of `x_n`, and the eigenvalue is `λ_n`. -/
theorem identify (E : EigenFamily) {γ : K} {s : ℝ} (hγ : ‖γ‖ = (3 : ℝ) ^ s) (hs3 : s < 3) {n : ℕ}
    (_hn : 1 ≤ n) {y : ℕ → K} {lam : K} (hyc : IsC0 y) (hyn : ‖y n - 1‖ < 1) (heig : Ur γ y = lam • y)
    (hlam : ‖lam‖ = (3 : ℝ) ^ (-(slope n : ℤ))) :
    lam = E.lam n ∧ ∃ κ : K, κ ≠ 0 ∧ scal γ y = κ • E.x n := by
  have hγ0 : γ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hγ
    exact (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) s).ne' hγ.symm
  have hlam0 : lam ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlam
    exact (zpow_pos (by norm_num : (0 : ℝ) < 3) _).ne' hlam.symm
  have hz : Uop (scal γ y) = lam • scal γ y := by
    rw [Uop_scal hγ0, heig]
    funext j
    simp only [scal, Pi.smul_apply, smul_eq_mul]
    ring
  have hk : ((Uop - lam • (1 : Module.End K (ℕ → K))) ^ 1) (scal γ y) = 0 := by
    rw [pow_one, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hz, sub_self]
  have hzc : IsC0 (scal γ y) := isC0_of_InS hs3 (InS_scal hγ hyc) hlam0 hk
  obtain ⟨b, -, hbsupp, hzb⟩ := E.diag hlam0 hzc hk
  have hsupp : ∀ m, m ≠ n → b m = 0 := by
    intro m hm
    by_contra hbm
    have h1 := hbsupp m hbm
    rcases Nat.eq_zero_or_pos m with rfl | hm1
    · rw [E.lam_zero] at h1
      exact hlam0 h1.symm
    · have h2 := E.norm_lam m hm1
      rw [h1, hlam] at h2
      have h3 := zpow_right_injective₀ (a := (3 : ℝ)) (by norm_num) (by norm_num) h2
      have h4 : slope n = slope m := by exact_mod_cast neg_injective h3
      exact hm (slope_strictMono.injective h4).symm
  have hzx : scal γ y = b n • E.x n := by
    rw [hzb]
    exact expand_eq_smul _ _ _ hsupp
  have hzn : scal γ y n ≠ 0 := by
    simp only [scal]
    refine mul_ne_zero (zpow_ne_zero _ hγ0) ?_
    intro h
    rw [h, zero_sub, norm_neg, norm_one] at hyn
    exact lt_irrefl _ hyn
  have hbn : b n ≠ 0 := by
    intro h
    apply hzn
    rw [hzx, h, zero_smul]
    rfl
  exact ⟨(hbsupp n hbn).symm, b n, hbn, hzx⟩

/-- `‖a‖ = 1` when `‖a - 1‖ < 1`. -/
theorem norm_eq_one_of_norm_sub_one_lt {a : K} (h : ‖a - 1‖ < 1) : ‖a‖ = 1 := by
  have h1 : ‖a - 1‖ ≠ ‖(1 : K)‖ := by
    rw [norm_one]
    exact h.ne
  calc ‖a‖ = ‖(a - 1) + 1‖ := by ring_nf
    _ = max ‖a - 1‖ ‖(1 : K)‖ := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1
    _ = 1 := by rw [norm_one]; exact max_eq_right h.le

/-- The bound of the proof of Corollary 8.4 at one radius: `v(x_{n,i}) ≥ 1 - |s| + s (n - i)`. -/
theorem norm_x_le_of_norm (E : EigenFamily) {γ : K} {s : ℝ} (hγ : ‖γ‖ = (3 : ℝ) ^ s) (hs : |s| < 1) {n i : ℕ}
    (hn : 1 ≤ n) (hin : i ≠ n) : ‖E.x n i‖ ≤ (3 : ℝ) ^ (s * ((i : ℝ) - n) - (1 - |s|)) := by
  have hc1 := rpow_eps_lt_one hs
  have hγ0 : γ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hγ
    exact (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) s).ne' hγ.symm
  obtain ⟨y, lam, hyc, hyn, heig, hlam, -⟩ := exists_eigvec_r hγ hs hn
  have hyn1 : ‖y n - 1‖ < 1 := by
    have := hyn n
    simp only [unitSeq, ite_true] at this
    exact this.trans_lt hc1
  obtain ⟨-, κ, hκ, hzx⟩ := identify E hγ (by linarith [(abs_lt.mp hs).2]) hn hyc hyn1 heig hlam
  have hxnn : ‖E.x n n‖ = 1 := by
    apply norm_eq_one_of_norm_sub_one_lt
    have := E.near.near n n
    simp only [unitSeq, ite_true] at this
    linarith
  have hκn : ‖κ‖ = (3 : ℝ) ^ (s * (n : ℝ)) := by
    have h := congrArg norm (congrFun hzx n)
    simp only [scal, Pi.smul_apply, smul_eq_mul] at h
    rw [norm_mul, norm_mul, norm_zpow_of_norm hγ, norm_eq_one_of_norm_sub_one_lt hyn1, hxnn] at h
    push_cast at h
    linarith
  have hyi : ‖y i‖ ≤ (3 : ℝ) ^ (-(1 - |s|)) := by
    have := hyn i
    simpa [unitSeq, hin] using this
  have hpos : 0 < ‖κ‖ := norm_pos_iff.mpr hκ
  have hxi : ‖E.x n i‖ = ‖γ ^ (i : ℤ)‖ * ‖y i‖ / ‖κ‖ := by
    have h := congrArg norm (congrFun hzx i)
    simp only [scal, Pi.smul_apply, smul_eq_mul, norm_mul] at h
    rw [h]
    field_simp
  rw [hxi, norm_zpow_of_norm hγ, hκn, div_le_iff₀ (Real.rpow_pos_of_pos (by norm_num) _)]
  calc (3 : ℝ) ^ (s * ((i : ℤ) : ℝ)) * ‖y i‖ ≤ (3 : ℝ) ^ (s * ((i : ℤ) : ℝ)) * (3 : ℝ) ^ (-(1 - |s|)) :=
        mul_le_mul_of_nonneg_left hyi (Real.rpow_nonneg (by norm_num) _)
    _ = (3 : ℝ) ^ (s * ((i : ℝ) - n) - (1 - |s|)) * (3 : ℝ) ^ (s * (n : ℝ)) := by
        rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
        congr 1
        push_cast
        ring

/-- The limit `s → ±1` over the radii `s = 3 - 6r`, `r ∈ (1/3, 2/3)` rational. -/
theorem le_zpow_of_forall_rat {f : ℝ} {d : ℤ} (_hd : d ≠ 0)
    (h : ∀ r : ℚ, 1 / 3 < r → r < 2 / 3 → f ≤ (3 : ℝ) ^ ((3 - 6 * (r : ℝ)) * d - (1 - |3 - 6 * (r : ℝ)|))) :
    f ≤ (3 : ℝ) ^ (-|d|) := by
  have ht : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have main : ∀ ε : ℚ, (ε = 1 ∨ ε = -1) → (ε : ℝ) * d = -|(d : ℝ)| → f ≤ (3 : ℝ) ^ (-|d|) := by
    intro ε hε hεd
    have hε2 : |(ε : ℝ)| = 1 := by
      rcases hε with rfl | rfl <;> simp
    let r : ℕ → ℚ := fun k => 1 / 2 - ε * (1 - 1 / ((k : ℚ) + 1)) / 6
    have hrs : ∀ k : ℕ, (3 : ℝ) - 6 * ((r k : ℚ) : ℝ) = (ε : ℝ) * (1 - 1 / ((k : ℝ) + 1)) := by
      intro k
      simp only [r]
      push_cast
      ring
    have hr : ∀ k : ℕ, 1 / 3 < r k ∧ r k < 2 / 3 := by
      intro k
      have hk : (0 : ℚ) ≤ k := k.cast_nonneg
      have h0 : (0 : ℚ) < 1 / ((k : ℚ) + 1) := by positivity
      have h1 : 1 / ((k : ℚ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      simp only [r]
      rcases hε with rfl | rfl <;> constructor <;> linarith
    have hg : Continuous (fun t : ℝ => (ε : ℝ) * (1 - t) * d - (1 - |(ε : ℝ) * (1 - t)|)) := by
      fun_prop
    have hval : (ε : ℝ) * (1 - 0) * d - (1 - |(ε : ℝ) * (1 - 0)|) = (((-|d| : ℤ)) : ℝ) := by
      rw [sub_zero, mul_one, hε2, sub_self, sub_zero, hεd]
      push_cast
      ring
    have hlim : Tendsto (fun k : ℕ => (3 : ℝ) ^ ((ε : ℝ) * (1 - 1 / ((k : ℝ) + 1)) * d -
        (1 - |(ε : ℝ) * (1 - 1 / ((k : ℝ) + 1))|))) atTop (𝓝 ((3 : ℝ) ^ (((-|d| : ℤ)) : ℝ))) := by
      have h1 := (hg.tendsto 0).comp ht
      rw [hval] at h1
      exact tendsto_const_nhds.rpow h1 (Or.inl (by norm_num))
    rw [← Real.rpow_intCast]
    refine ge_of_tendsto' hlim fun k => ?_
    have h2 := h (r k) (hr k).1 (hr k).2
    rwa [hrs k] at h2
  rcases le_or_gt 0 d with hd0 | hd0
  · refine main (-1) (Or.inr rfl) ?_
    have : (0 : ℝ) ≤ d := by exact_mod_cast hd0
    rw [abs_of_nonneg this]
    push_cast
    ring
  · refine main 1 (Or.inl rfl) ?_
    have : (d : ℝ) < 0 := by exact_mod_cast hd0
    rw [abs_of_neg this]
    push_cast
    ring

/-- `|s| < 1` for `s = 3 - 6r`, `1/3 < r < 2/3`. -/
theorem abs_s_lt_one {r : ℚ} (hr1 : 1 / 3 < r) (hr2 : r < 2 / 3) : |3 - 6 * (r : ℝ)| < 1 := by
  have h1 : ((1 / 3 : ℚ) : ℝ) < r := Rat.cast_lt.mpr hr1
  have h2 : (r : ℝ) < ((2 / 3 : ℚ) : ℝ) := Rat.cast_lt.mpr hr2
  push_cast at h1 h2
  rw [abs_lt]
  constructor <;> linarith

/-- `u^(r) e_0 = 0`. -/
theorem Ur_unitSeq_zero (γ : K) : Ur γ (unitSeq 0) = 0 := by
  funext i
  show ∑ j ∈ Finset.Icc 1 (3 * i), γ ^ ((j : ℤ) - i) * (u i j : K) * unitSeq 0 j = 0
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj0 : j ≠ 0 := by
    have := (Finset.mem_Icc.1 hj).1
    omega
  simp [unitSeq, hj0]

end CalegariSlopes.Conj5
