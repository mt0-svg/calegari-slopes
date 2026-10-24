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
# From any radius below three to the null sequences (Section 6.4)

`norm_u_sq_le` (Lemma 3.1 (d)), `InS_Uop` (Lemma 6.5 (a)) and `isC0_of_InS` (Theorem 2.4 (c)).

Lemma 3.1 (d), `2 v_3(u_ij) ≥ 3 (i + j) - 2`, is proved by induction from the recurrence `F = N + (1 - Q) F`
(`CalegariSlopes.Newton.u_rec`) in the integer form `3 ^ ⌊(3 (i + j) - 1) / 2⌋ ∣ u_ij`.
-/

open PowerSeries Filter Topology
open CalegariSlopes.Overconvergent (K S0dag U3 genEig jinv jinvK)

namespace CalegariSlopes.Spectral

/-! ## Lemma 3.1 (d) -/

/-- `u_ij = 3 ^ ⌊(3 (i + j) - 1) / 2⌋ z` with `z ∈ ℤ`, i.e. `v_3(u_ij) ≥ (3 (i + j) - 2) / 2`. -/
theorem u_dvd_half (i j : ℕ) : ∃ z : ℤ, u i j = 3 ^ ((3 * (i + j) - 1) / 2) * z := by
  have hadd : ∀ {e : ℕ} {x y : ℚ}, (∃ z : ℤ, x = 3 ^ e * z) → (∃ z : ℤ, y = 3 ^ e * z) →
      ∃ z : ℤ, x + y = 3 ^ e * z := by
    rintro e x y ⟨z₁, rfl⟩ ⟨z₂, rfl⟩
    exact ⟨z₁ + z₂, by push_cast; ring⟩
  have hite : ∀ {e : ℕ} {p : Prop} [Decidable p] {x : ℚ}, (p → ∃ z : ℤ, x = 3 ^ e * z) →
      ∃ z : ℤ, (if p then x else 0) = 3 ^ e * z := by
    intro e p _ x h
    split_ifs with hp
    · exact h hp
    · exact ⟨0, by simp⟩
  have hmul : ∀ {e e₁ : ℕ} (k : ℕ) (c : ℤ) {x : ℚ}, (∃ z : ℤ, x = 3 ^ e₁ * z) → e ≤ k + e₁ →
      ∃ z : ℤ, (3 ^ k * (c : ℚ)) * x = 3 ^ e * z := by
    rintro e e₁ k c x ⟨z, rfl⟩ h
    refine ⟨3 ^ (k + e₁ - e) * c * z, ?_⟩
    have h3 : (3 : ℚ) ^ k * 3 ^ e₁ = 3 ^ e * 3 ^ (k + e₁ - e) := by
      rw [← pow_add, ← pow_add, Nat.add_sub_cancel' h]
    push_cast
    linear_combination ((c : ℚ) * z) * h3
  have hzero : ∀ {e : ℕ} {x : ℚ}, x = 0 → ∃ z : ℤ, x = 3 ^ e * z := by
    rintro e x rfl
    exact ⟨0, by simp⟩
  suffices H : ∀ s, ∀ i j, i + j = s → ∃ z : ℤ, u i j = 3 ^ ((3 * (i + j) - 1) / 2) * z from H _ i j rfl
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro i j hs
  rw [CalegariSlopes.Newton.u_rec i j]
  repeat' apply hadd
  -- the constant terms
  · exact hite fun ⟨h1, h2⟩ => ⟨10, by subst h1 h2; norm_num⟩
  · exact hite fun ⟨h1, h2⟩ => ⟨4, by subst h1 h2; norm_num⟩
  · exact hite fun ⟨h1, h2⟩ => ⟨8, by subst h1 h2; norm_num⟩
  · exact hite fun ⟨h1, h2⟩ => ⟨1, by subst h1 h2; norm_num⟩
  · exact hite fun ⟨h1, h2⟩ => ⟨2, by subst h1 h2; norm_num⟩
  · exact hite fun ⟨h1, h2⟩ => ⟨3, by subst h1 h2; norm_num⟩
  -- the recursive terms
  · refine hite fun ⟨hi, hj⟩ => ?_
    rcases Nat.lt_or_ge (i - 1) 1 with h1 | h1
    · exact hzero (by rw [show i - 1 = 0 by omega, CalegariSlopes.Newton.u_zero_left, mul_zero])
    rcases Nat.lt_or_ge (j - 1) 1 with h2 | h2
    · exact hzero (by rw [show j - 1 = 0 by omega, CalegariSlopes.Newton.u_zero_right, mul_zero])
    obtain ⟨w, hw⟩ := hmul 3 10 (ih _ (by omega) (i - 1) (j - 1) rfl)
      (e := (3 * (i + j) - 1) / 2) (by omega)
    exact ⟨w, by rw [← hw]; push_cast; ring⟩
  · refine hite fun ⟨hi, hj⟩ => ?_
    rcases Nat.lt_or_ge (i - 2) 1 with h1 | h1
    · exact hzero (by rw [show i - 2 = 0 by omega, CalegariSlopes.Newton.u_zero_left, mul_zero])
    rcases Nat.lt_or_ge (j - 1) 1 with h2 | h2
    · exact hzero (by rw [show j - 1 = 0 by omega, CalegariSlopes.Newton.u_zero_right, mul_zero])
    obtain ⟨w, hw⟩ := hmul 5 4 (ih _ (by omega) (i - 2) (j - 1) rfl)
      (e := (3 * (i + j) - 1) / 2) (by omega)
    exact ⟨w, by rw [← hw]; push_cast; ring⟩
  · refine hite fun ⟨hi, hj⟩ => ?_
    rcases Nat.lt_or_ge (i - 1) 1 with h1 | h1
    · exact hzero (by rw [show i - 1 = 0 by omega, CalegariSlopes.Newton.u_zero_left, mul_zero])
    rcases Nat.lt_or_ge (j - 2) 1 with h2 | h2
    · exact hzero (by rw [show j - 2 = 0 by omega, CalegariSlopes.Newton.u_zero_right, mul_zero])
    obtain ⟨w, hw⟩ := hmul 5 4 (ih _ (by omega) (i - 1) (j - 2) rfl)
      (e := (3 * (i + j) - 1) / 2) (by omega)
    exact ⟨w, by rw [← hw]; push_cast; ring⟩
  · refine hite fun ⟨hi, hj⟩ => ?_
    rcases Nat.lt_or_ge (i - 3) 1 with h1 | h1
    · exact hzero (by rw [show i - 3 = 0 by omega, CalegariSlopes.Newton.u_zero_left, mul_zero])
    rcases Nat.lt_or_ge (j - 1) 1 with h2 | h2
    · exact hzero (by rw [show j - 1 = 0 by omega, CalegariSlopes.Newton.u_zero_right, mul_zero])
    obtain ⟨w, hw⟩ := hmul 6 1 (ih _ (by omega) (i - 3) (j - 1) rfl)
      (e := (3 * (i + j) - 1) / 2) (by omega)
    exact ⟨w, by rw [← hw]; push_cast; ring⟩
  · refine hite fun ⟨hi, hj⟩ => ?_
    rcases Nat.lt_or_ge (i - 2) 1 with h1 | h1
    · exact hzero (by rw [show i - 2 = 0 by omega, CalegariSlopes.Newton.u_zero_left, mul_zero])
    rcases Nat.lt_or_ge (j - 2) 1 with h2 | h2
    · exact hzero (by rw [show j - 2 = 0 by omega, CalegariSlopes.Newton.u_zero_right, mul_zero])
    obtain ⟨w, hw⟩ := hmul 6 1 (ih _ (by omega) (i - 2) (j - 2) rfl)
      (e := (3 * (i + j) - 1) / 2) (by omega)
    exact ⟨w, by rw [← hw]; push_cast; ring⟩
  · refine hite fun ⟨hi, hj⟩ => ?_
    rcases Nat.lt_or_ge (i - 1) 1 with h1 | h1
    · exact hzero (by rw [show i - 1 = 0 by omega, CalegariSlopes.Newton.u_zero_left, mul_zero])
    rcases Nat.lt_or_ge (j - 3) 1 with h2 | h2
    · exact hzero (by rw [show j - 3 = 0 by omega, CalegariSlopes.Newton.u_zero_right, mul_zero])
    obtain ⟨w, hw⟩ := hmul 6 1 (ih _ (by omega) (i - 1) (j - 3) rfl)
      (e := (3 * (i + j) - 1) / 2) (by omega)
    exact ⟨w, by rw [← hw]; push_cast; ring⟩

/-- Lemma 3.1 (d): `2 v_3(u_ij) ≥ 3 (i + j) - 2`. -/
theorem norm_u_sq_le (i j : ℕ) : ‖(u i j : ℚ_[3])‖ ^ 2 ≤ (3 : ℝ) ^ (2 - 3 * ((i : ℤ) + j)) := by
  obtain ⟨z, hz⟩ := u_dvd_half i j
  have h3 : ‖(3 : ℚ_[3])‖ = 3⁻¹ := by
    have := Padic.norm_p (p := 3)
    simpa using this
  have h1 : ‖(u i j : ℚ_[3])‖ ≤ (3 : ℝ) ^ (-(((3 * (i + j) - 1) / 2 : ℕ) : ℤ)) := by
    rw [hz]
    push_cast
    rw [norm_mul, norm_pow, h3]
    calc ((3 : ℝ)⁻¹) ^ ((3 * (i + j) - 1) / 2) * ‖(z : ℚ_[3])‖
        ≤ ((3 : ℝ)⁻¹) ^ ((3 * (i + j) - 1) / 2) * 1 := by
          gcongr
          exact Padic.norm_int_le_one z
      _ = (3 : ℝ) ^ (-(((3 * (i + j) - 1) / 2 : ℕ) : ℤ)) := by
          rw [mul_one, zpow_neg, zpow_natCast, inv_pow]
  calc ‖(u i j : ℚ_[3])‖ ^ 2 ≤ ((3 : ℝ) ^ (-(((3 * (i + j) - 1) / 2 : ℕ) : ℤ))) ^ 2 := by
        gcongr
    _ = (3 : ℝ) ^ (-(((3 * (i + j) - 1) / 2 : ℕ) : ℤ) * 2) := by
        rw [← zpow_natCast, ← zpow_mul]
        norm_num
    _ ≤ (3 : ℝ) ^ (2 - 3 * ((i : ℤ) + j)) := by
        apply zpow_le_zpow_right₀ (by norm_num)
        omega

/-- Lemma 3.1 (d) in `K` with a real exponent: `‖u_ij‖ ≤ 3 ^ (1 - (3/2)(i + j))`. -/
theorem norm_u_le_rpow (i j : ℕ) : ‖(u i j : K)‖ ≤ (3 : ℝ) ^ (1 - 3 / 2 * ((i : ℝ) + j)) := by
  rw [norm_ratCast_K]
  have h := norm_u_sq_le i j
  have hy : (0 : ℝ) < (3 : ℝ) ^ (1 - 3 / 2 * ((i : ℝ) + j)) := by positivity
  have hsq : ((3 : ℝ) ^ (1 - 3 / 2 * ((i : ℝ) + j))) ^ 2 = (3 : ℝ) ^ (2 - 3 * ((i : ℤ) + j)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  rw [← hsq] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hy.le two_ne_zero).1 h

/-! ## Lemma 6.5 (a) -/

/-- Lemma 6.5 (a), pointwise: `v_3((U a)_i) + φ(s) i ≥ min_{i ≤ 3j} (v_3(a_j) + s j) - 1`. -/
theorem norm_Uop_le (s : ℝ) (a : ℕ → K) (i : ℕ) (r : ℝ) (hr0 : 0 ≤ r)
    (hr : ∀ j, i ≤ 3 * j → ‖a j‖ * (3 : ℝ) ^ (-(s * j)) ≤ r) :
    ‖Uop a i‖ * (3 : ℝ) ^ (-(phiS s * i)) ≤ 3 * r := by
  have hsum : ‖Uop a i‖ ≤ 3 * r * (3 : ℝ) ^ (phiS s * i) := by
    show ‖bact u a i‖ ≤ _
    apply norm_sum_le_of_le _ (by positivity)
    intro j hj
    simp only [Finset.mem_Icc] at hj
    by_cases h3 : 3 * j < i
    · rw [ADB.u_eq_zero_of_gt i j h3, Rat.cast_zero, zero_mul, norm_zero]
      positivity
    push Not at h3
    have hu := norm_u_le_rpow i j
    have ha := hr j h3
    have ha' : ‖a j‖ ≤ r * (3 : ℝ) ^ (s * j) := by
      rw [Real.rpow_neg (by norm_num), ← div_eq_mul_inv, div_le_iff₀ (by positivity)] at ha
      exact ha
    have hexp : 1 - 3 / 2 * ((i : ℝ) + j) + s * j ≤ 1 + phiS s * i := by
      have hφ1 : 3 * s - 6 ≤ phiS s := le_max_left _ _
      have hφ2 : s / 3 - 2 ≤ phiS s := le_max_right _ _
      have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      have hij : (i : ℝ) ≤ 3 * j := by exact_mod_cast h3
      have hji : (j : ℝ) ≤ 3 * i := by exact_mod_cast hj.2
      rcases le_or_gt (3 / 2) s with hs | hs
      · nlinarith [mul_nonneg (sub_nonneg.2 hs) (sub_nonneg.2 hji), mul_nonneg (sub_nonneg.2 hφ1) hi0]
      · nlinarith [mul_nonneg (sub_nonneg.2 hs.le) (sub_nonneg.2 hij), mul_nonneg (sub_nonneg.2 hφ2) hi0]
    calc ‖(u i j : K) * a j‖ = ‖(u i j : K)‖ * ‖a j‖ := norm_mul _ _
      _ ≤ (3 : ℝ) ^ (1 - 3 / 2 * ((i : ℝ) + j)) * (r * (3 : ℝ) ^ (s * j)) :=
          mul_le_mul hu ha' (norm_nonneg _) (by positivity)
      _ = r * (3 : ℝ) ^ (1 - 3 / 2 * ((i : ℝ) + j) + s * j) := by
          rw [Real.rpow_add (by norm_num)]
          ring
      _ ≤ r * (3 : ℝ) ^ (1 + phiS s * i) := by
          gcongr
          norm_num
      _ = 3 * r * (3 : ℝ) ^ (phiS s * i) := by
          rw [Real.rpow_add (by norm_num), Real.rpow_one]
          ring
  calc ‖Uop a i‖ * (3 : ℝ) ^ (-(phiS s * i)) ≤ 3 * r * (3 : ℝ) ^ (phiS s * i) * (3 : ℝ) ^ (-(phiS s * i)) := by
        gcongr
    _ = 3 * r := by
        rw [mul_assoc, ← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero, mul_one]

/-- Lemma 6.5 (a): `U` maps `S_s` into `S_{φ(s)}`. -/
theorem InS_Uop {s : ℝ} {a : ℕ → K} (ha : InS s a) : InS (phiS s) (Uop a) := by
  rw [InS] at ha ⊢
  rw [Metric.tendsto_atTop] at ha ⊢
  intro ε hε
  have hε3 : ε / 6 > 0 := by linarith
  rcases ha (ε / 6) hε3 with ⟨J, hJ⟩
  refine ⟨3 * J, fun i hi => ?_⟩
  have hi' : (3 : ℕ) * J ≤ i := by omega
  -- need to show dist (‖(Uop a) i‖ * (3 : ℝ) ^ (-(phiS s * i))) 0 < ε
  rw [Real.dist_eq, sub_zero]
  have h_nonneg : 0 ≤ ‖(Uop a) i‖ * (3 : ℝ) ^ (-(phiS s * i)) := by
    positivity
  rw [abs_of_nonneg h_nonneg]
  -- Now we need ‖(Uop a) i‖ * (3 : ℝ) ^ (-(phiS s * i)) < ε
  -- Use norm_Uop_le
  have hbound := norm_Uop_le s a i (ε / 6) (by positivity) (fun j hj => ?_)
  · -- hbound gives ‖Uop a i‖ * (3 : ℝ) ^ (-(phiS s * i)) ≤ 3 * (ε / 6) = ε / 2
    have : 3 * (ε / 6) = ε / 2 := by ring
    rw [this] at hbound
    linarith
  · -- need to show: if i ≤ 3*j then ‖a j‖ * (3 : ℝ) ^ (-(s * j)) ≤ ε/6
    -- From hi: 3*J ≤ i, so J ≤ i/3
    -- If i ≤ 3*j, then j ≥ i/3 ≥ J
    -- So j ≥ J, and hJ gives the bound
    have hj' : J ≤ j := by
      have : i ≤ 3 * j := hj
      omega
    have h := hJ j hj'
    -- h : dist (‖a j‖ * (3 : ℝ) ^ (-(s * j))) 0 < ε / 6
    rw [Real.dist_eq, sub_zero] at h
    have h_nonneg_j : 0 ≤ ‖a j‖ * (3 : ℝ) ^ (-(s * j)) := by positivity
    rw [abs_of_nonneg h_nonneg_j] at h
    exact h.le

/-- `S_t` is stable under `U` for `t ∈ (-3, 3)` (`φ(t) ≤ t`). -/
theorem InS_Uop_self {t : ℝ} (h1 : -3 < t) (h2 : t < 3) {a : ℕ → K} (ha : InS t a) : InS t (Uop a) := by
  exact
    InS.mono (phiS_lt h1 h2).le (InS_Uop ha)

/-- `S_t` is stable under the powers of `U` for `t ∈ (-3, 3)`. -/
theorem InS_Uop_pow {t : ℝ} (h1 : -3 < t) (h2 : t < 3) {a : ℕ → K} (ha : InS t a) (m : ℕ) :
    InS t ((Uop ^ m) a) := by
  induction' m with m ih
  · simpa using ha
  · rw [pow_succ']
    simpa using InS_Uop_self h1 h2 ih

/-! ## Theorem 2.4 (c) -/

/-- `(U - μ) ^ k = (-μ) ^ k + U Q(U)` with `Q(U) = Σ_{m < k} C(k, m + 1) (-μ) ^ (k - m - 1) U ^ m`. -/
theorem iterate_sub_eq (μ : K) (k : ℕ) (a : ℕ → K) :
    ((Uop - μ • (1 : Module.End K (ℕ → K))) ^ k) a =
      (-μ) ^ k • a + Uop (∑ m ∈ Finset.range k, ((k.choose (m + 1) : K) * (-μ) ^ (k - (m + 1))) • (Uop ^ m) a) := by
  have hc : Commute Uop ((-μ) • (1 : Module.End K (ℕ → K))) := (Commute.one_right Uop).smul_right (-μ)
  have hsub : Uop - μ • (1 : Module.End K (ℕ → K)) = Uop + (-μ) • 1 := by
    rw [sub_eq_add_neg]
    congr 1
    exact (neg_smul μ 1).symm
  have hpow : (Uop - μ • (1 : Module.End K (ℕ → K))) ^ k =
      ∑ m ∈ Finset.range (k + 1), ((k.choose m : K) * (-μ) ^ (k - m)) • Uop ^ m := by
    rw [hsub, hc.add_pow]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_pow, one_pow, mul_smul_comm, mul_one, ← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul K,
      smul_smul]
  rw [hpow, Finset.sum_range_succ', LinearMap.add_apply, add_comm]
  congr 1
  · simp
  · rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul, LinearMap.smul_apply, pow_succ', Module.End.mul_apply]

/-- A generalized eigenvector for `μ ≠ 0` is `U h` with `h` in every `S_t`, `t ∈ (-3, 3)`, that holds it. -/
theorem exists_eq_Uop {μ : K} (hμ : μ ≠ 0) {k : ℕ} {a : ℕ → K}
    (hk : ((Uop - μ • (1 : Module.End K (ℕ → K))) ^ k) a = 0) :
    ∃ h : ℕ → K, a = Uop h ∧ ∀ t : ℝ, -3 < t → t < 3 → InS t a → InS t h := by
  have h_iter := iterate_sub_eq μ k a
  rw [hk] at h_iter
  set Q := ∑ m ∈ Finset.range k, ((k.choose (m + 1) : K) * (-μ) ^ (k - (m + 1))) • (Uop ^ m) a with hQ
  have h_eq : (-μ) ^ k • a + Uop Q = 0 := by
    calc
      (-μ) ^ k • a + Uop Q = ((Uop - μ • (1 : Module.End K (ℕ → K))) ^ k) a := by rw [iterate_sub_eq]
      _ = 0 := hk
  have hμ_pow_ne_zero : (-μ) ^ k ≠ 0 :=
    pow_ne_zero k (neg_ne_zero.mpr hμ)
  have hUopQ : Uop Q = -((-μ) ^ k • a) :=
    eq_neg_of_add_eq_zero_right h_eq
  set h := -(((-μ) ^ k)⁻¹) • Q with hh
  have ha_eq_Uop_h : a = Uop h := by
    calc
      a = (1 : K) • a := by simp
      _ = (((-μ) ^ k)⁻¹ * (-μ) ^ k) • a := by
        field_simp [hμ_pow_ne_zero]
      _ = ((-μ) ^ k)⁻¹ • ((-μ) ^ k • a) := by simp [mul_smul]
      _ = ((-μ) ^ k)⁻¹ • (-Uop Q) := by
        rw [hUopQ]
        simp
      _ = -(((-μ) ^ k)⁻¹) • Uop Q := by simp [neg_smul]
      _ = Uop (-(((-μ) ^ k)⁻¹) • Q) := by
        rw [← Uop.map_smul]
      _ = Uop h := by rw [hh]
  refine ⟨h, ha_eq_Uop_h, ?_⟩
  intro t ht1 ht2 ha_t
  rw [hh]
  have hQ_InS : InS t Q := by
    rw [hQ]
    apply InS.sum (Finset.range k)
    intro m hm
    apply InS.smul ((k.choose (m + 1) : K) * (-μ) ^ (k - (m + 1)))
    exact InS_Uop_pow ht1 ht2 ha_t m
  apply InS.smul (-(((-μ) ^ k)⁻¹))
  exact hQ_InS

/-- Theorem 2.4 (c). -/
theorem isC0_of_InS {s : ℝ} (hs : s < 3) {a : ℕ → K} (ha : InS s a) {μ : K} (hμ : μ ≠ 0) {k : ℕ}
    (hk : ((Uop - μ • (1 : Module.End K (ℕ → K))) ^ k) a = 0) : IsC0 a := by
  set t₀ := max s (-2) with ht₀
  have ht₀_low : -3 < t₀ := by
    rw [ht₀]
    exact lt_of_lt_of_le (by norm_num : (-3 : ℝ) < -2) (le_max_right _ _)
  have ht₀_high : t₀ < 3 := by
    rw [ht₀]
    exact max_lt hs (by norm_num : (-2 : ℝ) < 3)
  have ht₀_InS : InS t₀ a := InS.mono (le_max_left _ _) ha
  rcases exists_eq_Uop hμ hk with ⟨h, ha_eq_Uop_h, hprop⟩
  have h_induction : ∀ m : ℕ, ∀ t : ℝ, -3 < t → t < 3 → InS t a → InS (phiS^[m] t) a := by
    intro m
    induction' m with m ih
    · intro t _ _ ha_t
      simpa using ha_t
    · intro t ht_low ht_high ha_t
      have h_phi_low : -3 < phiS t := phiS_gt ht_low ht_high
      have h_phi_high : phiS t < 3 := lt_trans (phiS_lt ht_low ht_high) ht_high
      have h_InS_h : InS t h := hprop t ht_low ht_high ha_t
      have h_InS_phi : InS (phiS t) a := by
        have := InS_Uop h_InS_h
        rwa [ha_eq_Uop_h]
      rw [Function.iterate_succ_apply]
      exact ih (phiS t) h_phi_low h_phi_high h_InS_phi
  rcases exists_iterate_phiS_nonpos ht₀_low ht₀_high with ⟨m, hm⟩
  have h_InS_iter : InS (phiS^[m] t₀) a := h_induction m t₀ ht₀_low ht₀_high ht₀_InS
  have h_InS_zero : InS 0 a := InS.mono hm h_InS_iter
  exact (InS_zero_iff _).mp h_InS_zero

end CalegariSlopes.Spectral
