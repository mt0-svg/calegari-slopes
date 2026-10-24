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
# The q-series space (Proposition 2.2, Section 4.5)

`coeff_G_of_JHyp`, `Phi_eq_zero`, `U3_Phi` (Proposition 2.2 (i)) and `BR1`, `BR2` (Proposition 2.2 (ii), (iii)).

Proposition 2.2 (ii), (iii) without power series reversion. (J) says `27 jinv = G R(G)` with
`R = ((1 + X) (1 + 9 X) ^ 3)⁻¹` (`Rser`, integral). So `(27 jinv) ^ m = Σ_j r_{m,j} G ^ j` coefficientwise,
`r_{m,j} = [X ^ j] X ^ m R ^ m` (`rmat`), a unitriangular integral matrix (`PowerSeries.subst`); its inverse `γ` is
unitriangular and integral, and `G ^ j = Σ_m γ_{j,m} (27 jinv) ^ m`.
-/

open PowerSeries Filter Topology
open CalegariSlopes.Overconvergent (K S0dag U3 genEig jinv jinvK IsOverconvergent)

namespace CalegariSlopes.Spectral

/-! ## `G = 27 q + O(q ^ 2)` and the injectivity of `Φ` -/

/-- `jinv = q + O(q ^ 2)`. -/
theorem coeff_jinv_zero_one : coeff 0 jinv = 0 ∧ coeff 1 jinv = 1 := by
  have s3 : ArithmeticFunction.sigma 3 1 = 1 := by
    simp only [ArithmeticFunction.sigma_apply]; decide
  have s5 : ArithmeticFunction.sigma 5 1 = 1 := by
    simp only [ArithmeticFunction.sigma_apply]; decide
  have e0 : coeff 0 Overconvergent.E4q = 1 := by simp [Overconvergent.E4q]
  have e1 : coeff 1 Overconvergent.E4q = 240 := by simp [Overconvergent.E4q, s3]
  have f0 : coeff 0 Overconvergent.E6q = 1 := by simp [Overconvergent.E6q]
  have f1 : coeff 1 Overconvergent.E6q = -504 := by simp [Overconvergent.E6q, s5]
  have a0 : coeff 0 (Overconvergent.E4q ^ 3) = 1 ∧ coeff 1 (Overconvergent.E4q ^ 3) = 720 := by
    simp only [pow_succ, pow_zero, one_mul, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [e0, e1]
  have b0 : coeff 0 (Overconvergent.E6q ^ 2) = 1 ∧ coeff 1 (Overconvergent.E6q ^ 2) = -1008 := by
    simp only [pow_succ, pow_zero, one_mul, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [f0, f1]
  have d0 : coeff 0 Overconvergent.Dq = 0 ∧ coeff 1 Overconvergent.Dq = 1 := by
    simp only [Overconvergent.Dq, coeff_smul, map_sub, a0.1, a0.2, b0.1, b0.2, smul_eq_mul]
    norm_num
  have hc : constantCoeff (Overconvergent.E4q ^ 3) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply]; exact a0.1
  have hm : Overconvergent.E4q ^ 3 * jinv = Overconvergent.Dq := by
    rw [Overconvergent.jinv, mul_comm Overconvergent.Dq, ← mul_assoc,
      PowerSeries.mul_inv_cancel _ (by rw [hc]; norm_num), one_mul]
  have h : ∀ n, coeff n (Overconvergent.E4q ^ 3 * jinv) = coeff n Overconvergent.Dq := fun n => by rw [hm]
  have h0 := h 0
  have h1 := h 1
  simp only [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_zero, a0.1, a0.2, d0.1, d0.2] at h0 h1
  norm_num at h0 h1
  have j0 : coeff 0 jinv = 0 := by rw [coeff_zero_eq_constantCoeff_apply]; exact h0
  refine ⟨j0, ?_⟩
  linear_combination h1 - 720 * h0

/-- (J) gives `G = 27 q + O(q ^ 2)`. -/
theorem coeff_G_of_JHyp {G : PowerSeries ℚ} (hJ : JHyp G) : coeff 0 G = 0 ∧ coeff 1 G = 27 := by
  rcases coeff_jinv_zero_one with ⟨h0j, h1j⟩
  set P := 27 * (1 + G) * (1 + 9 * G) ^ 3 with hP
  have hGP : jinv * P = G := hJ
  have h0G : coeff 0 G = 0 := by
    rw [← hGP]
    simp [coeff_mul, h0j]
  have hconstG : constantCoeff G = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, h0G]
  have hcoeff0P : coeff 0 P = 27 := by
    rw [hP]
    simp [coeff_zero_eq_constantCoeff_apply, map_mul, map_add, map_pow, map_one, map_ofNat, hconstG]
  have h1G : coeff 1 G = 27 := by
    rw [← hGP]
    simp [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
      h0j, h1j, hcoeff0P]
  exact ⟨h0G, h1G⟩

/-- `[q ^ N] U_3 F = [q ^ {3N}] F`. -/
theorem coeff_U3 (F : PowerSeries K) (N : ℕ) : coeff N (U3 F) = coeff (3 * N) F := by
  simp [U3]

/-- `[q ^ N] Φ(a) = Σ_{1 ≤ j ≤ N} a_j [q ^ N] G ^ j`. -/
theorem coeff_Phi (G : PowerSeries ℚ) (a : ℕ → K) (N : ℕ) :
    coeff N (Phi G a) = ∑ j ∈ Finset.Icc 1 N, a j * coeff N (GK G ^ j) := by
  simp [Phi]

/-- `[q ^ N] G ^ j` over `K` is the image of the rational coefficient. -/
theorem coeff_GK_pow (G : PowerSeries ℚ) (j N : ℕ) : coeff N (GK G ^ j) = ((coeff N (G ^ j) : ℚ) : K) := by
  have h : GK G ^ j = PowerSeries.map (algebraMap ℚ K) (G ^ j) := by
    calc
      GK G ^ j = (PowerSeries.map (algebraMap ℚ K) G) ^ j := rfl
      _ = PowerSeries.map (algebraMap ℚ K) (G ^ j) := by rw [map_pow]
  rw [h, coeff_map]
  simp

/-- `[q ^ N] jinv ^ m` over `K` is the image of the rational coefficient. -/
theorem coeff_jinvK_pow (m N : ℕ) : coeff N (jinvK ^ m) = ((coeff N (jinv ^ m) : ℚ) : K) := by
  dsimp [jinvK]
  rw [← RingHom.map_pow (PowerSeries.map (algebraMap ℚ K)) jinv m, PowerSeries.coeff_map]
  rfl

/-- `[q ^ N] G ^ j = 0` for `N < j` when `G = O(q)`. -/
theorem coeff_pow_of_lt {G : PowerSeries ℚ} (h0 : coeff 0 G = 0) {N j : ℕ} (h : N < j) :
    coeff N (G ^ j) = 0 := by
  have hX_dvd : PowerSeries.X ∣ G := (PowerSeries.X_dvd_iff).mpr (by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    exact h0)
  have hXj_dvd : PowerSeries.X ^ j ∣ G ^ j := pow_dvd_pow_of_dvd hX_dvd j
  have h_all : ∀ m < j, coeff m (G ^ j) = 0 := ((PowerSeries.X_pow_dvd_iff).mp hXj_dvd)
  exact h_all N h

/-- `[q ^ N] G ^ j = 0` for `N < j` when `G = O(q)`, over `K`. -/
theorem coeff_GK_pow_of_lt {G : PowerSeries ℚ} (h0 : coeff 0 G = 0) {N j : ℕ} (h : N < j) :
    coeff N (GK G ^ j) = 0 := by
  rw [coeff_GK_pow, coeff_pow_of_lt h0 h]
  simp

/-- `[q ^ N] G ^ j` over `K` is the image of the rational coefficient. -/
theorem coeff_GK_pow_self_aux_coeff_GK_pow (G : PowerSeries ℚ) (j N : ℕ) : coeff N (CalegariSlopes.Spectral.GK G ^ j) = ((coeff N (G ^ j) : ℚ) : K) := by
  dsimp [CalegariSlopes.Spectral.GK]
  rw [← map_pow (PowerSeries.map (algebraMap ℚ K)) G j, PowerSeries.coeff_map]
  rfl

/-- `[q ^ j] G ^ j = ([q] G) ^ j` when `G = O(q)`. -/
theorem coeff_GK_pow_self {G : PowerSeries ℚ} (h0 : coeff 0 G = 0) (j : ℕ) :
    coeff j (GK G ^ j) = ((coeff 1 G : ℚ) : K) ^ j := by
  rw [coeff_GK_pow_self_aux_coeff_GK_pow]
  rw [← Rat.cast_pow]
  congr 1
  have hX_dvd : X ∣ G := by
    rw [PowerSeries.X_dvd_iff]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
  rcases hX_dvd with ⟨H, hG⟩
  rw [hG]
  rw [mul_pow]
  rw [PowerSeries.coeff_X_pow_mul']
  simp

/-- `Φ` is injective on the coordinates `j ≥ 1`. -/
theorem Phi_eq_zero {G : PowerSeries ℚ} (h0 : coeff 0 G = 0) (h1 : coeff 1 G ≠ 0) {a : ℕ → K}
    (h : Phi G a = 0) : ∀ j, 1 ≤ j → a j = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj
  have hc := congrArg (coeff j) h
  rw [coeff_Phi, map_zero, Finset.sum_eq_single j] at hc
  · rw [coeff_GK_pow_self h0] at hc
    have hne : ((coeff 1 G : ℚ) : K) ^ j ≠ 0 := pow_ne_zero _ (Rat.cast_ne_zero.2 h1)
    exact (mul_eq_zero.1 hc).resolve_right hne
  · intro i hi hij
    simp only [Finset.mem_Icc] at hi
    rw [ih i (by omega) hi.1, zero_mul]
  · intro hj'
    exact absurd (Finset.mem_Icc.2 ⟨hj, le_rfl⟩) hj'

/-! ## Proposition 2.2 (i) -/

/-- (C4) on coefficients, over `K`: `[q ^ {3N}] G ^ j = Σ_{1 ≤ i ≤ 3j} u_ij [q ^ N] G ^ i`, `j ≥ 1`. -/
theorem coeff_three_mul_GK_pow {G : PowerSeries ℚ} (hC4 : C4 G) {j : ℕ} (hj : 1 ≤ j) (N : ℕ) :
    coeff (3 * N) (GK G ^ j) = ∑ i ∈ Finset.Icc 1 (3 * j), (u i j : K) * coeff N (GK G ^ i) := by
  have h := congrArg (coeff N) (hC4 j hj)
  simp only [U3Q, coeff_mk, map_sum, PowerSeries.coeff_smul, smul_eq_mul] at h
  rw [coeff_GK_pow, h, Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Rat.cast_mul, coeff_GK_pow]

/-- Proposition 2.2 (i): `U_3 Φ(a) = Φ(U a)`, from (C4). -/
theorem U3_Phi {G : PowerSeries ℚ} (hC4 : C4 G) (h0 : coeff 0 G = 0) (a : ℕ → K) :
    U3 (Phi G a) = Phi G (Uop a) := by
  ext N
  have hL : coeff N (U3 (Phi G a)) =
      ∑ j ∈ Finset.Icc 1 (3 * N), a j * coeff (3 * N) (GK G ^ j) := by
    rw [coeff_U3, coeff_Phi]
  have hR : coeff N (Phi G (Uop a)) = ∑ i ∈ Finset.Icc 1 N,
      (∑ j ∈ Finset.Icc 1 (3 * i), (u i j : K) * a j) * coeff N (GK G ^ i) := by
    rw [coeff_Phi]
    rfl
  have hL2 : ∑ j ∈ Finset.Icc 1 (3 * N), a j * coeff (3 * N) (GK G ^ j) =
      ∑ j ∈ Finset.Icc 1 (3 * N), ∑ i ∈ Finset.Icc 1 N, (u i j : K) * a j * coeff N (GK G ^ i) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
    rw [coeff_three_mul_GK_pow hC4 hj1 N, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i _ => (by ring : a j * ((u i j : K) * coeff N (GK G ^ i)) =
      (u i j : K) * a j * coeff N (GK G ^ i))]
    rw [Finset.sum_subset (s₂ := Finset.Icc 1 (3 * j + N))
      (by intro i hi; simp only [Finset.mem_Icc] at hi ⊢; omega)
      (by
        intro i hi hi'
        simp only [Finset.mem_Icc, not_and, not_le] at hi hi'
        rw [ADB.u_eq_zero_of_gt i j (hi' hi.1)]
        simp)]
    symm
    apply Finset.sum_subset (by intro i hi; simp only [Finset.mem_Icc] at hi ⊢; omega)
    intro i hi hi'
    simp only [Finset.mem_Icc, not_and, not_le] at hi hi'
    rw [coeff_GK_pow_of_lt h0 (hi' hi.1)]
    simp
  have hR2 : ∑ i ∈ Finset.Icc 1 N, (∑ j ∈ Finset.Icc 1 (3 * i), (u i j : K) * a j) *
      coeff N (GK G ^ i) =
      ∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 (3 * N), (u i j : K) * a j * coeff N (GK G ^ i) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_Icc] at hi
    rw [Finset.sum_mul]
    apply Finset.sum_subset (by intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega)
    intro j hj hj'
    simp only [Finset.mem_Icc, not_and, not_le] at hj hj'
    rw [u_eq_zero_of_lt hi.1 (hj' hj.1)]
    simp
  rw [hL, hR, hL2, hR2, Finset.sum_comm]

/-! ## The change of basis between `G ^ j` and `(27 jinv) ^ m` -/

/-- `R(X) = ((1 + X) (1 + 9 X) ^ 3)⁻¹`. -/
noncomputable def Rser : PowerSeries ℚ := ((1 + X) * (1 + 9 * X) ^ 3)⁻¹

/-- `r_{m,j} = [X ^ j] X ^ m R(X) ^ m`. -/
noncomputable def rmat (m j : ℕ) : ℚ := coeff j (X ^ m * Rser ^ m)

/-- `R` has integer coefficients. -/
theorem Rser_integral : ∃ g : PowerSeries ℤ, Rser = PowerSeries.map (Int.castRingHom ℚ) g := by
  have hP : constantCoeff ((1 + X) * (1 + 9 * X) ^ 3 : PowerSeries ℤ) = ((1 : ℤˣ) : ℤ) := by simp
  refine ⟨PowerSeries.invOfUnit ((1 + X) * (1 + 9 * X) ^ 3) 1, ?_⟩
  have h1 := PowerSeries.mul_invOfUnit ((1 + X) * (1 + 9 * X) ^ 3 : PowerSeries ℤ) 1 hP
  have h3 := congrArg (PowerSeries.map (Int.castRingHom ℚ)) h1
  rw [map_mul, map_one, map_mul, map_pow, map_add, map_add, map_one, map_mul, PowerSeries.map_X,
    map_ofNat] at h3
  rw [Rser]
  symm
  exact (PowerSeries.eq_inv_iff_mul_eq_one (by simp)).2 (by rw [mul_comm]; exact h3)

/-- `r_{m,j}` is an integer. -/
theorem rmat_integral (m j : ℕ) : ∃ z : ℤ, rmat m j = z := by
  obtain ⟨g, hg⟩ := Rser_integral
  refine ⟨coeff j (X ^ m * g ^ m), ?_⟩
  have h : (X : PowerSeries ℚ) ^ m * Rser ^ m = PowerSeries.map (Int.castRingHom ℚ) (X ^ m * g ^ m) := by
    rw [hg, map_mul, map_pow, map_pow, PowerSeries.map_X]
  rw [rmat, h, PowerSeries.coeff_map]
  simp

theorem norm_rmat_le (m j : ℕ) : ‖(rmat m j : ℚ_[3])‖ ≤ 1 := by
  obtain ⟨z, hz⟩ := rmat_integral m j
  rw [hz, Rat.cast_intCast]
  exact Padic.norm_int_le_one z

theorem rmat_eq_zero_of_lt {m j : ℕ} (h : j < m) : rmat m j = 0 := by
  rw [rmat, coeff_X_pow_mul']
  split_ifs with h'
  · omega
  · rfl

theorem rmat_self (m : ℕ) : rmat m m = 1 := by
  rw [rmat, coeff_X_pow_mul']
  simp [Rser, coeff_zero_eq_constantCoeff_apply]

/-- `G = O(q)` can be substituted. -/
theorem hasSubst_of_coeff_zero {G : PowerSeries ℚ} (h0 : coeff 0 G = 0) : PowerSeries.HasSubst G :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (by rwa [← coeff_zero_eq_constantCoeff_apply])

/-- `(1 + G) (1 + 9 G) ^ 3 = 1 + O(q)` when `G = O(q)`. -/
theorem constantCoeff_P {G : PowerSeries ℚ} (h0 : coeff 0 G = 0) :
    constantCoeff ((1 + G) * (1 + 9 * G) ^ 3) = 1 := by
  rw [coeff_zero_eq_constantCoeff_apply] at h0
  simp [h0]

/-- The coefficients of a substitution `f(G)`, `G = O(q)`: `[q ^ N] f(G) = Σ_{j ≤ N} [X ^ j] f [q ^ N] G ^ j`. -/
theorem coeff_subst_eq {G : PowerSeries ℚ} (h0 : coeff 0 G = 0) (f : PowerSeries ℚ) (N : ℕ) :
    coeff N (PowerSeries.subst G f) = ∑ j ∈ Finset.range (N + 1), coeff j f * coeff N (G ^ j) := by
  rw [PowerSeries.coeff_subst' (hasSubst_of_coeff_zero h0) f N,
    finsum_eq_sum_of_support_subset _ (s := Finset.range (N + 1))]
  · simp only [smul_eq_mul]
  · intro j hj
    rw [Function.mem_support] at hj
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hj
    rw [coeff_pow_of_lt h0 (by omega), smul_zero]

/-- `R(G) = ((1 + G) (1 + 9 G) ^ 3)⁻¹`. -/
theorem subst_Rser {G : PowerSeries ℚ} (h0 : coeff 0 G = 0) :
    PowerSeries.subst G Rser = ((1 + G) * (1 + 9 * G) ^ 3)⁻¹ := by
  have hG := hasSubst_of_coeff_zero h0
  have hP : constantCoeff ((1 + X) * (1 + 9 * X) ^ 3 : PowerSeries ℚ) = 1 := by simp
  have hR : Rser * ((1 + X) * (1 + 9 * X) ^ 3) = 1 :=
    PowerSeries.inv_mul_cancel _ (by rw [hP]; exact one_ne_zero)
  have hS : PowerSeries.subst G Rser * ((1 + G) * (1 + 9 * G) ^ 3) = 1 := by
    have h := congrArg (PowerSeries.substAlgHom hG) hR
    rw [map_mul, map_one, map_mul, map_pow, map_add, map_add, map_one, map_mul,
      PowerSeries.substAlgHom_X hG, map_ofNat, PowerSeries.coe_substAlgHom] at h
    exact h
  exact (PowerSeries.eq_inv_iff_mul_eq_one (by rw [constantCoeff_P h0]; exact one_ne_zero)).2 hS

/-- (J) as `27 jinv = G R(G)`. -/
theorem twentyseven_jinv {G : PowerSeries ℚ} (hJ : JHyp G) :
    27 * jinv = G * ((1 + G) * (1 + 9 * G) ^ 3)⁻¹ := by
  have h0 := (coeff_G_of_JHyp hJ).1
  have hQ : constantCoeff ((1 + G) * (1 + 9 * G) ^ 3) ≠ 0 := by
    rw [constantCoeff_P h0]; exact one_ne_zero
  have h1 : (27 * jinv) * ((1 + G) * (1 + 9 * G) ^ 3) = G := by
    rw [show (27 * jinv) * ((1 + G) * (1 + 9 * G) ^ 3) = jinv * (27 * (1 + G) * (1 + 9 * G) ^ 3) by ring]
    exact hJ
  calc 27 * jinv = 27 * jinv * (((1 + G) * (1 + 9 * G) ^ 3) * ((1 + G) * (1 + 9 * G) ^ 3)⁻¹) := by
        rw [PowerSeries.mul_inv_cancel _ hQ, mul_one]
    _ = G * ((1 + G) * (1 + 9 * G) ^ 3)⁻¹ := by rw [← mul_assoc, h1]

/-- `(27 jinv) ^ m = Σ_j r_{m,j} G ^ j`, coefficientwise. -/
theorem coeff_jinv_pow {G : PowerSeries ℚ} (hJ : JHyp G) (m N : ℕ) :
    27 ^ m * coeff N (jinv ^ m) = ∑ j ∈ Finset.range (N + 1), rmat m j * coeff N (G ^ j) := by
  have h0 := (coeff_G_of_JHyp hJ).1
  have hG := hasSubst_of_coeff_zero h0
  have h1 : 27 * jinv = PowerSeries.subst G (X * Rser) := by
    rw [twentyseven_jinv hJ, PowerSeries.subst_mul hG, PowerSeries.subst_X hG, subst_Rser h0]
  have h2 : (27 * jinv) ^ m = PowerSeries.subst G (X ^ m * Rser ^ m) := by
    rw [h1, ← PowerSeries.subst_pow hG, mul_pow]
  have h3 : coeff N ((27 * jinv) ^ m) = 27 ^ m * coeff N (jinv ^ m) := by
    rw [mul_pow, ← map_ofNat (C (R := ℚ)) 27, ← map_pow, coeff_C_mul]
  rw [← h3, h2, coeff_subst_eq h0]
  rfl

/-- Row `j` of the inverse of a unitriangular matrix `r`: `γ_jk = 0` for `k < j`, `γ_jj = 1`,
`γ_jk = -Σ_{j ≤ m < k} γ_jm r_mk` for `k > j`. -/
noncomputable def invUT (r : ℕ → ℕ → ℚ) (j k : ℕ) : ℚ :=
  if k < j then 0 else if k = j then 1 else
    -∑ m ∈ (Finset.Ico j k).attach, invUT r j m.1 * r m.1 k
termination_by k
decreasing_by exact (Finset.mem_Ico.1 m.2).2

theorem invUT_of_lt (r : ℕ → ℕ → ℚ) {j k : ℕ} (h : k < j) : invUT r j k = 0 := by
  rw [invUT, if_pos h]

theorem invUT_self (r : ℕ → ℕ → ℚ) (j : ℕ) : invUT r j j = 1 := by
  rw [invUT, if_neg (lt_irrefl j), if_pos rfl]

theorem invUT_of_gt (r : ℕ → ℕ → ℚ) {j k : ℕ} (h : j < k) :
    invUT r j k = -∑ m ∈ Finset.Ico j k, invUT r j m * r m k := by
  rw [invUT, if_neg (by omega), if_neg (by omega),
    Finset.sum_attach (Finset.Ico j k) (fun m => invUT r j m * r m k)]

/-- `γ r = 1`. -/
theorem sum_invUT_mul (r : ℕ → ℕ → ℚ) (hr1 : ∀ m, r m m = 1) (j k : ℕ) :
    ∑ m ∈ Finset.range (k + 1), invUT r j m * r m k = if j = k then 1 else 0 := by
  rcases lt_trichotomy k j with h | rfl | h
  · simp only [show j ≠ k by omega, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro m hm
    rw [invUT_of_lt r (by simp only [Finset.mem_range] at hm; omega), zero_mul]
  · rw [Finset.sum_range_succ, invUT_self, hr1, mul_one,
      Finset.sum_eq_zero (fun m hm => by
        rw [invUT_of_lt r (by simp only [Finset.mem_range] at hm; omega), zero_mul])]
    simp
  · rw [Finset.sum_range_succ, hr1, mul_one, invUT_of_gt r h]
    have hs : ∑ m ∈ Finset.range k, invUT r j m * r m k =
        ∑ m ∈ Finset.Ico j k, invUT r j m * r m k := by
      rw [Finset.range_eq_Ico]
      symm
      apply Finset.sum_subset (Finset.Ico_subset_Ico_left (Nat.zero_le j))
      intro m hm hm'
      simp only [Finset.mem_Ico, not_and, not_lt] at hm hm'
      rw [invUT_of_lt r (by by_contra hc; exact absurd (hm' (by omega)) (by omega)), zero_mul]
    rw [hs]
    simp [show j ≠ k by omega]

/-- `γ` is integral when `r` is. -/
theorem norm_invUT_le (r : ℕ → ℕ → ℚ) (hrint : ∀ m j, ‖(r m j : ℚ_[3])‖ ≤ 1) (j k : ℕ) :
    ‖(invUT r j k : ℚ_[3])‖ ≤ 1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases lt_trichotomy k j with h | rfl | h
  · rw [invUT_of_lt r h]
    simp
  · rw [invUT_self]
    simp
  · rw [invUT_of_gt r h, Rat.cast_neg, norm_neg, Rat.cast_sum]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro m hm
    rw [Rat.cast_mul, norm_mul]
    exact (mul_le_mul (ih m (Finset.mem_Ico.1 hm).2) (hrint m k) (norm_nonneg _) zero_le_one).trans
      (by norm_num)

/-- The inverse of a unitriangular integral matrix is unitriangular and integral. -/
theorem exists_inverse_unitriangular (r : ℕ → ℕ → ℚ) (hr0 : ∀ m j, j < m → r m j = 0) (hr1 : ∀ m, r m m = 1)
    (hrint : ∀ m j, ‖(r m j : ℚ_[3])‖ ≤ 1) :
    ∃ γ : ℕ → ℕ → ℚ, (∀ j m, m < j → γ j m = 0) ∧ (∀ j m, ‖(γ j m : ℚ_[3])‖ ≤ 1) ∧
      ∀ j k, ∑ m ∈ Finset.range (k + 1), γ j m * r m k = if j = k then 1 else 0 :=
  ⟨invUT r, fun _ _ h => invUT_of_lt r h, norm_invUT_le r hrint, sum_invUT_mul r hr1⟩

/-- `G ^ j = Σ_m γ_{j,m} (27 jinv) ^ m`, coefficientwise, with `γ` unitriangular and integral. -/
theorem exists_Gpow_expand {G : PowerSeries ℚ} (hJ : JHyp G) :
    ∃ γ : ℕ → ℕ → ℚ, (∀ j m, m < j → γ j m = 0) ∧ (∀ j m, ‖(γ j m : ℚ_[3])‖ ≤ 1) ∧
      ∀ j N, coeff N (G ^ j) = ∑ m ∈ Finset.range (N + 1), γ j m * 27 ^ m * coeff N (jinv ^ m) := by
  obtain ⟨γ, hγ0, hγ1, hγ⟩ := exists_inverse_unitriangular rmat (fun m j h => rmat_eq_zero_of_lt h)
    rmat_self norm_rmat_le
  refine ⟨γ, hγ0, hγ1, fun j N => ?_⟩
  have h0 := (coeff_G_of_JHyp hJ).1
  simp_rw [mul_assoc, coeff_jinv_pow hJ, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  have h2 : ∀ l ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1), γ j m * rmat m l * coeff N (G ^ l) =
      (if j = l then 1 else 0) * coeff N (G ^ l) := by
    intro l hl
    rw [← hγ j l, Finset.sum_mul]
    symm
    apply Finset.sum_subset
    · intro m hm
      simp only [Finset.mem_range] at hm hl ⊢
      omega
    · intro m _ hm'
      simp only [Finset.mem_range, not_lt] at hm'
      rw [rmat_eq_zero_of_lt (by omega : l < m)]
      simp
  rw [Finset.sum_congr rfl h2]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with h
  · rfl
  · exact coeff_pow_of_lt h0 (by omega)

/-! ## Proposition 2.2 (ii), (BR1): from `Σ c_m jinv ^ m` to `Σ a_j G ^ j` -/

/-- `a_j = Σ_{m ≤ j} c_m 27 ^ {-m} r_{m,j}`, the coordinates of `Σ c_m jinv ^ m` in the basis `G ^ j`. -/
noncomputable def jcoef (c : ℕ → K) (j : ℕ) : K :=
  ∑ m ∈ Finset.range (j + 1), c m * ((((27 : ℚ) ^ m)⁻¹ * rmat m j : ℚ) : K)

theorem jcoef_zero {c : ℕ → K} (hc0 : c 0 = 0) : jcoef c 0 = 0 := by
  simp [jcoef, hc0]

/-- `Φ(a) = Σ c_m jinv ^ m` for `a = jcoef c`, coefficientwise. -/
theorem coeff_Phi_jcoef {G : PowerSeries ℚ} (hJ : JHyp G) {c : ℕ → K} (hc0 : c 0 = 0) (N : ℕ) :
    coeff N (Phi G (jcoef c)) = ∑ m ∈ Finset.range (N + 1), c m * coeff N (jinvK ^ m) := by
  have h1 : ∀ m, coeff N (jinvK ^ m) = ∑ j ∈ Finset.range (N + 1),
      ((((27 : ℚ) ^ m)⁻¹ * rmat m j : ℚ) : K) * coeff N (GK G ^ j) := by
    intro m
    have h27 : ((27 : ℚ) ^ m) ≠ 0 := pow_ne_zero _ (by norm_num)
    have h2 : coeff N (jinv ^ m) =
        ((27 : ℚ) ^ m)⁻¹ * ∑ j ∈ Finset.range (N + 1), rmat m j * coeff N (G ^ j) := by
      rw [← coeff_jinv_pow hJ m N, inv_mul_cancel_left₀ h27]
    rw [coeff_jinvK_pow, h2, Finset.mul_sum, Rat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coeff_GK_pow, ← mul_assoc, Rat.cast_mul]
  rw [coeff_Phi]
  simp_rw [h1, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  have h3 : ∀ j ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1),
      c m * ((((27 : ℚ) ^ m)⁻¹ * rmat m j : ℚ) : K) * coeff N (GK G ^ j) =
        jcoef c j * coeff N (GK G ^ j) := by
    intro j hj
    rw [jcoef, Finset.sum_mul]
    symm
    apply Finset.sum_subset
    · intro m hm
      simp only [Finset.mem_range] at hm hj ⊢
      omega
    · intro m hm hm'
      simp only [Finset.mem_range, not_lt] at hm hm'
      rw [rmat_eq_zero_of_lt (by omega : j < m)]
      simp
  rw [Finset.sum_congr rfl h3]
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢
    omega
  · intro j hjr hj'
    simp only [Finset.mem_Icc, not_and, not_le] at hj'
    simp only [Finset.mem_range] at hjr
    have hj0 : j = 0 := by
      by_contra h
      have := hj' (Nat.one_le_iff_ne_zero.2 h)
      omega
    rw [hj0, jcoef_zero hc0, zero_mul]

/-- `‖27‖_3 = 1/27`. -/
theorem norm_27 : ‖((27 : ℚ) : ℚ_[3])‖ = (27 : ℝ)⁻¹ := by
  have h : ((27 : ℚ) : ℚ_[3]) = ((3 : ℕ) : ℚ_[3]) ^ 3 := by norm_num
  rw [h, Padic.norm_p_pow]
  norm_num

/-- `‖a_j‖ ≤ max_{m ≤ j} ‖c_m‖ 27 ^ m`. -/
theorem norm_jcoef_le (c : ℕ → K) (j : ℕ) : ∃ m ≤ j, ‖jcoef c j‖ ≤ ‖c m‖ * (27 : ℝ) ^ m := by
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (Finset.range (j + 1))
    (fun m => ‖c m‖ * (27 : ℝ) ^ m) ⟨0, Finset.mem_range.2 (Nat.succ_pos j)⟩
  refine ⟨m, Nat.lt_succ_iff.1 (Finset.mem_range.1 hm), ?_⟩
  apply norm_sum_le_of_le _ (by positivity)
  intro k hk
  rw [norm_mul, norm_ratCast_K]
  have h27 : ‖((((27 : ℚ) ^ k)⁻¹ * rmat k j : ℚ) : ℚ_[3])‖ ≤ (27 : ℝ) ^ k := by
    rw [Rat.cast_mul, norm_mul, Rat.cast_inv, norm_inv, Rat.cast_pow, norm_pow, norm_27, inv_pow,
      inv_inv]
    calc (27 : ℝ) ^ k * ‖(rmat k j : ℚ_[3])‖ ≤ (27 : ℝ) ^ k * 1 := by
          gcongr
          exact norm_rmat_le k j
      _ = (27 : ℝ) ^ k := mul_one _
  calc ‖c k‖ * ‖((((27 : ℚ) ^ k)⁻¹ * rmat k j : ℚ) : ℚ_[3])‖ ≤ ‖c k‖ * (27 : ℝ) ^ k := by
        gcongr
    _ ≤ ‖c m‖ * (27 : ℝ) ^ m := hmax k hk

/-- An overconvergent `c` gives `a = jcoef c ∈ S_s` for some `s < 3`. -/
theorem InS_jcoef {c : ℕ → K} (hc : IsOverconvergent c) : ∃ s : ℝ, s < 3 ∧ InS s (jcoef c) := by
  obtain ⟨t, ht, htc⟩ := hc
  have hτ0 : 0 < min t 1 := lt_min ht one_pos
  have hτ1 : min t 1 ≤ 1 := min_le_right _ _
  have hτt : min t 1 ≤ t := min_le_left _ _
  set τ := min t 1 with hτ
  refine ⟨3 - τ, by linarith, ?_⟩
  have hρ0 : 0 ≤ (3 : ℝ) ^ (τ - 3) := by positivity
  have hρ1 : (3 : ℝ) ^ (τ - 3) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have he : Tendsto (fun m : ℕ => ‖c m‖ * (3 : ℝ) ^ (τ * m)) atTop (𝓝 0) := by
    refine squeeze_zero (fun m => by positivity) (fun m => ?_) htc
    gcongr
    norm_num
  show Tendsto (fun j : ℕ => ‖jcoef c j‖ * (3 : ℝ) ^ (-((3 - τ) * j))) atTop (𝓝 0)
  refine tendsto_zero_of_le_geom _ _ ((3 : ℝ) ^ (τ - 3)) (fun j => by positivity)
    (fun m => by positivity) he hρ0 hρ1 (fun j => ?_)
  obtain ⟨m, hmj, hm⟩ := norm_jcoef_le c j
  refine ⟨m, hmj, ?_⟩
  have key : (27 : ℝ) ^ m * (3 : ℝ) ^ (-((3 - τ) * j)) =
      (3 : ℝ) ^ (τ * m) * ((3 : ℝ) ^ (τ - 3)) ^ (j - m) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (τ - 3)), ← Real.rpow_mul (by norm_num),
      show (27 : ℝ) ^ m = (3 : ℝ) ^ ((3 * m : ℕ) : ℝ) by rw [Real.rpow_natCast, pow_mul]; norm_num,
      ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1
    push_cast [Nat.cast_sub hmj]
    ring
  calc ‖jcoef c j‖ * (3 : ℝ) ^ (-((3 - τ) * j)) ≤ ‖c m‖ * 27 ^ m * (3 : ℝ) ^ (-((3 - τ) * j)) := by
        gcongr
    _ = ‖c m‖ * (3 : ℝ) ^ (τ * m) * ((3 : ℝ) ^ (τ - 3)) ^ (j - m) := by
        rw [mul_assoc, key, mul_assoc]

/-- Proposition 2.2 (ii), (BR1), from (J). -/
theorem BR1 {G : PowerSeries ℚ} (hJ : JHyp G) {F : PowerSeries K} (hF : F ∈ S0dag) :
    ∃ s : ℝ, s < 3 ∧ ∃ a : ℕ → K, a 0 = 0 ∧ InS s a ∧ F = Phi G a := by
  obtain ⟨c, hc0, hc, hFc⟩ := hF
  obtain ⟨s, hs, hsa⟩ := InS_jcoef hc
  refine ⟨s, hs, jcoef c, jcoef_zero hc0, hsa, ?_⟩
  ext N
  rw [hFc N, coeff_Phi_jcoef hJ hc0 N]

/-! ## Proposition 2.2 (iii), (BR2): from `Σ a_j G ^ j` to `Σ c_m jinv ^ m` -/

/-- `c_m = 27 ^ m Σ_{1 ≤ j ≤ m} a_j γ_{j,m}`, the coordinates of `Σ a_j G ^ j` in the basis `jinv ^ m`. -/
noncomputable def gcoef (γ : ℕ → ℕ → ℚ) (a : ℕ → K) (m : ℕ) : K :=
  ∑ j ∈ Finset.Icc 1 m, a j * ((γ j m * 27 ^ m : ℚ) : K)

theorem gcoef_zero (γ : ℕ → ℕ → ℚ) (a : ℕ → K) : gcoef γ a 0 = 0 := by
  simp [gcoef]

/-- `Φ(a) = Σ c_m jinv ^ m` for `c = gcoef γ a`, coefficientwise. -/
theorem coeff_Phi_gcoef {G : PowerSeries ℚ} (γ : ℕ → ℕ → ℚ) (hγ0 : ∀ j m, m < j → γ j m = 0)
    (hγ : ∀ j N, coeff N (G ^ j) = ∑ m ∈ Finset.range (N + 1), γ j m * 27 ^ m * coeff N (jinv ^ m))
    (a : ℕ → K) (N : ℕ) :
    coeff N (Phi G a) = ∑ m ∈ Finset.range (N + 1), gcoef γ a m * coeff N (jinvK ^ m) := by
  have h1 : ∀ j, coeff N (GK G ^ j) =
      ∑ m ∈ Finset.range (N + 1), ((γ j m * 27 ^ m : ℚ) : K) * coeff N (jinvK ^ m) := by
    intro j
    rw [coeff_GK_pow, hγ j N, Rat.cast_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [coeff_jinvK_pow, Rat.cast_mul]
  rw [coeff_Phi]
  simp_rw [h1, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [gcoef, Finset.sum_mul]
  symm
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_Icc, Finset.mem_range] at hj hm ⊢
    omega
  · intro j hj hj'
    simp only [Finset.mem_Icc, not_and, not_le] at hj hj'
    rw [hγ0 j m (hj' hj.1)]
    simp

/-- `c = gcoef γ a` is overconvergent for `a ∈ c₀` and `γ` integral (`‖c_m‖ ≤ 27 ^ {-m} ‖a‖`). -/
theorem isOverconvergent_gcoef (γ : ℕ → ℕ → ℚ) (hγ1 : ∀ j m, ‖(γ j m : ℚ_[3])‖ ≤ 1) {a : ℕ → K}
    (ha : IsC0 a) : IsOverconvergent (gcoef γ a) := by
  obtain ⟨R, hR0, hR⟩ := ha.exists_bound
  have h27 : ∀ j m, ‖((γ j m * 27 ^ m : ℚ) : K)‖ ≤ ((1 : ℝ) / 27) ^ m := by
    intro j m
    rw [norm_ratCast_K, Rat.cast_mul, norm_mul, Rat.cast_pow, norm_pow, norm_27]
    calc ‖(γ j m : ℚ_[3])‖ * ((27 : ℝ)⁻¹) ^ m ≤ 1 * ((27 : ℝ)⁻¹) ^ m := by
          gcongr
          exact hγ1 j m
      _ = ((1 : ℝ) / 27) ^ m := by rw [one_mul, one_div]
  have hb : ∀ m, ‖gcoef γ a m‖ ≤ R * ((1 : ℝ) / 27) ^ m := by
    intro m
    apply norm_sum_le_of_le _ (by positivity)
    intro j _
    rw [norm_mul]
    exact mul_le_mul (hR j) (h27 j m) (norm_nonneg _) hR0
  refine ⟨1, one_pos, ?_⟩
  have hlim : Tendsto (fun m : ℕ => R * ((1 : ℝ) / 9) ^ m) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 9)
      (by norm_num)).const_mul R
  refine squeeze_zero (fun m => by positivity) (fun m => ?_) hlim
  rw [one_mul, Real.rpow_natCast]
  calc ‖gcoef γ a m‖ * (3 : ℝ) ^ m ≤ R * ((1 : ℝ) / 27) ^ m * (3 : ℝ) ^ m := by
        gcongr
        exact hb m
    _ = R * ((1 : ℝ) / 9) ^ m := by
        rw [mul_assoc, ← mul_pow]
        norm_num

/-- Proposition 2.2 (iii), (BR2), from (J). -/
theorem BR2 {G : PowerSeries ℚ} (hJ : JHyp G) {a : ℕ → K} (ha : IsC0 a) : Phi G a ∈ S0dag := by
  obtain ⟨γ, hγ0, hγ1, hγ⟩ := exists_Gpow_expand hJ
  exact ⟨gcoef γ a, gcoef_zero γ a, isOverconvergent_gcoef γ hγ1 ha, coeff_Phi_gcoef γ hγ0 hγ a⟩

end CalegariSlopes.Spectral
