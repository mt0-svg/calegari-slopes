/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Spectral.Contraction
public import CalegariSlopes.Spectral.Diag
public import CalegariSlopes.Spectral.Radius
public import CalegariSlopes.Spectral.QSeries

@[expose] public section

/-!
# The spectral step and the proof of Theorem 1.2

The statements that the proof of Theorem 1.2 in Section 2 uses, each restated below as an `example` and proved by the
lemma of the same name in `Basic`, `Seq`, `Contraction`, `Diag`, `Radius` or `QSeries`. The assembly follows; it ends
with `calegari_conjecture_overconvergent_of`, the proof of Theorem 1.2 for any series `G` with the two properties of
Theorem 2.1.
-/

open PowerSeries Filter Topology
open CalegariSlopes.Overconvergent (K S0dag U3 genEig jinv jinvK)

namespace CalegariSlopes.Spectral

/-! ## Lemma 3.4 -/

/- `slope (k + 1) ≥ slope k + 2`; used through strict monotonicity. -/
example : StrictMono slope := by
  apply slope_strictMono

/-! ## Lemma 6.1: perturbation of the unit basis of `c₀` -/

/- The series `Σ_n b_n x_n i` converges for `b ∈ c₀`. -/
example {x : ℕ → ℕ → K} {c : ℝ} (hx : NearBasis x c) {b : ℕ → K} (hb : IsC0 b)
    (i : ℕ) : Summable fun n => b n * x n i := by
  apply NearBasis.summable
  all_goals assumption

/- Lemma 6.1: `Σ_n b_n x_n` is in `c₀`. -/
example {x : ℕ → ℕ → K} {c : ℝ} (hx : NearBasis x c) {b : ℕ → K} (hb : IsC0 b) :
    IsC0 (expand x b) := by
  apply NearBasis.isC0_expand
  all_goals assumption

/- Lemma 6.1, injectivity (`‖Σ_n b_n x_n‖ = ‖b‖`). -/
example {x : ℕ → ℕ → K} {c : ℝ} (hx : NearBasis x c) {b : ℕ → K}
    (hb : IsC0 b) (h : expand x b = 0) : b = 0 := by
  apply NearBasis.eq_zero_of_expand_eq_zero
  all_goals assumption

/- Lemma 6.1: every `F ∈ c₀` is `Σ_n b_n x_n` for some `b ∈ c₀`. -/
example {x : ℕ → ℕ → K} {c : ℝ} (hx : NearBasis x c) {F : ℕ → K}
    (hF : IsC0 F) : ∃ b, IsC0 b ∧ expand x b = F := by
  apply NearBasis.exists_expand_eq
  all_goals assumption

/- A banded matrix acts termwise on `Σ_n b_n x_n` (Lemma 6.1, for finite rows). -/
example {x : ℕ → ℕ → K} {c : ℝ} (hx : NearBasis x c) {b : ℕ → K} (hb : IsC0 b)
    (M : ℕ → ℕ → ℚ) : bact M (expand x b) = expand (fun n => bact M (x n)) b := by
  apply NearBasis.bact_expand
  all_goals assumption

/-! ## Lemma 6.2: the matrix `C = B A` -/

/- `C_ij = 0` for `j > 3 i`. -/
example {i j : ℕ} (h : 3 * i < j) : Cm i j = 0 := by
  apply Cm_eq_zero_of_lt
  all_goals assumption

/- `C_ij = 0` for `i > 3 j`. -/
example {i j : ℕ} (h : 3 * j < i) : Cm i j = 0 := by
  apply Cm_eq_zero_of_gt
  all_goals assumption

/- `v_3(C_ij) ≥ |i - j|`. -/
example (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    ‖(Cm i j : ℚ_[3])‖ ≤ (3 : ℝ) ^ (-|(i : ℤ) - j|) := by
  apply norm_Cm_le
  all_goals assumption

/- `v_3(C_ii - 1) ≥ 2`. -/
example (i : ℕ) (hi : 1 ≤ i) :
    ‖((Cm i i - 1 : ℚ) : ℚ_[3])‖ ≤ (3 : ℝ) ^ (-2 : ℤ) := by
  apply norm_Cm_self_sub_one_le
  all_goals assumption

/-! ## Lemma 6.3 -/

/- A matrix with `M_ij = 0` for `i > 3 j` and entries of norm `≤ 1` maps `c₀` into `c₀` (`A`, `C`, `u`). -/
example (M : ℕ → ℕ → ℚ) (hband : ∀ i j, 3 * j < i → M i j = 0)
    (hM : ∀ i j, ‖(M i j : ℚ_[3])‖ ≤ 1) {a : ℕ → K} (ha : IsC0 a) : IsC0 (bact M a) := by
  apply isC0_bact
  all_goals assumption

/- Lemma 6.3, first part: `‖A w - w‖ ≤ ‖w‖ / 3` (coordinates `k ≥ 1`). -/
example (w : ℕ → K) (r : ℝ) (hw : ∀ j, ‖w j‖ ≤ r) (k : ℕ) (hk : 1 ≤ k) :
    ‖bact ADB.A w k - w k‖ ≤ r / 3 := by
  apply norm_bact_A_sub_le
  all_goals assumption

/- Lemma 6.3, second part: `U (A w) = A (D (C w))` for every sequence `w`, from Theorem 2.3. -/
example (w : ℕ → K) :
    bact u (bact ADB.A w) = bact ADB.A (fun p => (ADB.D p : K) * bact Cm w p) := by
  apply bact_u_bact_A

/-! ## Proposition 6.4: the contraction and its fixed point -/

/- Proposition 6.4: for `n ≥ 1` there are `y ∈ c₀` with `y_0 = y_n = 0`, `‖y‖ ≤ 1/3`, and `μ` with
`v_3(μ - 1) ≥ 2`, such that `w = e_n + y` satisfies `D_i (C w)_i = D_n μ w_i` for every `i ≥ 1` (the fixed point of
the contraction `T` on `Y = {y : y_n = 0, ‖y‖ ≤ 1/3}`). -/
example (n : ℕ) (hn : 1 ≤ n) :
    ∃ (y : ℕ → K) (μ : K), y 0 = 0 ∧ y n = 0 ∧ (∀ j, ‖y j‖ ≤ 1 / 3) ∧ IsC0 y ∧ ‖μ - 1‖ ≤ 1 / 9 ∧
      ∀ i, 1 ≤ i → (ADB.D i : K) * bact Cm (wv n y) i = (ADB.D n : K) * μ * wv n y i := by
  apply exists_eigen_DC
  all_goals assumption

/-! ## Theorem 2.4 (a): the eigenvectors of `U` -/
/- Theorem 2.4 (a). -/
example : Nonempty EigenFamily := by
  apply exists_eigenFamily

/-! ## Theorem 2.4 (b): diagonalization in `c₀` -/

/- Theorem 2.4 (b): for `μ ≠ 0`, a generalized eigenvector `a ∈ c₀` of `U` is `Σ_n b_n x_n` with `b ∈ c₀`
supported on the `n` with `λ_n = μ`. -/
example (E : EigenFamily) {μ : K} (hμ : μ ≠ 0) {k : ℕ} {a : ℕ → K} (ha : IsC0 a)
    (hk : ((Uop - μ • (1 : Module.End K (ℕ → K))) ^ k) a = 0) :
    ∃ b : ℕ → K, IsC0 b ∧ (∀ n, b n ≠ 0 → E.lam n = μ) ∧ a = expand E.x b := by
  apply EigenFamily.diag
  all_goals assumption

/-! ## Section 6.4: from any radius below three to the null sequences -/

/- Lemma 3.1 (d): `2 v_3(u_ij) ≥ 3 (i + j) - 2`. -/
example (i j : ℕ) : ‖(u i j : ℚ_[3])‖ ^ 2 ≤ (3 : ℝ) ^ (2 - 3 * ((i : ℤ) + j)) := by
  apply norm_u_sq_le

/- Lemma 6.5 (a): `U` maps `S_s` into `S_{φ(s)}`. -/
example {s : ℝ} {a : ℕ → K} (ha : InS s a) : InS (phiS s) (Uop a) := by
  apply InS_Uop
  all_goals assumption

/- Lemma 6.5 (b): `φ(s) < s` on `(-3, 3)`. -/
example {s : ℝ} (h1 : -3 < s) (h2 : s < 3) : phiS s < s := by
  apply phiS_lt
  all_goals assumption

/- Lemma 6.5 (b): `φ` maps `(-3, 3)` into `(-3, 3)` (lower end). -/
example {s : ℝ} (h1 : -3 < s) (h2 : s < 3) : -3 < phiS s := by
  apply phiS_gt
  all_goals assumption

/- Lemma 6.5 (b): the iterates of `φ` from `s ∈ (-3, 3)` reach `(-∞, 0]`. -/
example {s : ℝ} (h1 : -3 < s) (h2 : s < 3) : ∃ m : ℕ, phiS^[m] s ≤ 0 := by
  apply exists_iterate_phiS_nonpos
  all_goals assumption

/- Theorem 2.4 (c): for `s < 3` and `μ ≠ 0`, a generalized eigenvector of `U` in `S_s` is in `c₀`. -/
example {s : ℝ} (hs : s < 3) {a : ℕ → K} (ha : InS s a) {μ : K} (hμ : μ ≠ 0) {k : ℕ}
    (hk : ((Uop - μ • (1 : Module.End K (ℕ → K))) ^ k) a = 0) : IsC0 a := by
  apply isC0_of_InS
  all_goals assumption

/-! ## Proposition 2.2: the q-series space (Section 4.5) -/

/- (J) gives `G = 27 q + O(q ^ 2)` (`jinv = q + O(q ^ 2)`). -/
example {G : PowerSeries ℚ} (hJ : JHyp G) : coeff 0 G = 0 ∧ coeff 1 G = 27 := by
  apply coeff_G_of_JHyp
  all_goals assumption

/- `Φ` is injective on the coordinates `j ≥ 1` (`[q ^ j₀] Φ(a) = 27 ^ j₀ a_j₀` at the first nonzero `a_j₀`). -/
example {G : PowerSeries ℚ} (h0 : coeff 0 G = 0) (h1 : coeff 1 G ≠ 0) {a : ℕ → K}
    (h : Phi G a = 0) : ∀ j, 1 ≤ j → a j = 0 := by
  apply Phi_eq_zero
  all_goals assumption

/- Proposition 2.2 (i): `U_3 Φ(a) = Φ(U a)`, from (C4). -/
example {G : PowerSeries ℚ} (hC4 : C4 G) (h0 : coeff 0 G = 0) (a : ℕ → K) :
    U3 (Phi G a) = Phi G (Uop a) := by
  apply U3_Phi
  all_goals assumption

/- Proposition 2.2 (ii), from (J): every `F ∈ S0dag` is `Φ(a)` with `a ∈ S_s` for some `s < 3`, `a_0 = 0`. -/
example {G : PowerSeries ℚ} (hJ : JHyp G) {F : PowerSeries K} (hF : F ∈ S0dag) :
    ∃ s : ℝ, s < 3 ∧ ∃ a : ℕ → K, a 0 = 0 ∧ InS s a ∧ F = Phi G a := by
  apply BR1
  all_goals assumption

/- Proposition 2.2 (iii), from (J): `Φ(c₀) ⊆ S0dag`. -/
example {G : PowerSeries ℚ} (hJ : JHyp G) {a : ℕ → K} (ha : IsC0 a) : Phi G a ∈ S0dag := by
  apply BR2
  all_goals assumption

/-! ## The assembly: the proof of Theorem 1.2 (Section 2) -/

theorem Uop_apply_zero (a : ℕ → K) : Uop a 0 = 0 := by
  simp [Uop, bact]

/-- The spectator coordinate: `((U - μ) ^ k a)_0 = (-μ) ^ k a_0`. -/
theorem iterate_apply_zero (μ : K) (k : ℕ) (a : ℕ → K) :
    ((Uop - μ • (1 : Module.End K (ℕ → K))) ^ k) a 0 = (-μ) ^ k * a 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Pi.sub_apply,
      Pi.smul_apply, Uop_apply_zero, ih, smul_eq_mul, pow_succ']
    ring

/-- `(U_3 - μ) ^ k Φ(a) = Φ((U - μ) ^ k a)`, from Proposition 2.2 (i). -/
theorem iterate_Phi {G : PowerSeries ℚ} (hC4 : C4 G) (h0 : coeff 0 G = 0) (μ : K) (k : ℕ) (a : ℕ → K) :
    ((U3 - μ • (1 : Module.End K (PowerSeries K))) ^ k) (Phi G a) =
      Phi G (((Uop - μ • (1 : Module.End K (ℕ → K))) ^ k) a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.sub_apply, U3_Phi hC4 h0, map_sub, LinearMap.smul_apply, LinearMap.smul_apply,
      Module.End.one_apply, Module.End.one_apply, map_smul]

/-- A coefficient sequence supported on one index. -/
theorem expand_eq_smul (x : ℕ → ℕ → K) (b : ℕ → K) (m : ℕ) (hb : ∀ n, n ≠ m → b n = 0) :
    expand x b = b m • x m := by
  funext i
  simp only [expand, Pi.smul_apply, smul_eq_mul]
  rw [tsum_eq_single m fun n hn => by rw [hb n hn, zero_mul]]

/-- The generalized eigenspace of `U_3` on `S0dag`, for `μ ≠ 0`, lies in `K Φ(x_m)` with `λ_m = μ`, or is `0`. -/
theorem EigenFamily.genEig_le (E : EigenFamily) {G : PowerSeries ℚ} (hC4 : C4 G) (hJ : JHyp G) {μ : K}
    (hμ : μ ≠ 0) {F : PowerSeries K} (hF : F ∈ genEig μ) :
    ∃ b : ℕ → K, (∀ n, b n ≠ 0 → E.lam n = μ) ∧ F = Phi G (expand E.x b) := by
  obtain ⟨h0, h1⟩ := coeff_G_of_JHyp hJ
  obtain ⟨hS, hG⟩ := Submodule.mem_inf.mp hF
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace U3 μ F).mp hG
  obtain ⟨s, hs, a, ha0, haS, rfl⟩ := BR1 hJ hS
  have hka : ((Uop - μ • (1 : Module.End K (ℕ → K))) ^ k) a = 0 := by
    rw [iterate_Phi hC4 h0] at hk
    funext j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [iterate_apply_zero, ha0, mul_zero, Pi.zero_apply]
    · exact Phi_eq_zero h0 (by rw [h1]; norm_num) hk j hj
  obtain ⟨b, -, hbμ, hab⟩ := E.diag hμ (isC0_of_InS hs haS hμ hka) hka
  exact ⟨b, hbμ, by rw [hab]⟩

/-- `Φ(x_m) ≠ 0`. -/
theorem EigenFamily.Phi_x_ne_zero (E : EigenFamily) {G : PowerSeries ℚ} (hJ : JHyp G) {m : ℕ} (hm : 1 ≤ m) :
    Phi G (E.x m) ≠ 0 := by
  obtain ⟨h0, h1⟩ := coeff_G_of_JHyp hJ
  intro h
  have h1 := Phi_eq_zero h0 (by rw [h1]; norm_num) h m hm
  have h2 := E.near.near m m
  simp only [h1, unitSeq, ite_true, zero_sub, norm_neg, norm_one] at h2
  norm_num at h2

/-- `Φ(x_m)` is an eigenvector of `U_3` in `S0dag`, for the eigenvalue `λ_m`. -/
theorem EigenFamily.Phi_x_mem (E : EigenFamily) {G : PowerSeries ℚ} (hC4 : C4 G) (hJ : JHyp G) (m : ℕ) :
    Phi G (E.x m) ∈ genEig (E.lam m) := by
  refine Submodule.mem_inf.mpr ⟨BR2 hJ (E.near.isC0 m), ?_⟩
  refine (Module.End.mem_maxGenEigenspace U3 _ _).mpr ⟨1, ?_⟩
  rw [iterate_Phi hC4 (coeff_G_of_JHyp hJ).1, pow_one, LinearMap.sub_apply, E.eig m, LinearMap.smul_apply,
    Module.End.one_apply, sub_self, map_zero]

/-- The eigenvalues are pairwise distinct (their norms are, by Lemma 3.4). -/
theorem EigenFamily.lam_injective (E : EigenFamily) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (h : E.lam m = E.lam n) : m = n := by
  have h1 := E.norm_lam m hm
  have h2 := E.norm_lam n hn
  rw [h, h2] at h1
  have := zpow_right_injective₀ (a := (3 : ℝ)) (by norm_num) (by norm_num) h1
  exact slope_strictMono.injective (by exact_mod_cast neg_injective this.symm)

/-- **Theorem 1.2** for any `G` with (C4) and (J), the properties of Theorem 2.1: the statement of
`CalegariSlopes.Overconvergent.calegari_conjecture_overconvergent`, with `ev n = λ_n`. -/
theorem calegari_conjecture_overconvergent_of (G : PowerSeries ℚ) (hC4 : C4 G) (hJ : JHyp G) :
    ∃ ev : ℕ+ → K, (∀ i, ‖ev i‖ = (3 : ℝ) ^ (-(Overconvergent.slope i : ℤ))) ∧
      ∀ μ : K, μ ≠ 0 → FiniteDimensional K (genEig μ) ∧
        Module.finrank K (genEig μ) = Nat.card {i : ℕ+ // ev i = μ} := by
  obtain ⟨E⟩ := exists_eigenFamily
  refine ⟨fun i => E.lam i, fun i => E.norm_lam i i.pos, fun μ hμ => ?_⟩
  by_cases hex : ∃ i : ℕ+, E.lam i = μ
  · obtain ⟨i, hi⟩ := hex
    have heq : genEig μ = K ∙ Phi G (E.x i) := by
      apply le_antisymm
      · intro F hF
        obtain ⟨b, hbμ, rfl⟩ := E.genEig_le hC4 hJ hμ hF
        have hb : ∀ n, n ≠ (i : ℕ) → b n = 0 := by
          intro n hn
          by_contra hbn
          have hlam := hbμ n hbn
          rcases Nat.eq_zero_or_pos n with rfl | hpos
          · exact hμ (hlam.symm.trans E.lam_zero)
          · exact hn (E.lam_injective hpos i.pos (hlam.trans hi.symm))
        rw [expand_eq_smul _ _ _ hb, map_smul]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      · rw [Submodule.span_singleton_le_iff_mem, ← hi]
        exact E.Phi_x_mem hC4 hJ i
    have : Unique {j : ℕ+ // E.lam j = μ} :=
      { default := ⟨i, hi⟩
        uniq := fun j => Subtype.ext (PNat.coe_injective
          (E.lam_injective j.1.pos i.pos (j.2.trans hi.symm))) }
    rw [heq, Nat.card_unique, finrank_span_singleton (E.Phi_x_ne_zero hJ i.pos)]
    exact ⟨inferInstance, rfl⟩
  · simp only [not_exists] at hex
    have heq : genEig μ = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr fun F hF => ?_
      obtain ⟨b, hbμ, rfl⟩ := E.genEig_le hC4 hJ hμ hF
      have hb : b = 0 := by
        funext n
        by_contra hbn
        have hlam := hbμ n hbn
        rcases Nat.eq_zero_or_pos n with rfl | hpos
        · exact hμ (hlam.symm.trans E.lam_zero)
        · exact hex ⟨n, hpos⟩ hlam
      rw [hb]
      have : expand E.x 0 = 0 := by
        funext j
        simp [expand]
      rw [this, map_zero]
    have : IsEmpty {j : ℕ+ // E.lam j = μ} := ⟨fun j => hex j.1 j.2⟩
    rw [heq, Nat.card_of_isEmpty, finrank_bot]
    exact ⟨inferInstance, rfl⟩

end CalegariSlopes.Spectral
