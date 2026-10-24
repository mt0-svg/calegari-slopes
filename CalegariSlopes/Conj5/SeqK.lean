/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Spectral.Main
public import CalegariSlopes.Conj5.SpectralDefs

@[expose] public section

/-!
# Sequences over `K`: matrices with entries in `K`, expansions in a near basis

The facts of `CalegariSlopes.Spectral.Seq` and `CalegariSlopes.Spectral.Diag` that the spectral expansion at radius
`r` needs, for matrices with entries in `K` (the scaled matrices `γ ^ (j - i) M_ij`) and for any near basis and any
operator acting termwise on expansions: `kact` (a `K`-matrix acting by the rows `1 ≤ j ≤ 3 i`), its termwise action
on `Σ_n b_n x_n`, the diagonalization argument of Theorem 2.4 (b) for an operator acting termwise, the uniqueness of
the expansion, and `‖Σ_n b_n x_n‖ = ‖b‖` (Lemma 6.1).
-/

open Filter Topology
open CalegariSlopes.Overconvergent (K)
open CalegariSlopes.Spectral

namespace CalegariSlopes.Conj5

/-- A `K`-matrix acting by rows: `(M a)_i = Σ_{1 ≤ j ≤ 3i} M_ij a_j` (zero at `i = 0`). -/
noncomputable def kact (M : ℕ → ℕ → K) (a : ℕ → K) (i : ℕ) : K :=
  ∑ j ∈ Finset.Icc 1 (3 * i), M i j * a j

theorem kact_apply_zero (M : ℕ → ℕ → K) (a : ℕ → K) : kact M a 0 = 0 := by
  simp [kact]

/-- `u^(r)` is the `K`-matrix `γ ^ (j - i) u_ij` acting by rows. -/
theorem Ur_apply (γ : K) (a : ℕ → K) : Ur γ a = kact (fun i j => γ ^ ((j : ℤ) - i) * (u i j : K)) a := rfl

/-- A `K`-matrix acting by rows acts termwise on `Σ_n b_n x_n`. -/
theorem NearBasis.kact_expand {x : ℕ → ℕ → K} {c : ℝ} (hx : NearBasis x c) {b : ℕ → K} (hb : IsC0 b)
    (M : ℕ → ℕ → K) : kact M (expand x b) = expand (fun n => kact M (x n)) b := by
  funext i
  simp only [kact, expand]
  calc
    ∑ j ∈ Finset.Icc 1 (3 * i), M i j * (∑' n, b n * x n j)
        = ∑ j ∈ Finset.Icc 1 (3 * i), ∑' n, M i j * (b n * x n j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [tsum_mul_left]
    _ = ∑' n, ∑ j ∈ Finset.Icc 1 (3 * i), M i j * (b n * x n j) := by
      refine (Summable.tsum_finsetSum ?_).symm
      intro j _
      exact (hx.summable hb j).mul_left (M i j)
    _ = ∑' n, b n * (∑ j ∈ Finset.Icc 1 (3 * i), M i j * x n j) := by
      refine tsum_congr fun n => ?_
      simp [Finset.mul_sum, mul_left_comm]

/-- A `K`-matrix with `M_ij = 0` for `i > 3 j` and entries of norm `≤ 1` on the rows `i ≥ 1` maps `c₀` into `c₀`. -/
theorem isC0_kact (M : ℕ → ℕ → K) (hband : ∀ i j, 3 * j < i → M i j = 0) (hM : ∀ i j, 1 ≤ i → ‖M i j‖ ≤ 1)
    {a : ℕ → K} (ha : IsC0 a) : IsC0 (kact M a) := by
  have ha_norm : Tendsto (fun n => ‖a n‖) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_zero_iff_norm_tendsto_zero (f := a) (a := atTop)).mp ha
  have ha_metric := (Metric.tendsto_atTop (a := 0)).mp ha_norm
  apply (Metric.tendsto_atTop (a := 0)).mpr
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨J, hJ⟩ := ha_metric (ε / 2) hε2
  refine ⟨3 * J, fun i hi => ?_⟩
  have hbound : ∀ j ∈ Finset.Icc 1 (3 * i), ‖M i j * a j‖ ≤ ε / 2 := by
    intro j hj
    have hi1 : 1 ≤ i := by have := (Finset.mem_Icc.mp hj); omega
    by_cases h : 3 * j < i
    · simp [hband i j h, hε2.le]
    · have hJj : J ≤ j := by omega
      have ha_j : ‖a j‖ < ε / 2 := by
        have := hJ j hJj
        simpa [dist_eq_norm, Real.norm_of_nonneg (norm_nonneg _)] using this
      calc
        ‖M i j * a j‖ = ‖M i j‖ * ‖a j‖ := norm_mul _ _
        _ ≤ 1 * (ε / 2) := mul_le_mul (hM i j hi1) ha_j.le (norm_nonneg _) (by linarith)
        _ = ε / 2 := by simp
  have hsum : ‖∑ j ∈ Finset.Icc 1 (3 * i), M i j * a j‖ ≤ ε / 2 :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε2.le hbound
  simpa [kact, dist_eq_norm] using hsum.trans_lt (by linarith)

/-! ## Diagonalization for an operator acting termwise (Theorem 2.4 (b)) -/

/-- `(T - μ) ^ k (Σ_n b_n x_n) = Σ_n (λ_n - μ) ^ k b_n x_n` for `T` acting termwise, and the new coefficients are
in `c₀`. -/
theorem iterate_expand_of_termwise {x : ℕ → ℕ → K} {c : ℝ} (hx : NearBasis x c) (lam : ℕ → K)
    (hlam : ∀ n, ‖lam n‖ ≤ 1) (T : Module.End K (ℕ → K))
    (hT : ∀ b, IsC0 b → T (expand x b) = expand x (fun n => lam n * b n)) (μ : K) (k : ℕ) {b : ℕ → K}
    (hb : IsC0 b) :
    IsC0 (fun n => (lam n - μ) ^ k * b n) ∧
      ((T - μ • (1 : Module.End K (ℕ → K))) ^ k) (expand x b) = expand x (fun n => (lam n - μ) ^ k * b n) := by
  induction k with
  | zero => simp [hb]
  | succ k ih =>
    obtain ⟨hC0, hEq⟩ := ih
    set b' := fun n : ℕ => (lam n - μ) ^ k * b n with hb'_def
    have h_bound : ∀ n, ‖lam n - μ‖ ≤ 1 + ‖μ‖ := fun n =>
      (norm_sub_le _ _).trans (by linarith [hlam n])
    have h1 : IsC0 (fun n => (lam n - μ) * b' n) := by
      have := IsC0.mul_bounded hC0 (fun n => lam n - μ) (1 + ‖μ‖) h_bound
      simpa [mul_comm] using this
    have h_pow : ∀ n, (lam n - μ) ^ (k + 1) * b n = (lam n - μ) * b' n := by
      intro n
      simp [hb'_def, pow_succ', mul_assoc]
    have hlamb : IsC0 (fun n => lam n * b' n) := by
      have := IsC0.mul_bounded hC0 lam 1 hlam
      simpa [mul_comm] using this
    refine ⟨by simpa [h_pow] using h1, ?_⟩
    rw [pow_succ', Module.End.mul_apply, hEq, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      hT b' hC0]
    funext i
    have hs1 := hx.summable hC0 i
    have hs2 := hx.summable hlamb i
    simp only [expand, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [← tsum_mul_left, ← Summable.tsum_sub hs2 (hs1.mul_left μ)]
    refine tsum_congr fun n => ?_
    rw [h_pow n]
    ring

/-- Theorem 2.4 (b) for an operator `T` acting termwise on the expansions in a near basis: a generalized
eigenvector `a ∈ c₀` of `T` for `μ` is `Σ_n b_n x_n` with `b ∈ c₀` supported on the `n` with `λ_n = μ`. -/
theorem diag_of_termwise {x : ℕ → ℕ → K} {c : ℝ} (hx : NearBasis x c) (lam : ℕ → K) (hlam : ∀ n, ‖lam n‖ ≤ 1)
    (T : Module.End K (ℕ → K)) (hT : ∀ b, IsC0 b → T (expand x b) = expand x (fun n => lam n * b n)) {μ : K}
    {k : ℕ} {a : ℕ → K} (ha : IsC0 a) (hk : ((T - μ • (1 : Module.End K (ℕ → K))) ^ k) a = 0) :
    ∃ b : ℕ → K, IsC0 b ∧ (∀ n, b n ≠ 0 → lam n = μ) ∧ a = expand x b := by
  obtain ⟨b, hb, hab⟩ := hx.exists_expand_eq ha
  obtain ⟨hiter, h_eq⟩ := iterate_expand_of_termwise hx lam hlam T hT μ k hb
  have hzero : expand x (fun n => (lam n - μ) ^ k * b n) = 0 := by
    rw [← h_eq, hab]
    exact hk
  have hcoeff := hx.eq_zero_of_expand_eq_zero hiter hzero
  refine ⟨b, hb, fun n hbn => ?_, hab.symm⟩
  have hpow : (lam n - μ) ^ k * b n = 0 := congr_fun hcoeff n
  rcases mul_eq_zero.mp hpow with h | h
  · exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero h)
  · exact absurd h hbn

/-! ## Uniqueness of the expansion and the norm -/

/-- `expand` is subtractive on `c₀`. -/
theorem NearBasis.expand_sub {x : ℕ → ℕ → K} {c : ℝ} (hx : NearBasis x c) {b b' : ℕ → K} (hb : IsC0 b)
    (hb' : IsC0 b') : expand x (b - b') = expand x b - expand x b' := by
  calc
    expand x (b - b') = expand x (b + (-1 : K) • b') := by
      simp [sub_eq_add_neg]
    _ = expand x b + expand x ((-1 : K) • b') := hx.expand_add hb (hb'.smul (-1))
    _ = expand x b + ((-1 : K) • expand x b') := by rw [expand_smul]
    _ = expand x b - expand x b' := by simp [sub_eq_add_neg]

/-- Lemma 6.1: every `a ∈ c₀` is `Σ_n b_n x_n` for exactly one `b ∈ c₀`. -/
theorem NearBasis.existsUnique_expand {x : ℕ → ℕ → K} {c : ℝ} (hx : NearBasis x c) {a : ℕ → K}
    (ha : IsC0 a) : ∃! b, IsC0 b ∧ expand x b = a := by
  obtain ⟨b, hb, hb_eq⟩ := hx.exists_expand_eq ha
  refine ⟨b, ⟨hb, hb_eq⟩, ?_⟩
  intro b' ⟨hb', hb'_eq⟩
  have hsub : expand x (b' - b) = 0 := by
    calc
      expand x (b' - b) = expand x b' - expand x b := CalegariSlopes.Conj5.NearBasis.expand_sub hx hb' hb
      _ = a - a := by rw [hb'_eq, hb_eq]
      _ = 0 := by simp
  have hzero : b' - b = 0 := hx.eq_zero_of_expand_eq_zero (hb'.sub hb) hsub
  exact sub_eq_zero.mp hzero

/-- A `c₀` sequence attains the maximum of its norms. -/
theorem IsC0.exists_max_norm {a : ℕ → K} (ha : IsC0 a) : ∃ m, ∀ n, ‖a n‖ ≤ ‖a m‖ := by
  by_cases h : ∀ n, a n = 0
  · refine ⟨0, fun n => ?_⟩
    rw [h n, h 0, norm_zero]
  · push Not at h
    obtain ⟨n₀, hn₀⟩ := h
    have hε : 0 < ‖a n₀‖ := norm_pos_iff.mpr hn₀
    have hnorm : Tendsto (fun k : ℕ => ‖a k‖) atTop (𝓝 (0 : ℝ)) := by
      simpa [norm_zero] using ha.norm
    have hlim := (Metric.tendsto_atTop.mp ha) (‖a n₀‖) hε
    rcases hlim with ⟨N, hN⟩
    -- hN : ∀ n ≥ N, dist (a n) 0 < ‖a n₀‖
    have hN' : ∀ k ≥ N, ‖a k‖ < ‖a n₀‖ := by
      intro k hk
      have := hN k hk
      simpa [dist_eq_norm] using this
    -- Let Mmax be large enough so that n₀ is in the range
    let Mmax := Nat.max N (n₀ + 1)
    have hM : n₀ ∈ Finset.range Mmax := by
      apply Finset.mem_range.mpr
      have : n₀ + 1 ≤ Mmax := Nat.le_max_right _ _
      omega
    have hM_nonempty : (Finset.range Mmax).Nonempty := ⟨n₀, hM⟩
    obtain ⟨m, hm, hm_max⟩ := Finset.exists_max_image (Finset.range Mmax) (fun i => ‖a i‖) hM_nonempty
    refine ⟨m, fun k => ?_⟩
    by_cases hk : k ∈ Finset.range Mmax
    · exact hm_max k hk
    · have hk' : Mmax ≤ k := by
        have : ¬ k < Mmax := by simpa [Finset.mem_range] using hk
        omega
      have hkN : N ≤ k := le_trans (Nat.le_max_left _ _) hk'
      have hlt : ‖a k‖ < ‖a n₀‖ := hN' k hkN
      have hle : ‖a n₀‖ ≤ ‖a m‖ := hm_max n₀ hM
      linarith

/-- `‖(Σ_n b_n x_n)_i‖ ≤ R` when every `‖b_n‖ ≤ R`. -/
theorem NearBasis.norm_expand_le {x : ℕ → ℕ → K} {c : ℝ} (hx : NearBasis x c) {b : ℕ → K} {R : ℝ}
    (hR : 0 ≤ R) (hb : ∀ n, ‖b n‖ ≤ R) (i : ℕ) : ‖expand x b i‖ ≤ R := by
  have h_norm_one : ∀ n, ‖x n i‖ ≤ 1 := by
    intro n
    have hnear := hx.near n i
    have hunit : ‖unitSeq n i‖ ≤ (1 : ℝ) := by
      unfold unitSeq
      split
      · simp
      · simp
    have hc1 : c ≤ 1 := le_of_lt hx.lt_one
    calc
      ‖x n i‖ = ‖(x n i - unitSeq n i) + unitSeq n i‖ := by simp
      _ ≤ max ‖x n i - unitSeq n i‖ ‖unitSeq n i‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ max c 1 := max_le_max hnear hunit
      _ = 1 := max_eq_right hc1
  have h_norm : ∀ n, ‖b n * x n i‖ ≤ R := by
    intro n
    calc
      ‖b n * x n i‖ = ‖b n‖ * ‖x n i‖ := norm_mul _ _
      _ ≤ R * 1 := mul_le_mul (hb n) (h_norm_one n) (norm_nonneg _) (by linarith)
      _ = R := by simp
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hR h_norm

/-- At an index `m` where `‖b_m‖` is maximal, `‖(Σ_n b_n x_n)_m‖ = ‖b_m‖`. -/
theorem NearBasis.norm_expand_eq_of_max {x : ℕ → ℕ → K} {c : ℝ} (hx : NearBasis x c) {b : ℕ → K}
    (hb : IsC0 b) {m : ℕ} (hm : ∀ n, ‖b n‖ ≤ ‖b m‖) : ‖expand x b m‖ = ‖b m‖ := by
  have h_expand : expand x b m = b m + ∑' n, b n * (x n m - unitSeq n m) := hx.expand_eq_add hb m
  have h_norm_tsum : ‖∑' n, b n * (x n m - unitSeq n m)‖ ≤ c * ‖b m‖ :=
    hx.norm_tsum_sub_le (norm_nonneg _) hm m
  set t := ∑' n, b n * (x n m - unitSeq n m) with ht
  have h_eq : expand x b m = b m + t := h_expand
  rcases eq_or_ne (b m) 0 with (hzero | hnonzero)
  · -- case b m = 0
    have htz : t = 0 := by
      have : ‖t‖ ≤ 0 := by
        calc
          ‖t‖ ≤ c * ‖b m‖ := h_norm_tsum
          _ = c * 0 := by rw [hzero, norm_zero]
          _ = 0 := mul_zero _
      have hnorm0 : ‖t‖ = 0 := le_antisymm this (norm_nonneg _)
      exact norm_eq_zero.mp hnorm0
    rw [h_eq, hzero, htz, add_zero, norm_zero]
  · -- case b m ≠ 0
    have hpos : 0 < ‖b m‖ := by
      have h_nonneg := norm_nonneg (b m)
      have h_ne_zero : ‖b m‖ ≠ 0 := mt norm_eq_zero.mp hnonzero
      exact lt_of_le_of_ne h_nonneg h_ne_zero.symm
    have h_lt : c * ‖b m‖ < ‖b m‖ := by
      nlinarith [hx.lt_one, hpos]
    have h_norm_ne : ‖b m‖ ≠ ‖t‖ := by
      intro heq
      have hle : ‖b m‖ ≤ c * ‖b m‖ := by
        calc
          ‖b m‖ = ‖t‖ := heq
          _ ≤ c * ‖b m‖ := h_norm_tsum
      nlinarith [hx.lt_one, hpos]
    have h_t_le : ‖t‖ ≤ ‖b m‖ :=
      le_trans h_norm_tsum (le_of_lt h_lt)
    calc
      ‖expand x b m‖ = ‖b m + t‖ := by rw [h_eq]
      _ = max ‖b m‖ ‖t‖ := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_norm_ne
      _ = ‖b m‖ := max_eq_left h_t_le

/-- Lemma 6.1: `‖Σ_n b_n x_n‖ = ‖b‖` (sup norms). -/
theorem NearBasis.iSup_norm_expand {x : ℕ → ℕ → K} {c : ℝ} (hx : NearBasis x c) {b : ℕ → K} (hb : IsC0 b) :
    ⨆ i, ‖expand x b i‖ = ⨆ n, ‖b n‖ := by
  apply le_antisymm
  · -- ⨆ i, ‖expand x b i‖ ≤ ⨆ n, ‖b n‖
    refine ciSup_le fun i => ?_
    have hR : 0 ≤ ⨆ n, ‖b n‖ := by
      have h0 : 0 ≤ ‖b 0‖ := norm_nonneg _
      have hle : ‖b 0‖ ≤ ⨆ n, ‖b n‖ := by
        have hbdd : BddAbove (Set.range fun n : ℕ => ‖b n‖) := by
          obtain ⟨r, hr, hbnd⟩ := IsC0.exists_bound hb
          refine ⟨r, ?_⟩
          rintro y ⟨n, rfl⟩
          exact hbnd n
        exact le_ciSup hbdd 0
      exact h0.trans hle
    have hb_le : ∀ n, ‖b n‖ ≤ ⨆ n, ‖b n‖ := by
      intro n
      have hbdd : BddAbove (Set.range fun n' : ℕ => ‖b n'‖) := by
        obtain ⟨r, hr, hbnd⟩ := IsC0.exists_bound hb
        refine ⟨r, ?_⟩
        rintro y ⟨m, rfl⟩
        exact hbnd m
      exact le_ciSup hbdd n
    exact NearBasis.norm_expand_le hx hR hb_le i
  · -- ⨆ n, ‖b n‖ ≤ ⨆ i, ‖expand x b i‖
    refine ciSup_le fun n => ?_
    obtain ⟨m, hm⟩ := IsC0.exists_max_norm hb
    have h_eq : ‖b m‖ = ‖expand x b m‖ := (NearBasis.norm_expand_eq_of_max hx hb hm).symm
    have h_expand_le : ‖expand x b m‖ ≤ ⨆ i, ‖expand x b i‖ := by
      have hbdd : BddAbove (Set.range fun i : ℕ => ‖expand x b i‖) := by
        obtain ⟨r, hr, hbnd⟩ := IsC0.exists_bound hb
        refine ⟨r, ?_⟩
        rintro y ⟨i, rfl⟩
        exact NearBasis.norm_expand_le hx hr hbnd i
      exact le_ciSup hbdd m
    calc
      ‖b n‖ ≤ ‖b m‖ := hm n
      _ = ‖expand x b m‖ := h_eq
      _ ≤ ⨆ i, ‖expand x b i‖ := h_expand_le

end CalegariSlopes.Conj5
