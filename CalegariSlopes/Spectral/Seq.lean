/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Spectral.Defs

@[expose] public section

/-!
# Sequences over `K = ℂ_[3]`: `c₀`, `S_s`, a fixed point theorem, Lemma 6.1 (Section 6.1)

`NearBasis.summable`, `NearBasis.isC0_expand`, `NearBasis.eq_zero_of_expand_eq_zero`, `NearBasis.exists_expand_eq`,
`NearBasis.bact_expand` (Lemma 6.1) and `phiS_lt`, `phiS_gt`, `exists_iterate_phiS_nonpos` (Lemma 6.5 (b)), with the
generic facts they use: sup bounds of `c₀` sequences, the ultrametric bound of a series, a fixed point theorem for
maps of sequences contracting coordinatewise, the spaces `S_s`.
-/

open PowerSeries Filter Topology
open CalegariSlopes.Overconvergent (K S0dag U3 genEig jinv jinvK)

namespace CalegariSlopes.Spectral

/-! ## Generic facts on `c₀` and series in `K` -/

/-- A `c₀` sequence is bounded. -/
theorem IsC0.exists_bound {a : ℕ → K} (ha : IsC0 a) : ∃ r : ℝ, 0 ≤ r ∧ ∀ i, ‖a i‖ ≤ r := by
  have h_bounded : Bornology.IsBounded (Set.range a) :=
    Metric.isBounded_range_of_tendsto a ha
  obtain ⟨C, hC⟩ := (isBounded_iff_forall_norm_le.mp h_bounded)
  refine ⟨max C 0, le_max_right _ _, fun i => ?_⟩
  have h := hC (a i) ⟨i, rfl⟩
  exact le_trans h (le_max_left _ _)

/-- A sequence tending to `0` in the complete ultrametric field `K` is summable. -/
theorem summable_of_isC0 {f : ℕ → K} (hf : IsC0 f) : Summable f := by
  have hcofinite : Tendsto f Filter.cofinite (𝓝 0) := by
    simpa [IsC0, Nat.cofinite_eq_atTop] using hf
  exact NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hcofinite

/-- The ultrametric bound of a series: `‖Σ' f‖ ≤ r` when every `‖f n‖ ≤ r`. -/
theorem norm_tsum_le_of_le {f : ℕ → K} {r : ℝ} (hr : 0 ≤ r) (h : ∀ n, ‖f n‖ ≤ r) : ‖∑' n, f n‖ ≤ r := by
  exact
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hr h

/-- The ultrametric bound of a finite sum: `‖Σ_{j ∈ s} f j‖ ≤ r` when every `‖f j‖ ≤ r`. -/
theorem norm_sum_le_of_le {ι : Type*} (s : Finset ι) {f : ι → K} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ j ∈ s, ‖f j‖ ≤ r) : ‖∑ j ∈ s, f j‖ ≤ r := by
  exact
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr h

/-- A coordinatewise bound by a `c₀` sequence of norms. -/
theorem IsC0.of_norm_le {a b : ℕ → K} (hb : IsC0 b) (h : ∀ i, ‖a i‖ ≤ ‖b i‖) : IsC0 a := by
  exact squeeze_zero_norm h (tendsto_zero_iff_norm_tendsto_zero.mp hb)

theorem IsC0.add {a b : ℕ → K} (ha : IsC0 a) (hb : IsC0 b) : IsC0 (a + b) := by
  exact
    (Tendsto.add ha hb).trans (by simp)

theorem IsC0.sub {a b : ℕ → K} (ha : IsC0 a) (hb : IsC0 b) : IsC0 (a - b) := by
  have h := Filter.Tendsto.sub ha hb
  have h' : Tendsto (a - b) atTop (𝓝 (0 - 0)) := h
  simpa [IsC0, sub_self] using h'

theorem IsC0.smul {a : ℕ → K} (c : K) (ha : IsC0 a) : IsC0 (c • a) := by
  simpa [IsC0] using (ha.const_smul c).congr (fun n => by simp)

/-- Multiplying by a bounded sequence keeps `c₀`. -/
theorem IsC0.mul_bounded {a : ℕ → K} (ha : IsC0 a) (m : ℕ → K) (r : ℝ) (hm : ∀ n, ‖m n‖ ≤ r) :
    IsC0 (fun n => m n * a n) := by
  have ha_norm : Tendsto (fun n => ‖a n‖) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp ha
  have h_bound : ∀ n, ‖m n * a n‖ ≤ r * ‖a n‖ := by
    intro n
    calc
      ‖m n * a n‖ = ‖m n‖ * ‖a n‖ := norm_mul (m n) (a n)
      _ ≤ r * ‖a n‖ := mul_le_mul_of_nonneg_right (hm n) (norm_nonneg _)
  have h_tendsto : Tendsto (fun n => r * ‖a n‖) atTop (𝓝 0) := by
    simpa [zero_mul] using ha_norm.const_mul r
  exact squeeze_zero_norm h_bound h_tendsto

theorem isC0_unitSeq (n : ℕ) : IsC0 (unitSeq n) := by
  unfold IsC0 unitSeq
  refine tendsto_atTop_of_eventually_const (i₀ := n + 1) (fun i hi => ?_)
  have : i ≠ n := by omega
  simp [this]

theorem isC0_wv {n : ℕ} {y : ℕ → K} (hy : IsC0 y) : IsC0 (wv n y) := by
  have hwv : wv n y = unitSeq n + y := by
    funext j
    rfl
  rw [hwv]
  exact IsC0.add (isC0_unitSeq n) hy

/-! ## A fixed point theorem for maps of sequences -/

/-- The Banach fixed point theorem on the ball `{y ∈ c₀ : ‖y‖ ≤ r, y = 0 on Z}`, for a map contracting the
coordinatewise sup distance by `c < 1`. -/
theorem exists_fixed_seq (T : (ℕ → K) → ℕ → K) (r c : ℝ) (Z : Set ℕ) (hr : 0 ≤ r) (hc0 : 0 ≤ c)
    (hc1 : c < 1)
    (hmaps : ∀ y : ℕ → K, (∀ i, ‖y i‖ ≤ r) → (∀ i ∈ Z, y i = 0) → IsC0 y →
      (∀ i, ‖T y i‖ ≤ r) ∧ (∀ i ∈ Z, T y i = 0) ∧ IsC0 (T y))
    (hlip : ∀ y y' : ℕ → K, (∀ i, ‖y i‖ ≤ r) → (∀ i ∈ Z, y i = 0) → IsC0 y →
      (∀ i, ‖y' i‖ ≤ r) → (∀ i ∈ Z, y' i = 0) → IsC0 y' →
      ∀ d : ℝ, 0 ≤ d → (∀ i, ‖y i - y' i‖ ≤ d) → ∀ i, ‖T y i - T y' i‖ ≤ c * d) :
    ∃ y : ℕ → K, (∀ i, ‖y i‖ ≤ r) ∧ (∀ i ∈ Z, y i = 0) ∧ IsC0 y ∧ T y = y := by
  obtain ⟨ys, hys0, hys_succ⟩ : ∃ ys : ℕ → ℕ → K, ys 0 = 0 ∧ ∀ k, ys (k + 1) = T (ys k) :=
    ⟨fun k => T^[k] 0, rfl, fun k => Function.iterate_succ_apply' T k 0⟩
  have hB : ∀ k, (∀ i, ‖ys k i‖ ≤ r) ∧ (∀ i ∈ Z, ys k i = 0) ∧ IsC0 (ys k) := by
    intro k
    induction k with
    | zero =>
      rw [hys0]
      exact ⟨fun i => by simp [hr], fun i _ => rfl, tendsto_const_nhds⟩
    | succ k ih =>
      rw [hys_succ]
      exact hmaps _ ih.1 ih.2.1 ih.2.2
  have hstep : ∀ k i, ‖ys (k + 1) i - ys k i‖ ≤ r * c ^ k := by
    intro k
    induction k with
    | zero =>
      intro i
      have h := (hB 1).1 i
      rw [hys_succ 0, hys0] at h ⊢
      simpa using h
    | succ k ih =>
      intro i
      rw [hys_succ (k + 1), hys_succ k]
      have h := hlip (ys (k + 1)) (ys k) (hB _).1 (hB _).2.1 (hB _).2.2 (hB _).1 (hB _).2.1 (hB _).2.2
        (r * c ^ k) (by positivity) ih i
      rw [hys_succ k] at h
      calc ‖T (T (ys k)) i - T (ys k) i‖ ≤ c * (r * c ^ k) := h
        _ = r * c ^ (k + 1) := by ring
  have hdist : ∀ i k, dist (ys k i) (ys (k + 1) i) ≤ r * c ^ k := fun i k => by
    rw [dist_comm, dist_eq_norm]; exact hstep k i
  have hcau : ∀ i, CauchySeq fun k => ys k i := fun i => cauchySeq_of_le_geometric c r hc1 (hdist i)
  choose z hz using fun i => cauchySeq_tendsto_of_complete (hcau i)
  have hclose : ∀ k i, ‖ys k i - z i‖ ≤ r * c ^ k / (1 - c) := fun k i => by
    rw [← dist_eq_norm]; exact dist_le_of_le_geometric_of_tendsto c r hc1 (hdist i) (hz i) k
  have hpos : ∀ k : ℕ, 0 ≤ r * c ^ k / (1 - c) := fun k => div_nonneg (by positivity) (by linarith)
  have heps : Tendsto (fun k : ℕ => r * c ^ k / (1 - c)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).const_mul r).div_const (1 - c)
  have hzr : ∀ i, ‖z i‖ ≤ r := fun i => le_of_tendsto' ((hz i).norm) fun k => (hB k).1 i
  have hzZ : ∀ i ∈ Z, z i = 0 := fun i hi =>
    tendsto_nhds_unique (hz i) (tendsto_const_nhds.congr fun k => ((hB k).2.1 i hi).symm)
  have hzc : IsC0 z := by
    show Tendsto z atTop (𝓝 0)
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k, hk⟩ := (heps.eventually (gt_mem_nhds (half_pos hε))).exists
    obtain ⟨I, hI⟩ := Metric.tendsto_atTop.1 (hB k).2.2 (ε / 2) (half_pos hε)
    refine ⟨I, fun i hi => ?_⟩
    have h1 := hI i hi
    rw [dist_zero_right] at h1 ⊢
    have h2 := hclose k i
    rw [norm_sub_rev] at h2
    calc ‖z i‖ = ‖(z i - ys k i) + ys k i‖ := by rw [sub_add_cancel]
      _ ≤ ‖z i - ys k i‖ + ‖ys k i‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := by linarith
      _ = ε := add_halves ε
  refine ⟨z, hzr, hzZ, hzc, funext fun i => ?_⟩
  have h1 : Tendsto (fun k => ys (k + 1) i) atTop (𝓝 (z i)) := (hz i).comp (tendsto_add_atTop_nat 1)
  have h3 : Tendsto (fun k : ℕ => c * (r * c ^ k / (1 - c))) atTop (𝓝 0) := by
    simpa using heps.const_mul c
  have h2 : Tendsto (fun k => ys (k + 1) i) atTop (𝓝 (T z i)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) h3
    rw [hys_succ k, norm_sub_rev]
    exact hlip z (ys k) hzr hzZ hzc (hB k).1 (hB k).2.1 (hB k).2.2 _ (hpos k)
      (fun j => by rw [norm_sub_rev]; exact hclose k j) i
  exact (tendsto_nhds_unique h1 h2).symm

/-! ## Lemma 6.1: perturbation of the unit basis -/

/-- The vectors of a `NearBasis` have coordinates of norm `≤ 1`. -/
theorem NearBasis.norm_le_one {x : ℕ → ℕ → K} {c : ℝ} (hx : NearBasis x c) (n i : ℕ) : ‖x n i‖ ≤ 1 := by
  have h_near : ‖x n i - unitSeq n i‖ ≤ c := hx.near n i
  have h_unit : ‖unitSeq n i‖ ≤ 1 := by
    unfold unitSeq
    split
    · exact norm_one.le
    · exact norm_zero.le.trans (by norm_num)
  have h_max : max c 1 = 1 := by
    exact max_eq_right (le_of_lt hx.lt_one)
  calc
    ‖x n i‖ = ‖(x n i - unitSeq n i) + unitSeq n i‖ := by
      simp [sub_add_cancel]
    _ ≤ max ‖x n i - unitSeq n i‖ ‖unitSeq n i‖ :=
      IsUltrametricDist.norm_add_le_max _ _
    _ ≤ max c 1 := max_le_max h_near h_unit
    _ = 1 := h_max

/-- The series `Σ_n b_n x_n i` converges for `b ∈ c₀`. -/
theorem NearBasis.summable {x : ℕ → ℕ → K} {c : ℝ} (hx : NearBasis x c) {b : ℕ → K} (hb : IsC0 b)
    (i : ℕ) : Summable fun n => b n * x n i := by
  have h : ∀ n, ‖b n * x n i‖ ≤ ‖b n‖ := by
    intro n
    calc
      ‖b n * x n i‖ = ‖b n‖ * ‖x n i‖ := norm_mul (b n) (x n i)
      _ ≤ ‖b n‖ * 1 := mul_le_mul_of_nonneg_left (hx.norm_le_one n i) (norm_nonneg _)
      _ = ‖b n‖ := mul_one _
  have h_isC0 : IsC0 (fun n => b n * x n i) := IsC0.of_norm_le hb h
  exact summable_of_isC0 h_isC0

/-- `Σ_n b_n x_n i = b_i + Σ_n b_n (x_n - e_n)_i`. -/
theorem NearBasis.expand_eq_add {x : ℕ → ℕ → K} {c : ℝ} (hx : NearBasis x c) {b : ℕ → K} (hb : IsC0 b)
    (i : ℕ) : expand x b i = b i + ∑' n, b n * (x n i - unitSeq n i) := by
  have hsum_unit : Summable fun n : ℕ => b n * unitSeq n i := by
    have h := hasSum_single (f := fun n => b n * unitSeq n i) i (fun n hn => by
      have : unitSeq n i = 0 := by simp [unitSeq, hn.symm]
      rw [this, mul_zero])
    exact h.summable
  have hsum_diff : Summable fun n : ℕ => b n * (x n i - unitSeq n i) := by
    have hsum_x : Summable fun n : ℕ => b n * x n i := hx.summable hb i
    have h := hsum_x.sub hsum_unit
    simpa [mul_sub] using h
  calc
    expand x b i = ∑' n, b n * x n i := rfl
    _ = ∑' n, (b n * unitSeq n i + b n * (x n i - unitSeq n i)) := by
      refine tsum_congr (fun n => ?_)
      ring
    _ = (∑' n, b n * unitSeq n i) + (∑' n, b n * (x n i - unitSeq n i)) := by
      rw [Summable.tsum_add hsum_unit hsum_diff]
    _ = b i + ∑' n, b n * (x n i - unitSeq n i) := by
      have htsum : ∑' n, b n * unitSeq n i = b i := by
        rw [tsum_eq_single i (fun n hn => by simp [unitSeq, hn.symm])]
        simp [unitSeq]
      rw [htsum]

/-- `‖Σ_n b_n (x_n - e_n)_i‖ ≤ c r` when `‖b‖ ≤ r`. -/
theorem NearBasis.norm_tsum_sub_le {x : ℕ → ℕ → K} {c : ℝ} (hx : NearBasis x c) {b : ℕ → K} {r : ℝ}
    (hr : 0 ≤ r) (hb : ∀ n, ‖b n‖ ≤ r) (i : ℕ) : ‖∑' n, b n * (x n i - unitSeq n i)‖ ≤ c * r := by
  have h_nonneg_cr : 0 ≤ c * r := mul_nonneg hx.nonneg hr
  apply norm_tsum_le_of_le h_nonneg_cr
  intro n
  calc
    ‖b n * (x n i - unitSeq n i)‖ = ‖b n‖ * ‖x n i - unitSeq n i‖ := norm_mul _ _
    _ ≤ r * c := mul_le_mul (hb n) (hx.near n i) (norm_nonneg _) hr
    _ = c * r := mul_comm _ _

/-- Lemma 6.1: `Σ_n b_n x_n` is in `c₀`. -/
theorem NearBasis.isC0_expand {x : ℕ → ℕ → K} {c : ℝ} (hx : NearBasis x c) {b : ℕ → K} (hb : IsC0 b) :
    IsC0 (expand x b) := by
  have hP : IsC0 (fun i => ∑' n, b n * (x n i - unitSeq n i)) := by
    obtain ⟨R, hR0, hR⟩ := hb.exists_bound
    show Tendsto _ atTop (𝓝 0)
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hb (ε / 2) (half_pos hε)
    have hR1 : 0 < R + 1 := by linarith
    have hxn : ∀ n, Tendsto (fun i => x n i - unitSeq n i) atTop (𝓝 0) := fun n => by
      exact (hx.isC0 n).sub (isC0_unitSeq n)
    have hev : ∀ᶠ i in atTop, ∀ n ∈ Finset.range N, ‖x n i - unitSeq n i‖ < ε / (2 * (R + 1)) := by
      rw [Filter.eventually_all_finset]
      intro n _
      exact (tendsto_zero_iff_norm_tendsto_zero.1 (hxn n)).eventually (gt_mem_nhds (by positivity))
    obtain ⟨I, hI⟩ := Filter.eventually_atTop.1 hev
    refine ⟨I, fun i hi => ?_⟩
    rw [dist_zero_right]
    have h : ‖∑' n, b n * (x n i - unitSeq n i)‖ ≤ ε / 2 := by
      apply norm_tsum_le_of_le (by positivity)
      intro n
      rw [norm_mul]
      by_cases hn : n < N
      · have h1 := hI i hi n (Finset.mem_range.2 hn)
        calc ‖b n‖ * ‖x n i - unitSeq n i‖ ≤ R * (ε / (2 * (R + 1))) :=
              mul_le_mul (hR n) h1.le (norm_nonneg _) hR0
          _ = ε / 2 * (R / (R + 1)) := by field_simp
          _ ≤ ε / 2 * 1 := by
              gcongr
              exact div_le_one_of_le₀ (by linarith) hR1.le
          _ = ε / 2 := mul_one _
      · have h1 := hN n (not_lt.1 hn)
        rw [dist_zero_right] at h1
        calc ‖b n‖ * ‖x n i - unitSeq n i‖ ≤ (ε / 2) * 1 :=
              mul_le_mul h1.le ((hx.near n i).trans hx.lt_one.le) (norm_nonneg _) (by positivity)
          _ = ε / 2 := mul_one _
    linarith
  have heq : expand x b = b + fun i => ∑' n, b n * (x n i - unitSeq n i) :=
    funext fun i => hx.expand_eq_add hb i
  rw [heq]
  exact hb.add hP

/-- `expand` is additive on `c₀`. -/
theorem NearBasis.expand_add {x : ℕ → ℕ → K} {c : ℝ} (hx : NearBasis x c) {b b' : ℕ → K} (hb : IsC0 b)
    (hb' : IsC0 b') : expand x (b + b') = expand x b + expand x b' := by
  funext i
  have h1 := hx.summable hb i
  have h2 := hx.summable hb' i
  calc
    expand x (b + b') i = ∑' n, (b + b') n * x n i := rfl
    _ = ∑' n, (b n + b' n) * x n i := rfl
    _ = ∑' n, (b n * x n i + b' n * x n i) := by simp [add_mul]
    _ = (∑' n, b n * x n i) + (∑' n, b' n * x n i) := (h1.hasSum.add h2.hasSum).tsum_eq
    _ = expand x b i + expand x b' i := rfl

/-- `expand` is homogeneous. -/
theorem expand_smul (x : ℕ → ℕ → K) (c : K) (b : ℕ → K) : expand x (c • b) = c • expand x b := by
  funext i
  simp only [expand, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [tsum_mul_left]

/-- Lemma 6.1, injectivity (`‖Σ_n b_n x_n‖ = ‖b‖`). -/
theorem NearBasis.eq_zero_of_expand_eq_zero {x : ℕ → ℕ → K} {c : ℝ} (hx : NearBasis x c) {b : ℕ → K}
    (hb : IsC0 b) (h : expand x b = 0) : b = 0 := by
  obtain ⟨R, hR_nonneg, hR_bound⟩ := hb.exists_bound
  have h_bound_pow : ∀ k : ℕ, ∀ i : ℕ, ‖b i‖ ≤ c ^ k * R := by
    intro k
    induction' k with k ih
    · intro i; simpa using hR_bound i
    · intro i
      have h_expand_zero : expand x b i = 0 := by rw [h, Pi.zero_apply]
      have h_add := hx.expand_eq_add hb i
      rw [h_expand_zero] at h_add
      have h_eq : b i = -∑' n, b n * (x n i - unitSeq n i) := by
        have h_add' := h_add.symm
        exact (add_eq_zero_iff_eq_neg.mp h_add')
      rw [h_eq, norm_neg]
      have h_nonneg : 0 ≤ c ^ k * R := by
        have hc_pow : 0 ≤ c ^ k := pow_nonneg hx.nonneg k
        nlinarith
      have h_tsum := hx.norm_tsum_sub_le h_nonneg ih i
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using h_tsum
  have h_tendsto : Tendsto (fun k : ℕ => c ^ k * R) atTop (𝓝 0) := by
    have h_c_pow : Tendsto (fun k : ℕ => c ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hx.nonneg hx.lt_one
    simpa using h_c_pow.mul_const R
  ext i
  have h_norm_le_zero : ‖b i‖ ≤ 0 := by
    have h_le : ∀ k : ℕ, ‖b i‖ ≤ (fun k : ℕ => c ^ k * R) k := by
      intro k; exact h_bound_pow k i
    exact ge_of_tendsto' h_tendsto h_le
  have h_norm_zero : ‖b i‖ = 0 := by linarith [norm_nonneg (b i), h_norm_le_zero]
  exact norm_eq_zero.mp h_norm_zero

/-- Lemma 6.1: every `F ∈ c₀` is `Σ_n b_n x_n` for some `b ∈ c₀` (fixed point of `b ↦ F - (X - I) b`). -/
theorem NearBasis.exists_expand_eq {x : ℕ → ℕ → K} {c : ℝ} (hx : NearBasis x c) {F : ℕ → K}
    (hF : IsC0 F) : ∃ b, IsC0 b ∧ expand x b = F := by
  -- Get a bound r for F
  obtain ⟨r, hr, hF_bound⟩ := IsC0.exists_bound hF
  have hc_nonneg : 0 ≤ c := hx.nonneg
  have hc_lt_one : c < 1 := hx.lt_one
  -- Define the map T for the fixed point theorem
  set T : (ℕ → K) → ℕ → K := fun b i => F i - ∑' n, b n * (x n i - unitSeq n i) with hT_def
  -- Apply the Banach fixed point theorem on c₀
  obtain ⟨b, hb_bound, hbZ, hb_isC0, hb_fixed⟩ := exists_fixed_seq
    T r c (∅ : Set ℕ) hr hc_nonneg hc_lt_one
    (by
      -- hmaps: T maps the ball of radius r into itself, preserves Z = ∅, and preserves c₀
      intro y hy_bound hyZ hy_isC0
      have hTy_bound : ∀ i, ‖T y i‖ ≤ r := by
        intro i
        dsimp [T]
        -- By the ultrametric inequality: ‖a - b‖ ≤ max ‖a‖ ‖b‖
        have h_norm : ‖F i - ∑' n, y n * (x n i - unitSeq n i)‖ ≤
            max ‖F i‖ ‖∑' n, y n * (x n i - unitSeq n i)‖ := by
          calc
            ‖F i - ∑' n, y n * (x n i - unitSeq n i)‖ =
                ‖F i + (-(∑' n, y n * (x n i - unitSeq n i)))‖ := by
              congr 1
              ring
            _ ≤ max ‖F i‖ ‖-(∑' n, y n * (x n i - unitSeq n i))‖ :=
              IsUltrametricDist.norm_add_le_max _ _
            _ = max ‖F i‖ ‖∑' n, y n * (x n i - unitSeq n i)‖ := by simp
        have h_bound1 : ‖F i‖ ≤ r := hF_bound i
        have h_bound2 : ‖∑' n, y n * (x n i - unitSeq n i)‖ ≤ c * r :=
          NearBasis.norm_tsum_sub_le hx hr hy_bound i
        have h_cr_le_r : c * r ≤ r := by
          have hc_le_one : c ≤ 1 := by linarith
          nlinarith
        have h_max : max ‖F i‖ ‖∑' n, y n * (x n i - unitSeq n i)‖ ≤ r :=
          max_le h_bound1 (h_bound2.trans h_cr_le_r)
        exact h_norm.trans h_max
      have hTyZ : ∀ i ∈ (∅ : Set ℕ), T y i = 0 := by
        intro i hi; exfalso; exact hi
      have hTy_isC0 : IsC0 (T y) := by
        have h_expand_isC0 : IsC0 (expand x y) := NearBasis.isC0_expand hx hy_isC0
        have h_eq : T y = F - (expand x y - y) := by
          ext i
          dsimp [T]
          rw [NearBasis.expand_eq_add hx hy_isC0 i]
          ring
        rw [h_eq]
        exact IsC0.sub hF (IsC0.sub h_expand_isC0 hy_isC0)
      exact ⟨hTy_bound, hTyZ, hTy_isC0⟩)
    (by
      -- hlip: T is Lipschitz with constant c
      intro y y' hy_bound hyZ hy_isC0 hy'_bound hy'Z hy'_isC0 d hd h_norm_diff
      intro i
      dsimp [T]
      -- We need: ‖(F i - ∑' n, y n * (x n i - unitSeq n i)) - (F i - ∑' n, y' n * (x n i - unitSeq n i))‖ ≤ c * d
      -- First, simplify the expression using tsum_sub
      have h_summable_y : Summable fun n : ℕ => y n * (x n i - unitSeq n i) := by
        apply summable_of_isC0
        simpa [mul_comm] using IsC0.mul_bounded hy_isC0 (fun n => x n i - unitSeq n i) c (fun n => hx.near n i)
      have h_summable_y' : Summable fun n : ℕ => y' n * (x n i - unitSeq n i) := by
        apply summable_of_isC0
        simpa [mul_comm] using IsC0.mul_bounded hy'_isC0 (fun n => x n i - unitSeq n i) c (fun n => hx.near n i)
      have h_sub_eq : (F i - ∑' n, y n * (x n i - unitSeq n i)) -
          (F i - ∑' n, y' n * (x n i - unitSeq n i)) =
          ∑' n, (y' n - y n) * (x n i - unitSeq n i) := by
        calc
          (F i - ∑' n, y n * (x n i - unitSeq n i)) - (F i - ∑' n, y' n * (x n i - unitSeq n i)) =
              (∑' n, y' n * (x n i - unitSeq n i)) - (∑' n, y n * (x n i - unitSeq n i)) := by ring
          _ = ∑' n, (y' n * (x n i - unitSeq n i) - y n * (x n i - unitSeq n i)) := by
            rw [← Summable.tsum_sub h_summable_y' h_summable_y]
          _ = ∑' n, ((y' n - y n) * (x n i - unitSeq n i)) := by
            refine tsum_congr fun n => ?_
            ring
      rw [h_sub_eq]
      -- Now apply NearBasis.norm_tsum_sub_le to (y' - y)
      have h_norm_yy' : ∀ n, ‖(y' - y) n‖ ≤ d := by
        intro n
        calc
          ‖(y' - y) n‖ = ‖y' n - y n‖ := rfl
          _ = ‖-(y n - y' n)‖ := by rw [neg_sub]
          _ = ‖y n - y' n‖ := by rw [norm_neg]
          _ ≤ d := h_norm_diff n
      exact NearBasis.norm_tsum_sub_le hx hd h_norm_yy' i)
  -- From the fixed point b = T b, derive expand x b = F
  have h_expand : expand x b = F := by
    ext i
    calc
      expand x b i = b i + ∑' n, b n * (x n i - unitSeq n i) := by
        rw [NearBasis.expand_eq_add hx hb_isC0 i]
      _ = (F i - ∑' n, b n * (x n i - unitSeq n i)) + ∑' n, b n * (x n i - unitSeq n i) := by
        -- hb_fixed : T b = b, so T b i = b i, i.e., F i - ∑' n, b n * (x n i - unitSeq n i) = b i
        have h_fixed_i : T b i = b i := by rw [hb_fixed]
        dsimp [T] at h_fixed_i
        rw [h_fixed_i]
      _ = F i := by ring
  exact ⟨b, hb_isC0, h_expand⟩

/-- A banded matrix acts termwise on `Σ_n b_n x_n` (Lemma 6.1, for finite rows). -/
theorem NearBasis.bact_expand {x : ℕ → ℕ → K} {c : ℝ} (hx : NearBasis x c) {b : ℕ → K} (hb : IsC0 b)
    (M : ℕ → ℕ → ℚ) : bact M (expand x b) = expand (fun n => bact M (x n)) b := by
  funext i
  simp only [bact, expand]
  calc
    ∑ j ∈ Finset.Icc 1 (3 * i), (M i j : K) * (∑' n, b n * x n j)
        = ∑ j ∈ Finset.Icc 1 (3 * i), ∑' n, (M i j : K) * (b n * x n j) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [tsum_mul_left]
    _ = ∑' n, ∑ j ∈ Finset.Icc 1 (3 * i), (M i j : K) * (b n * x n j) := by
      refine (Summable.tsum_finsetSum ?_).symm
      intro j hj
      have hsum := hx.summable hb j
      exact hsum.mul_left (M i j : K)
    _ = ∑' n, b n * (∑ j ∈ Finset.Icc 1 (3 * i), (M i j : K) * x n j) := by
      refine tsum_congr fun n => ?_
      simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
    _ = ∑' n, b n * bact M (x n) i := rfl

/-! ## The spaces `S_s` -/

theorem InS_zero_iff (a : ℕ → K) : InS 0 a ↔ IsC0 a := by
  simp [InS, IsC0, tendsto_zero_iff_norm_tendsto_zero]

/-- `S_s ⊆ S_t` for `s ≤ t`. -/
theorem InS.mono {s t : ℝ} (hst : s ≤ t) {a : ℕ → K} (ha : InS s a) : InS t a := by
  unfold InS at ha ⊢
  have h_nonneg : ∀ j, 0 ≤ ‖a j‖ * (3 : ℝ) ^ (-(t * j)) := by
    intro j
    have h_norm : 0 ≤ ‖a j‖ := norm_nonneg _
    have h_rpow : 0 ≤ (3 : ℝ) ^ (-(t * (j : ℝ))) := Real.rpow_nonneg (by norm_num) _
    exact mul_nonneg h_norm h_rpow
  have h_le : ∀ j, ‖a j‖ * (3 : ℝ) ^ (-(t * j)) ≤ ‖a j‖ * (3 : ℝ) ^ (-(s * j)) := by
    intro j
    have h_exp : -(t * (j : ℝ)) ≤ -(s * (j : ℝ)) := by
      have h_mul : s * (j : ℝ) ≤ t * (j : ℝ) :=
        mul_le_mul_of_nonneg_right hst (by exact mod_cast Nat.zero_le j)
      linarith
    have h_rpow : (3 : ℝ) ^ (-(t * (j : ℝ))) ≤ (3 : ℝ) ^ (-(s * (j : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h_exp
    gcongr
  have h_zero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h_zero ha h_nonneg h_le

theorem InS.add {s : ℝ} {a b : ℕ → K} (ha : InS s a) (hb : InS s b) : InS s (a + b) := by
  unfold InS
  have hsum : Tendsto (fun j : ℕ => ‖a j‖ * (3 : ℝ) ^ (-(s * j)) + ‖b j‖ * (3 : ℝ) ^ (-(s * j))) atTop (𝓝 (0 + 0)) :=
    Tendsto.add ha hb
  have hsum0 : Tendsto (fun j : ℕ => ‖a j‖ * (3 : ℝ) ^ (-(s * j)) + ‖b j‖ * (3 : ℝ) ^ (-(s * j))) atTop (𝓝 0) := by
    simpa [add_zero] using hsum
  apply squeeze_zero
  · intro j
    positivity
  · intro j
    have hnorm : ‖(a + b) j‖ ≤ ‖a j‖ + ‖b j‖ := by
      calc
        ‖(a + b) j‖ = ‖a j + b j‖ := rfl
        _ ≤ ‖a j‖ + ‖b j‖ := norm_add_le _ _
    have hpos : 0 ≤ (3 : ℝ) ^ (-(s * (j : ℝ))) := by positivity
    have := mul_le_mul_of_nonneg_right hnorm hpos
    -- this gives ‖(a+b)j‖ * 3^(-s*j) ≤ (‖a j‖ + ‖b j‖) * 3^(-s*j)
    -- and (‖a j‖ + ‖b j‖) * 3^(-s*j) = ‖a j‖ * 3^(-s*j) + ‖b j‖ * 3^(-s*j)
    calc
      ‖(a + b) j‖ * (3 : ℝ) ^ (-(s * (j : ℝ))) ≤ (‖a j‖ + ‖b j‖) * (3 : ℝ) ^ (-(s * (j : ℝ))) :=
        mul_le_mul_of_nonneg_right hnorm hpos
      _ = ‖a j‖ * (3 : ℝ) ^ (-(s * (j : ℝ))) + ‖b j‖ * (3 : ℝ) ^ (-(s * (j : ℝ))) := by ring
  · exact hsum0

theorem InS.smul {s : ℝ} (c : K) {a : ℕ → K} (ha : InS s a) : InS s (c • a) := by
  simpa [InS, norm_smul, mul_assoc] using ha.const_mul ‖c‖

theorem InS.zero (s : ℝ) : InS s (0 : ℕ → K) := by
  simp [InS]

theorem InS.sum {s : ℝ} {ι : Type*} (t : Finset ι) {a : ι → ℕ → K} (ha : ∀ i ∈ t, InS s (a i)) :
    InS s (∑ i ∈ t, a i) := by
  classical
    induction' t using Finset.induction_on with i t hi ih
    · simp [InS]
    · rw [Finset.sum_insert hi]
      have hi_mem : InS s (a i) := ha i (Finset.mem_insert_self i t)
      have hsum_mem : InS s (∑ j ∈ t, a j) := ih fun j hj => ha j (Finset.mem_insert_of_mem hj)
      have add_lemma {a b : ℕ → K} (ha' : InS s a) (hb' : InS s b) : InS s (a + b) := by
        have ha_tendsto : Tendsto (fun j : ℕ => ‖a j‖ * (3 : ℝ) ^ (-(s * (j : ℝ)))) atTop (𝓝 0) := ha'
        have hb_tendsto : Tendsto (fun j : ℕ => ‖b j‖ * (3 : ℝ) ^ (-(s * (j : ℝ)))) atTop (𝓝 0) := hb'
        have h_norm (j : ℕ) : ‖(a + b) j‖ * (3 : ℝ) ^ (-(s * (j : ℝ))) ≤
            ‖a j‖ * (3 : ℝ) ^ (-(s * (j : ℝ))) + ‖b j‖ * (3 : ℝ) ^ (-(s * (j : ℝ))) := by
          have h := norm_add_le (a j) (b j)
          have hpos' : 0 ≤ (3 : ℝ) ^ (-(s * (j : ℝ))) := by positivity
          calc
            ‖(a + b) j‖ * (3 : ℝ) ^ (-(s * (j : ℝ))) = ‖a j + b j‖ * (3 : ℝ) ^ (-(s * (j : ℝ))) := by simp
            _ ≤ (‖a j‖ + ‖b j‖) * (3 : ℝ) ^ (-(s * (j : ℝ))) := by gcongr
            _ = ‖a j‖ * (3 : ℝ) ^ (-(s * (j : ℝ))) + ‖b j‖ * (3 : ℝ) ^ (-(s * (j : ℝ))) := by ring
        have hsum : Tendsto (fun j : ℕ => ‖a j‖ * (3 : ℝ) ^ (-(s * (j : ℝ))) + ‖b j‖ * (3 : ℝ) ^ (-(s * (j : ℝ)))) atTop (𝓝 0) := by
          simpa using ha_tendsto.add hb_tendsto
        have h_nonneg : ∀ j, (0 : ℝ) ≤ ‖(a + b) j‖ * (3 : ℝ) ^ (-(s * (j : ℝ))) := by
          intro j; positivity
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum h_nonneg h_norm
      exact add_lemma hi_mem hsum_mem

/-! ## Lemma 6.5 (b): the map `φ` -/

/-- Lemma 6.5 (b): `φ(s) < s` on `(-3, 3)`. -/
theorem phiS_lt {s : ℝ} (h1 : -3 < s) (h2 : s < 3) : phiS s < s := by
  unfold phiS
  apply max_lt
  · linarith
  · linarith

/-- Lemma 6.5 (b): `φ` maps `(-3, 3)` into `(-3, 3)` (lower end). -/
theorem phiS_gt {s : ℝ} (h1 : -3 < s) (h2 : s < 3) : -3 < phiS s := by
  have h : -3 < s / 3 - 2 := by
    linarith
  have hle : s / 3 - 2 ≤ phiS s := le_max_right _ _
  linarith

/-- Lemma 6.5 (b): the iterates of `φ` from `s ∈ (-3, 3)` reach `(-∞, 0]`. -/
theorem exists_iterate_phiS_nonpos {s : ℝ} (h1 : -3 < s) (h2 : s < 3) : ∃ m : ℕ, phiS^[m] s ≤ 0 := by
  have hpos : 0 < 3 - s := sub_pos.mpr h2
  have h_main : ∀ k : ℕ, ∀ s : ℝ, -3 < s → s < 3 → (3/2 : ℝ) ≤ ((3 : ℝ) ^ k * (3 - s)) → ∃ m : ℕ, phiS^[m] s ≤ 0 := by
    intro k
    induction' k with k ih
    · intro s hs1 hs2 h
      have hsq : s ≤ 3/2 := by linarith
      by_cases hs0 : s ≤ 0
      · refine ⟨0, ?_⟩
        simpa [Function.iterate_zero_apply] using hs0
      · push Not at hs0
        have hineq1 : 3 * s - 6 ≤ s / 3 - 2 := by
          nlinarith
        have hphiS_eq : phiS s = s / 3 - 2 := by
          dsimp [phiS]
          exact max_eq_right hineq1
        have hphiS_nonpos : phiS s ≤ 0 := by
          rw [hphiS_eq]
          nlinarith
        refine ⟨1, ?_⟩
        simpa [Function.iterate_one] using hphiS_nonpos
    · intro s hs1 hs2 h
      by_cases hsq : s ≤ 3/2
      · have hineq1 : 3 * s - 6 ≤ s / 3 - 2 := by
          nlinarith
        have hphiS_eq : phiS s = s / 3 - 2 := by
          dsimp [phiS]
          exact max_eq_right hineq1
        have hphiS_nonpos : phiS s ≤ 0 := by
          rw [hphiS_eq]
          nlinarith
        refine ⟨1, ?_⟩
        simpa [Function.iterate_one] using hphiS_nonpos
      · push Not at hsq
        have hineq2 : s / 3 - 2 ≤ 3 * s - 6 := by
          nlinarith
        have hphiS_eq : phiS s = 3 * s - 6 := by
          dsimp [phiS]
          exact max_eq_left hineq2
        have hphiS_gt : -3 < phiS s := phiS_gt hs1 hs2
        have hphiS_lt' : phiS s < s := phiS_lt hs1 hs2
        have hphiS_lt : phiS s < 3 := by linarith
        have h_three_sub_phiS : 3 - phiS s = 3 * (3 - s) := by
          rw [hphiS_eq]
          ring
        have h_ineq : (3/2 : ℝ) ≤ ((3 : ℝ) ^ k * (3 - phiS s)) := by
          rw [h_three_sub_phiS]
          have : ((3 : ℝ) ^ k * (3 * (3 - s))) = ((3 : ℝ) ^ (k + 1) * (3 - s)) := by
            ring
          rw [this]
          exact h
        rcases ih (phiS s) hphiS_gt hphiS_lt h_ineq with ⟨m, hm⟩
        refine ⟨m + 1, ?_⟩
        rw [Function.iterate_succ_apply]
        exact hm
  have h_exists_k : ∃ k : ℕ, (3/2 : ℝ) ≤ ((3 : ℝ) ^ k * (3 - s)) := by
    have h_arch : ∃ k : ℕ, (3/2 : ℝ) / (3 - s) < (3 : ℝ) ^ k := by
      have h_one_lt_three : 1 < (3 : ℝ) := by norm_num
      exact pow_unbounded_of_one_lt ((3/2 : ℝ) / (3 - s)) h_one_lt_three
    rcases h_arch with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h_mul : (3/2 : ℝ) < ((3 : ℝ) ^ k * (3 - s)) := by
      calc
        (3/2 : ℝ) = ((3/2 : ℝ) / (3 - s)) * (3 - s) := by field_simp [hpos.ne.symm]
        _ < (3 : ℝ) ^ k * (3 - s) := by
          nlinarith
    linarith
  rcases h_exists_k with ⟨k, hk⟩
  exact h_main k s h1 h2 hk

/-! ## A decay lemma for Proposition 2.2 (ii) -/

/-- If `f j ≤ e m ρ ^ (j - m)` for some `m ≤ j`, with `e → 0`, `e ≥ 0` and `0 ≤ ρ < 1`, then `f → 0`
(for `f ≥ 0`). -/
theorem tendsto_zero_of_le_geom (f e : ℕ → ℝ) (ρ : ℝ) (hf : ∀ j, 0 ≤ f j) (he0 : ∀ m, 0 ≤ e m)
    (he : Tendsto e atTop (𝓝 0)) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (h : ∀ j, ∃ m ≤ j, f j ≤ e m * ρ ^ (j - m)) : Tendsto f atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Since e → 0, eventually e m < ε
  have he_metric := (Metric.tendsto_atTop.mp he) ε hε
  rcases he_metric with ⟨M, hM⟩
  have hM' : ∀ m ≥ M, e m < ε := by
    intro m hm
    have hdist := hM m hm
    rw [Real.dist_eq, sub_zero] at hdist
    have habs : |e m| = e m := abs_of_nonneg (he0 m)
    rw [habs] at hdist
    exact hdist
  -- e is bounded above (since convergent)
  have h_bdd : BddAbove (Set.range e) := he.bddAbove_range
  rcases h_bdd with ⟨E, hE⟩
  have hE_nonneg : 0 ≤ E := by
    have h0 : e 0 ∈ Set.range e := ⟨0, rfl⟩
    have h0E := hE h0
    linarith [he0 0, h0E]
  have hE_bound : ∀ m, e m ≤ E := by
    intro m
    apply hE
    exact ⟨m, rfl⟩
  -- Since ρ^n → 0, we have E * ρ^n → 0
  have hρ_tendsto : Tendsto (fun n : ℕ => ρ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
  have hEρ_tendsto : Tendsto (fun n : ℕ => E * ρ ^ n) atTop (𝓝 0) := by
    have := hρ_tendsto.const_mul E
    simpa [mul_comm] using this
  have hEρ_metric := (Metric.tendsto_atTop.mp hEρ_tendsto) ε hε
  rcases hEρ_metric with ⟨L, hL⟩
  have hL' : ∀ n ≥ L, E * ρ ^ n < ε := by
    intro n hn
    have hdist := hL n hn
    rw [Real.dist_eq, sub_zero] at hdist
    have habs : |E * ρ ^ n| = E * ρ ^ n := abs_of_nonneg (by
      have hpow : 0 ≤ ρ ^ n := pow_nonneg hρ0 n
      nlinarith)
    rw [habs] at hdist
    exact hdist
  refine ⟨M + L, ?_⟩
  intro j hj
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hf j)]
  have hj_sum : M + L ≤ j := hj
  rcases h j with ⟨m, hm_le_j, hm_bound⟩
  by_cases hm_lt : m < M
  · -- case m < M
    have h_j_sub_m_ge_L : L ≤ j - m := by
      omega
    have h_pow : ρ ^ (j - m) ≤ ρ ^ L :=
      pow_le_pow_of_le_one hρ0 (by linarith) h_j_sub_m_ge_L
    have h_f_bound : f j ≤ E * ρ ^ L := by
      calc
        f j ≤ e m * ρ ^ (j - m) := hm_bound
        _ ≤ E * ρ ^ (j - m) := by
          nlinarith [hE_bound m, pow_nonneg hρ0 (j - m)]
        _ ≤ E * ρ ^ L := by nlinarith
    have h_lt : E * ρ ^ L < ε := hL' L (le_refl L)
    nlinarith
  · -- case M ≤ m
    have hm_ge_M : M ≤ m := by omega
    have h_pow_le_one : ρ ^ (j - m) ≤ 1 := by
      have h_nat : 0 ≤ j - m := Nat.zero_le _
      calc
        ρ ^ (j - m) ≤ ρ ^ 0 := pow_le_pow_of_le_one hρ0 (by linarith) h_nat
        _ = 1 := pow_zero _
    have h_f_bound : f j ≤ e m := by
      calc
        f j ≤ e m * ρ ^ (j - m) := hm_bound
        _ ≤ e m * 1 := mul_le_mul_of_nonneg_left h_pow_le_one (he0 m)
        _ = e m := mul_one _
    have h_lt : e m < ε := hM' m hm_ge_M
    nlinarith

end CalegariSlopes.Spectral
