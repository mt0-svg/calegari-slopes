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
# Diagonalization in `c₀` (Theorem 2.4 (b))

`EigenFamily.diag`, Theorem 2.4 (b), as in its proof in Section 6.3: `U (Σ b_n x_n) = Σ λ_n b_n x_n`, hence
`(U - μ) ^ k (Σ b_n x_n) = Σ (λ_n - μ) ^ k b_n x_n`, and the uniqueness of Lemma 6.1.
-/

open PowerSeries Filter Topology
open CalegariSlopes.Overconvergent (K S0dag U3 genEig jinv jinvK)

namespace CalegariSlopes.Spectral

/-- `‖λ_n‖ ≤ 1`. -/
theorem EigenFamily.norm_lam_le_one (E : EigenFamily) (n : ℕ) : ‖E.lam n‖ ≤ 1 := by
  by_cases hn : n = 0
  · subst hn
    rw [E.lam_zero, norm_zero]
    exact by norm_num
  · have hn1 : 1 ≤ n := Nat.one_le_of_lt (Nat.pos_of_ne_zero hn)
    rw [E.norm_lam n hn1]
    have hpos : 1 ≤ (3 : ℝ) := by norm_num
    have hnonpos : -(slope n : ℤ) ≤ 0 := by
      have hslope_nonneg : 0 ≤ (slope n : ℤ) := Nat.cast_nonneg _
      linarith
    exact zpow_le_one_of_nonpos₀ hpos hnonpos

/-- `U (Σ_n b_n x_n) = Σ_n λ_n b_n x_n` (proof of Theorem 2.4 (b)). -/
theorem EigenFamily.Uop_expand (E : EigenFamily) {b : ℕ → K} (hb : IsC0 b) :
    Uop (expand E.x b) = expand E.x (fun n => E.lam n * b n) := by
  calc
    Uop (expand E.x b) = bact u (expand E.x b) := rfl
    _ = expand (fun n => bact u (E.x n)) b := NearBasis.bact_expand E.near hb u
    _ = expand (fun n => Uop (E.x n)) b := rfl
    _ = expand (fun n => E.lam n • E.x n) b := by
      simp [E.eig]
    _ = expand E.x (fun n => E.lam n * b n) := by
      ext i
      simp [expand, Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm]

/-- `(U - μ) ^ k (Σ_n b_n x_n) = Σ_n (λ_n - μ) ^ k b_n x_n`, and the new coefficients are in `c₀`. -/
theorem EigenFamily.iterate_expand (E : EigenFamily) (μ : K) (k : ℕ) {b : ℕ → K} (hb : IsC0 b) :
    IsC0 (fun n => (E.lam n - μ) ^ k * b n) ∧
      ((Uop - μ • (1 : Module.End K (ℕ → K))) ^ k) (expand E.x b) =
        expand E.x (fun n => (E.lam n - μ) ^ k * b n) := by
  induction' k with k ih
  · -- k = 0
    refine ⟨?_, ?_⟩
    · -- IsC0 (fun n => (E.lam n - μ) ^ 0 * b n)
      simp [hb]
    · -- ((Uop - μ • 1) ^ 0) (expand E.x b) = expand E.x (fun n => (E.lam n - μ) ^ 0 * b n)
      simp
  · -- k → k+1
    rcases ih with ⟨hC0, hEq⟩
    set b' := fun n : ℕ => (E.lam n - μ) ^ k * b n with hb'_def
    have hb'_c0 : IsC0 b' := hC0
    have h_bound : ∀ n, ‖E.lam n - μ‖ ≤ 1 + ‖μ‖ := by
      intro n
      calc
        ‖E.lam n - μ‖ ≤ ‖E.lam n‖ + ‖μ‖ := norm_sub_le _ _
        _ ≤ 1 + ‖μ‖ := by
          have h := EigenFamily.norm_lam_le_one E n
          nlinarith
    have h_lam_sub_mu_c0 : IsC0 (fun n => (E.lam n - μ) * b' n) :=
      IsC0.mul_bounded hb'_c0 (fun n => E.lam n - μ) (1 + ‖μ‖) h_bound
    have h_pow_succ_mul : ∀ n, (E.lam n - μ) ^ (k + 1) * b n = (E.lam n - μ) * b' n := by
      intro n
      simp [hb'_def, pow_succ', mul_assoc]
    refine ⟨?_, ?_⟩
    · -- IsC0 (fun n => (E.lam n - μ) ^ (k+1) * b n)
      simpa [h_pow_succ_mul] using h_lam_sub_mu_c0
    · -- ((Uop - μ • 1) ^ (k+1)) (expand E.x b) = expand E.x (fun n => (E.lam n - μ) ^ (k+1) * b n)
      calc
        ((Uop - μ • (1 : Module.End K (ℕ → K))) ^ (k + 1)) (expand E.x b)
            = ((Uop - μ • (1 : Module.End K (ℕ → K))) *
                (Uop - μ • (1 : Module.End K (ℕ → K))) ^ k) (expand E.x b) := by
          rw [pow_succ']
        _ = (Uop - μ • (1 : Module.End K (ℕ → K)))
            (((Uop - μ • (1 : Module.End K (ℕ → K))) ^ k) (expand E.x b)) := by
          rw [Module.End.mul_apply]
        _ = (Uop - μ • (1 : Module.End K (ℕ → K))) (expand E.x b') := by rw [hEq]
        _ = Uop (expand E.x b') - (μ • (1 : Module.End K (ℕ → K))) (expand E.x b') := by
          rw [LinearMap.sub_apply]
        _ = Uop (expand E.x b') - μ • ((1 : Module.End K (ℕ → K)) (expand E.x b')) := by
          rw [LinearMap.smul_apply]
        _ = Uop (expand E.x b') - μ • expand E.x b' := by rw [Module.End.one_apply]
        _ = expand E.x (fun n => E.lam n * b' n) - μ • expand E.x b' := by
          rw [EigenFamily.Uop_expand E hb'_c0]
        _ = expand E.x (fun n => (E.lam n - μ) ^ (k + 1) * b n) := by
          ext i
          have h_summable_b' : Summable fun n => b' n * E.x n i :=
            E.near.summable hb'_c0 i
          have h_summable_lam_b' : Summable fun n => (E.lam n * b' n) * E.x n i := by
            have h_lam_c0 : IsC0 (fun n => E.lam n * b' n) := by
              have h_bound : ∀ n, ‖E.lam n‖ ≤ 1 := EigenFamily.norm_lam_le_one E
              exact IsC0.mul_bounded hb'_c0 (fun n => E.lam n) 1 h_bound
            exact E.near.summable h_lam_c0 i
          calc
            (expand E.x (fun n => E.lam n * b' n) - μ • expand E.x b') i
                = (expand E.x (fun n => E.lam n * b' n)) i - (μ • expand E.x b') i := rfl
            _ = (∑' n, (E.lam n * b' n) * E.x n i) - (μ • expand E.x b') i := rfl
            _ = (∑' n, (E.lam n * b' n) * E.x n i) - μ * (expand E.x b' i) := by
              simp
            _ = (∑' n, (E.lam n * b' n) * E.x n i) - μ * (∑' n, b' n * E.x n i) := rfl
            _ = (∑' n, (E.lam n * b' n) * E.x n i) - (∑' n, μ * (b' n * E.x n i)) := by
              rw [tsum_mul_left]
            _ = ∑' n, ((E.lam n * b' n) * E.x n i - μ * (b' n * E.x n i)) := by
              rw [← Summable.tsum_sub h_summable_lam_b' (h_summable_b'.mul_left μ)]
            _ = ∑' n, ((E.lam n - μ) * b' n) * E.x n i := by
              refine tsum_congr fun n => ?_
              ring
            _ = expand E.x (fun n => (E.lam n - μ) * b' n) i := rfl
            _ = expand E.x (fun n => (E.lam n - μ) ^ (k + 1) * b n) i := by
              simp [h_pow_succ_mul]

/-- Theorem 2.4 (b). -/
theorem EigenFamily.diag (E : EigenFamily) {μ : K} (hμ : μ ≠ 0) {k : ℕ} {a : ℕ → K} (ha : IsC0 a)
    (hk : ((Uop - μ • (1 : Module.End K (ℕ → K))) ^ k) a = 0) :
    ∃ b : ℕ → K, IsC0 b ∧ (∀ n, b n ≠ 0 → E.lam n = μ) ∧ a = expand E.x b := by
  obtain ⟨b, hb, hab⟩ := NearBasis.exists_expand_eq E.near ha
  obtain ⟨hiter, h_eq⟩ := EigenFamily.iterate_expand E μ k hb
  have hzero : expand E.x (fun n => (E.lam n - μ) ^ k * b n) = 0 := by
    rw [← h_eq, hab]
    exact hk
  have hcoeff : (fun n => (E.lam n - μ) ^ k * b n) = 0 :=
    NearBasis.eq_zero_of_expand_eq_zero E.near hiter hzero
  refine ⟨b, hb, ?_, hab.symm⟩
  intro n hbn
  have hpow : (E.lam n - μ) ^ k * b n = 0 := by
    simpa using congr_fun hcoeff n
  have hzero_pow : (E.lam n - μ) ^ k = 0 := by
    apply mul_eq_zero.mp at hpow
    cases' hpow with h h
    · exact h
    · contradiction
  have hzero_sub : E.lam n - μ = 0 := by
    by_cases hk0 : k = 0
    · subst hk0
      simp at hzero_pow
    · have := (pow_eq_zero_iff hk0).mp hzero_pow
      exact this
  exact sub_eq_zero.mp hzero_sub

end CalegariSlopes.Spectral
