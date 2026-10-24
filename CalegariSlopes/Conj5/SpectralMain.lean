/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Conj5.Ident

@[expose] public section

/-!
# Corollaries 8.3 and 8.4 of the paper, proved

Every theorem of `CalegariSlopes/ChallengeConj5Spectral.lean`, with the same name and statement: `exists_gamma`,
`spectral_expansion` (Corollary 8.3), `x_mem_L` (its last sentence), `norm_x_le` (Corollary 8.4). The proof is that
of the paper: the eigenvectors `y_n` of `u^(r)` come from the contraction (`exists_eigvec_r`) and are identified with
the `x_n` (`identify`); the expansion and the generalized eigenvectors follow from the near basis `y` (`SeqK`);
Corollary 8.4 is the limit `s → ±1` of the bounds at the radii `s = 3 - 6r` (`norm_x_le_of_norm`,
`le_zpow_of_forall_rat`). The challenge is not imported; Comparator checks the pair (`config-conj5-spectral.json`).
-/

open Filter Topology
open CalegariSlopes.Overconvergent (K)
open CalegariSlopes.Spectral

namespace CalegariSlopes.Conj5

theorem exists_gamma (r : ℚ) : ∃ γ : K, ‖γ‖ = (3 : ℝ) ^ (3 - 6 * (r : ℝ)) := by
  obtain ⟨γ, hγ⟩ := exists_norm_eq_rpow (3 - 6 * r)
  exact ⟨γ, by rw [hγ]; push_cast; ring_nf⟩

theorem spectral_expansion (E : EigenFamily) (r : ℚ) (hr1 : 1 / 3 < r) (hr2 : r < 2 / 3) (γ : K)
    (hγ : ‖γ‖ = (3 : ℝ) ^ (3 - 6 * (r : ℝ))) :
    ∃ y : ℕ → ℕ → K,
      y 0 = unitSeq 0 ∧ (∀ n, 1 ≤ n → y n 0 = 0) ∧
      (∀ n, IsC0 (y n)) ∧
      (∀ n i, ‖y n i - unitSeq n i‖ ≤ (3 : ℝ) ^ (-(1 - |3 - 6 * (r : ℝ)|))) ∧
      (∀ n, 1 ≤ n → Ur γ (y n) = E.lam n • y n) ∧
      (∀ a, IsC0 a → ∃! b, IsC0 b ∧ expand y b = a) ∧
      (∀ b, IsC0 b → ⨆ i, ‖expand y b i‖ = ⨆ n, ‖b n‖) ∧
      (∀ n, 1 ≤ n → ∀ a, IsC0 a →
        ((∃ k : ℕ, ((Ur γ - E.lam n • (1 : Module.End K (ℕ → K))) ^ k) a = 0) ↔ ∃ c : K, a = c • y n)) ∧
      (∀ μ : K, μ ≠ 0 → (∀ n, 1 ≤ n → E.lam n ≠ μ) → ∀ a, IsC0 a →
        (∃ k : ℕ, ((Ur γ - μ • (1 : Module.End K (ℕ → K))) ^ k) a = 0) → a = 0) := by
  have hs := abs_s_lt_one hr1 hr2
  have hc1 := rpow_eps_lt_one hs
  have hc0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 - |3 - 6 * (r : ℝ)|)) := Real.rpow_nonneg (by norm_num) _
  have hs3 : 3 - 6 * (r : ℝ) < 3 := by linarith [(abs_lt.mp hs).2]
  choose Y lam hYc hYn hYe hYl hY0 using fun (n : ℕ) (hn : 1 ≤ n) => exists_eigvec_r hγ hs hn
  have hlamE : ∀ n (hn : 1 ≤ n), lam n hn = E.lam n := fun n hn => by
    have hyn1 : ‖Y n hn n - 1‖ < 1 := by
      have := hYn n hn n
      simp only [unitSeq, ite_true] at this
      exact this.trans_lt hc1
    exact (identify E hγ hs3 hn (hYc n hn) hyn1 (hYe n hn) (hYl n hn)).1
  classical
  let y : ℕ → ℕ → K := fun n => if h : 1 ≤ n then Y n h else unitSeq 0
  have hy0 : y 0 = unitSeq 0 := by simp [y]
  have hyn : ∀ n (hn : 1 ≤ n), y n = Y n hn := fun n hn => by simp [y, hn]
  have hnear : NearBasis y ((3 : ℝ) ^ (-(1 - |3 - 6 * (r : ℝ)|))) := by
    refine ⟨hc0, hc1, fun n => ?_, fun n i => ?_⟩
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [hy0]
        exact isC0_unitSeq 0
      · rw [hyn n hn]
        exact hYc n hn
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [hy0, sub_self, norm_zero]
        exact hc0
      · rw [hyn n hn]
        exact hYn n hn i
  have heig : ∀ n, Ur γ (y n) = E.lam n • y n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hy0, E.lam_zero, zero_smul, Ur_unitSeq_zero]
    · rw [hyn n hn, hYe n hn, hlamE n hn]
  have hT : ∀ b, IsC0 b → Ur γ (expand y b) = expand y (fun n => E.lam n * b n) := by
    intro b hb
    rw [Ur_eq_kact, NearBasis.kact_expand hnear hb]
    funext i
    simp only [expand]
    refine tsum_congr fun n => ?_
    rw [← Ur_eq_kact, heig n]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨y, hy0, fun n hn => by rw [hyn n hn]; exact hY0 n hn, hnear.isC0, hnear.near, fun n _ => heig n,
    fun a ha => NearBasis.existsUnique_expand hnear ha, fun b hb => NearBasis.iSup_norm_expand hnear hb, ?_, ?_⟩
  · intro n hn a ha
    constructor
    · rintro ⟨k, hk⟩
      obtain ⟨b, -, hbsupp, rfl⟩ := diag_of_termwise hnear E.lam E.norm_lam_le_one (Ur γ) hT ha hk
      refine ⟨b n, expand_eq_smul _ _ _ fun m hm => ?_⟩
      by_contra hbm
      have h1 := hbsupp m hbm
      rcases Nat.eq_zero_or_pos m with rfl | hm1
      · rw [E.lam_zero] at h1
        have h2 := E.norm_lam n hn
        rw [← h1, norm_zero] at h2
        exact (zpow_pos (by norm_num : (0 : ℝ) < 3) _).ne' h2.symm
      · exact hm (E.lam_injective hm1 hn h1)
    · rintro ⟨c', rfl⟩
      refine ⟨1, ?_⟩
      rw [pow_one, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_smul, heig n, smul_comm,
        sub_self]
  · rintro μ hμ hne a ha ⟨k, hk⟩
    obtain ⟨b, -, hbsupp, rfl⟩ := diag_of_termwise hnear E.lam E.norm_lam_le_one (Ur γ) hT ha hk
    have hb0 : b = 0 := by
      funext m
      by_contra hbm
      have h1 := hbsupp m hbm
      rcases Nat.eq_zero_or_pos m with rfl | hm1
      · rw [E.lam_zero] at h1
        exact hμ h1.symm
      · exact hne m hm1 h1
    rw [hb0]
    funext i
    simp [expand]

theorem x_mem_L (E : EigenFamily) (r : ℚ) (hr1 : 1 / 3 < r) (hr2 : r < 2 / 3) (n : ℕ) (hn : 1 ≤ n) :
    InS (3 - 6 * (r : ℝ)) (E.x n) := by
  have hs := abs_s_lt_one hr1 hr2
  obtain ⟨γ, hγ⟩ := exists_gamma r
  obtain ⟨y, lam, hyc, hyn, heig, hlam, -⟩ := exists_eigvec_r hγ hs hn
  have hyn1 : ‖y n - 1‖ < 1 := by
    have := hyn n
    simp only [unitSeq, ite_true] at this
    exact this.trans_lt (rpow_eps_lt_one hs)
  obtain ⟨-, κ, hκ, hzx⟩ := identify E hγ (by linarith [(abs_lt.mp hs).2]) hn hyc hyn1 heig hlam
  have hx : E.x n = κ⁻¹ • scal γ y := by
    rw [hzx, smul_smul, inv_mul_cancel₀ hκ, one_smul]
  rw [hx]
  exact (InS_scal hγ hyc).smul κ⁻¹

theorem norm_x_le (E : EigenFamily) (n i : ℕ) (hn : 1 ≤ n) (hi : 1 ≤ i) :
    ‖E.x n i‖ ≤ (3 : ℝ) ^ (-|(i : ℤ) - n|) := by
  have _ := hi
  by_cases hin : i = n
  · subst hin
    simp only [sub_self, abs_zero, neg_zero, zpow_zero]
    exact E.near.norm_le_one i i
  · have hd : ((i : ℤ) - n) ≠ 0 := by omega
    refine le_zpow_of_forall_rat hd fun r hr1 hr2 => ?_
    have hs := abs_s_lt_one hr1 hr2
    obtain ⟨γ, hγ⟩ := exists_gamma r
    have h := norm_x_le_of_norm E hγ hs hn hin
    push_cast
    exact h

end CalegariSlopes.Conj5
