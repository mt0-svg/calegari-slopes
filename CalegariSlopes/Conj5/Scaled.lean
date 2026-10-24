/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Conj5.ContractionK

@[expose] public section

/-!
# The scaled matrices at radius `r` and the eigenvectors of `u^(r)`

The proof of Corollary 8.3 of the paper. For `γ ∈ K` with `‖γ‖ = 3 ^ s`, `|s| < 1`, `ε = 1 - |s|`:
`A^(r) = scM γ A`, `C^(r) = scM γ C`, `u^(r) = scM γ u` (`scM γ M i j = γ ^ (j - i) M_ij`). Conjugation by
`Λ a = (γ ^ j a_j)_j` (`scal γ`) turns `U A = A D C` into `u^(r) A^(r) = A^(r) D C^(r)`; the bounds
`v(A_ij) ≥ i - j` and `v(C_ij) ≥ |i - j|` give `‖A^(r) - I‖ ≤ 3 ^ (-ε)` and the hypotheses `CHyp` of the
contraction for `C^(r)` with `c = 3 ^ (-ε)`; its fixed point `w_n` gives `y_n = A^(r) w_n` with
`u^(r) y_n = D_n μ y_n`.
-/

open Filter Topology
open CalegariSlopes.Overconvergent (K)
open CalegariSlopes.Spectral

namespace CalegariSlopes.Conj5

/-- The scaled matrix `γ ^ (j - i) M_ij` (integer powers). -/
noncomputable def scM (γ : K) (M : ℕ → ℕ → ℚ) (i j : ℕ) : K := γ ^ ((j : ℤ) - i) * (M i j : K)

/-- `Λ a = (γ ^ j a_j)_j`. -/
noncomputable def scal (γ : K) (a : ℕ → K) (j : ℕ) : K := γ ^ (j : ℤ) * a j

theorem Ur_eq_kact (γ : K) (a : ℕ → K) : Ur γ a = kact (scM γ u) a := rfl

/-! ## Conjugation by `Λ` -/

/-- `Λ (M^(r) a) = M (Λ a)`. -/
theorem scal_kact_scM {γ : K} (hγ : γ ≠ 0) (M : ℕ → ℕ → ℚ) (a : ℕ → K) :
    scal γ (kact (scM γ M) a) = bact M (scal γ a) := by
  ext i
  simp only [scal, kact, scM, bact]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc
    γ ^ (i : ℤ) * ((γ ^ ((j : ℤ) - i) * (M i j : K)) * a j)
        = (γ ^ (i : ℤ) * γ ^ ((j : ℤ) - i)) * (M i j : K) * a j := by ring
    _ = γ ^ ((i : ℤ) + ((j : ℤ) - i)) * (M i j : K) * a j := by
      rw [zpow_add₀ hγ (i : ℤ) ((j : ℤ) - i)]
    _ = γ ^ (j : ℤ) * (M i j : K) * a j := by rw [add_sub_cancel]
    _ = (M i j : K) * (γ ^ (j : ℤ) * a j) := by ring

/-- `Λ` is injective. -/
theorem scal_injective {γ : K} (hγ : γ ≠ 0) {a b : ℕ → K} (h : scal γ a = scal γ b) : a = b := by
  ext j
  have h_eq : scal γ a j = scal γ b j := by rw [h]
  rw [CalegariSlopes.Conj5.scal, CalegariSlopes.Conj5.scal] at h_eq
  have h_pow_ne_zero : γ ^ (j : ℤ) ≠ 0 := zpow_ne_zero (j : ℤ) hγ
  exact mul_left_cancel₀ h_pow_ne_zero h_eq

/-- Lemma 6.3 at radius `r`, the identity: `u^(r) (A^(r) w) = A^(r) (D (C^(r) w))`. -/
theorem Ur_kact_Ag {γ : K} (hγ : γ ≠ 0) (w : ℕ → K) :
    Ur γ (kact (scM γ ADB.A) w) = kact (scM γ ADB.A) (fun p => (ADB.D p : K) * kact (scM γ Cm) w p) := by
  apply scal_injective hγ
  have hD : scal γ (fun p => (ADB.D p : K) * kact (scM γ Cm) w p) =
      fun p => (ADB.D p : K) * bact Cm (scal γ w) p := by
    funext p
    have h := congrFun (scal_kact_scM hγ Cm w) p
    simp only [scal] at h ⊢
    rw [← h]
    ring
  rw [Ur_eq_kact, scal_kact_scM hγ, scal_kact_scM hγ, scal_kact_scM hγ, hD]
  exact bact_u_bact_A _

/-- `U (Λ y) = Λ (u^(r) y)`. -/
theorem Uop_scal {γ : K} (hγ : γ ≠ 0) (y : ℕ → K) : Uop (scal γ y) = scal γ (Ur γ y) := by
  show bact u (scal γ y) = _
  rw [Ur_eq_kact, scal_kact_scM hγ]

/-! ## Bounds -/

/-- `‖γ ^ k‖ = 3 ^ (s k)`. -/
theorem norm_zpow_of_norm {γ : K} {s : ℝ} (hγ : ‖γ‖ = (3 : ℝ) ^ s) (k : ℤ) :
    ‖γ ^ k‖ = (3 : ℝ) ^ (s * k) := by
  calc
    ‖γ ^ k‖ = ‖γ‖ ^ k := by rw [norm_zpow]
    _ = ((3 : ℝ) ^ s) ^ k := by rw [hγ]
    _ = ((3 : ℝ) ^ s) ^ (k : ℝ) := by rw [Real.rpow_intCast]
    _ = (3 : ℝ) ^ (s * (k : ℝ)) := by
      rw [Real.rpow_mul (show (0 : ℝ) ≤ 3 by norm_num) s (k : ℝ)]
    _ = (3 : ℝ) ^ (s * k) := by simp

/-- An entry with `v(M_ij) ≥ |i - j|`, `i ≠ j`, scales to norm `≤ 3 ^ (-(1 - |s|))`. -/
theorem norm_scM_le {γ : K} {s : ℝ} (hγ : ‖γ‖ = (3 : ℝ) ^ s) (hs : |s| ≤ 1) (M : ℕ → ℕ → ℚ) {i j : ℕ}
    (hij : i ≠ j) (hM : ‖(M i j : ℚ_[3])‖ ≤ (3 : ℝ) ^ (-|(i : ℤ) - j|)) :
    ‖scM γ M i j‖ ≤ (3 : ℝ) ^ (-(1 - |s|)) := by
  have hd : (j : ℤ) - i ≠ 0 := by omega
  have hD : (1 : ℝ) ≤ |(j : ℝ) - i| := by
    have h1 := Int.one_le_abs hd
    exact_mod_cast h1
  have hM' : ‖(M i j : K)‖ ≤ (3 : ℝ) ^ (-|(j : ℝ) - i|) := by
    rw [norm_ratCast_K]
    refine hM.trans (le_of_eq ?_)
    rw [← Real.rpow_intCast, abs_sub_comm]
    push_cast
    rfl
  rw [scM, norm_mul, norm_zpow_of_norm hγ]
  push_cast
  calc (3 : ℝ) ^ (s * ((j : ℝ) - i)) * ‖(M i j : K)‖
      ≤ (3 : ℝ) ^ (s * ((j : ℝ) - i)) * (3 : ℝ) ^ (-|(j : ℝ) - i|) :=
        mul_le_mul_of_nonneg_left hM' (Real.rpow_nonneg (by norm_num) _)
    _ = (3 : ℝ) ^ (s * ((j : ℝ) - i) + -|(j : ℝ) - i|) := (Real.rpow_add (by norm_num) _ _).symm
    _ ≤ (3 : ℝ) ^ (-(1 - |s|)) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have h1 : s * ((j : ℝ) - i) ≤ |s| * |(j : ℝ) - i| := by
          rw [← abs_mul]
          exact le_abs_self _
        have h3 : 0 ≤ 1 - |s| := by linarith
        nlinarith [mul_nonneg h3 (sub_nonneg.2 hD)]

/-- `0 ≤ 3 ^ (-(1 - |s|)) < 1` for `|s| < 1`. -/
theorem rpow_eps_lt_one {s : ℝ} (hs : |s| < 1) : (3 : ℝ) ^ (-(1 - |s|)) < 1 := by
  refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ?_
  have hpos : 0 < 1 - |s| := by
    have := abs_nonneg s
    linarith
  linarith

/-- `C^(r)` satisfies the hypotheses of the contraction with `c = 3 ^ (-ε)`. -/
theorem chyp_Cg {γ : K} {s : ℝ} (hγ : ‖γ‖ = (3 : ℝ) ^ s) (hs : |s| < 1) :
    CHyp (scM γ Cm) ((3 : ℝ) ^ (-(1 - |s|))) := by
  have hCm0 : ∀ i, Cm i 0 = 0 := by
    intro i
    dsimp [Cm]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hA0 : ADB.A k 0 = 0 := by
      dsimp [ADB.A]
      simp
    simp [hA0]
  have h_nonneg : 0 ≤ (3 : ℝ) ^ (-(1 - |s|)) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  refine
    { nonneg := h_nonneg
      lt_one := rpow_eps_lt_one hs
      off := by
        intro i j hi hij
        by_cases hj0 : j = 0
        · subst hj0
          have hzero : scM γ Cm i 0 = 0 := by
            dsimp [scM]
            simp [hCm0 i]
          rw [hzero]
          simpa using h_nonneg
        · have hj1 : 1 ≤ j := Nat.one_le_of_lt (Nat.pos_of_ne_zero hj0)
          exact norm_scM_le hγ hs.le Cm hij (norm_Cm_le i j hi hj1)
      diag := by
        intro i hi
        have h_eq : scM γ Cm i i = (Cm i i : K) := by
          dsimp [scM]
          simp
        rw [h_eq]
        have h_cast : (Cm i i : K) - 1 = ((Cm i i - 1 : ℚ) : K) := by
          simp
        rw [h_cast]
        rw [norm_ratCast_K (Cm i i - 1)]
        have h_le : ‖((Cm i i - 1 : ℚ) : ℚ_[3])‖ ≤ (3 : ℝ) ^ (-2 : ℤ) :=
          norm_Cm_self_sub_one_le i hi
        have h_lt : (3 : ℝ) ^ (-2 : ℤ) < 1 := by
          norm_num
        linarith
      band := by
        intro i j h
        have hCm : Cm i j = 0 := Cm_eq_zero_of_gt h
        simp [scM, hCm]
    }

/-- The entries of `A^(r)` on the rows `i ≥ 1` have norm `≤ 1`. -/
theorem norm_scM_A_le_one {γ : K} {s : ℝ} (hγ : ‖γ‖ = (3 : ℝ) ^ s) (hs : |s| ≤ 1) {i : ℕ} (hi : 1 ≤ i)
    (j : ℕ) : ‖scM γ ADB.A i j‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · have hA : ADB.A i 0 = 0 := by
      simp [ADB.A]
    simp [scM, hA]
  rcases lt_or_ge i j with hij | hij
  · simp [scM, CalegariSlopes.Newton.A_eq_zero_of_lt i j hij]
  have hA := CalegariSlopes.Newton.norm_A_le i j hi hj1
  have hA' : ‖(ADB.A i j : K)‖ ≤ (3 : ℝ) ^ (-((i : ℝ) - j)) := by
    rw [norm_ratCast_K]
    refine hA.trans (le_of_eq ?_)
    rw [← Real.rpow_intCast]
    push_cast
    rfl
  rw [scM, norm_mul, norm_zpow_of_norm hγ]
  push_cast
  have hij' : (j : ℝ) ≤ i := by exact_mod_cast hij
  calc (3 : ℝ) ^ (s * ((j : ℝ) - i)) * ‖(ADB.A i j : K)‖
      ≤ (3 : ℝ) ^ (s * ((j : ℝ) - i)) * (3 : ℝ) ^ (-((i : ℝ) - j)) :=
        mul_le_mul_of_nonneg_left hA' (Real.rpow_nonneg (by norm_num) _)
    _ = (3 : ℝ) ^ (s * ((j : ℝ) - i) + -((i : ℝ) - j)) := (Real.rpow_add (by norm_num) _ _).symm
    _ ≤ 1 := by
        refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
        have h1 : -1 ≤ s := (abs_le.1 hs).1
        nlinarith

/-- Lemma 6.3 at radius `r`, the bound: `‖A^(r) w - w‖ ≤ 3 ^ (-ε) ‖w‖` (coordinates `k ≥ 1`). -/
theorem norm_kact_Ag_sub_le {γ : K} {s : ℝ} (hγ : ‖γ‖ = (3 : ℝ) ^ s) (hs : |s| ≤ 1) (w : ℕ → K) {r : ℝ}
    (hr : 0 ≤ r) (hw : ∀ j, ‖w j‖ ≤ r) {k : ℕ} (hk : 1 ≤ k) :
    ‖kact (scM γ ADB.A) w k - w k‖ ≤ (3 : ℝ) ^ (-(1 - |s|)) * r := by
  set C := (3 : ℝ) ^ (-(1 - |s|)) with hC
  have h_nonneg_C : 0 ≤ C := by
    rw [hC]
    exact Real.rpow_nonneg (by norm_num) _
  have h_nonneg_Cr : 0 ≤ C * r := mul_nonneg h_nonneg_C hr
  have h_decomp := kact_eq_diag_add_offd (scM γ ADB.A) w hk
  have h_diag : scM γ ADB.A k k = 1 := by
    dsimp [scM]
    have hA : ADB.A k k = 1 := CalegariSlopes.Newton.A_self k hk
    have h_pow : γ ^ ((k : ℤ) - k) = 1 := by
      simp [sub_self]
    simp [hA]
  have h_diff : kact (scM γ ADB.A) w k - w k = kact (offd (scM γ ADB.A)) w k := by
    rw [h_decomp]
    rw [h_diag]
    ring
  rw [h_diff]
  dsimp [kact]
  have h_bound : ∀ j ∈ Finset.Icc 1 (3 * k), ‖offd (scM γ ADB.A) k j * w j‖ ≤ C * r := by
    intro j hj
    rcases Finset.mem_Icc.mp hj with ⟨hj1, hj2⟩
    by_cases hj_eq : j = k
    · subst hj_eq
      simp [offd, h_nonneg_Cr]
    · by_cases hkj : k < j
      · have hA_zero : ADB.A k j = 0 := CalegariSlopes.Newton.A_eq_zero_of_lt k j hkj
        have h_scM_zero : scM γ ADB.A k j = 0 := by
          dsimp [scM]
          simp [hA_zero]
        simp [offd, h_scM_zero, h_nonneg_Cr]
      · have hj_lt_k : j < k := by omega
        have h_ne : k ≠ j := by omega
        have h_norm_A : ‖(ADB.A k j : ℚ_[3])‖ ≤ (3 : ℝ) ^ (-|(k : ℤ) - j|) := by
          have h_norm_A' := CalegariSlopes.Newton.norm_A_le k j hk hj1
          have hpos : 0 ≤ (k : ℤ) - j := by
            have : (j : ℤ) ≤ k := by exact mod_cast hj_lt_k.le
            omega
          have h_abs : |(k : ℤ) - j| = (k : ℤ) - j := abs_of_nonneg hpos
          rw [h_abs]
          exact h_norm_A'
        have h_norm_scM : ‖scM γ ADB.A k j‖ ≤ C := by
          dsimp [C]
          exact norm_scM_le hγ hs ADB.A h_ne h_norm_A
        rw [offd]
        simp [h_ne]
        exact mul_le_mul h_norm_scM (hw j) (norm_nonneg _) h_nonneg_C
  refine (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h_nonneg_Cr h_bound).trans ?_
  rfl

/-- `A^(r)` maps `c₀` into `c₀`. -/
theorem isC0_kact_Ag {γ : K} {s : ℝ} (hγ : ‖γ‖ = (3 : ℝ) ^ s) (hs : |s| ≤ 1) {w : ℕ → K} (hw : IsC0 w) :
    IsC0 (kact (scM γ ADB.A) w) := by
  apply isC0_kact (scM γ ADB.A)
  · intro i j h
    have hA := A_eq_zero_of_gt h
    simp [scM, hA]
  · intro i j hi
    exact norm_scM_A_le_one hγ hs hi j
  · exact hw

/-! ## The eigenvectors of `u^(r)` -/

/-- For `n ≥ 1`: `y = A^(r) w_n` and `λ = D_n μ`, with `y ∈ c₀`, `‖y - e_n‖ ≤ 3 ^ (-ε)`, `u^(r) y = λ y`,
`‖λ‖ = 3 ^ (-σ_n)`, `y_0 = 0`. -/
theorem exists_eigvec_r {γ : K} {s : ℝ} (hγ : ‖γ‖ = (3 : ℝ) ^ s) (hs : |s| < 1) {n : ℕ} (hn : 1 ≤ n) :
    ∃ (y : ℕ → K) (lam : K), IsC0 y ∧ (∀ i, ‖y i - unitSeq n i‖ ≤ (3 : ℝ) ^ (-(1 - |s|))) ∧
      Ur γ y = lam • y ∧ ‖lam‖ = (3 : ℝ) ^ (-(slope n : ℤ)) ∧ y 0 = 0 := by
  have hγ0 : γ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hγ
    exact (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) s).ne' hγ.symm
  have hC := chyp_Cg hγ hs
  obtain ⟨v, μ, -, -, hv, hvc, hμ, heq⟩ := hC.exists_eigen hn
  refine ⟨kact (scM γ ADB.A) (wv n v), (ADB.D n : K) * μ, isC0_kact_Ag hγ hs.le (isC0_wv hvc), ?_, ?_, ?_,
    kact_apply_zero _ _⟩
  · intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · have h2 : unitSeq n 0 = 0 := by simp only [unitSeq, ite_eq_right_iff]; omega
      rw [kact_apply_zero, h2, sub_zero, norm_zero]
      exact hC.nonneg
    · have h1 := norm_kact_Ag_sub_le hγ hs.le (wv n v) zero_le_one (norm_wv_le_one_of hC.lt_one.le hv) hi
      have h3 : kact (scM γ ADB.A) (wv n v) i - unitSeq n i =
          (kact (scM γ ADB.A) (wv n v) i - wv n v i) + v i := by
        simp only [wv]
        ring
      rw [h3]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hv i))
      simpa using h1
  · rw [Ur_kact_Ag hγ0]
    funext i
    show ∑ j ∈ Finset.Icc 1 (3 * i), scM γ ADB.A i j * ((ADB.D j : K) * kact (scM γ Cm) (wv n v) j) =
      ((ADB.D n : K) * μ) * ∑ j ∈ Finset.Icc 1 (3 * i), scM γ ADB.A i j * wv n v j
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [heq j (Finset.mem_Icc.1 hj).1]
    ring
  · have hμ1 : ‖μ‖ = 1 := by
      have h1 : ‖(1 : K)‖ ≠ ‖μ - 1‖ := by
        rw [norm_one]
        exact hμ.ne'
      calc ‖μ‖ = ‖1 + (μ - 1)‖ := by ring_nf
        _ = max ‖(1 : K)‖ ‖μ - 1‖ := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1
        _ = 1 := by rw [norm_one]; exact max_eq_left hμ.le
    rw [norm_mul, norm_ratCast_K, CalegariSlopes.Newton.norm_D, hμ1, mul_one]

end CalegariSlopes.Conj5
