/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Bridge.JBasic

@[expose] public section

/-! # Lemma 4.2, the uniqueness lemma, with a weight -/

open PowerSeries
open CalegariSlopes.Overconvergent (E4q E6q Dq jinv)
open CalegariSlopes.Spectral (JHyp)

namespace CalegariSlopes.Bridge

/-! ## Lemma 4.2 -/

theorem coeff_mul_low (a f : ℚ⟦X⟧) (n : ℕ) (hlow : ∀ m < n, coeff m f = 0) :
    coeff n (a * f) = constantCoeff a * coeff n f := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i a * coeff j f),
    Finset.sum_range_succ', Finset.sum_eq_zero (fun i hi => by
      rw [hlow _ (by simp at hi; omega), mul_zero])]
  simp

theorem lemmaU {k : ℕ} (w : ℚ⟦X⟧) (N : Matrix (Fin k) (Fin k) ℚ⟦X⟧) (e : Fin k → ℚ⟦X⟧) (n₀ : ℕ)
    (hsys : ∀ i, w * theta (e i) = ∑ j, N i j * e j)
    (hdet : ∀ n : ℕ, n₀ ≤ n →
      (((n : ℚ) * constantCoeff w) • (1 : Matrix (Fin k) (Fin k) ℚ) - N.map constantCoeff).det ≠ 0)
    (hbase : ∀ i, ∀ m < n₀, coeff m (e i) = 0) : e = 0 := by
  have hcoeff : ∀ n, ∀ i, coeff n (e i) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : n < n₀
      · exact fun i => hbase i n hn
      · push Not at hn
        have hv : (((n : ℚ) * constantCoeff w) • (1 : Matrix (Fin k) (Fin k) ℚ) - N.map constantCoeff).mulVec
            (fun i => coeff n (e i)) = 0 := by
          funext i
          have h := congrArg (coeff n) (hsys i)
          have hth : ∀ m < n, coeff m (theta (e i)) = 0 := fun m hm => by
            rw [coeff_theta, ih m hm i, mul_zero]
          rw [coeff_mul_low _ _ _ hth, coeff_theta, map_sum] at h
          rw [Finset.sum_congr rfl (fun j _ => coeff_mul_low (N i j) (e j) n (fun m hm => ih m hm j))] at h
          rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.map_apply,
            Pi.zero_apply]
          rw [← h]
          ring
        intro i
        exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero (hdet n hn) hv) i
  funext i
  ext n
  simpa using hcoeff n i

end CalegariSlopes.Bridge
