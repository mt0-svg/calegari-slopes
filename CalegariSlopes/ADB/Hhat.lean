/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.ADB.Theta

@[expose] public section

/-!
# The generating series of `R S` and its degree bound (for Lemma 5.3)

The proof of Lemma 5.3. With `G = θ_x F` (coefficients
`S i j = i u i j`), `Hhat G = Σ_{a,b} x^{2-a} y^{2-b} r_ab(θ_x - a, θ_y - b) G` has the coefficient `(R S)(i, j)` at
`x^{i+2} y^{j+2}` (`coeff_Hhat_G`), and `Hhat G ∈ Frac 12 38 38` (`Frac_Hhat_G`): `Hhat G Q^12` is a polynomial
supported in `[0, 38]^2`.
-/

open MvPowerSeries

namespace CalegariSlopes.ADB

/-- `m_a` as a polynomial. -/
noncomputable def mPoly (a : ℕ) : Polynomial ℚ :=
  match a with
  | 0 => 9 * Polynomial.X ^ 2 * (Polynomial.X + 1) ^ 2 * (Polynomial.X + 2) ^ 2
  | 1 => 18 * Polynomial.X * (Polynomial.X + 1) ^ 3 * (Polynomial.X + 2) ^ 2
  | _ => Polynomial.X * (Polynomial.X + 1) * (Polynomial.X + 2) ^ 2 * (3 * Polynomial.X + 4) *
      (3 * Polynomial.X + 5)

/-- `n_a` as a polynomial. -/
noncomputable def nPoly (a : ℕ) : Polynomial ℚ :=
  match a with
  | 0 => -81 * (Polynomial.X + 1) ^ 2 * (Polynomial.X + 2) ^ 2
  | 1 => -18 * Polynomial.X * (Polynomial.X + 2) ^ 2 * (5 * Polynomial.X + 7)
  | _ => -Polynomial.X * (Polynomial.X + 1) * (3 * Polynomial.X + 4) * (3 * Polynomial.X + 5)

/-- `r_ab(I - a, J - b) = m_a(I - a) n_b(J - b) - n_a(I - a) m_b(J - b)`, the multiplier of the term `(a, b)`. -/
def rShift (a b I J : ℕ) : ℚ :=
  mC a ((I : ℚ) - a) * nC b ((J : ℚ) - b) - nC a ((I : ℚ) - a) * mC b ((J : ℚ) - b)

/-- `Hhat f = Σ_{a,b < 3} x^{2-a} y^{2-b} mulC (rShift a b) f`. -/
noncomputable def Hhat (f : MvPowerSeries (Fin 2) ℚ) : MvPowerSeries (Fin 2) ℚ :=
  ∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3, X 0 ^ (2 - a) * X 1 ^ (2 - b) * mulC (rShift a b) f

/-- `G = θ_x F`, the generating series of `S i j = i u i j`. -/
noncomputable def G : MvPowerSeries (Fin 2) ℚ := thX F

theorem ex_le_ex (a b i j : ℕ) : ex a b ≤ ex i j ↔ a ≤ i ∧ b ≤ j := by
  rw [Finsupp.le_def, Fin.forall_fin_two]
  simp [ex]

theorem ex_sub_ex (a b i j : ℕ) : ex i j - ex a b = ex (i - a) (j - b) := by
  ext v; fin_cases v <;> simp [ex]

theorem X_pow_mul_X_pow (a b : ℕ) :
    (X 0 ^ a * X 1 ^ b : MvPowerSeries (Fin 2) ℚ) = monomial (ex a b) 1 := by
  simp only [X_pow_eq, monomial_mul_monomial, mul_one, ex]

theorem mPoly_eval (a : ℕ) (k : ℚ) : (mPoly a).eval k = mC a k := by
  rcases a with _ | _ | a <;> simp [mPoly, mC]

theorem nPoly_eval (a : ℕ) (k : ℚ) : (nPoly a).eval k = nC a k := by
  rcases a with _ | _ | a <;> simp [nPoly, nC]

theorem mPoly_natDegree (a : ℕ) : (mPoly a).natDegree ≤ 6 := by
  rcases a with _ | _ | a <;> simp only [mPoly] <;> compute_degree

theorem nPoly_natDegree (a : ℕ) : (nPoly a).natDegree ≤ 4 := by
  rcases a with _ | _ | a <;> simp only [nPoly] <;> compute_degree

/-- The multiplier `rShift a b` is a difference of two products of polynomials of degrees `(6, 4)` and `(4, 6)`. -/
theorem mulC_rShift (a b : ℕ) (f : MvPowerSeries (Fin 2) ℚ) :
    mulC (rShift a b) f =
      mulC (fun I _ => ((mPoly a).comp (Polynomial.X - Polynomial.C (a : ℚ))).eval (I : ℚ))
          (mulC (fun _ J => ((nPoly b).comp (Polynomial.X - Polynomial.C (b : ℚ))).eval (J : ℚ)) f) -
        mulC (fun I _ => ((nPoly a).comp (Polynomial.X - Polynomial.C (a : ℚ))).eval (I : ℚ))
          (mulC (fun _ J => ((mPoly b).comp (Polynomial.X - Polynomial.C (b : ℚ))).eval (J : ℚ)) f) := by
  ext n
  simp only [coeff_mulC, map_sub, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, mPoly_eval, nPoly_eval, rShift]
  ring

theorem natDegree_comp_shift (P : Polynomial ℚ) (c : ℚ) (n : ℕ) (hP : P.natDegree ≤ n) :
    (P.comp (Polynomial.X - Polynomial.C c)).natDegree ≤ n := by
  calc (P.comp (Polynomial.X - Polynomial.C c)).natDegree
      ≤ P.natDegree * (Polynomial.X - Polynomial.C c).natDegree := Polynomial.natDegree_comp_le
    _ = P.natDegree := by rw [Polynomial.natDegree_X_sub_C, mul_one]
    _ ≤ n := hP

theorem Frac_mulC_rShift (a b : ℕ) {e dx dy : ℕ} {f : MvPowerSeries (Fin 2) ℚ} (h : Frac e dx dy f) :
    Frac (e + 10) (dx + 30) (dy + 30) (mulC (rShift a b) f) := by
  rw [mulC_rShift]
  have h1 := Frac_mulC_polyX _ (natDegree_comp_shift _ (a : ℚ) 6 (mPoly_natDegree a))
    (Frac_mulC_polyY _ (natDegree_comp_shift _ (b : ℚ) 4 (nPoly_natDegree b)) h)
  have h2 := Frac_mulC_polyX _ (natDegree_comp_shift _ (a : ℚ) 4 (nPoly_natDegree a))
    (Frac_mulC_polyY _ (natDegree_comp_shift _ (b : ℚ) 6 (mPoly_natDegree b)) h)
  exact Frac_sub h1 h2

theorem Frac_Hhat {e dx dy : ℕ} {f : MvPowerSeries (Fin 2) ℚ} (h : Frac e dx dy f) :
    Frac (e + 10) (dx + 32) (dy + 32) (Hhat f) := by
  unfold Hhat
  refine Frac_sum _ _ fun a ha => Frac_sum _ _ fun b hb => ?_
  have ha : a < 3 := Finset.mem_range.mp ha
  have hb : b < 3 := Finset.mem_range.mp hb
  exact Frac_mono (by omega) (by omega) (Frac_mul_X_pow (2 - a) (2 - b) (Frac_mulC_rShift a b h))

theorem Frac_G : Frac 2 6 6 G := by
  exact Frac_thX Frac_F

theorem Frac_Hhat_G : Frac 12 38 38 (Hhat G) := by
  exact Frac_Hhat Frac_G

theorem coeff_G (i j : ℕ) : coeff (ex i j) G = S i j := by
  unfold G thX S
  rw [coeff_mulC, ex_apply_zero]
  rfl

/-- The coefficients of `Hhat f`, natural boundaries included. -/
theorem coeff_Hhat (f : MvPowerSeries (Fin 2) ℚ) (I J : ℕ) :
    coeff (ex I J) (Hhat f) = ∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3,
      if 2 ≤ I + a ∧ 2 ≤ J + b then
        rShift a b (I + a - 2) (J + b - 2) * coeff (ex (I + a - 2) (J + b - 2)) f
      else 0 := by
  unfold Hhat
  simp only [map_sum]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
  have ha' : a < 3 := Finset.mem_range.mp ha
  have hb' : b < 3 := Finset.mem_range.mp hb
  rw [X_pow_mul_X_pow, coeff_monomial_mul, ex_sub_ex]
  by_cases h : 2 ≤ I + a ∧ 2 ≤ J + b
  · rw [if_pos ((ex_le_ex _ _ _ _).mpr ⟨by omega, by omega⟩), if_pos h, one_mul, coeff_mulC, ex_apply_zero, ex_apply_one,
      show I - (2 - a) = I + a - 2 by omega, show J - (2 - b) = J + b - 2 by omega]
  · rw [if_neg (fun hle => h (by have := (ex_le_ex _ _ _ _).mp hle; omega)), if_neg h]

/-- The translation lemma: the coefficient of `x^{i+2} y^{j+2}` in `Hhat G` is `(R S)(i, j)`. -/
theorem coeff_Hhat_G (i j : ℕ) : coeff (ex (i + 2) (j + 2)) (Hhat G) = R S i j := by
  rw [coeff_Hhat, R]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
  rw [if_pos (by omega), coeff_G, show i + 2 + a - 2 = i + a by omega, show j + 2 + b - 2 = j + b by omega]
  unfold rShift
  push_cast
  ring_nf

end CalegariSlopes.ADB
