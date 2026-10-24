/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Bridge.TheoremA
public import CalegariSlopes.Bridge.C4Defs
public import CalegariSlopes.Bridge.C4Ring
public import CalegariSlopes.Bridge.C4U3

@[expose] public section

/-!
# Theorem 4.5, level nine

(I3), part (a), from Lemma 4.3; (I2), part (b), by Lemma 4.2 with `k = 1` on `Ep' = (1 - W³) G' - W³`; (I1) and
`a2 = V₃ a2 (1 + 2W)²`, part (c), by Lemma 4.2 with `k = 2` on
`(K, Ee') = (a2 - V₃ a2 (1 + 2W)², (1 - W)³ G - 9W(1 + W + W²))`, weight `6 (1 + G)(1 + 2W)³`,
`N(0) = [[-3, 4], [0, 6]]`. Inputs from `JBasic`, `LemmaU`, `Ram`, `TheoremA`: `theta_Sol`, `theta_V3`, `theta_G`,
`ram_E2`, `ram_V3`, `two_mul_a2`, `theoremA`, `lemmaU`, the small coefficients.
-/

open PowerSeries
open CalegariSlopes.Overconvergent (E4q E6q)

namespace CalegariSlopes.Bridge.Level9

/-! ## Leibniz rule, base cases, `b` -/

theorem theta_Ep (w gp : ℚ⟦X⟧) :
    theta ((1 - w ^ 3) * gp - w ^ 3) = -(3 * w ^ 2 * theta w) * gp + (1 - w ^ 3) * theta gp - 3 * w ^ 2 * theta w := by
  simp only [map_sub, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
    Derivation.map_one_eq_zero]
  push_cast
  ring

theorem theta_K (a u w : ℚ⟦X⟧) :
    theta (a - u * (1 + 2 * w) ^ 2) = theta a - theta u * (1 + 2 * w) ^ 2 - 4 * u * (1 + 2 * w) * theta w := by
  simp only [map_sub, map_add, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
    theta_ofNat, Derivation.map_one_eq_zero]
  push_cast
  ring

theorem theta_Ee (w g : ℚ⟦X⟧) :
    theta ((1 - w) ^ 3 * g - 9 * w * (1 + w + w ^ 2)) =
      -(3 * (1 - w) ^ 2 * theta w) * g + (1 - w) ^ 3 * theta g - 9 * ((1 + 2 * w + 3 * w ^ 2) * theta w) := by
  simp only [map_sub, map_add, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
    theta_ofNat, Derivation.map_one_eq_zero]
  push_cast
  ring

theorem base_Ep (w gp : ℚ⟦X⟧) (hw : Coeffs4 w 0 3 0 0) (hg : Coeffs4 gp 0 0 0 27) :
    ∀ m < 4, coeff m ((1 - w ^ 3) * gp - w ^ 3) = 0 := by
  have hw3 := hw.mul (hw.mul hw)
  have h := ((Coeffs4.one.sub hw3).mul hg).sub hw3
  simp only [pow_three]
  obtain ⟨h0, h1, h2, h3⟩ := h
  intro m hm
  interval_cases m
  · rw [h0]; norm_num
  · rw [h1]; norm_num
  · rw [h2]; norm_num
  · rw [h3]; norm_num

theorem base_K (a u w : ℚ⟦X⟧) (ha0 : coeff 0 a = 1) (ha1 : coeff 1 a = 12)
    (hu0 : coeff 0 u = 1) (hu1 : coeff 1 u = 0) (hw0 : coeff 0 w = 0) (hw1 : coeff 1 w = 3) :
    ∀ m < 2, coeff m (a - u * (1 + 2 * w) ^ 2) = 0 := by
  intro m hm
  interval_cases m
  · -- m = 0
    rw [map_sub (coeff 0)]
    rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    rw [ha0, hu0]
    have hsq0 : (coeff 0) ((1 + 2 * w) ^ 2) = 1 := by
      rw [pow_two, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
      simp [map_add, coeff_one, hw0]
    rw [hsq0]
    norm_num
  · -- m = 1
    rw [map_sub (coeff 1)]
    rw [PowerSeries.coeff_mul]
    have h_anti1 : Finset.HasAntidiagonal.antidiagonal 1 = {(0,1), (1,0)} := by
      decide
    rw [h_anti1]
    simp [Finset.sum_insert, Finset.sum_singleton, ha1, hu0, hu1]
    have hsq1 : (coeff 1) ((1 + 2 * w) ^ 2) = 12 := by
      rw [pow_two, PowerSeries.coeff_mul]
      have h_anti1' : Finset.HasAntidiagonal.antidiagonal 1 = {(0,1), (1,0)} := by
        decide
      rw [h_anti1']
      simp [Finset.sum_insert, Finset.sum_singleton, map_add, coeff_one, hw0, hw1]
      ring
    rw [hsq1]
    norm_num

theorem base_Ee (w g : ℚ⟦X⟧) (hw0 : coeff 0 w = 0) (hw1 : coeff 1 w = 3)
    (hg0 : coeff 0 g = 0) (hg1 : coeff 1 g = 27) :
    ∀ m < 2, coeff m ((1 - w) ^ 3 * g - 9 * w * (1 + w + w ^ 2)) = 0 := by
  intro m hm
  interval_cases m
  · -- m = 0
    simp [coeff_mul, Finset.sum_singleton, hw0, hg0, map_sub, coeff_one]
  · -- m = 1
    simp [coeff_mul, Finset.Nat.antidiagonal_succ, Finset.sum_singleton, Finset.sum_insert, hw0, hw1, hg0, hg1, map_sub, coeff_one, pow_succ]
    norm_num

theorem constantCoeff_bW : constantCoeff bW = 1 := by
  unfold bW V3
  rw [PowerSeries.constantCoeff_expand 3 three_ne_zero]
  rw [map_mul]
  rw [CalegariSlopes.Bridge.constantCoeff_a2]
  rw [one_mul]
  rw [PowerSeries.constantCoeff_inv]
  rw [map_add]
  rw [map_one]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [CalegariSlopes.Bridge.coeff_Sol_zero]
  rw [add_zero]
  rw [inv_one]

theorem bW_mul : bW * (1 + V3 (Sol a2 27)) = V3 a2 := by
  have hconst : PowerSeries.constantCoeff (1 + Sol a2 27) ≠ 0 := by
    rw [map_add, PowerSeries.constantCoeff_one, ← PowerSeries.coeff_zero_eq_constantCoeff,
      CalegariSlopes.Bridge.coeff_Sol_zero, add_zero]
    exact one_ne_zero
  have h_inv : (1 + Sol a2 27)⁻¹ * (1 + Sol a2 27) = 1 :=
    PowerSeries.inv_mul_cancel _ hconst
  calc
    bW * (1 + V3 (Sol a2 27)) = V3 (a2 * (1 + Sol a2 27)⁻¹) * (1 + V3 (Sol a2 27)) := rfl
    _ = V3 (a2 * (1 + Sol a2 27)⁻¹) * V3 (1 + Sol a2 27) := by rw [map_add, map_one]
    _ = V3 ((a2 * (1 + Sol a2 27)⁻¹) * (1 + Sol a2 27)) := (map_mul V3 _ _).symm
    _ = V3 (a2 * ((1 + Sol a2 27)⁻¹ * (1 + Sol a2 27))) := by rw [mul_assoc]
    _ = V3 (a2 * 1) := by rw [h_inv]
    _ = V3 a2 := by simp

/-! ## (I3) and the first coefficients of `W` -/

/-- (I3), Theorem 4.5 (a): `W` has only exponents `≡ 1 (mod 3)`. -/
theorem I3 (n : ℕ) (hn : n % 3 ≠ 1) : coeff n W = 0 :=
  coeff_Sol_V3 _ 3 n hn

theorem coeffs_W : Coeffs4 W 0 3 0 0 :=
  ⟨coeff_Sol_zero _ _, coeff_Sol_one _ _, I3 2 (by norm_num), I3 3 (by norm_num)⟩

theorem coeffs_V3G : Coeffs4 (V3 (Sol a2 27)) 0 0 0 27 := by
  obtain ⟨h0, h1, h2, h3⟩ := coeff_V3_small (Sol a2 27)
  obtain ⟨g0, g1, -, -⟩ := coeff_G_small
  exact ⟨h0.trans g0, h1, h2, h3.trans g1⟩

theorem constantCoeff_V3 (f : ℚ⟦X⟧) : constantCoeff (V3 f) = constantCoeff f := by
  simp [V3]

/-! ## θ of the atoms -/

theorem theta_W : theta W = bW * W :=
  theta_Sol bW 3 constantCoeff_bW

theorem theta_V3G : theta (V3 (Sol a2 27)) = 3 * V3 a2 * V3 (Sol a2 27) := by
  rw [theta_V3, theta_G, map_mul]
  ring

/-! ## (I2) -/

/-- (I2), Theorem 4.5 (b): `(1 - W³) G(q³) = W³`. -/
theorem I2 : (1 - W ^ 3) * V3 (Sol a2 27) = W ^ 3 := by
  set Gp := V3 (Sol a2 27) with hGp
  set u2 := V3 a2 with hu2
  have cu2 : constantCoeff u2 = 1 := by rw [hu2, constantCoeff_V3, constantCoeff_a2]
  let e : Fin 1 → ℚ⟦X⟧ := ![(1 - W ^ 3) * Gp - W ^ 3]
  let N : Matrix (Fin 1) (Fin 1) ℚ⟦X⟧ := !![3 * u2]
  have hsys : ∀ i, (1 : ℚ⟦X⟧) * theta (e i) = ∑ j, N i j * e j := by
    intro i
    fin_cases i
    simp only [Fin.sum_univ_one, e, N, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.zero_eta]
    rw [theta_Ep]
    exact rowB_Ep W Gp u2 bW (theta W) (theta Gp) theta_W theta_V3G bW_mul
  have hN0 : N.map constantCoeff = !![3] := by
    ext i j
    fin_cases i
    fin_cases j
    simp [N, cu2, constantCoeff_ofNat]
  have he := lemmaU 1 N e 4 hsys (fun n hn => by
      rw [hN0, map_one, mul_one, Matrix.det_fin_one]
      have : (4 : ℚ) ≤ n := by exact_mod_cast hn
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.of_apply,
        Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
      intro h
      linarith)
    (fun i m hm => by
      fin_cases i
      exact base_Ep W Gp coeffs_W coeffs_V3G m hm)
  have h0 : (1 - W ^ 3) * Gp - W ^ 3 = 0 := congrFun he 0
  exact sub_eq_zero.mp h0

/-! ## θ of `a2`, `V₃ a2`, `W` -/

theorem four_ne_zero' : (4 : ℚ⟦X⟧) ≠ 0 := fun h => by
  simpa [constantCoeff_ofNat] using congrArg constantCoeff h

/-- `6 (1 + G) θ a2 = a2 ((1 + G) P + (3G - 1) a2)`, from Theorem 4.1 and the first two identities of Theorem 4.4. -/
theorem theta_a2 :
    6 * (1 + Sol a2 27) * theta a2 = a2 * ((1 + Sol a2 27) * E2q + (3 * Sol a2 27 - 1) * a2) := by
  obtain ⟨he1, he2, -, -⟩ := theoremA
  obtain ⟨h4P3, -, -⟩ := ram_V3
  have hp := two_mul_a2
  have hta : 2 * theta a2 = 3 * theta (V3 E2q) - theta E2q := by
    have h := congrArg theta hp
    rw [theta_A] at h
    simpa [Derivation.leibniz, theta_ofNat, smul_eq_mul] using h
  exact mul_left_cancel₀ four_ne_zero'
    (row_ta a2 (Sol a2 27) E2q (V3 E2q) E4q (V3 E4q) (theta E2q) (theta (V3 E2q)) (theta a2) hp hta ram_E2
      h4P3 he1 he2)

/-- `2 θ u2 = u2 (P₃ + (4 W³ - 1) u2)`, `u2 = V₃ a2`, after (I2). -/
theorem theta_u2 : 2 * theta (V3 a2) = V3 a2 * (V3 E2q + (4 * W ^ 3 - 1) * V3 a2) := by
  have h := congrArg V3 theta_a2
  simp only [map_mul, map_add, map_sub, map_one, map_ofNat] at h
  have ht : theta (V3 a2) = 3 * V3 (theta a2) := theta_V3 a2
  have hI2 := I2
  linear_combination 2 * ht + (1 - W ^ 3) * h
    + (-6 * V3 (theta a2) + V3 a2 * V3 E2q + 3 * V3 a2 ^ 2) * hI2

/-- `θ W = u2 (1 - W³) W`, after (I2). -/
theorem theta_W' : theta W = V3 a2 * (1 - W ^ 3) * W := by
  have hI2 := I2
  have hb := bW_mul
  linear_combination theta_W - bW * W * hI2 + (1 - W ^ 3) * W * hb

/-! ## (I1) -/

theorem I1_and : (1 - W) ^ 3 * Sol a2 27 = 9 * W * (1 + W + W ^ 2) ∧ a2 = V3 a2 * (1 + 2 * W) ^ 2 := by
  set G := Sol a2 27 with hG
  set u2 := V3 a2 with hu2
  have hp : E2q = 3 * V3 E2q - 2 * a2 := by linear_combination two_mul_a2
  have hp3 : V3 E2q = 3 * V3 (V3 E2q) - 2 * u2 := by
    have h := congrArg V3 two_mul_a2
    simp only [map_mul, map_sub, map_ofNat] at h
    linear_combination h
  have hta := theta_a2
  have htu := theta_u2
  have htW := theta_W'
  have htG : theta G = a2 * G := theta_G
  -- constant coefficients
  have c0 : ∀ f : ℚ⟦X⟧, constantCoeff f = coeff 0 f := fun f => (coeff_zero_eq_constantCoeff_apply f).symm
  have cG : constantCoeff G = 0 := by rw [c0]; exact coeff_G_small.1
  have cW : constantCoeff W = 0 := by rw [c0]; exact coeffs_W.1
  have ca2 : constantCoeff a2 = 1 := constantCoeff_a2
  have cu2 : constantCoeff u2 = 1 := by rw [hu2, constantCoeff_V3, constantCoeff_a2]
  have cP9 : constantCoeff (V3 (V3 E2q)) = 1 := by rw [constantCoeff_V3, constantCoeff_V3, constantCoeff_E2q]
  let e : Fin 2 → ℚ⟦X⟧ := ![a2 - u2 * (1 + 2 * W) ^ 2, (1 - W) ^ 3 * G - 9 * W * (1 + W + W ^ 2)]
  let N : Matrix (Fin 2) (Fin 2) ℚ⟦X⟧ :=
    !![(1 + G) * (9 * V3 (V3 E2q) * (1 + 2 * W) ^ 3 + 3 * (32 * u2 * W ^ 5 + 32 * u2 * W ^ 4
        + (40 * u2 + 4 * (a2 - u2 * (1 + 2 * W) ^ 2)) * W ^ 3 + 16 * u2 * W ^ 2
        + (6 * (a2 - u2 * (1 + 2 * W) ^ 2) - 8 * u2) * W - 4 * u2 - (a2 - u2 * (1 + 2 * W) ^ 2))), 4 * a2 ^ 2;
      54 * (1 + G) * (1 + 2 * W) ^ 3 * W * (1 + W + W ^ 2),
        6 * (1 + G) * (1 + 2 * W) ^ 3 * (a2 - 3 * u2 * W * (1 + W + W ^ 2))]
  have hsys : ∀ i, 6 * (1 + G) * (1 + 2 * W) ^ 3 * theta (e i) = ∑ j, N i j * e j := by
    intro i
    fin_cases i <;> simp only [Fin.sum_univ_two, e, N, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one]
    · rw [theta_K]
      linear_combination rowB_K a2 u2 W G E2q (V3 E2q) (V3 (V3 E2q)) (theta a2) (theta u2) (theta W) hp hp3 hta
        htu htW
    · rw [theta_Ee]
      linear_combination rowB_E a2 u2 W G (theta W) (theta G) htW htG
  have hN0 : N.map constantCoeff = !![-3, 4; 0, 6] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [N, cG, cW, ca2, cu2, cP9, constantCoeff_ofNat]
    norm_num
  have cw : constantCoeff (6 * (1 + G) * (1 + 2 * W) ^ 3) = 6 := by
    simp [cG, cW, constantCoeff_ofNat]
  have he := lemmaU _ N e 2 hsys (fun n hn => by
      rw [hN0, cw, Matrix.det_fin_two]
      have : (2 : ℚ) ≤ n := by exact_mod_cast hn
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq,
        Fin.zero_eq_one_iff, Fin.one_eq_zero_iff, smul_eq_mul, mul_one, mul_zero, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        OfNat.ofNat_ne_one, not_false_eq_true]
      intro h
      nlinarith)
    (fun i m hm => by
      fin_cases i
      · exact base_K a2 u2 W coeff_a2_small.1 coeff_a2_small.2.1 ((coeff_V3_small a2).1.trans coeff_a2_small.1)
          (coeff_V3_small a2).2.1 coeffs_W.1 coeffs_W.2.1 m hm
      · exact base_Ee W G coeffs_W.1 coeffs_W.2.1 coeff_G_small.1 coeff_G_small.2.1 m hm)
  have hK : a2 - u2 * (1 + 2 * W) ^ 2 = 0 := congrFun he 0
  have hE : (1 - W) ^ 3 * G - 9 * W * (1 + W + W ^ 2) = 0 := congrFun he 1
  exact ⟨sub_eq_zero.mp hE, sub_eq_zero.mp hK⟩

/-- (I1), Theorem 4.5 (c): `(1 - W)³ G = 9 W (1 + W + W²)`. -/
theorem I1 : (1 - W) ^ 3 * Sol a2 27 = 9 * W * (1 + W + W ^ 2) :=
  I1_and.1

/-- The companion of (I1): `a2 = a2(q³) (1 + 2W)²`. -/
theorem a2_eq : a2 = V3 a2 * (1 + 2 * W) ^ 2 :=
  I1_and.2

end CalegariSlopes.Bridge.Level9
