/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Bridge.Ram
public import CalegariSlopes.Bridge.LemmaU

@[expose] public section

/-! # Theorem 4.4, level three -/

open PowerSeries
open CalegariSlopes.Overconvergent (E4q E6q Dq jinv)
open CalegariSlopes.Spectral (JHyp)

namespace CalegariSlopes.Bridge

/-! ## Theorem 4.4: the closed system of the four defects

The rows are identities in any commutative ring: `p1 q1 r1 p3 q3 r3 g` stand for `P Q R P₃ Q₃ R₃ G`, `A = 3 p3 - p1`
for `2 a2`, the `t`-variables for their images by `θ`, related by Theorem 4.1 at `q` and `q³` and `2 θG = A G`; the left
sides are `48 (1 + g) θEᵢ` expanded by the Leibniz rule. -/

theorem row1 {R : Type*} [CommRing R] (p1 q1 r1 p3 q3 g A tp1 tq1 tp3 tg : R)
    (hA : A = 3 * p3 - p1) (h1 : 12 * tp1 = p1 ^ 2 - q1) (h2 : 3 * tq1 = p1 * q1 - r1)
    (h4 : 4 * tp3 = p3 ^ 2 - q3) (hg : 2 * tg = A * g) :
    48 * (1 + g) * (4 * tg * q1 + 4 * (1 + g) * tq1 - 2 * A * (3 * tp3 - tp1) * (1 + 9 * g) - 9 * A ^ 2 * tg) =
      2 * ((5 * g + 9) * p1 + 3 * (3 * g - 1) * p3) * (4 * (1 + g) * q1 - A ^ 2 * (1 + 9 * g))
      + 2 * (9 * g + 1) * A * (36 * (1 + g) * q3 - A ^ 2 * (9 + g))
      - 8 * (8 * (1 + g) ^ 2 * r1 - A ^ 3 * (1 - 18 * g - 27 * g ^ 2)) := by
  subst hA
  linear_combination 24 * (1 + g) * (4 * q1 - 9 * (3 * p3 - p1) ^ 2) * hg + 64 * (1 + g) ^ 2 * h2
    - 72 * (3 * p3 - p1) * (1 + g) * (1 + 9 * g) * h4 + 8 * (3 * p3 - p1) * (1 + g) * (1 + 9 * g) * h1

theorem row2 {R : Type*} [CommRing R] (p1 q1 p3 q3 r3 g A tp1 tp3 tq3 tg : R)
    (hA : A = 3 * p3 - p1) (h1 : 12 * tp1 = p1 ^ 2 - q1)
    (h4 : 4 * tp3 = p3 ^ 2 - q3) (h5 : tq3 = p3 * q3 - r3) (hg : 2 * tg = A * g) :
    48 * (1 + g) * (36 * tg * q3 + 36 * (1 + g) * tq3 - 2 * A * (3 * tp3 - tp1) * (9 + g) - A ^ 2 * tg) =
      -2 * (g + 9) * A * (4 * (1 + g) * q1 - A ^ 2 * (1 + 9 * g))
      + 2 * (-(13 * g + 9) * p1 + 3 * (21 * g + 17) * p3) * (36 * (1 + g) * q3 - A ^ 2 * (9 + g))
      - 8 * (216 * (1 + g) ^ 2 * r3 - A ^ 3 * (27 + 18 * g - g ^ 2)) := by
  subst hA
  linear_combination 24 * (1 + g) * (36 * q3 - (3 * p3 - p1) ^ 2) * hg + 1728 * (1 + g) ^ 2 * h5
    - 72 * (3 * p3 - p1) * (1 + g) * (9 + g) * h4 + 8 * (3 * p3 - p1) * (1 + g) * (9 + g) * h1

theorem row3 {R : Type*} [CommRing R] (p1 q1 r1 p3 q3 g A tp1 tr1 tp3 tg : R)
    (hA : A = 3 * p3 - p1) (h1 : 12 * tp1 = p1 ^ 2 - q1) (h3 : 2 * tr1 = p1 * r1 - q1 ^ 2)
    (h4 : 4 * tp3 = p3 ^ 2 - q3) (hg : 2 * tg = A * g) :
    48 * (1 + g) * (16 * (1 + g) * tg * r1 + 8 * (1 + g) ^ 2 * tr1
        - 3 * A ^ 2 * (3 * tp3 - tp1) * (1 - 18 * g - 27 * g ^ 2) - A ^ 3 * (-18 * tg - 54 * g * tg)) =
      (-3 * (45 * g ^ 2 + 62 * g + 9) * A ^ 2 - 12 * (1 + g) * (4 * (1 + g) * q1 - A ^ 2 * (1 + 9 * g)))
          * (4 * (1 + g) * q1 - A ^ 2 * (1 + 9 * g))
      - 3 * (27 * g ^ 2 + 18 * g - 1) * A ^ 2 * (36 * (1 + g) * q3 - A ^ 2 * (9 + g))
      + 24 * ((1 - g) * p1 + 6 * g * p3) * (8 * (1 + g) ^ 2 * r1 - A ^ 3 * (1 - 18 * g - 27 * g ^ 2)) := by
  subst hA
  linear_combination 24 * (1 + g) * (16 * (1 + g) * r1 + (3 * p3 - p1) ^ 3 * (18 + 54 * g)) * hg
    + 192 * (1 + g) ^ 3 * h3
    - 108 * (3 * p3 - p1) ^ 2 * (1 + g) * (1 - 18 * g - 27 * g ^ 2) * h4
    + 12 * (3 * p3 - p1) ^ 2 * (1 + g) * (1 - 18 * g - 27 * g ^ 2) * h1

theorem row4 {R : Type*} [CommRing R] (p1 q1 p3 q3 r3 g A tp1 tp3 tr3 tg : R)
    (hA : A = 3 * p3 - p1) (h1 : 12 * tp1 = p1 ^ 2 - q1)
    (h4 : 4 * tp3 = p3 ^ 2 - q3) (h6 : 2 * tr3 = 3 * (p3 * r3 - q3 ^ 2)) (hg : 2 * tg = A * g) :
    48 * (1 + g) * (432 * (1 + g) * tg * r3 + 216 * (1 + g) ^ 2 * tr3
        - 3 * A ^ 2 * (3 * tp3 - tp1) * (27 + 18 * g - g ^ 2) - A ^ 3 * (18 * tg - 2 * g * tg)) =
      3 * (g ^ 2 - 18 * g - 27) * A ^ 2 * (4 * (1 + g) * q1 - A ^ 2 * (1 + 9 * g))
      + (-3 * (9 * g ^ 2 + 62 * g + 45) * A ^ 2 - 12 * (1 + g) * (36 * (1 + g) * q3 - A ^ 2 * (9 + g)))
          * (36 * (1 + g) * q3 - A ^ 2 * (9 + g))
      + 24 * (-2 * g * p1 + 3 * (3 * g + 1) * p3) * (216 * (1 + g) ^ 2 * r3 - A ^ 3 * (27 + 18 * g - g ^ 2)) := by
  subst hA
  linear_combination 24 * (1 + g) * (432 * (1 + g) * r3 - (3 * p3 - p1) ^ 3 * (18 - 2 * g)) * hg
    + 5184 * (1 + g) ^ 3 * h6
    - 108 * (3 * p3 - p1) ^ 2 * (1 + g) * (27 + 18 * g - g ^ 2) * h4
    + 12 * (3 * p3 - p1) ^ 2 * (1 + g) * (27 + 18 * g - g ^ 2) * h1

/-- `N(0)` of the system of the four defects with weight `48 (1 + G)`; the proof of Theorem 4.4 writes the system with
weight `1 + g`. Characteristic polynomial `x² (x - 48) (x - 144)`. -/
theorem det_N0 (x : ℚ) :
    (x • (1 : Matrix (Fin 4) (Fin 4) ℚ) -
      !![12, 4, -8, 0; -36, 84, 0, -8; -108, 12, 24, 0; -324, -540, 0, 72]).det =
      x ^ 2 * (x - 48) * (x - 144) := by
  have hM : x • (1 : Matrix (Fin 4) (Fin 4) ℚ) -
      !![12, 4, -8, 0; -36, 84, 0, -8; -108, 12, 24, 0; -324, -540, 0, 72] =
      !![x - 12, -4, 8, 0; 36, x - 84, 0, 8; 108, -12, x - 24, 0; 324, 540, 0, x - 72] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hM, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  ring

/-! ### First four coefficients of sums and products -/

theorem Coeffs4.add {f g : ℚ⟦X⟧} {a0 a1 a2 a3 b0 b1 b2 b3 : ℚ} (hf : Coeffs4 f a0 a1 a2 a3)
    (hg : Coeffs4 g b0 b1 b2 b3) : Coeffs4 (f + g) (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3) := by
  obtain ⟨f0, f1, f2, f3⟩ := hf
  obtain ⟨g0, g1, g2, g3⟩ := hg
  simp only [Coeffs4, map_add, f0, f1, f2, f3, g0, g1, g2, g3, and_self]

theorem Coeffs4.sub {f g : ℚ⟦X⟧} {a0 a1 a2 a3 b0 b1 b2 b3 : ℚ} (hf : Coeffs4 f a0 a1 a2 a3)
    (hg : Coeffs4 g b0 b1 b2 b3) : Coeffs4 (f - g) (a0 - b0) (a1 - b1) (a2 - b2) (a3 - b3) := by
  obtain ⟨f0, f1, f2, f3⟩ := hf
  obtain ⟨g0, g1, g2, g3⟩ := hg
  simp only [Coeffs4, map_sub, f0, f1, f2, f3, g0, g1, g2, g3, and_self]

theorem Coeffs4.mul {f g : ℚ⟦X⟧} {a0 a1 a2 a3 b0 b1 b2 b3 : ℚ} (hf : Coeffs4 f a0 a1 a2 a3)
    (hg : Coeffs4 g b0 b1 b2 b3) :
    Coeffs4 (f * g) (a0 * b0) (a0 * b1 + a1 * b0) (a0 * b2 + a1 * b1 + a2 * b0)
      (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) := by
  obtain ⟨f0, f1, f2, f3⟩ := hf
  obtain ⟨g0, g1, g2, g3⟩ := hg
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [coeff_mul, Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_cons,
      Finset.sum_map, Finset.sum_singleton, Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk,
      Prod.map_apply, Nat.succ_eq_add_one, zero_add, Nat.reduceAdd, Function.Embedding.refl_apply, f0, f1, f2, f3,
      g0, g1, g2, g3] <;> ring

theorem Coeffs4.one : Coeffs4 (1 : ℚ⟦X⟧) 1 0 0 0 := by
  simp [Coeffs4, coeff_one]

theorem Coeffs4.ofNat (n : ℕ) [n.AtLeastTwo] :
    Coeffs4 (no_index (OfNat.ofNat n : ℚ⟦X⟧)) (OfNat.ofNat n) 0 0 0 := by
  have h : (OfNat.ofNat n : ℚ⟦X⟧) = C (OfNat.ofNat n : ℚ) := rfl
  simp only [Coeffs4, h, coeff_C]
  simp

/-! ### Base case mod `q⁴` (proof of Theorem 4.4), for any series with the first coefficients of `P Q R P₃ Q₃ R₃ G` -/

theorem base_E1 (p1 q1 p3 g : ℚ⟦X⟧) (hp1 : Coeffs4 p1 1 (-24) (-72) (-96))
    (hq1 : Coeffs4 q1 1 240 2160 6720) (hp3 : Coeffs4 p3 1 0 0 (-24)) (hg : Coeffs4 g 0 27 324 2430) :
    ∀ m < 4, coeff m (4 * (1 + g) * q1 - (3 * p3 - p1) ^ 2 * (1 + 9 * g)) = 0 := by
  have hA := (Coeffs4.ofNat 3).mul hp3 |>.sub hp1
  have h := (((Coeffs4.ofNat 4).mul (Coeffs4.one.add hg)).mul hq1).sub
    ((hA.mul hA).mul (Coeffs4.one.add ((Coeffs4.ofNat 9).mul hg)))
  rw [pow_two]
  obtain ⟨h0, h1, h2, h3⟩ := h
  intro m hm
  interval_cases m
  · rw [h0]; norm_num
  · rw [h1]; norm_num
  · rw [h2]; norm_num
  · rw [h3]; norm_num

theorem base_E2 (p1 p3 q3 g : ℚ⟦X⟧) (hp1 : Coeffs4 p1 1 (-24) (-72) (-96))
    (hp3 : Coeffs4 p3 1 0 0 (-24)) (hq3 : Coeffs4 q3 1 0 0 240) (hg : Coeffs4 g 0 27 324 2430) :
    ∀ m < 4, coeff m (36 * (1 + g) * q3 - (3 * p3 - p1) ^ 2 * (9 + g)) = 0 := by
  have hA := (Coeffs4.ofNat 3).mul hp3 |>.sub hp1
  have h := (((Coeffs4.ofNat 36).mul (Coeffs4.one.add hg)).mul hq3).sub
    ((hA.mul hA).mul ((Coeffs4.ofNat 9).add hg))
  rw [pow_two]
  obtain ⟨h0, h1, h2, h3⟩ := h
  intro m hm
  interval_cases m
  · rw [h0]; norm_num
  · rw [h1]; norm_num
  · rw [h2]; norm_num
  · rw [h3]; norm_num

theorem base_E3 (p1 r1 p3 g : ℚ⟦X⟧) (hp1 : Coeffs4 p1 1 (-24) (-72) (-96))
    (hr1 : Coeffs4 r1 1 (-504) (-16632) (-122976)) (hp3 : Coeffs4 p3 1 0 0 (-24))
    (hg : Coeffs4 g 0 27 324 2430) :
    ∀ m < 4, coeff m (8 * (1 + g) ^ 2 * r1 - (3 * p3 - p1) ^ 3 * (1 - 18 * g - 27 * g ^ 2)) = 0 := by
  have hA := (Coeffs4.ofNat 3).mul hp3 |>.sub hp1
  have h1g := Coeffs4.one.add hg
  have h := (((Coeffs4.ofNat 8).mul (h1g.mul h1g)).mul hr1).sub
    ((hA.mul (hA.mul hA)).mul ((Coeffs4.one.sub ((Coeffs4.ofNat 18).mul hg)).sub
      ((Coeffs4.ofNat 27).mul (hg.mul hg))))
  simp only [pow_two, pow_three]
  obtain ⟨h0, h1, h2, h3⟩ := h
  intro m hm
  interval_cases m
  · rw [h0]; norm_num
  · rw [h1]; norm_num
  · rw [h2]; norm_num
  · rw [h3]; norm_num

theorem base_E4 (p1 p3 r3 g : ℚ⟦X⟧) (hp1 : Coeffs4 p1 1 (-24) (-72) (-96))
    (hp3 : Coeffs4 p3 1 0 0 (-24)) (hr3 : Coeffs4 r3 1 0 0 (-504)) (hg : Coeffs4 g 0 27 324 2430) :
    ∀ m < 4, coeff m (216 * (1 + g) ^ 2 * r3 - (3 * p3 - p1) ^ 3 * (27 + 18 * g - g ^ 2)) = 0 := by
  have hA := (Coeffs4.ofNat 3).mul hp3 |>.sub hp1
  have h1g := Coeffs4.one.add hg
  have h := (((Coeffs4.ofNat 216).mul (h1g.mul h1g)).mul hr3).sub
    ((hA.mul (hA.mul hA)).mul (((Coeffs4.ofNat 27).add ((Coeffs4.ofNat 18).mul hg)).sub (hg.mul hg)))
  simp only [pow_two, pow_three]
  obtain ⟨h0, h1, h2, h3⟩ := h
  intro m hm
  interval_cases m
  · rw [h0]; norm_num
  · rw [h1]; norm_num
  · rw [h2]; norm_num
  · rw [h3]; norm_num

/-! ### θ of the atoms and of the defects -/

theorem theta_ofNat (n : ℕ) [n.AtLeastTwo] : theta (no_index (OfNat.ofNat n : ℚ⟦X⟧)) = 0 := by
  rw [show (OfNat.ofNat n : ℚ⟦X⟧) = ((OfNat.ofNat n : ℕ) : ℚ⟦X⟧) from (Nat.cast_ofNat).symm]
  exact theta.map_natCast _

theorem constantCoeff_ofNat (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (no_index (OfNat.ofNat n : ℚ⟦X⟧)) = (OfNat.ofNat n : ℚ) := by
  rw [show (OfNat.ofNat n : ℚ⟦X⟧) = ((OfNat.ofNat n : ℕ) : ℚ⟦X⟧) from (Nat.cast_ofNat).symm, map_natCast]
  exact Nat.cast_ofNat

theorem theta_E1 (G Q A : ℚ⟦X⟧) : theta (4 * (1 + G) * Q - A ^ 2 * (1 + 9 * G)) =
    4 * theta G * Q + 4 * (1 + G) * theta Q - 2 * A * theta A * (1 + 9 * G) - 9 * A ^ 2 * theta G := by
  simp only [map_sub, map_add, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
    theta_ofNat, Derivation.map_one_eq_zero]
  push_cast
  ring

theorem theta_E2 (G Q3 A : ℚ⟦X⟧) : theta (36 * (1 + G) * Q3 - A ^ 2 * (9 + G)) =
    36 * theta G * Q3 + 36 * (1 + G) * theta Q3 - 2 * A * theta A * (9 + G) - A ^ 2 * theta G := by
  simp only [map_sub, map_add, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
    theta_ofNat, Derivation.map_one_eq_zero]
  push_cast
  ring

theorem theta_E3 (G R A : ℚ⟦X⟧) : theta (8 * (1 + G) ^ 2 * R - A ^ 3 * (1 - 18 * G - 27 * G ^ 2)) =
    16 * (1 + G) * theta G * R + 8 * (1 + G) ^ 2 * theta R
      - 3 * A ^ 2 * theta A * (1 - 18 * G - 27 * G ^ 2) - A ^ 3 * (-18 * theta G - 54 * G * theta G) := by
  simp only [map_sub, map_add, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
    theta_ofNat, Derivation.map_one_eq_zero]
  push_cast
  ring

theorem theta_E4 (G R3 A : ℚ⟦X⟧) : theta (216 * (1 + G) ^ 2 * R3 - A ^ 3 * (27 + 18 * G - G ^ 2)) =
    432 * (1 + G) * theta G * R3 + 216 * (1 + G) ^ 2 * theta R3
      - 3 * A ^ 2 * theta A * (27 + 18 * G - G ^ 2) - A ^ 3 * (18 * theta G - 2 * G * theta G) := by
  simp only [map_sub, map_add, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
    theta_ofNat, Derivation.map_one_eq_zero]
  push_cast
  ring

theorem theta_A (P P3 : ℚ⟦X⟧) : theta (3 * P3 - P) = 3 * theta P3 - theta P := by
  simp only [map_sub, Derivation.leibniz, smul_eq_mul, theta_ofNat]
  ring

/-- Theorem 4.1 at `q³`. -/
theorem ram_V3 :
    4 * theta (V3 E2q) = V3 E2q ^ 2 - V3 E4q ∧ theta (V3 E4q) = V3 E2q * V3 E4q - V3 E6q ∧
      2 * theta (V3 E6q) = 3 * (V3 E2q * V3 E6q - V3 E4q ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [theta_V3, ← mul_assoc, show (4 : ℚ⟦X⟧) * 3 = 12 by norm_num,
      show (12 : ℚ⟦X⟧) = V3 12 from (map_ofNat V3 12).symm, ← map_mul, ram_E2, map_sub, map_pow]
  · rw [theta_V3, show (3 : ℚ⟦X⟧) = V3 3 from (map_ofNat V3 3).symm, ← map_mul, ram_E4, map_sub, map_mul]
  · rw [theta_V3, ← mul_assoc, show (2 : ℚ⟦X⟧) * 3 = 3 * 2 by norm_num, mul_assoc,
      show (2 : ℚ⟦X⟧) = V3 2 from (map_ofNat V3 2).symm, ← map_mul, ram_E6, map_sub, map_mul, map_pow]

theorem constantCoeff_E2q : constantCoeff E2q = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]; exact coeff_E2q_small.1

/-- The atoms have the first coefficients of the proof of Theorem 4.4. -/
theorem coeffs4_atoms :
    Coeffs4 E2q 1 (-24) (-72) (-96) ∧ Coeffs4 E4q 1 240 2160 6720 ∧
      Coeffs4 E6q 1 (-504) (-16632) (-122976) ∧ Coeffs4 (V3 E2q) 1 0 0 (-24) ∧
      Coeffs4 (V3 E4q) 1 0 0 240 ∧ Coeffs4 (V3 E6q) 1 0 0 (-504) ∧ Coeffs4 (Sol a2 27) 0 27 324 2430 := by
  obtain ⟨p0, p1, p2, p3⟩ := coeff_E2q_small
  obtain ⟨q0, q1, q2, q3⟩ := coeff_E4q_small
  obtain ⟨r0, r1, r2, r3⟩ := coeff_E6q_small
  obtain ⟨vp0, vp1, vp2, vp3⟩ := coeff_V3_small E2q
  obtain ⟨vq0, vq1, vq2, vq3⟩ := coeff_V3_small E4q
  obtain ⟨vr0, vr1, vr2, vr3⟩ := coeff_V3_small E6q
  refine ⟨⟨p0, p1, p2, p3⟩, ⟨q0, q1, q2, q3⟩, ⟨r0, r1, r2, r3⟩, ⟨?_, vp1, vp2, ?_⟩, ⟨?_, vq1, vq2, ?_⟩,
    ⟨?_, vr1, vr2, ?_⟩, coeff_G_small⟩ <;> simp_all

/-- Theorem 4.4, the four level 3 identities for `G = Sol a2 27`. -/
theorem theoremA :
    (1 + Sol a2 27) * E4q = a2 ^ 2 * (1 + 9 * Sol a2 27) ∧
      9 * (1 + Sol a2 27) * V3 E4q = a2 ^ 2 * (9 + Sol a2 27) ∧
      (1 + Sol a2 27) ^ 2 * E6q = a2 ^ 3 * (1 - 18 * Sol a2 27 - 27 * Sol a2 27 ^ 2) ∧
      27 * (1 + Sol a2 27) ^ 2 * V3 E6q = a2 ^ 3 * (27 + 18 * Sol a2 27 - Sol a2 27 ^ 2) := by
  set G := Sol a2 27 with hGdef
  set P := E2q
  set Q := E4q
  set R := E6q
  set P3 := V3 E2q
  set Q3 := V3 E4q
  set R3 := V3 E6q
  set A := 3 * P3 - P with hAdef
  obtain ⟨hP, hQ, hR, hP3, hQ3, hR3, hG⟩ := coeffs4_atoms
  obtain ⟨h4P3, hQ3t, h2R3⟩ := ram_V3
  have hA2 : 2 * a2 = A := two_mul_a2
  have hgt : 2 * theta G = A * G := by rw [theta_G, ← hA2]; ring
  have tA := theta_A P P3
  set E1 := 4 * (1 + G) * Q - A ^ 2 * (1 + 9 * G) with hE1
  set E2 := 36 * (1 + G) * Q3 - A ^ 2 * (9 + G) with hE2
  set E3 := 8 * (1 + G) ^ 2 * R - A ^ 3 * (1 - 18 * G - 27 * G ^ 2) with hE3
  set E4 := 216 * (1 + G) ^ 2 * R3 - A ^ 3 * (27 + 18 * G - G ^ 2) with hE4
  have b1 := base_E1 P Q P3 G hP hQ hP3 hG
  have b2 := base_E2 P P3 Q3 G hP hP3 hQ3 hG
  have b3 := base_E3 P R P3 G hP hR hP3 hG
  have b4 := base_E4 P P3 R3 G hP hP3 hR3 hG
  -- constant coefficients of the atoms
  have c0 : ∀ f : ℚ⟦X⟧, constantCoeff f = coeff 0 f := fun f => (coeff_zero_eq_constantCoeff_apply f).symm
  have cP : constantCoeff P = 1 := by rw [c0]; exact hP.1
  have cP3 : constantCoeff P3 = 1 := by rw [c0]; exact hP3.1
  have cG : constantCoeff G = 0 := by rw [c0]; exact hG.1
  have cA : constantCoeff A = 2 := by simp only [hAdef, map_sub, map_mul, cP, cP3, map_ofNat]; norm_num
  have cE1 : constantCoeff E1 = 0 := by rw [c0]; exact b1 0 (by norm_num)
  have cE2 : constantCoeff E2 = 0 := by rw [c0]; exact b2 0 (by norm_num)
  -- the system
  let e : Fin 4 → ℚ⟦X⟧ := ![E1, E2, E3, E4]
  let N : Matrix (Fin 4) (Fin 4) ℚ⟦X⟧ :=
    !![2 * ((5 * G + 9) * P + 3 * (3 * G - 1) * P3), 2 * (9 * G + 1) * A, -8, 0;
      -2 * (G + 9) * A, 2 * (-(13 * G + 9) * P + 3 * (21 * G + 17) * P3), 0, -8;
      -3 * (45 * G ^ 2 + 62 * G + 9) * A ^ 2 - 12 * (1 + G) * E1, -3 * (27 * G ^ 2 + 18 * G - 1) * A ^ 2,
        24 * ((1 - G) * P + 6 * G * P3), 0;
      3 * (G ^ 2 - 18 * G - 27) * A ^ 2, -3 * (9 * G ^ 2 + 62 * G + 45) * A ^ 2 - 12 * (1 + G) * E2, 0,
        24 * (-2 * G * P + 3 * (3 * G + 1) * P3)]
  have hsys : ∀ i, 48 * (1 + G) * theta (e i) = ∑ j, N i j * e j := by
    intro i
    fin_cases i <;> simp only [Fin.sum_univ_four, e, N, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.vecHead,
      Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    · rw [hE1, theta_E1, tA]
      linear_combination row1 P Q R P3 Q3 G A (theta P) (theta Q) (theta P3) (theta G) hAdef ram_E2 ram_E4 h4P3 hgt
    · rw [hE2, theta_E2, tA]
      linear_combination row2 P Q P3 Q3 R3 G A (theta P) (theta P3) (theta Q3) (theta G) hAdef ram_E2 h4P3 hQ3t hgt
    · rw [hE3, theta_E3, tA]
      linear_combination row3 P Q R P3 Q3 G A (theta P) (theta R) (theta P3) (theta G) hAdef ram_E2 ram_E6 h4P3 hgt
    · rw [hE4, theta_E4, tA]
      linear_combination row4 P Q P3 Q3 R3 G A (theta P) (theta P3) (theta R3) (theta G) hAdef ram_E2 h4P3 h2R3 hgt
  have hN0 : N.map constantCoeff = !![12, 4, -8, 0; -36, 84, 0, -8; -108, 12, 24, 0; -324, -540, 0, 72] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [N, cP, cP3, cG, cA, cE1, cE2, constantCoeff_ofNat] <;> norm_num
  have cw : constantCoeff (48 * (1 + G)) = 48 := by simp [cG, constantCoeff_ofNat]
  have he := lemmaU (48 * (1 + G)) N e 4 hsys (fun n hn => by
      rw [hN0, cw, det_N0]
      have : (4 : ℚ) ≤ n := by exact_mod_cast hn
      have h1 : (n : ℚ) * 48 ≠ 0 := by positivity
      have h2 : (n : ℚ) * 48 - 48 ≠ 0 := by nlinarith
      have h3 : (n : ℚ) * 48 - 144 ≠ 0 := by nlinarith
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 h1) h2) h3)
    (fun i m hm => by fin_cases i <;> simp [e] <;> [exact b1 m hm; exact b2 m hm; exact b3 m hm; exact b4 m hm])
  have z1 : E1 = 0 := congrFun he 0
  have z2 : E2 = 0 := congrFun he 1
  have z3 : E3 = 0 := congrFun he 2
  have z4 : E4 = 0 := congrFun he 3
  have h4 : (4 : ℚ⟦X⟧) ≠ 0 := fun h => by simpa [constantCoeff_ofNat] using congrArg constantCoeff h
  have h8 : (8 : ℚ⟦X⟧) ≠ 0 := fun h => by simpa [constantCoeff_ofNat] using congrArg constantCoeff h
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine sub_eq_zero.mp ((mul_eq_zero.mp ?_).resolve_left h4)
    linear_combination z1 - hE1 - (1 + 9 * G) * (A + 2 * a2) * hA2
  · refine sub_eq_zero.mp ((mul_eq_zero.mp ?_).resolve_left h4)
    linear_combination z2 - hE2 - (9 + G) * (A + 2 * a2) * hA2
  · refine sub_eq_zero.mp ((mul_eq_zero.mp ?_).resolve_left h8)
    linear_combination z3 - hE3 - (1 - 18 * G - 27 * G ^ 2) * (A ^ 2 + 2 * a2 * A + 4 * a2 ^ 2) * hA2
  · refine sub_eq_zero.mp ((mul_eq_zero.mp ?_).resolve_left h8)
    linear_combination z4 - hE4 - (27 + 18 * G - G ^ 2) * (A ^ 2 + 2 * a2 * A + 4 * a2 ^ 2) * hA2
end CalegariSlopes.Bridge
