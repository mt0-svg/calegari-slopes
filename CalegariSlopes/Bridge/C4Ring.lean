/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Identities in commutative rings

The three identities of Lemma 4.6 (`ring_L1`, `ring_L2`, `ring_ME`) and the rows of the level 9 systems in the proof
of Theorem 4.5: `rowB_Ep` for (b), `rowB_K`, `rowB_E` for (c), `row_ta` for `θ a2`.
-/

namespace CalegariSlopes.Bridge.Level9

/-- A factor `d` with `d c = 1` cancels. -/
theorem eq_zero_of_pow_mul_eq_zero {R : Type*} [CommRing R] (d c T : R) (n : ℕ) (hc : d * c = 1)
    (h : d ^ n * T = 0) : T = 0 := by
  calc T = (d * c) ^ n * T := by rw [hc, one_pow, one_mul]
    _ = c ^ n * (d ^ n * T) := by ring
    _ = 0 := by rw [h, mul_zero]

theorem ring_L1 {R : Type*} [CommRing R] (w g g' : R)
    (h1 : (1 - w) ^ 3 * g = 9 * w * (1 + w + w ^ 2)) (h2 : (1 - w ^ 3) * g' = w ^ 3) :
    g = (90 * g' + 324 * g' ^ 2 + 243 * g' ^ 3) + w * (9 + 171 * g' + 405 * g' ^ 2 + 243 * g' ^ 3)
      + w ^ 2 * (36 + 279 * g' + 486 * g' ^ 2 + 243 * g' ^ 3) := by
  have hc : (1 - w ^ 3) * (1 + g') = 1 := by linear_combination h2
  have e1 : (1 - w ^ 3) ^ 3 * g = 9 * w * (1 + w + w ^ 2) ^ 4 := by
    linear_combination (1 + w + w ^ 2) ^ 3 * h1
  rw [← sub_eq_zero]
  refine eq_zero_of_pow_mul_eq_zero (1 - w ^ 3) (1 + g') _ 3 hc ?_
  have key : (1 - w ^ 3) ^ 3 * (g - ((90 * g' + 324 * g' ^ 2 + 243 * g' ^ 3)
      + w * (9 + 171 * g' + 405 * g' ^ 2 + 243 * g' ^ 3) + w ^ 2 * (36 + 279 * g' + 486 * g' ^ 2 + 243 * g' ^ 3))) =
      (1 - w ^ 3) ^ 3 * g
        - (90 * (1 - w ^ 3) ^ 2 * ((1 - w ^ 3) * g') + 324 * (1 - w ^ 3) * ((1 - w ^ 3) * g') ^ 2
          + 243 * ((1 - w ^ 3) * g') ^ 3)
        - w * (9 * (1 - w ^ 3) ^ 3 + 171 * (1 - w ^ 3) ^ 2 * ((1 - w ^ 3) * g')
          + 405 * (1 - w ^ 3) * ((1 - w ^ 3) * g') ^ 2 + 243 * ((1 - w ^ 3) * g') ^ 3)
        - w ^ 2 * (36 * (1 - w ^ 3) ^ 3 + 279 * (1 - w ^ 3) ^ 2 * ((1 - w ^ 3) * g')
          + 486 * (1 - w ^ 3) * ((1 - w ^ 3) * g') ^ 2 + 243 * ((1 - w ^ 3) * g') ^ 3) := by ring
  rw [key, e1, h2]
  ring

theorem ring_L2 {R : Type*} [CommRing R] (w g g' : R)
    (h1 : (1 - w) ^ 3 * g = 9 * w * (1 + w + w ^ 2)) (h2 : (1 - w ^ 3) * g' = w ^ 3) :
    g ^ 2 = (648 * g' + 486 * g' ^ 2) + w * (486 * g' + 486 * g' ^ 2) + w ^ 2 * (81 - 162 * g' - 243 * g' ^ 2)
      + (270 * g' + 972 * g' ^ 2 + 729 * g' ^ 3) * g := by
  have hc : (1 - w ^ 3) * (1 + g') = 1 := by linear_combination h2
  have e1 : (1 - w ^ 3) ^ 3 * g = 9 * w * (1 + w + w ^ 2) ^ 4 := by
    linear_combination (1 + w + w ^ 2) ^ 3 * h1
  rw [← sub_eq_zero]
  refine eq_zero_of_pow_mul_eq_zero (1 - w ^ 3) (1 + g') _ 6 hc ?_
  have key : (1 - w ^ 3) ^ 6 * (g ^ 2 - ((648 * g' + 486 * g' ^ 2) + w * (486 * g' + 486 * g' ^ 2)
      + w ^ 2 * (81 - 162 * g' - 243 * g' ^ 2) + (270 * g' + 972 * g' ^ 2 + 729 * g' ^ 3) * g)) =
      ((1 - w ^ 3) ^ 3 * g) ^ 2
        - (648 * (1 - w ^ 3) ^ 5 * ((1 - w ^ 3) * g') + 486 * (1 - w ^ 3) ^ 4 * ((1 - w ^ 3) * g') ^ 2)
        - w * (486 * (1 - w ^ 3) ^ 5 * ((1 - w ^ 3) * g') + 486 * (1 - w ^ 3) ^ 4 * ((1 - w ^ 3) * g') ^ 2)
        - w ^ 2 * (81 * (1 - w ^ 3) ^ 6 - 162 * (1 - w ^ 3) ^ 5 * ((1 - w ^ 3) * g')
          - 243 * (1 - w ^ 3) ^ 4 * ((1 - w ^ 3) * g') ^ 2)
        - (270 * (1 - w ^ 3) ^ 2 * ((1 - w ^ 3) * g') + 972 * (1 - w ^ 3) * ((1 - w ^ 3) * g') ^ 2
          + 729 * ((1 - w ^ 3) * g') ^ 3) * ((1 - w ^ 3) ^ 3 * g) := by ring
  rw [key, e1, h2]
  ring

/-- The level 3 modular equation between `g = G(q)` and `g' = G(q³)`. -/
theorem ring_ME {R : Type*} [CommRing R] (w g g' : R) (h1 : (1 - w) ^ 3 * g = 9 * w * (1 + w + w ^ 2))
    (h2 : (1 - w ^ 3) * g' = w ^ 3) :
    g ^ 3 = 729 * g' + (270 * g' + 972 * g' ^ 2 + 729 * g' ^ 3) * g ^ 2 + (972 * g' + 729 * g' ^ 2) * g := by
  have hc : (1 - w ^ 3) * (1 + g') = 1 := by linear_combination h2
  have e1 : (1 - w ^ 3) ^ 3 * g = 9 * w * (1 + w + w ^ 2) ^ 4 := by
    linear_combination (1 + w + w ^ 2) ^ 3 * h1
  rw [← sub_eq_zero]
  refine eq_zero_of_pow_mul_eq_zero (1 - w ^ 3) (1 + g') _ 9 hc ?_
  have key : (1 - w ^ 3) ^ 9 * (g ^ 3 - (729 * g' + (270 * g' + 972 * g' ^ 2 + 729 * g' ^ 3) * g ^ 2
      + (972 * g' + 729 * g' ^ 2) * g)) =
      ((1 - w ^ 3) ^ 3 * g) ^ 3 - 729 * (1 - w ^ 3) ^ 8 * ((1 - w ^ 3) * g')
        - (270 * (1 - w ^ 3) ^ 2 * ((1 - w ^ 3) * g') + 972 * (1 - w ^ 3) * ((1 - w ^ 3) * g') ^ 2
          + 729 * ((1 - w ^ 3) * g') ^ 3) * ((1 - w ^ 3) ^ 3 * g) ^ 2
        - (972 * (1 - w ^ 3) ^ 5 * ((1 - w ^ 3) * g') + 729 * (1 - w ^ 3) ^ 4 * ((1 - w ^ 3) * g') ^ 2)
          * ((1 - w ^ 3) ^ 3 * g) := by ring
  rw [key, e1, h2]
  ring

theorem rowB_Ep {R : Type*} [CommRing R] (w gp u b tw tgp : R) (htw : tw = b * w)
    (htgp : tgp = 3 * u * gp) (hb : b * (1 + gp) = u) :
    1 * (-(3 * w ^ 2 * tw) * gp + (1 - w ^ 3) * tgp - 3 * w ^ 2 * tw) = 3 * u * ((1 - w ^ 3) * gp - w ^ 3) := by
  subst htw htgp
  linear_combination (-3 * w ^ 3) * hb

theorem row_ta {R : Type*} [CommRing R] (a g p p3 q q3 tp tp3 ta : R)
    (hp : 2 * a = 3 * p3 - p) (hta : 2 * ta = 3 * tp3 - tp) (h1 : 12 * tp = p ^ 2 - q) (h4 : 4 * tp3 = p3 ^ 2 - q3)
    (he1 : (1 + g) * q = a ^ 2 * (1 + 9 * g)) (he2 : 9 * (1 + g) * q3 = a ^ 2 * (9 + g)) :
    4 * (6 * (1 + g) * ta) = 4 * (a * ((1 + g) * p + (3 * g - 1) * a)) := by
  linear_combination 12 * (1 + g) * hta + 9 * (1 + g) * h4 - (1 + g) * h1 - he2 + he1
    - (1 + g) * (3 * p3 + p + 2 * a) * hp

theorem rowB_E {R : Type*} [CommRing R] (a u w g tw tg : R)
    (htw : tw = u * (1 - w ^ 3) * w) (htg : tg = a * g) :
    6 * (1 + g) * (1 + 2 * w) ^ 3 *
        (-(3 * (1 - w) ^ 2 * tw) * g + (1 - w) ^ 3 * tg - 9 * ((1 + 2 * w + 3 * w ^ 2) * tw)) =
      54 * (1 + g) * (1 + 2 * w) ^ 3 * w * (1 + w + w ^ 2) * (a - u * (1 + 2 * w) ^ 2)
      + 6 * (1 + g) * (1 + 2 * w) ^ 3 * (a - 3 * u * w * (1 + w + w ^ 2)) *
        ((1 - w) ^ 3 * g - 9 * w * (1 + w + w ^ 2)) := by
  subst htw htg
  ring

theorem rowB_K {R : Type*} [CommRing R] (a u w g p p3 p9 ta tu tw : R)
    (hp : p = 3 * p3 - 2 * a) (hp3 : p3 = 3 * p9 - 2 * u)
    (hta : 6 * (1 + g) * ta = a * ((1 + g) * p + (3 * g - 1) * a)) (htu : 2 * tu = u * (p3 + (4 * w ^ 3 - 1) * u))
    (htw : tw = u * (1 - w ^ 3) * w) :
    6 * (1 + g) * (1 + 2 * w) ^ 3 * (ta - tu * (1 + 2 * w) ^ 2 - 4 * u * (1 + 2 * w) * tw) =
      (1 + g) * (9 * p9 * (1 + 2 * w) ^ 3 + 3 * (32 * u * w ^ 5 + 32 * u * w ^ 4
        + (40 * u + 4 * (a - u * (1 + 2 * w) ^ 2)) * w ^ 3 + 16 * u * w ^ 2
        + (6 * (a - u * (1 + 2 * w) ^ 2) - 8 * u) * w - 4 * u - (a - u * (1 + 2 * w) ^ 2)))
        * (a - u * (1 + 2 * w) ^ 2)
      + 4 * a ^ 2 * ((1 - w) ^ 3 * g - 9 * w * (1 + w + w ^ 2)) := by
  subst hp hp3 htw
  linear_combination (1 + 2 * w) ^ 3 * hta - 3 * (1 + g) * (1 + 2 * w) ^ 5 * htu

end CalegariSlopes.Bridge.Level9
