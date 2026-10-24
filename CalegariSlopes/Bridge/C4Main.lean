/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Bridge.Level9
public import CalegariSlopes.Bridge.C4Col

@[expose] public section

/-!
# Theorem 2.1 (b) for `G = Sol a2 27`

The proof of Theorem 2.1 (b) in Section 4.4: the identities `ring_L1`, `ring_L2`, `ring_ME` of Lemma 4.6 at
`(w, g, g') = (W, G, V₃ G)` (Theorem 4.5 (b), (c)) write `G`, `G²`, `G³` as `V₃(·) + W V₃(·) + W² V₃(·)` plus
`V₃(·)`-multiples of lower powers of `G`; `U₃` of them (`U3Q_V3_mul`, `U3Q_one`, and Theorem 4.5 (a) for
`U₃ W = U₃ W² = 0`) is the recurrence `IsColRec` of `T_j = U₃ (G ʲ)`, which `S_j = Σ_{1 ≤ i ≤ 3j} u_ij G ⁱ`
satisfies too (`isColRec_S`, Lemma 4.7); uniqueness gives Theorem 2.1 (b).
-/

open PowerSeries
open CalegariSlopes.Spectral (U3Q)

namespace CalegariSlopes.Bridge.Level9

/-- `T_j = U₃ (G ʲ)` satisfies the recurrence of the columns of `u` at `x = G` (Section 4.4). -/
theorem isColRec_T : IsColRec (Sol a2 27) (fun j => if j = 0 then 0 else U3Q (Sol a2 27 ^ j)) := by
  set G := Sol a2 27 with hG
  have h1 : (1 - W) ^ 3 * G = 9 * W * (1 + W + W ^ 2) := I1
  have h2 : (1 - W ^ 3) * V3 G = W ^ 3 := I2
  obtain ⟨hW1, hW2⟩ := U3Q_of_mod_one W I3
  have L1 := ring_L1 W G (V3 G) h1 h2
  have L2 := ring_L2 W G (V3 G) h1 h2
  have ME := ring_ME W G (V3 G) h1 h2
  have hV : ∀ x : ℚ⟦X⟧, U3Q (V3 x) = x := fun x => by
    rw [← mul_one (V3 x), U3Q_V3_mul, U3Q_one, mul_one]
  have key : ∀ x y z : ℚ⟦X⟧, U3Q (V3 x + W * V3 y + W ^ 2 * V3 z) = x := by
    intro x y z
    rw [U3Q_add, U3Q_add, hV, mul_comm W, mul_comm (W ^ 2), U3Q_V3_mul, U3Q_V3_mul, hW1, hW2]
    ring
  -- the level 3 modular equation, multiplied by `G ^ k`
  have hME : ∀ k : ℕ, U3Q (G ^ (k + 3)) = 729 * G * U3Q (G ^ k)
      + (270 * G + 972 * G ^ 2 + 729 * G ^ 3) * U3Q (G ^ (k + 2)) + (972 * G + 729 * G ^ 2) * U3Q (G ^ (k + 1)) := by
    intro k
    have e : G ^ (k + 3) = V3 (729 * G) * G ^ k + V3 (270 * G + 972 * G ^ 2 + 729 * G ^ 3) * G ^ (k + 2)
        + V3 (972 * G + 729 * G ^ 2) * G ^ (k + 1) := by
      simp only [map_add, map_mul, map_pow, map_ofNat]
      linear_combination G ^ k * ME
    rw [e, U3Q_add, U3Q_add, U3Q_V3_mul, U3Q_V3_mul, U3Q_V3_mul]
  refine ⟨by simp, fun j hj => ?_⟩
  obtain _ | _ | _ | _ | j := j
  · omega
  · -- j = 1
    have e : G ^ 1 = V3 (90 * G + 324 * G ^ 2 + 243 * G ^ 3) + W * V3 (9 + 171 * G + 405 * G ^ 2 + 243 * G ^ 3)
        + W ^ 2 * V3 (36 + 279 * G + 486 * G ^ 2 + 243 * G ^ 3) := by
      simp only [map_add, map_mul, map_pow, map_ofNat]
      linear_combination L1
    simp only [fnRec, Nat.reduceAdd, Nat.one_ne_zero, ↓reduceIte, Nat.sub_self, Nat.reduceSub, mul_zero,
      add_zero]
    rw [e, key]
  · -- j = 2
    have e : G ^ 2 = V3 (648 * G + 486 * G ^ 2) + W * V3 (486 * G + 486 * G ^ 2)
        + W ^ 2 * V3 (81 - 162 * G - 243 * G ^ 2) + V3 (270 * G + 972 * G ^ 2 + 729 * G ^ 3) * G := by
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
      linear_combination L2
    simp only [fnRec, Nat.reduceAdd, OfNat.ofNat_ne_zero, ↓reduceIte, Nat.reduceSub, OfNat.ofNat_ne_one,
      Nat.one_ne_zero, mul_zero, add_zero, pow_one]
    conv_lhs => rw [e, U3Q_add, key, U3Q_V3_mul]
  · -- j = 3
    have h := hME 0
    simp only [zero_add, pow_zero, U3Q_one, mul_one, pow_one] at h
    simp only [fnRec, Nat.reduceAdd, OfNat.ofNat_ne_zero, ↓reduceIte, Nat.reduceSub, OfNat.ofNat_ne_one,
      Nat.one_ne_zero, mul_zero, add_zero, pow_one, Nat.sub_self, show (3 : ℕ) ≠ 2 by decide]
    linear_combination h
  · -- j ≥ 4
    have h := hME (j + 1)
    simp only [fnRec, show j + 1 + 1 + 1 + 1 ≠ 0 by omega, show j + 1 + 1 + 1 + 1 ≠ 1 by omega,
      show j + 1 + 1 + 1 + 1 ≠ 2 by omega, show j + 1 + 1 + 1 + 1 ≠ 3 by omega, ↓reduceIte,
      show j + 1 + 1 + 1 + 1 - 1 = j + 3 by omega, show j + 1 + 1 + 1 + 1 - 2 = j + 2 by omega,
      show j + 1 + 1 + 1 + 1 - 3 = j + 1 by omega, show j + 3 ≠ 0 by omega, show j + 2 ≠ 0 by omega,
      show j + 1 ≠ 0 by omega, zero_add]
    rw [show j + 1 + 1 + 1 + 1 = j + 1 + 3 by omega, h]
    ring

end CalegariSlopes.Bridge.Level9

namespace CalegariSlopes.Bridge

open Level9 in
/-- **Theorem 2.1 (b)** for `G = Sol a2 27`: `U₃ (G ʲ) = Σ_{1 ≤ i ≤ 3j} u_ij G ⁱ` in `ℚ⟦q⟧` for every `j ≥ 1`. -/
theorem c4_Sol : Spectral.C4 (Sol a2 27) := by
  intro j hj
  have h := congrFun (isColRec_T.unique (isColRec_S (Sol a2 27))) j
  simp only [show j ≠ 0 by omega, ↓reduceIte] at h
  exact h

end CalegariSlopes.Bridge
