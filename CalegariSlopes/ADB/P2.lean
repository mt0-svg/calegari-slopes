/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.ADB.BoxCheck
public import CalegariSlopes.ADB.UTab

@[expose] public section

/-!
# Lemma 5.3: `(R S)(i, j) = 0` for all `i, j`

The proof of Lemma 5.3: `Hhat G ∈ Frac 12 38 38` (degree bound) and its coefficients vanish on
`[0, 38]^2` (box check), so `Hhat G = 0`, and its coefficient at `x^{i+2} y^{j+2}` is `(R S)(i, j)`. The table of
`UTab.lean` passes the recurrence of `u` (`rec_ok`) and the box check row by row (`box_row_I`), in the kernel
(`decide +kernel`, one declaration per row).
-/

namespace CalegariSlopes.ADB.Proof

open CalegariSlopes CalegariSlopes.ADB CalegariSlopes.ADB.Tab

/-- The table is `u` on `[0, 38]^2`: it satisfies the recurrence `u_rec` there. -/
theorem rec_ok : recCheck tab 38 = true := by decide +kernel

theorem box_row_0 : boxRow tab 38 0 = true := by decide +kernel

theorem box_row_1 : boxRow tab 38 1 = true := by decide +kernel

theorem box_row_2 : boxRow tab 38 2 = true := by decide +kernel

theorem box_row_3 : boxRow tab 38 3 = true := by decide +kernel

theorem box_row_4 : boxRow tab 38 4 = true := by decide +kernel

theorem box_row_5 : boxRow tab 38 5 = true := by decide +kernel

theorem box_row_6 : boxRow tab 38 6 = true := by decide +kernel

theorem box_row_7 : boxRow tab 38 7 = true := by decide +kernel

theorem box_row_8 : boxRow tab 38 8 = true := by decide +kernel

theorem box_row_9 : boxRow tab 38 9 = true := by decide +kernel

theorem box_row_10 : boxRow tab 38 10 = true := by decide +kernel

theorem box_row_11 : boxRow tab 38 11 = true := by decide +kernel

theorem box_row_12 : boxRow tab 38 12 = true := by decide +kernel

theorem box_row_13 : boxRow tab 38 13 = true := by decide +kernel

theorem box_row_14 : boxRow tab 38 14 = true := by decide +kernel

theorem box_row_15 : boxRow tab 38 15 = true := by decide +kernel

theorem box_row_16 : boxRow tab 38 16 = true := by decide +kernel

theorem box_row_17 : boxRow tab 38 17 = true := by decide +kernel

theorem box_row_18 : boxRow tab 38 18 = true := by decide +kernel

theorem box_row_19 : boxRow tab 38 19 = true := by decide +kernel

theorem box_row_20 : boxRow tab 38 20 = true := by decide +kernel

theorem box_row_21 : boxRow tab 38 21 = true := by decide +kernel

theorem box_row_22 : boxRow tab 38 22 = true := by decide +kernel

theorem box_row_23 : boxRow tab 38 23 = true := by decide +kernel

theorem box_row_24 : boxRow tab 38 24 = true := by decide +kernel

theorem box_row_25 : boxRow tab 38 25 = true := by decide +kernel

theorem box_row_26 : boxRow tab 38 26 = true := by decide +kernel

theorem box_row_27 : boxRow tab 38 27 = true := by decide +kernel

theorem box_row_28 : boxRow tab 38 28 = true := by decide +kernel

theorem box_row_29 : boxRow tab 38 29 = true := by decide +kernel

theorem box_row_30 : boxRow tab 38 30 = true := by decide +kernel

theorem box_row_31 : boxRow tab 38 31 = true := by decide +kernel

theorem box_row_32 : boxRow tab 38 32 = true := by decide +kernel

theorem box_row_33 : boxRow tab 38 33 = true := by decide +kernel

theorem box_row_34 : boxRow tab 38 34 = true := by decide +kernel

theorem box_row_35 : boxRow tab 38 35 = true := by decide +kernel

theorem box_row_36 : boxRow tab 38 36 = true := by decide +kernel

theorem box_row_37 : boxRow tab 38 37 = true := by decide +kernel

theorem box_row_38 : boxRow tab 38 38 = true := by decide +kernel

/-- The box check on `[0, 38]^2`. -/
theorem box_ok : ∀ I ≤ 38, boxRow tab 38 I = true := by
  intro I hI
  interval_cases I
  exacts [box_row_0, box_row_1, box_row_2, box_row_3, box_row_4, box_row_5, box_row_6, box_row_7,
    box_row_8, box_row_9, box_row_10, box_row_11, box_row_12, box_row_13, box_row_14, box_row_15,
    box_row_16, box_row_17, box_row_18, box_row_19, box_row_20, box_row_21, box_row_22, box_row_23,
    box_row_24, box_row_25, box_row_26, box_row_27, box_row_28, box_row_29, box_row_30, box_row_31,
    box_row_32, box_row_33, box_row_34, box_row_35, box_row_36, box_row_37, box_row_38]

/-- The generating series of `R S` vanishes. -/
theorem Hhat_G_eq_zero : Hhat G = 0 := Hhat_G_eq_zero_of_checks tab rec_ok box_ok

/-- Lemma 5.3: `R` kills `S_ij = i u_ij`. -/
theorem RS_zero (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) : R S i j = 0 := by
  rw [← coeff_Hhat_G, Hhat_G_eq_zero, map_zero]

end CalegariSlopes.ADB.Proof
