/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.ADB.Hhat
public import CalegariSlopes.ADB.URec

@[expose] public section

/-!
# The box check of Lemma 5.3, for any table `T`

The computation in the proof of Lemma 5.3. Two Boolean checks on a table `T : ℕ → ℕ → ℕ` indexed by
`[0, 38]^2`: `recCheck T 38` (`T` satisfies the recurrence `u_rec` of `u`, verbatim, so `T = u` on the box) and
`boxRow T 38 I` for `I ≤ 38` (the coefficient of `x^I y^J` of `Hhat G`, computed from `T` over `ℤ`, vanishes). Together
with `Frac_Hhat_G` they give `Hhat G = 0`. The checks run in the kernel on the packed table of `UTab.lean`.
-/

open MvPowerSeries

namespace CalegariSlopes.ADB

/-- `allLe f n = f 0 && ... && f n`. -/
def allLe (f : ℕ → Bool) : ℕ → Bool
  | 0 => f 0
  | n + 1 => f (n + 1) && allLe f n

/-- The right side of `u_rec` for a table `T`, over `ℕ`. -/
def recRhs (T : ℕ → ℕ → ℕ) (i j : ℕ) : ℕ :=
  (if 1 = i ∧ 1 = j then 90 else 0) + (if 2 = i ∧ 1 = j then 324 else 0) +
  (if 1 = i ∧ 2 = j then 648 else 0) + (if 3 = i ∧ 1 = j then 243 else 0) +
  (if 2 = i ∧ 2 = j then 486 else 0) + (if 1 = i ∧ 3 = j then 729 else 0) +
  ((if 1 ≤ i ∧ 1 ≤ j then 270 * T (i - 1) (j - 1) else 0) +
  (if 2 ≤ i ∧ 1 ≤ j then 972 * T (i - 2) (j - 1) else 0) +
  (if 1 ≤ i ∧ 2 ≤ j then 972 * T (i - 1) (j - 2) else 0) +
  (if 3 ≤ i ∧ 1 ≤ j then 729 * T (i - 3) (j - 1) else 0) +
  (if 2 ≤ i ∧ 2 ≤ j then 729 * T (i - 2) (j - 2) else 0) +
  (if 1 ≤ i ∧ 3 ≤ j then 729 * T (i - 1) (j - 3) else 0))

/-- Row `i` of the recurrence check: `T i j = 0` on the axes, `T i j = recRhs T i j` elsewhere, `j ≤ n`. -/
def recRow (T : ℕ → ℕ → ℕ) (n i : ℕ) : Bool :=
  allLe (fun j => if i = 0 ∨ j = 0 then T i j == 0 else T i j == recRhs T i j) n

/-- The recurrence check on `[0, n]^2`. -/
def recCheck (T : ℕ → ℕ → ℕ) (n : ℕ) : Bool := allLe (recRow T n) n

/-- `m_a` over `ℤ`, products written out. -/
def mCZ (a : ℕ) (k : ℤ) : ℤ :=
  match a with
  | 0 => 9 * (k * k) * ((k + 1) * (k + 1)) * ((k + 2) * (k + 2))
  | 1 => 18 * k * ((k + 1) * (k + 1) * (k + 1)) * ((k + 2) * (k + 2))
  | _ => k * (k + 1) * ((k + 2) * (k + 2)) * (3 * k + 4) * (3 * k + 5)

/-- `n_a` over `ℤ`, products written out. -/
def nCZ (a : ℕ) (k : ℤ) : ℤ :=
  match a with
  | 0 => -81 * ((k + 1) * (k + 1)) * ((k + 2) * (k + 2))
  | 1 => -18 * k * ((k + 2) * (k + 2)) * (5 * k + 7)
  | _ => -k * (k + 1) * (3 * k + 4) * (3 * k + 5)

/-- The term `(a, b)` of the coefficient of `x^I y^J` in `Hhat G`, computed from the table `T` in place of `u`. -/
def boxTerm (T : ℕ → ℕ → ℕ) (I J a b : ℕ) : ℤ :=
  if 2 ≤ I + a ∧ 2 ≤ J + b then
    (mCZ a ((I : ℤ) - 2) * nCZ b ((J : ℤ) - 2) - nCZ a ((I : ℤ) - 2) * mCZ b ((J : ℤ) - 2)) *
      (((I + a - 2 : ℕ) : ℤ) * (T (I + a - 2) (J + b - 2) : ℤ))
  else 0

/-- The coefficient of `x^I y^J` in `Hhat G`, computed from `T`. -/
def boxAt (T : ℕ → ℕ → ℕ) (I J : ℕ) : ℤ :=
  boxTerm T I J 0 0 + boxTerm T I J 0 1 + boxTerm T I J 0 2 +
  boxTerm T I J 1 0 + boxTerm T I J 1 1 + boxTerm T I J 1 2 +
  boxTerm T I J 2 0 + boxTerm T I J 2 1 + boxTerm T I J 2 2

/-- Row `I` of the box check, `J ≤ n`. -/
def boxRow (T : ℕ → ℕ → ℕ) (n I : ℕ) : Bool := allLe (fun J => boxAt T I J == 0) n

theorem allLe_iff (f : ℕ → Bool) (n : ℕ) : allLe f n = true ↔ ∀ i ≤ n, f i = true := by
  induction n with
  | zero =>
    simp only [allLe, Nat.le_zero, forall_eq]
  | succ n ih =>
    simp only [allLe, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_or_ge i (n + 1) with h | h
      · exact h2 i (by omega)
      · rw [show i = n + 1 by omega]; exact h1
    · intro h; exact ⟨h _ le_rfl, fun i hi => h i (by omega)⟩

theorem mCZ_cast (a : ℕ) (k : ℤ) : ((mCZ a k : ℤ) : ℚ) = mC a (k : ℚ) := by
  rcases a with _ | _ | a <;> simp only [mCZ, mC] <;> push_cast <;> ring

theorem nCZ_cast (a : ℕ) (k : ℤ) : ((nCZ a k : ℤ) : ℚ) = nC a (k : ℚ) := by
  rcases a with _ | _ | a <;> simp only [nCZ, nC] <;> push_cast <;> ring

/-- The cast of `recRhs` is the right side of `u_rec` with `u` replaced by the cast of `T`. -/
theorem recRhs_cast (T : ℕ → ℕ → ℕ) (i j : ℕ) :
    ((recRhs T i j : ℕ) : ℚ) =
      (if 1 = i ∧ 1 = j then 90 else 0) + (if 2 = i ∧ 1 = j then 324 else 0) +
      (if 1 = i ∧ 2 = j then 648 else 0) + (if 3 = i ∧ 1 = j then 243 else 0) +
      (if 2 = i ∧ 2 = j then 486 else 0) + (if 1 = i ∧ 3 = j then 729 else 0) +
      ((if 1 ≤ i ∧ 1 ≤ j then 270 * (T (i - 1) (j - 1) : ℚ) else 0) +
      (if 2 ≤ i ∧ 1 ≤ j then 972 * (T (i - 2) (j - 1) : ℚ) else 0) +
      (if 1 ≤ i ∧ 2 ≤ j then 972 * (T (i - 1) (j - 2) : ℚ) else 0) +
      (if 3 ≤ i ∧ 1 ≤ j then 729 * (T (i - 3) (j - 1) : ℚ) else 0) +
      (if 2 ≤ i ∧ 2 ≤ j then 729 * (T (i - 2) (j - 2) : ℚ) else 0) +
      (if 1 ≤ i ∧ 3 ≤ j then 729 * (T (i - 1) (j - 3) : ℚ) else 0)) := by
  simp only [recRhs, Nat.cast_add, Nat.cast_ite, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero]

/-- A table that passes the recurrence check on `[0, n]^2` is `u` there. -/
theorem u_eq_of_recCheck (T : ℕ → ℕ → ℕ) (n : ℕ) (h : recCheck T n = true) :
    ∀ i j, i ≤ n → j ≤ n → u i j = T i j := by
  have hrow := (allLe_iff _ _).mp h
  have hent : ∀ i j, i ≤ n → j ≤ n →
      (if i = 0 ∨ j = 0 then T i j == 0 else T i j == recRhs T i j) = true :=
    fun i j hi hj => (allLe_iff _ _).mp (hrow i hi) j hj
  intro i j
  induction hs : i + j using Nat.strong_induction_on generalizing i j with
  | _ s ih =>
  intro hi hj
  have he := hent i j hi hj
  by_cases h0 : i = 0 ∨ j = 0
  · rw [if_pos h0, beq_iff_eq] at he
    rcases h0 with rfl | rfl
    · rw [u_zero_left, he, Nat.cast_zero]
    · rw [u_zero_right, he, Nat.cast_zero]
  · rw [if_neg h0, beq_iff_eq] at he
    have IH : ∀ a b, 1 ≤ a → 1 ≤ b → a ≤ i → b ≤ j → u (i - a) (j - b) = T (i - a) (j - b) :=
      fun a b ha hb hai hbj => ih (i - a + (j - b)) (by omega) (i - a) (j - b) rfl (by omega) (by omega)
    rw [u_rec, he, recRhs_cast]
    have t1 : (if 1 ≤ i ∧ 1 ≤ j then 270 * u (i - 1) (j - 1) else 0) =
        (if 1 ≤ i ∧ 1 ≤ j then 270 * (T (i - 1) (j - 1) : ℚ) else 0) := by
      split_ifs with hc
      · rw [IH 1 1 le_rfl le_rfl hc.1 hc.2]
      · rfl
    have t2 : (if 2 ≤ i ∧ 1 ≤ j then 972 * u (i - 2) (j - 1) else 0) =
        (if 2 ≤ i ∧ 1 ≤ j then 972 * (T (i - 2) (j - 1) : ℚ) else 0) := by
      split_ifs with hc
      · rw [IH 2 1 (by norm_num) le_rfl hc.1 hc.2]
      · rfl
    have t3 : (if 1 ≤ i ∧ 2 ≤ j then 972 * u (i - 1) (j - 2) else 0) =
        (if 1 ≤ i ∧ 2 ≤ j then 972 * (T (i - 1) (j - 2) : ℚ) else 0) := by
      split_ifs with hc
      · rw [IH 1 2 le_rfl (by norm_num) hc.1 hc.2]
      · rfl
    have t4 : (if 3 ≤ i ∧ 1 ≤ j then 729 * u (i - 3) (j - 1) else 0) =
        (if 3 ≤ i ∧ 1 ≤ j then 729 * (T (i - 3) (j - 1) : ℚ) else 0) := by
      split_ifs with hc
      · rw [IH 3 1 (by norm_num) le_rfl hc.1 hc.2]
      · rfl
    have t5 : (if 2 ≤ i ∧ 2 ≤ j then 729 * u (i - 2) (j - 2) else 0) =
        (if 2 ≤ i ∧ 2 ≤ j then 729 * (T (i - 2) (j - 2) : ℚ) else 0) := by
      split_ifs with hc
      · rw [IH 2 2 (by norm_num) (by norm_num) hc.1 hc.2]
      · rfl
    have t6 : (if 1 ≤ i ∧ 3 ≤ j then 729 * u (i - 1) (j - 3) else 0) =
        (if 1 ≤ i ∧ 3 ≤ j then 729 * (T (i - 1) (j - 3) : ℚ) else 0) := by
      split_ifs with hc
      · rw [IH 1 3 le_rfl (by norm_num) hc.1 hc.2]
      · rfl
    rw [t1, t2, t3, t4, t5, t6]

/-- With `T = u` on `[0, n]^2`, `boxAt T I J` is the coefficient of `x^I y^J` in `Hhat G` there. -/
theorem coeff_Hhat_G_eq_boxAt (T : ℕ → ℕ → ℕ) (n : ℕ)
    (hT : ∀ i j, i ≤ n → j ≤ n → u i j = T i j) (I J : ℕ) (hI : I ≤ n) (hJ : J ≤ n) :
    coeff (ex I J) (Hhat G) = ((boxAt T I J : ℤ) : ℚ) := by
  have key : ∀ a ∈ Finset.range 3, ∀ b ∈ Finset.range 3,
      (if 2 ≤ I + a ∧ 2 ≤ J + b then
        rShift a b (I + a - 2) (J + b - 2) * coeff (ex (I + a - 2) (J + b - 2)) G else 0) =
      ((boxTerm T I J a b : ℤ) : ℚ) := by
    intro a ha b hb
    have ha : a < 3 := Finset.mem_range.mp ha
    have hb : b < 3 := Finset.mem_range.mp hb
    unfold boxTerm
    split_ifs with hc
    · rw [coeff_G, S, hT _ _ (by omega) (by omega)]
      unfold rShift
      have e1 : ((I + a - 2 : ℕ) : ℚ) - a = (I : ℚ) - 2 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      have e2 : ((J + b - 2 : ℕ) : ℚ) - b = (J : ℚ) - 2 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [e1, e2]
      push_cast [mCZ_cast, nCZ_cast]
      ring
    · simp
  rw [coeff_Hhat, Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => key a ha b hb]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, boxAt]
  push_cast
  ring

/-- The two checks on `[0, 38]^2` give `Hhat G = 0`. -/
theorem Hhat_G_eq_zero_of_checks (T : ℕ → ℕ → ℕ) (hrec : recCheck T 38 = true)
    (hbox : ∀ I ≤ 38, boxRow T 38 I = true) : Hhat G = 0 := by
  refine eq_zero_of_Frac Frac_Hhat_G fun I J hI hJ => ?_
  rw [coeff_Hhat_G_eq_boxAt T 38 (u_eq_of_recCheck T 38 hrec) I J hI hJ]
  have h := (allLe_iff _ _).mp (hbox I hI) J hJ
  rw [beq_iff_eq] at h
  rw [h, Int.cast_zero]

end CalegariSlopes.ADB
