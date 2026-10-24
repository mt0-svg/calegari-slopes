/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Bridge.C4Defs
public import CalegariSlopes.Bridge.JBasic

@[expose] public section

/-!
# `U₃` on `ℚ⟦q⟧` and Lemma 4.3

The rules of `U₃` used in the proof of Theorem 2.1 (b) (Section 4.4), and the second part of Lemma 4.3
(`Sol (V₃ b₀) c` has only exponents `≡ 1 (mod 3)`).
-/

open PowerSeries
open CalegariSlopes.Spectral (U3Q)

namespace CalegariSlopes.Bridge.Level9

theorem U3Q_add (f g : ℚ⟦X⟧) : U3Q (f + g) = U3Q f + U3Q g := by
  ext n
  simp [CalegariSlopes.Spectral.U3Q]

theorem U3Q_V3_mul (h F : ℚ⟦X⟧) : U3Q (V3 h * F) = h * U3Q F := by
  ext n
  simp [U3Q, V3, PowerSeries.coeff_mul, PowerSeries.coeff_mk, PowerSeries.coeff_expand]
  simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [← Finset.sum_filter]
  apply Finset.sum_nbij' (fun k => k / 3) (fun i => 3 * i)
  · -- h₁: if k ∈ filtered set, then k/3 ∈ range(n+1)
    intro k hk
    rw [Finset.mem_filter] at hk
    rcases hk with ⟨hk_range, hk_div⟩
    rw [Finset.mem_range]
    rcases hk_div with ⟨i, hi⟩
    have : k < 3 * n + 1 := Finset.mem_range.mp hk_range
    rw [hi] at this
    omega
  · -- h₂: if i ∈ range(n+1), then 3*i ∈ filtered set
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Finset.mem_filter, Finset.mem_range]
    constructor
    · omega
    · exact ⟨i, by ring⟩
  · -- h₃: (3*(k/3)) = k when 3∣k
    intro k hk
    rw [Finset.mem_filter] at hk
    rcases hk with ⟨hk_range, hk_div⟩
    rcases hk_div with ⟨i, hi⟩
    rw [hi]
    simp
  · -- h₄: (3*i)/3 = i
    intro i hi
    simp
  · -- h₅: summands match: coeff (k/3) h * coeff (3n - k) F = coeff (k/3) h * coeff (3*(n - k/3)) F
    intro k hk
    rw [Finset.mem_filter] at hk
    rcases hk with ⟨hk_range, hk_div⟩
    rcases hk_div with ⟨i, hi⟩
    rw [hi]
    simp [Nat.mul_sub_left_distrib]

theorem U3Q_one : U3Q 1 = 1 := by
  ext n
  simp [CalegariSlopes.Spectral.U3Q, coeff_one]

theorem U3Q_of_mod_one (w : ℚ⟦X⟧) (hw : ∀ n : ℕ, n % 3 ≠ 1 → coeff n w = 0) :
    U3Q w = 0 ∧ U3Q (w ^ 2) = 0 := by
  have hmod3 : ∀ n : ℕ, (3 * n) % 3 = 0 := by
    intro n
    simp
  constructor
  · -- U3Q w = 0
    ext n
    unfold U3Q
    rw [PowerSeries.coeff_mk]
    simp [hw (3 * n) (by
      rw [hmod3 n]
      decide)]
  · -- U3Q (w ^ 2) = 0
    ext n
    unfold U3Q
    rw [PowerSeries.coeff_mk, sq, PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    have hp_sum : p.1 + p.2 = 3 * n := by
      simpa using hp
    by_cases ha : p.1 % 3 = 1
    · by_cases hb : p.2 % 3 = 1
      · -- both are 1 mod 3, impossible since sum would be 2 mod 3
        have hsum_mod : (p.1 + p.2) % 3 = 2 := by
          rw [Nat.add_mod, ha, hb]
        rw [hp_sum] at hsum_mod
        have : (3 * n) % 3 = 0 := hmod3 n
        rw [this] at hsum_mod
        norm_num at hsum_mod
      · -- b not 1 mod 3, so coeff p.2 w = 0
        rw [hw p.2 hb, mul_zero]
    · -- a not 1 mod 3, so coeff p.1 w = 0
      rw [hw p.1 ha, zero_mul]

theorem coeff_Sol_V3 (b0 : ℚ⟦X⟧) (c : ℚ) (n : ℕ) (hn : n % 3 ≠ 1) :
    coeff n (Sol (V3 b0) c) = 0 := by
  revert hn
  refine Nat.strong_induction_on n ?_
  intro m ih hm
  match m with
  | 0 => exact coeff_Sol_zero (V3 b0) c
  | 1 =>
    have : 1 % 3 = 1 := by norm_num
    exact absurd this hm
  | m+2 =>
    rw [coeff_Sol_add_two (V3 b0) c m]
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hdiv : 3 ∣ (k : ℕ) + 1
    · have h_lt : m + 1 - (k : ℕ) < m + 2 := by
        have hk_le : (k : ℕ) ≤ m := by
          have := k.2
          omega
        omega
      have h_mod : (m + 1 - (k : ℕ)) % 3 ≠ 1 := by
        omega
      rw [ih (m + 1 - (k : ℕ)) h_lt h_mod, mul_zero]
    · have hcoeff : coeff ((k : ℕ) + 1) (V3 b0) = 0 := by
        rw [V3, coeff_expand_of_not_dvd (p := 3) (hp := three_ne_zero) (h := hdiv)]
      rw [hcoeff, zero_mul]

end CalegariSlopes.Bridge.Level9
