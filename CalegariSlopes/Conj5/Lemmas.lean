/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Newton.Proofs

@[expose] public section

/-!
# Section 8 of the paper: the lemmas on the entries of `A` and `B`

* Lemma 3.2 as valuations: `padicValRat_B_ge`, `padicValRat_A_ge` (from
  `CalegariSlopes.Newton.padicNorm_B_div_le`).
* Lemma 8.1 (b) and (c): the first superdiagonal `B_succ`, the first subdiagonal `A_succ`, their
  valuations `padicValRat_B_succ`, `padicValRat_A_succ`; the witnesses `B_24`, `A_42` and their
  valuations.
* The uniqueness of an LDU factorization with unit triangular outer factors (`ldu_unique`), for Lemma 8.1 (a).
-/

namespace CalegariSlopes.Conj5

open CalegariSlopes CalegariSlopes.ADB

/-! ## Lemma 3.2 as valuations -/

/-- `v_3(B_pk) ≥ k - p` for `1 ≤ p < k` and `B_pk ≠ 0`. -/
theorem padicValRat_B_ge (p k : ℕ) (hp : 1 ≤ p) (h : p < k) (hB : B p k ≠ 0) :
    (k : ℤ) - p ≤ padicValRat 3 (B p k) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hk_pos : k ≠ 0 := by linarith
  have hk0 : (k : ℚ) ≠ 0 := by
    intro hzero
    apply hk_pos
    exact_mod_cast hzero
  have hdiv0 : B p k / (k : ℚ) ≠ 0 := div_ne_zero hB hk0
  have hle := CalegariSlopes.Newton.padicNorm_B_div_le p k hp h
  have hnorm_eq : padicNorm 3 (B p k / (k : ℚ)) = (3 : ℚ) ^ (-padicValRat 3 (B p k / (k : ℚ))) :=
    padicNorm.eq_zpow_of_nonzero hdiv0
  rw [hnorm_eq] at hle
  have hone : 1 < (3 : ℚ) := by norm_num
  have h_exp_ineq : -padicValRat 3 (B p k / (k : ℚ)) ≤ -((k : ℤ) - p) :=
    ((zpow_le_zpow_iff_right₀ hone).mp hle)
  have h_exp_ineq2 : (k : ℤ) - p ≤ padicValRat 3 (B p k / (k : ℚ)) := by linarith
  have hval_div : padicValRat 3 (B p k / (k : ℚ)) = padicValRat 3 (B p k) - padicValRat 3 (k : ℚ) :=
    padicValRat.div hB hk0
  rw [hval_div] at h_exp_ineq2
  have hval_k_nonneg : 0 ≤ padicValRat 3 (k : ℚ) := by
    rw [padicValRat.of_nat]
    exact Nat.cast_nonneg _
  linarith

/-- `v_3(A_ip) ≥ i - p` for `1 ≤ p < i` and `A_ip ≠ 0`. -/
theorem padicValRat_A_ge (i p : ℕ) (hp : 1 ≤ p) (h : p < i) (hA : A i p ≠ 0) :
    (i : ℤ) - p ≤ padicValRat 3 (A i p) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  -- rewrite A i p = (p : ℚ) * (B p i / (i : ℚ))
  have hA_eq : A i p = (p : ℚ) * (B p i / (i : ℚ)) := by
    dsimp [A]
    ring
  rw [hA_eq]
  have hp_ne_zero : (p : ℚ) ≠ 0 := by
    intro hzero
    have : (p : ℕ) = 0 := by exact_mod_cast hzero
    linarith
  have hi_ne_zero : (i : ℚ) ≠ 0 := by
    intro hzero
    have : (i : ℕ) = 0 := by exact_mod_cast hzero
    linarith
  have hB_ne_zero : B p i ≠ 0 := by
    intro hzero
    apply hA
    rw [hA_eq, hzero]
    simp
  have h_div_ne_zero : B p i / (i : ℚ) ≠ 0 :=
    div_ne_zero hB_ne_zero hi_ne_zero
  rw [padicValRat.mul hp_ne_zero h_div_ne_zero]
  have hp_val_nonneg : 0 ≤ padicValRat 3 (p : ℚ) := by
    rw [padicValRat.of_nat]
    exact Nat.cast_nonneg _
  have h_bound : padicNorm 3 (B p i / (i : ℚ)) ≤ (3 : ℚ) ^ (-((i : ℤ) - p)) :=
    Newton.padicNorm_B_div_le p i hp h
  have h_norm_eq : padicNorm 3 (B p i / (i : ℚ)) = (3 : ℚ) ^ (-padicValRat 3 (B p i / (i : ℚ))) :=
    padicNorm.eq_zpow_of_nonzero h_div_ne_zero
  rw [h_norm_eq] at h_bound
  have h_three_gt_one : 1 < (3 : ℚ) := by norm_num
  have h_exp_le : -padicValRat 3 (B p i / (i : ℚ)) ≤ -((i : ℤ) - p) :=
    ((zpow_le_zpow_iff_right₀ h_three_gt_one).mp h_bound)
  have h_val_ge : (i : ℤ) - p ≤ padicValRat 3 (B p i / (i : ℚ)) := by
    linarith
  linarith

/-! ## Lemma 8.1 (b) and (c): the first super- and subdiagonal -/

/-- `μ(m + 1, m + 2, 1) = 4 (m + 1)(m + 2)^2`. -/
theorem mu_succ (m : ℕ) : mu (m + 1) (m + 2) 1 = 4 * ((m : ℚ) + 1) * ((m : ℚ) + 2) ^ 2 := by
  unfold mu
  rw [ite_eq_left (by omega)]
  rw [show 2 * (m + 1) + 1 - 1 = 2 * m + 2 by omega, show m + 1 + 2 * 1 - (m + 2) = 1 by omega,
    show m + 2 - (m + 1) - 1 = 0 by omega, show m + 1 - 1 = m by omega,
    show m + 1 + (m + 2) = 2 * m + 3 by omega, show 2 * (m + 1) + 2 * 1 = 2 * m + 4 by omega,
    show 2 * (m + 1) = 2 * m + 2 by omega, show m + 1 + 1 = m + 2 by omega]
  rw [show 2 * m + 4 = (2 * m + 3) + 1 by omega, Nat.factorial_succ (2 * m + 3),
    show m + 2 = (m + 1) + 1 by omega, Nat.factorial_succ (m + 1), Nat.factorial_succ m]
  have h1 : ((2 * m + 3).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : ((2 * m + 2).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h3 : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  push_cast
  field_simp
  ring

/-- `r_1(m + 1) = (3m + 4)(3m + 5)`. -/
theorem r_one (m : ℕ) : r 1 (m + 1) = (3 * (m : ℚ) + 4) * (3 * (m : ℚ) + 5) := by
  unfold r
  rw [show 3 * (m + 1) + 3 * 1 = (3 * m + 5) + 1 by omega, Nat.factorial_succ (3 * m + 5),
    show 3 * m + 5 = (3 * m + 4) + 1 by omega, Nat.factorial_succ (3 * m + 4),
    show 3 * m + 4 = (3 * m + 3) + 1 by omega, Nat.factorial_succ (3 * m + 3),
    show 3 * (m + 1) = 3 * m + 3 by omega, show m + 1 + 1 = (m + 1) + 1 by omega,
    Nat.factorial_succ (m + 1)]
  have h1 : ((3 * m + 3).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h3 : ((m + 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  push_cast
  field_simp
  ring

/-- `B_{i,i+1} = 36 i (i + 1)^2 / ((3i + 1)(3i + 2))`. -/
theorem B_succ (i : ℕ) (hi : 1 ≤ i) :
    B i (i + 1) = 36 * (i : ℚ) * ((i : ℚ) + 1) ^ 2 / ((3 * (i : ℚ) + 1) * (3 * (i : ℚ) + 2)) := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  unfold B
  rw [Finset.sum_eq_single 1]
  · rw [show m + 1 + 1 = m + 2 by omega, mu_succ, r_one]
    push_cast
    have : (3 * (m : ℚ) + 4) ≠ 0 := by positivity
    have : (3 * (m : ℚ) + 5) ≠ 0 := by positivity
    field_simp
    ring
  · intro t _ ht
    unfold mu
    rw [ite_eq_right (by omega)]
    simp
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- `A_{i+1,i} = 36 i^2 (i + 1) / ((3i + 1)(3i + 2))`. -/
theorem A_succ (i : ℕ) (hi : 1 ≤ i) :
    A (i + 1) i = 36 * (i : ℚ) ^ 2 * ((i : ℚ) + 1) / ((3 * (i : ℚ) + 1) * (3 * (i : ℚ) + 2)) := by
  dsimp [A]
  rw [B_succ i hi]
  push_cast
  field_simp [show (i : ℚ) + 1 ≠ 0 from by positivity, show 3 * (i : ℚ) + 1 ≠ 0 from by positivity,
    show 3 * (i : ℚ) + 2 ≠ 0 from by positivity]

/-- `v_3(A_{i+1,i}) = 2 + 2 v_3(i) + v_3(i + 1)`. -/
theorem padicValRat_A_succ (i : ℕ) (hi : 1 ≤ i) :
    padicValRat 3 (A (i + 1) i) = 2 + 2 * (padicValNat 3 i : ℤ) + (padicValNat 3 (i + 1) : ℤ) := by
  have hA := A_succ i hi
  rw [hA]
  have h36 : (36 : ℚ) = (3 : ℚ) ^ 2 * (4 : ℚ) := by norm_num
  rw [h36]
  have hnum_ne_zero : ((3 : ℚ) ^ 2 * (4 : ℚ) * ((i : ℚ) ^ 2) * ((i : ℚ) + 1)) ≠ 0 := by
    positivity
  have hden_ne_zero : (((3 : ℚ) * (i : ℚ) + 1) * ((3 : ℚ) * (i : ℚ) + 2)) ≠ 0 := by
    positivity
  rw [padicValRat.div hnum_ne_zero hden_ne_zero]
  have hnum : padicValRat 3 ((3 : ℚ) ^ 2 * (4 : ℚ) * ((i : ℚ) ^ 2) * ((i : ℚ) + 1)) =
      2 + 2 * (padicValNat 3 i : ℤ) + (padicValNat 3 (i + 1) : ℤ) := by
    have h3sq : padicValRat 3 ((3 : ℚ) ^ 2) = (2 : ℤ) := by
      have h3 : padicValRat 3 (3 : ℚ) = (1 : ℤ) := by
        simpa using padicValRat.of_nat (p := 3) (n := 3)
      have h := padicValRat.pow (p := 3) (q := (3 : ℚ)) (k := 2)
      rw [h, h3]; norm_num
    have h4 : padicValRat 3 (4 : ℚ) = (0 : ℤ) := by
      have h_val : padicValNat 3 4 = 0 := by
        have h_not_dvd : ¬ (3 : ℕ) ∣ (4 : ℕ) := by omega
        have h_ne_zero : (4 : ℕ) ≠ 0 := by omega
        have h_iff := (dvd_iff_padicValNat_ne_zero (p := 3) (n := 4)) h_ne_zero
        have h := mt h_iff.mpr h_not_dvd
        exact not_ne_iff.mp h
      simpa [h_val] using padicValRat.of_nat (p := 3) (n := 4)
    have hi_sq : padicValRat 3 ((i : ℚ) ^ 2) = (2 : ℤ) * (padicValNat 3 i : ℤ) := by
      have h := padicValRat.pow (p := 3) (q := (i : ℚ)) (k := 2)
      have h_of_nat : padicValRat 3 (i : ℚ) = (padicValNat 3 i : ℤ) := by
        simp
      simp [h_of_nat]
    have hi_plus_one : padicValRat 3 ((i : ℚ) + 1) = (padicValNat 3 (i + 1) : ℤ) := by
      have : (i : ℚ) + 1 = ((i + 1 : ℕ) : ℚ) := by
        push_cast
        ring
      rw [this]
      simpa using padicValRat.of_nat (p := 3) (n := i + 1)
    have h_mul1 : padicValRat 3 (((3 : ℚ) ^ 2 * (4 : ℚ) * ((i : ℚ) ^ 2)) * ((i : ℚ) + 1)) =
        padicValRat 3 ((3 : ℚ) ^ 2 * (4 : ℚ) * ((i : ℚ) ^ 2)) + padicValRat 3 ((i : ℚ) + 1) := by
      rw [padicValRat.mul (by positivity) (by positivity)]
    have h_mul2 : padicValRat 3 (((3 : ℚ) ^ 2 * (4 : ℚ)) * ((i : ℚ) ^ 2)) =
        padicValRat 3 ((3 : ℚ) ^ 2 * (4 : ℚ)) + padicValRat 3 ((i : ℚ) ^ 2) := by
      rw [padicValRat.mul (by positivity) (by positivity)]
    have h_mul3 : padicValRat 3 ((3 : ℚ) ^ 2 * (4 : ℚ)) =
        padicValRat 3 ((3 : ℚ) ^ 2) + padicValRat 3 (4 : ℚ) := by
      rw [padicValRat.mul (by norm_num) (by norm_num)]
    calc
      padicValRat 3 ((3 : ℚ) ^ 2 * (4 : ℚ) * ((i : ℚ) ^ 2) * ((i : ℚ) + 1)) =
          padicValRat 3 (((3 : ℚ) ^ 2 * (4 : ℚ) * ((i : ℚ) ^ 2)) * ((i : ℚ) + 1)) := by ring
      _ = padicValRat 3 ((3 : ℚ) ^ 2 * (4 : ℚ) * ((i : ℚ) ^ 2)) + padicValRat 3 ((i : ℚ) + 1) := by rw [h_mul1]
      _ = padicValRat 3 (((3 : ℚ) ^ 2 * (4 : ℚ)) * ((i : ℚ) ^ 2)) + padicValRat 3 ((i : ℚ) + 1) := by ring
      _ = (padicValRat 3 ((3 : ℚ) ^ 2 * (4 : ℚ)) + padicValRat 3 ((i : ℚ) ^ 2)) + padicValRat 3 ((i : ℚ) + 1) := by rw [h_mul2]
      _ = ((padicValRat 3 ((3 : ℚ) ^ 2) + padicValRat 3 (4 : ℚ)) + padicValRat 3 ((i : ℚ) ^ 2)) + padicValRat 3 ((i : ℚ) + 1) := by rw [h_mul3]
      _ = ((2 : ℤ) + (0 : ℤ) + (2 : ℤ) * (padicValNat 3 i : ℤ)) + (padicValNat 3 (i + 1) : ℤ) := by rw [h3sq, h4, hi_sq, hi_plus_one]
      _ = 2 + 2 * (padicValNat 3 i : ℤ) + (padicValNat 3 (i + 1) : ℤ) := by ring
  have hden : padicValRat 3 (((3 : ℚ) * (i : ℚ) + 1) * ((3 : ℚ) * (i : ℚ) + 2)) = (0 : ℤ) := by
    have h1 : padicValRat 3 ((3 : ℚ) * (i : ℚ) + 1) = (0 : ℤ) := by
      have : (3 : ℚ) * (i : ℚ) + 1 = ((3 * i + 1 : ℕ) : ℚ) := by
        push_cast
        ring
      rw [this]
      have h_not_dvd : ¬ (3 : ℕ) ∣ (3 * i + 1 : ℕ) := by
        omega
      have h_ne_zero : (3 * i + 1 : ℕ) ≠ 0 := by omega
      have h_iff := (dvd_iff_padicValNat_ne_zero (p := 3) (n := 3 * i + 1)) h_ne_zero
      have h_val : padicValNat 3 (3 * i + 1) = 0 := by
        have h := mt h_iff.mpr h_not_dvd
        exact not_ne_iff.mp h
      simpa [h_val] using padicValRat.of_nat (p := 3) (n := 3 * i + 1)
    have h2 : padicValRat 3 ((3 : ℚ) * (i : ℚ) + 2) = (0 : ℤ) := by
      have : (3 : ℚ) * (i : ℚ) + 2 = ((3 * i + 2 : ℕ) : ℚ) := by
        push_cast
        ring
      rw [this]
      have h_not_dvd : ¬ (3 : ℕ) ∣ (3 * i + 2 : ℕ) := by
        omega
      have h_ne_zero : (3 * i + 2 : ℕ) ≠ 0 := by omega
      have h_iff := (dvd_iff_padicValNat_ne_zero (p := 3) (n := 3 * i + 2)) h_ne_zero
      have h_val : padicValNat 3 (3 * i + 2) = 0 := by
        have h := mt h_iff.mpr h_not_dvd
        exact not_ne_iff.mp h
      simpa [h_val] using padicValRat.of_nat (p := 3) (n := 3 * i + 2)
    rw [padicValRat.mul (by positivity) (by positivity), h1, h2, add_zero]
  rw [hnum, hden, sub_zero]

/-- `v_3(B_{i,i+1}) = 2 + v_3(i) + 2 v_3(i + 1)`, from `B_{i,i+1} = ((i + 1)/i) A_{i+1,i}`. -/
theorem padicValRat_B_succ (i : ℕ) (hi : 1 ≤ i) :
    padicValRat 3 (B i (i + 1)) = 2 + (padicValNat 3 i : ℤ) + 2 * (padicValNat 3 (i + 1) : ℤ) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hi0 : (i : ℚ) ≠ 0 := by exact_mod_cast (show i ≠ 0 by omega)
  have hi1 : (i : ℚ) + 1 ≠ 0 := by positivity
  have hB : B i (i + 1) = ((i : ℚ) + 1) / i * A (i + 1) i := by
    rw [A]
    push_cast
    field_simp
  have hA0 : A (i + 1) i ≠ 0 := by
    rw [A_succ i hi]
    have : (0 : ℚ) < i := by exact_mod_cast (show 0 < i by omega)
    positivity
  rw [hB, padicValRat.mul (div_ne_zero hi1 hi0) hA0, padicValRat.div hi1 hi0, padicValRat_A_succ i hi,
    show (i : ℚ) + 1 = ((i + 1 : ℕ) : ℚ) by push_cast; ring, padicValRat.of_nat, padicValRat.of_nat]
  ring

/-! ## The witnesses -/

theorem B_24 : B 2 4 = 3060 / 77 := by
  simp only [CalegariSlopes.ADB.B, CalegariSlopes.ADB.mu, CalegariSlopes.ADB.r, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

theorem A_42 : A 4 2 = 1530 / 77 := by
  rw [CalegariSlopes.ADB.A, B_24]
  norm_num

theorem padicValRat_B_24 : padicValRat 3 (B 2 4) = 2 := by
  rw [CalegariSlopes.Conj5.B_24]
  have h3060 : (3060 : ℚ) ≠ 0 := by norm_num
  have h77 : (77 : ℚ) ≠ 0 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [padicValRat.div h3060 h77]
  have h3060_val : padicValRat 3 (3060 : ℚ) = (padicValNat 3 3060 : ℤ) := padicValRat.of_nat
  have h77_val : padicValRat 3 (77 : ℚ) = (padicValNat 3 77 : ℤ) := padicValRat.of_nat
  rw [h3060_val, h77_val]
  have h3060_padic : padicValNat 3 3060 = 2 := by
    have h3060_eq : (3060 : ℕ) = 3 ^ 2 * 340 := by norm_num
    rw [h3060_eq]
    have h9 : (3 ^ 2 : ℕ) ≠ 0 := by norm_num
    have h340 : (340 : ℕ) ≠ 0 := by norm_num
    rw [padicValNat.mul h9 h340, padicValNat.prime_pow 2,
      padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ (3 : ℕ) ∣ 340)]
  have h77_padic : padicValNat 3 77 = 0 :=
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ (3 : ℕ) ∣ 77)
  rw [h3060_padic, h77_padic]
  simp

theorem padicValRat_A_42 : padicValRat 3 (A 4 2) = 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA42 : A 4 2 = (1530 : ℚ) / (77 : ℚ) := by
    simpa [A] using congrArg (fun x : ℚ => x) (A_42)
  rw [hA42]
  rw [padicValRat.div (by norm_num) (by norm_num)]
  have h1530' : padicValRat 3 (1530 : ℚ) = (padicValNat 3 1530 : ℤ) := by
    simpa using padicValRat.of_nat (p := 3) (n := 1530)
  have h77' : padicValRat 3 (77 : ℚ) = (padicValNat 3 77 : ℤ) := by
    simpa using padicValRat.of_nat (p := 3) (n := 77)
  rw [h1530', h77']
  have h1530 : padicValNat 3 1530 = 2 := by
    have h1530_eq : 1530 = (3:ℕ)^2 * 170 := by norm_num
    rw [h1530_eq]
    rw [padicValNat.mul (by norm_num) (by norm_num)]
    rw [padicValNat.prime_pow (n := 2)]
    have h3_not_dvd_170 : ¬ (3 : ℕ) ∣ 170 := by norm_num
    rw [padicValNat.eq_zero_of_not_dvd h3_not_dvd_170]
  have h77 : padicValNat 3 77 = 0 := by
    have h3_not_dvd_77 : ¬ (3 : ℕ) ∣ 77 := by norm_num
    rw [padicValNat.eq_zero_of_not_dvd h3_not_dvd_77]
  rw [h1530, h77]
  simp

/-! ## Uniqueness of the LDU factorization -/

/-- Two factorizations `A₁ D₁ B₁ = A₂ D₂ B₂` (indices `≥ 1`, `Σ_{1 ≤ p ≤ min(i, j)}`) with unit diagonals in the
outer factors and `D₁` without zero agree: `D₁ n = D₂ n`, `B₁ n j = B₂ n j` for `j ≥ n`, `A₁ i n = A₂ i n` for
`i ≥ n`. -/
theorem ldu_unique {K : Type*} [Field K] (A₁ B₁ A₂ B₂ : ℕ → ℕ → K) (D₁ D₂ : ℕ → K)
    (hA₁ : ∀ i, 1 ≤ i → A₁ i i = 1) (hB₁ : ∀ i, 1 ≤ i → B₁ i i = 1)
    (hA₂ : ∀ i, 1 ≤ i → A₂ i i = 1) (hB₂ : ∀ i, 1 ≤ i → B₂ i i = 1)
    (hD : ∀ p, 1 ≤ p → D₁ p ≠ 0)
    (h : ∀ i j, 1 ≤ i → 1 ≤ j →
      ∑ p ∈ Finset.Icc 1 (min i j), A₁ i p * D₁ p * B₁ p j =
        ∑ p ∈ Finset.Icc 1 (min i j), A₂ i p * D₂ p * B₂ p j)
    (n : ℕ) (hn : 1 ≤ n) :
    D₁ n = D₂ n ∧ (∀ j, n ≤ j → B₁ n j = B₂ n j) ∧ (∀ i, n ≤ i → A₁ i n = A₂ i n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- the partial sums over `p ≤ m` agree, for an entry `(i, j)` with `i, j ≥ m + 1`
  have low : ∀ i j, m + 1 ≤ i → m + 1 ≤ j →
      ∑ p ∈ Finset.Icc 1 m, A₁ i p * D₁ p * B₁ p j = ∑ p ∈ Finset.Icc 1 m, A₂ i p * D₂ p * B₂ p j := by
    intro i j hi hj
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨hp1, hpm⟩ := Finset.mem_Icc.mp hp
    obtain ⟨e1, e2, e3⟩ := ih p (by omega) hp1
    rw [e1, e2 j (by omega), e3 i (by omega)]
  have split : ∀ i j, m + 1 ≤ i → m + 1 ≤ j → min i j = m + 1 →
      A₁ i (m + 1) * D₁ (m + 1) * B₁ (m + 1) j = A₂ i (m + 1) * D₂ (m + 1) * B₂ (m + 1) j := by
    intro i j hi hj hmin
    have := h i j (by omega) (by omega)
    rw [hmin, Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), low i j hi hj] at this
    exact add_left_cancel this
  have hDeq : D₁ (m + 1) = D₂ (m + 1) := by
    have := split (m + 1) (m + 1) le_rfl le_rfl (min_self _)
    rwa [hA₁ _ (by omega), hB₁ _ (by omega), hA₂ _ (by omega), hB₂ _ (by omega), one_mul, one_mul,
      mul_one, mul_one] at this
  have hD0 := hD (m + 1) (by omega)
  refine ⟨hDeq, fun j hj => ?_, fun i hi => ?_⟩
  · have := split (m + 1) j le_rfl hj (min_eq_left hj)
    rw [hA₁ _ (by omega), hA₂ _ (by omega), one_mul, one_mul, ← hDeq] at this
    exact mul_left_cancel₀ hD0 this
  · have := split i (m + 1) hi le_rfl (min_eq_right hi)
    rw [hB₁ _ (by omega), hB₂ _ (by omega), mul_one, mul_one, ← hDeq] at this
    exact mul_right_cancel₀ hD0 this

end CalegariSlopes.Conj5
