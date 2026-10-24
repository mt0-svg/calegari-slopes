/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg; William Coram (`norm_tsum_eq_of_dominant`, `norm_det_le_pow_of_row_bound`)
-/
module

public import CalegariSlopes.ADB.Defs

@[expose] public section

/-!
# The Newton step: Lemmas 3.1 to 3.4, Lemma 7.2 and the proof of Corollary 7.1

Theorem 2.3 enters only as the hypothesis `hadb : ADBHyp`, so this module imports `ADB.Defs` alone; `newton` is
Corollary 7.1 under that hypothesis.

`norm_tsum_eq_of_dominant` and `norm_det_le_pow_of_row_bound` are taken from W. Coram,
github.com/WilliamCoram/PhD, file `PhD/Main/TateFredholm/06_Slopes.lean`, commit 659ce260 (Apache 2.0): the section
variables become binders, two names follow the current Mathlib, and the proofs are otherwise the source's.
-/

open CalegariSlopes CalegariSlopes.ADB

namespace CalegariSlopes.Newton

/-! ## Definitions -/

/-- Loeffler's identity, Theorem 2.3, in the form of `CalegariSlopes.ADB.adb`. -/
def ADBHyp : Prop :=
  ∀ i j : ℕ, 1 ≤ i → 1 ≤ j → ∑ p ∈ Finset.Icc 1 (min i j), A i p * D p * B p j = u i j

/-- `w(k) = slope(k) - 2k = 2 v_3((2k)!/k!)`. -/
def wslope (k : ℕ) : ℕ := 2 * padicValNat 3 ((2 * k).factorial / k.factorial)

/-- `W_n = w(1) + ... + w(n)`. -/
def Wn (n : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 n, wslope i

/-- `V_n = slope(1) + ... + slope(n)`. -/
def Vn (n : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 n, slope i

/-- `{1, ..., n}` as a set of positive integers. -/
def Ipn (n : ℕ) : Finset ℕ+ := (Finset.range n).map ⟨Nat.succPNat, Nat.succPNat_injective⟩

/-- `sum(S)`, the sum of the elements of `S`. -/
def psum (S : Finset ℕ+) : ℕ := ∑ s ∈ S, (s : ℕ)

/-! ## The index sets -/

theorem mem_Ipn (n : ℕ) (s : ℕ+) : s ∈ Ipn n ↔ (s : ℕ) ≤ n := by
  simp only [Ipn, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [Nat.succPNat_coe]
    omega
  · intro h
    refine ⟨(s : ℕ) - 1, by have := s.pos; omega, ?_⟩
    apply PNat.eq
    rw [Nat.succPNat_coe]
    have := s.pos
    omega

theorem card_Ipn (n : ℕ) : (Ipn n).card = n := by
  simp [Ipn]

/-! ## Lemma 3.2 (Loeffler's Lemma 3.1) -/

/-- `B_pk = 0` for `k < p`. -/
theorem B_eq_zero_of_lt (p k : ℕ) (h : k < p) : B p k = 0 := by
  unfold B
  refine Finset.sum_eq_zero ?_
  intro t _
  unfold mu
  split
  · rename_i hg
    rcases hg with ⟨_, hptk, _⟩
    omega
  · simp

/-- `B_pp = 1`. -/
theorem B_self (p : ℕ) (hp : 1 ≤ p) : B p p = 1 := by
  unfold B
  rw [Finset.sum_eq_single 0 ?_ ?_]
  · -- goal is now: 3^(2*0) * mu p p 0 / r 0 p = 1
    have h_mu : mu p p 0 = 1 := by
      unfold mu
      have hguard0 : p ≤ p + 2 * 0 ∧ p + 0 ≤ p ∧ 0 ≤ p := by
        constructor <;> omega
      have h0fac : (0 : ℕ).factorial = 1 := by simp
      simp [hguard0, h0fac]
      have hsum : p + p = 2 * p := by omega
      simp [hsum]
      field_simp
      have h2p : (2 * p).factorial = (2 * p) * (2 * p - 1).factorial := by
        calc
          (2 * p).factorial = ((2 * p - 1) + 1).factorial := by
            rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * p)]
          _ = ((2 * p - 1) + 1) * (2 * p - 1).factorial := by rw [Nat.factorial_succ]
          _ = (2 * p) * (2 * p - 1).factorial := by
            rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * p)]
      rw [h2p]
      push_cast
      ring
    have h_r : r 0 p = 1 := by
      unfold r
      have h3 : (3 * p).factorial ≠ 0 := Nat.factorial_ne_zero _
      have hp : p.factorial ≠ 0 := Nat.factorial_ne_zero _
      field_simp [h3, hp]
      simp
    calc
      3 ^ (2 * 0) * mu p p 0 / r 0 p = 1 * mu p p 0 / r 0 p := by simp
      _ = mu p p 0 / r 0 p := by simp
      _ = mu p p 0 / 1 := by rw [h_r]
      _ = mu p p 0 := by simp
      _ = 1 := by rw [h_mu]
  · -- for t ∈ range (p + 1), t ≠ 0 → term = 0
    intro t ht hne
    have hguard : ¬ (p + t ≤ p) := by
      have htpos : 0 < t := Nat.pos_of_ne_zero hne
      omega
    unfold mu
    simp [hguard]
  · -- 0 ∉ range (p + 1) → term = 0 (vacuously true since 0 ∈ range (p + 1))
    intro h
    exfalso
    apply h
    rw [Finset.mem_range]
    omega

theorem padicNorm_r_eq_one (t i : ℕ) : padicNorm 3 (r t i) = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have f0 : ∀ n : ℕ, ((n.factorial : ℕ) : ℚ) ≠ 0 := fun n => by exact_mod_cast Nat.factorial_ne_zero n
  have hr0 : r t i ≠ 0 := by unfold r; positivity
  have hv : padicValRat 3 (r t i) = 0 := by
    unfold r
    rw [padicValRat.div (by positivity) (by positivity), padicValRat.mul (f0 _) (f0 _),
      padicValRat.mul (by positivity) (f0 _), padicValRat.mul (by positivity) (f0 _), padicValRat.pow]
    have h33 : padicValRat 3 (3 : ℚ) = 1 := by
      have := padicValRat.self (p := 3) (by norm_num)
      exact_mod_cast this
    rw [h33]
    simp only [padicValRat.of_nat]
    have ha : padicValNat 3 (3 * i + 3 * t).factorial = padicValNat 3 (i + t).factorial + (i + t) := by
      rw [show 3 * i + 3 * t = 3 * (i + t) by ring, padicValNat_factorial_mul]
    have hb : padicValNat 3 (3 * i).factorial = padicValNat 3 i.factorial + i := padicValNat_factorial_mul i
    rw [ha, hb]
    push_cast
    ring
  rw [padicNorm.eq_zpow_of_nonzero hr0, hv]
  simp

theorem mu_div_eq_bracket (i j t : ℕ) (hi : 1 ≤ i) (ht : 1 ≤ t) (h1 : j ≤ i + 2 * t) (h2 : i + t ≤ j)
    (h3 : t ≤ i) :
    mu i j t / j = ((2 * (2 * i + 2 * t).choose (i + j) * (2 * i + t - 1).descFactorial (t - 1) *
      j.choose (i + t) * i.descFactorial t : ℕ) : ℚ) := by
  rw [mu, ite_eq_left ⟨h1, h2, h3⟩]
  have e1 : (2 * i + 2 * t).choose (i + j) * (i + j).factorial * (i + 2 * t - j).factorial =
      (2 * i + 2 * t).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show i + j ≤ 2 * i + 2 * t by omega)
    rwa [show 2 * i + 2 * t - (i + j) = i + 2 * t - j by omega] at this
  have e2 : j.choose (i + t) * (i + t).factorial * (j - i - t).factorial = j.factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show i + t ≤ j by omega)
    rwa [show j - (i + t) = j - i - t by omega] at this
  have e3 : (2 * i).factorial * (2 * i + t - 1).descFactorial (t - 1) = (2 * i + t - 1).factorial := by
    have := Nat.factorial_mul_descFactorial (show t - 1 ≤ 2 * i + t - 1 by omega)
    rwa [show 2 * i + t - 1 - (t - 1) = 2 * i by omega] at this
  have e4 : (i - t).factorial * i.descFactorial t = i.factorial := Nat.factorial_mul_descFactorial h3
  have q1 : ((2 * i + 2 * t).factorial : ℚ) =
      ((2 * i + 2 * t).choose (i + j) : ℚ) * (i + j).factorial * (i + 2 * t - j).factorial := by
    exact_mod_cast e1.symm
  have q2 : (j.factorial : ℚ) = (j.choose (i + t) : ℚ) * (i + t).factorial * (j - i - t).factorial := by
    exact_mod_cast e2.symm
  have q3 : ((2 * i + t - 1).factorial : ℚ) = ((2 * i).factorial : ℚ) * (2 * i + t - 1).descFactorial (t - 1) := by
    exact_mod_cast e3.symm
  have q4 : (i.factorial : ℚ) = ((i - t).factorial : ℚ) * i.descFactorial t := by
    exact_mod_cast e4.symm
  have hj : (j : ℚ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  have f0 : ∀ n : ℕ, ((n.factorial : ℕ) : ℚ) ≠ 0 := fun n => by exact_mod_cast Nat.factorial_ne_zero n
  rw [q1, q2, q3, q4]
  push_cast
  field_simp

theorem padicNorm_term_div_le (i j t : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    padicNorm 3 (3 ^ (2 * t) * mu i j t / r t i / j) ≤ (3 : ℚ) ^ (-((j : ℤ) - i)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hg : j ≤ i + 2 * t ∧ i + t ≤ j ∧ t ≤ i
  · obtain ⟨h1, h2, h3⟩ := hg
    have ht : 1 ≤ t := by omega
    rw [show 3 ^ (2 * t) * mu i j t / r t i / j = 3 ^ (2 * t) * (mu i j t / j) / r t i by ring,
      mu_div_eq_bracket i j t hi ht h1 h2 h3, padicNorm.div, padicNorm.mul, padicNorm_r_eq_one,
      div_one]
    have hp : padicNorm 3 ((3 : ℚ) ^ (2 * t)) = (3 : ℚ) ^ (-((2 * t : ℕ) : ℤ)) := by
      rw [padicNorm.eq_zpow_of_nonzero (by positivity), padicValRat.pow]
      have h33 : padicValRat 3 (3 : ℚ) = 1 := by
        have := padicValRat.self (p := 3) (by norm_num)
        exact_mod_cast this
      rw [h33, mul_one]
      norm_num
    rw [hp]
    calc (3 : ℚ) ^ (-((2 * t : ℕ) : ℤ)) * padicNorm 3 (((2 * (2 * i + 2 * t).choose (i + j) *
          (2 * i + t - 1).descFactorial (t - 1) * j.choose (i + t) * i.descFactorial t : ℕ) : ℚ))
        ≤ (3 : ℚ) ^ (-((2 * t : ℕ) : ℤ)) * 1 :=
          mul_le_mul_of_nonneg_left (padicNorm.of_nat _) (by positivity)
      _ ≤ (3 : ℚ) ^ (-((j : ℤ) - i)) := by
          rw [mul_one]
          exact zpow_le_zpow_right₀ (by norm_num) (by push_cast; omega)
  · rw [mu, ite_eq_right hg]
    simp only [mul_zero, zero_div, padicNorm.zero]
    positivity

/-- `v_3(B_pk / k) ≥ k - p` for `k > p` (each term of the sum defining `B_pk` is `3^{2t} k` times an integer over
a `3`-adic unit, with `2t ≥ k - p`). -/
theorem padicNorm_B_div_le (p k : ℕ) (hp : 1 ≤ p) (h : p < k) :
    padicNorm 3 (B p k / k) ≤ (3 : ℚ) ^ (-((k : ℤ) - p)) := by
  rw [B, Finset.sum_div]
  exact padicNorm.sum_le' (fun t _ => padicNorm_term_div_le p k t hp h) (by positivity)

/-- `v_3(B_pk) ≥ k - p` for all `p ≥ 1` and `k`. -/
theorem norm_B_le (p k : ℕ) (hp : 1 ≤ p) : ‖(B p k : ℚ_[3])‖ ≤ (3 : ℝ) ^ (-((k : ℤ) - p)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases lt_trichotomy k p with h | rfl | h
  · rw [B_eq_zero_of_lt p k h, Rat.cast_zero, norm_zero]
    positivity
  · rw [B_self k hp, Rat.cast_one, norm_one, sub_self, neg_zero, zpow_zero]
  · have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have hB : B p k = k * (B p k / k) := by field_simp
    rw [Padic.eq_padicNorm, hB, padicNorm.mul]
    have h1 := padicNorm.of_nat (p := 3) k
    have h2 := padicNorm_B_div_le p k hp h
    have : padicNorm 3 (k : ℚ) * padicNorm 3 (B p k / k) ≤ (3 : ℚ) ^ (-((k : ℤ) - p)) := by
      calc _ ≤ 1 * (3 : ℚ) ^ (-((k : ℤ) - p)) := mul_le_mul h1 h2 (padicNorm.nonneg _) zero_le_one
        _ = _ := one_mul _
    have h4 := Rat.cast_le (K := ℝ) |>.mpr this
    rw [Rat.cast_zpow, Rat.cast_ofNat] at h4
    exact h4

/-- `A_ip = 0` for `p > i`. -/
theorem A_eq_zero_of_lt (i p : ℕ) (h : i < p) : A i p = 0 := by
  rw [A, B_eq_zero_of_lt p i h, mul_zero]

/-- `A_ii = 1`. -/
theorem A_self (i : ℕ) (hi : 1 ≤ i) : A i i = 1 := by
  have hi0 : (i : ℚ) ≠ 0 := by exact_mod_cast (show i ≠ 0 by omega)
  rw [A, B_self i hi, div_self hi0, one_mul]

/-- `v_3(A_ip) ≥ i - p` for all `i, p ≥ 1`. -/
theorem norm_A_le (i p : ℕ) (hi : 1 ≤ i) (hp : 1 ≤ p) :
    ‖(A i p : ℚ_[3])‖ ≤ (3 : ℝ) ^ (-((i : ℤ) - p)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases lt_trichotomy i p with h | rfl | h
  · rw [A_eq_zero_of_lt i p h, Rat.cast_zero, norm_zero]
    positivity
  · rw [A_self i hi, Rat.cast_one, norm_one, sub_self, neg_zero, zpow_zero]
  · have hi0 : (i : ℚ) ≠ 0 := by exact_mod_cast (show i ≠ 0 by omega)
    have hA : A i p = p * (B p i / i) := by
      rw [A]
      field_simp
    rw [Padic.eq_padicNorm, hA, padicNorm.mul]
    have h1 := padicNorm.of_nat (p := 3) p
    have h2 := padicNorm_B_div_le p i hp h
    have : padicNorm 3 (p : ℚ) * padicNorm 3 (B p i / i) ≤ (3 : ℚ) ^ (-((i : ℤ) - p)) := by
      calc _ ≤ 1 * (3 : ℚ) ^ (-((i : ℤ) - p)) := mul_le_mul h1 h2 (padicNorm.nonneg _) zero_le_one
        _ = _ := one_mul _
    have h4 := Rat.cast_le (K := ℝ) |>.mpr this
    rw [Rat.cast_zpow, Rat.cast_ofNat] at h4
    exact h4

/-! ## Lemma 3.3 -/

theorem padicValNat_div_factorial (k : ℕ) :
    padicValNat 3 ((2 * k).factorial / k.factorial) + padicValNat 3 k.factorial =
      padicValNat 3 (2 * k).factorial := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd : k.factorial ∣ (2 * k).factorial := Nat.factorial_dvd_factorial (by omega)
  have hq : (2 * k).factorial / k.factorial ≠ 0 :=
    (Nat.div_pos (Nat.factorial_le (by omega)) (Nat.factorial_pos _)).ne'
  rw [← padicValNat.mul hq (Nat.factorial_ne_zero _), Nat.div_mul_cancel hd]

theorem padicValNat_div_factorial_succ (k : ℕ) :
    padicValNat 3 ((2 * (k + 1)).factorial / (k + 1).factorial) =
      padicValNat 3 ((2 * k).factorial / k.factorial) + padicValNat 3 (2 * k + 1) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd : k.factorial ∣ (2 * k).factorial := Nat.factorial_dvd_factorial (by omega)
  set m := (2 * k).factorial / k.factorial with hm
  have hmk : (2 * k).factorial = m * k.factorial := (Nat.div_mul_cancel hd).symm
  have hm0 : m ≠ 0 := (Nat.div_pos (Nat.factorial_le (by omega)) (Nat.factorial_pos _)).ne'
  have h1 : (2 * (k + 1)).factorial = (m * (2 * (2 * k + 1))) * (k + 1).factorial := by
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ, hmk,
      Nat.factorial_succ]
    ring
  rw [h1, Nat.mul_div_cancel _ (Nat.factorial_pos _), padicValNat.mul hm0 (by omega),
    padicValNat.mul (by norm_num) (by omega)]
  have h2 : padicValNat 3 2 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [h2, zero_add]

theorem D_pos (k : ℕ) : 0 < D k := by
  unfold D
  positivity

theorem padicValRat_D (k : ℕ) : padicValRat 3 (D k) = slope k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h6 : padicValNat 3 (6 * k).factorial = padicValNat 3 (2 * k).factorial + 2 * k := by
    rw [show 6 * k = 3 * (2 * k) by ring, padicValNat_factorial_mul]
  have h3 : padicValNat 3 (3 * k).factorial = padicValNat 3 k.factorial + k :=
    padicValNat_factorial_mul k
  have hdiv := padicValNat_div_factorial k
  have f0 : ∀ n : ℕ, ((n.factorial : ℕ) : ℚ) ≠ 0 := fun n => by exact_mod_cast Nat.factorial_ne_zero n
  unfold D slope
  rw [padicValRat.div (by positivity) (by positivity), padicValRat.mul (by positivity) (f0 _),
    padicValRat.mul (by positivity) (f0 _), padicValRat.mul (by positivity) (f0 _),
    padicValRat.pow, padicValRat.mul (by norm_num) (by positivity), padicValRat.pow]
  have h33 : padicValRat 3 (3 : ℚ) = 1 := by
    have := padicValRat.self (p := 3) (by norm_num)
    exact_mod_cast this
  rw [h33]
  rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num]
  simp only [padicValRat.of_nat]
  have h2 : padicValNat 3 2 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [h2, h6, h3, ← hdiv]
  push_cast
  ring

/-- `v_3(D_k) = slope(k)`. -/
theorem norm_D (k : ℕ) : ‖(D k : ℚ_[3])‖ = (3 : ℝ) ^ (-(slope k : ℤ)) := by
  rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero (D_pos k).ne', padicValRat_D]
  push_cast
  rfl

/-! ## Lemma 3.4 and the counting of Section 7 -/

/-- `w` is nondecreasing: `w(k + 1) - w(k) = 2 v_3(2k + 1)`. -/
theorem wslope_mono : Monotone wslope := by
  refine monotone_nat_of_le_succ fun k => ?_
  unfold wslope
  rw [padicValNat_div_factorial_succ]
  omega

/-- Helper: `|T| ≤ max T` for a nonempty set of positive integers. -/
theorem card_le_max' (T : Finset ℕ+) (h : T.Nonempty) : T.card ≤ ((T.max' h : ℕ+) : ℕ) := by
  have hsub : T ⊆ Finset.Icc 1 (T.max' h) := fun t ht =>
    Finset.mem_Icc.2 ⟨t.2, T.le_max' t ht⟩
  have := Finset.card_le_card hsub
  rw [PNat.card_Icc] at this
  simpa using this

/-- For a nondecreasing `g` and a set `T` of `n` positive integers, `Σ_{t ∈ T} g(t) ≥ g(1) + ... + g(n)`. -/
theorem sum_Icc_le_sum (g : ℕ → ℤ) (hg : Monotone g) (T : Finset ℕ+) :
    ∑ i ∈ Finset.Icc 1 T.card, g i ≤ ∑ t ∈ T, g (t : ℕ) := by
  induction h : T.card generalizing T with
  | zero =>
    rw [Finset.card_eq_zero] at h
    simp [h]
  | succ n ih =>
    have hne : T.Nonempty := Finset.card_pos.1 (by omega)
    set m := T.max' hne with hm
    have hmT : m ∈ T := T.max'_mem hne
    have hcard : (T.erase m).card = n := by rw [Finset.card_erase_of_mem hmT, h]; rfl
    have hle : n + 1 ≤ (m : ℕ) := h ▸ card_le_max' T hne
    rw [Finset.sum_Icc_succ_top (by omega), ← Finset.add_sum_erase T _ hmT]
    have := ih (T.erase m) hcard
    have := hg hle
    linarith

/-- Helper: `2 (1 + ... + n) = n (n + 1)`. -/
theorem two_mul_sum_Icc (n : ℕ) : 2 * ∑ i ∈ Finset.Icc 1 n, i = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    ring

/-- A set `T` of `n` positive integers other than `{1, ..., n}` has `2 sum(T) ≥ n(n + 1) + 2`. -/
theorem psum_ge_of_ne (T : Finset ℕ+) (hT : T ≠ Ipn T.card) :
    T.card * (T.card + 1) + 2 ≤ 2 * psum T := by
  induction h : T.card generalizing T with
  | zero =>
    rw [h] at hT
    exact absurd (Finset.card_eq_zero.1 h) (by simpa [Ipn] using hT)
  | succ n ih =>
    have hne : T.Nonempty := Finset.card_pos.1 (by omega)
    set m := T.max' hne with hm
    have hmT : m ∈ T := T.max'_mem hne
    have hcard : (T.erase m).card = n := by rw [Finset.card_erase_of_mem hmT, h]; rfl
    have hle : n + 1 ≤ (m : ℕ) := h ▸ card_le_max' T hne
    have hsplit : psum T = (m : ℕ) + psum (T.erase m) := by
      rw [psum, psum, ← Finset.add_sum_erase T _ hmT]
    have hbase : n * (n + 1) ≤ 2 * psum (T.erase m) := by
      have h1 := sum_Icc_le_sum (fun i => (i : ℤ)) (fun a b hab => by simp only; exact_mod_cast hab) (T.erase m)
      rw [hcard] at h1
      have h2 := two_mul_sum_Icc n
      have h3 : (∑ i ∈ Finset.Icc 1 n, i : ℕ) ≤ psum (T.erase m) := by
        have h1' : ((∑ i ∈ Finset.Icc 1 n, i : ℕ) : ℤ) ≤ ((psum (T.erase m) : ℕ) : ℤ) := by
          rw [psum]; push_cast; exact h1
        exact_mod_cast h1'
      omega
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · have hne' : T.erase m ≠ Ipn n := by
        intro hT'
        apply hT
        rw [h, ← Finset.insert_erase hmT, hT']
        ext s
        rw [Finset.mem_insert, mem_Ipn, mem_Ipn]
        constructor
        · rintro (rfl | hs) <;> omega
        · intro hs
          rcases Nat.lt_or_ge (s : ℕ) (n + 1) with h' | h'
          · right; omega
          · left; apply PNat.eq; omega
      have := ih (T.erase m) (by rw [hcard]; exact hne') hcard
      rw [hsplit]
      nlinarith
    · rw [hsplit]
      nlinarith

/-- `V_n = n(n + 1) + W_n`. -/
theorem Vn_eq (n : ℕ) : Vn n = n * (n + 1) + Wn n := by
  unfold Vn Wn
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ih]
    unfold slope wslope
    ring

/-! ### The recurrence of `u` -/

section URec

open MvPowerSeries

/-- Exponent `x ^ i * y ^ j`. -/
noncomputable abbrev e (i j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j

lemma e_apply_zero (i j : ℕ) : e i j 0 = i := by simp [e]

lemma e_apply_one (i j : ℕ) : e i j 1 = j := by simp [e]

lemma e_le_e (a b i j : ℕ) : e a b ≤ e i j ↔ a ≤ i ∧ b ≤ j := by
  rw [Finsupp.le_def, Fin.forall_fin_two]
  simp [e_apply_zero, e_apply_one]

lemma e_sub_e (a b i j : ℕ) : e i j - e a b = e (i - a) (j - b) := by
  ext k
  fin_cases k <;> simp [e_apply_zero, e_apply_one]

lemma e_eq_zero (i j : ℕ) : e i j = 0 ↔ i = 0 ∧ j = 0 := by
  constructor
  · intro h
    have h0 := congrArg (· 0) h
    have h1 := congrArg (· 1) h
    simp only [e_apply_zero, e_apply_one, Finsupp.coe_zero, Pi.zero_apply] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩
    simp [e]

lemma u_eq (i j : ℕ) : u i j = coeff (e i j) F := rfl

lemma x_pow_mul_y_pow (a b : ℕ) :
    (x ^ a * y ^ b : MvPowerSeries (Fin 2) ℚ) = monomial (e a b) 1 := by
  simp only [x, y, X_pow_eq, monomial_mul_monomial, mul_one, e]

lemma coeff_e_mul (a b i j : ℕ) (φ : MvPowerSeries (Fin 2) ℚ) :
    coeff (e i j) (x ^ a * (y ^ b * φ)) =
      if a ≤ i ∧ b ≤ j then coeff (e (i - a) (j - b)) φ else 0 := by
  rw [← mul_assoc, x_pow_mul_y_pow, coeff_monomial_mul]
  simp only [e_le_e, e_sub_e, one_mul]

lemma coeff_e (a b i j : ℕ) :
    coeff (e i j) (x ^ a * y ^ b : MvPowerSeries (Fin 2) ℚ) = if a = i ∧ b = j then 1 else 0 := by
  have h := coeff_e_mul a b i j 1
  rw [mul_one] at h
  rw [h, coeff_one]
  by_cases hab : a ≤ i ∧ b ≤ j
  · simp only [hab, and_self, ite_true, e_eq_zero]
    by_cases hij : a = i ∧ b = j
    · simp [hij]
    · rw [ite_eq_right_iff.mpr (fun h => absurd ⟨by omega, by omega⟩ hij), ite_eq_right_iff.mpr]
      exact fun h => absurd h hij
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hab), ite_eq_right_iff.mpr]
    exact fun h => absurd ⟨h.1.le, h.2.le⟩ hab

/-- `N` as a sum of monomials. -/
lemma N_eq : N = C 90 * (x ^ 1 * y ^ 1) + C 324 * (x ^ 2 * y ^ 1) + C 648 * (x ^ 1 * y ^ 2) +
    C 243 * (x ^ 3 * y ^ 1) + C 486 * (x ^ 2 * y ^ 2) + C 729 * (x ^ 1 * y ^ 3) := by
  simp only [N, map_ofNat]
  ring

/-- `1 - Q` as a sum of monomials. -/
lemma one_sub_Q_eq : 1 - Q = C 270 * (x ^ 1 * y ^ 1) + C 972 * (x ^ 2 * y ^ 1) +
    C 972 * (x ^ 1 * y ^ 2) + C 729 * (x ^ 3 * y ^ 1) + C 729 * (x ^ 2 * y ^ 2) +
    C 729 * (x ^ 1 * y ^ 3) := by
  simp only [Q, map_ofNat]
  ring

lemma constantCoeff_Q : constantCoeff Q = 1 := by
  simp [Q, x, y]

/-- `Q⁻¹` is a two-sided inverse of `Q`, so `F` is the power series of `N / Q`. -/
lemma Q_mul_F : Q * F = N := by
  rw [F, mul_comm N, ← mul_assoc, MvPowerSeries.mul_inv_cancel Q (by rw [constantCoeff_Q]; norm_num),
    one_mul]

/-- The recurrence `F = N + (1 - Q) * F`, coefficientwise; the truncated subtractions are harmless since
`u 0 j = u i 0 = 0` (lemmas `u_zero_left`, `u_zero_right`). -/
lemma u_rec (i j : ℕ) :
    u i j =
      (if 1 = i ∧ 1 = j then 90 else 0) + (if 2 = i ∧ 1 = j then 324 else 0) +
      (if 1 = i ∧ 2 = j then 648 else 0) + (if 3 = i ∧ 1 = j then 243 else 0) +
      (if 2 = i ∧ 2 = j then 486 else 0) + (if 1 = i ∧ 3 = j then 729 else 0) +
      ((if 1 ≤ i ∧ 1 ≤ j then 270 * u (i - 1) (j - 1) else 0) +
      (if 2 ≤ i ∧ 1 ≤ j then 972 * u (i - 2) (j - 1) else 0) +
      (if 1 ≤ i ∧ 2 ≤ j then 972 * u (i - 1) (j - 2) else 0) +
      (if 3 ≤ i ∧ 1 ≤ j then 729 * u (i - 3) (j - 1) else 0) +
      (if 2 ≤ i ∧ 2 ≤ j then 729 * u (i - 2) (j - 2) else 0) +
      (if 1 ≤ i ∧ 3 ≤ j then 729 * u (i - 1) (j - 3) else 0)) := by
  have hF : F = N + (1 - Q) * F := by rw [sub_mul, one_mul, Q_mul_F]; ring
  have h := congrArg (coeff (e i j)) hF
  rw [N_eq, one_sub_Q_eq] at h
  simp only [map_add, add_mul, mul_assoc, coeff_C_mul, coeff_e_mul, coeff_e, ← u_eq, mul_ite,
    mul_one, mul_zero] at h
  exact h

lemma u_zero_left (j : ℕ) : u 0 j = 0 := by
  rw [u_rec]; simp

lemma u_zero_right (i : ℕ) : u i 0 = 0 := by
  rw [u_rec]; simp

end URec

/-! ## Lemma 3.1 (a) (from `F` alone) -/

/-- `u_ij` is an integer divisible by `3 ^ (i + j)`: `F(x/3, y/3)` has integer coefficients. -/
theorem u_dvd (i j : ℕ) : ∃ z : ℤ, u i j = 3 ^ (i + j) * z := by
  induction hn : i + j using Nat.strong_induction_on generalizing i j with
  | _ n ih =>
  subst hn
  have IH : ∀ a b, a + b < i + j → ∃ z : ℤ, u a b = 3 ^ (a + b) * z :=
    fun a b h => ih (a + b) h a b rfl
  have T : ∀ (a b c : ℕ) (K : ℤ), a + b + c = i + j → a + b < i + j →
      ∃ z : ℤ, (3 ^ c * K : ℚ) * u a b = 3 ^ (i + j) * z := by
    intro a b c K h1 h2
    obtain ⟨z, hz⟩ := IH a b h2
    exact ⟨K * z, by rw [hz, ← h1, pow_add]; push_cast; ring⟩
  have C : ∀ (q : ℚ) (c : Prop) [Decidable c], (c → ∃ z : ℤ, q = 3 ^ (i + j) * z) →
      ∃ z : ℤ, (if c then q else 0) = 3 ^ (i + j) * z := by
    intro q c _ h
    by_cases hc : c
    · rw [ite_eq_left hc]; exact h hc
    · exact ⟨0, by rw [ite_eq_right hc]; simp⟩
  have Add : ∀ q r : ℚ, (∃ z : ℤ, q = 3 ^ (i + j) * z) → (∃ z : ℤ, r = 3 ^ (i + j) * z) →
      ∃ z : ℤ, q + r = 3 ^ (i + j) * z := by
    rintro q r ⟨z, rfl⟩ ⟨w, rfl⟩
    exact ⟨z + w, by push_cast; ring⟩
  have K : ∀ (a b c : ℕ) (K : ℤ) (q : ℚ), q = 3 ^ c * K → a + b + c = i + j → a + b < i + j →
      ∃ z : ℤ, q * u a b = 3 ^ (i + j) * z := by
    intro a b c K q hq h1 h2
    rw [hq]
    exact T a b c K h1 h2
  rw [u_rec]
  refine Add _ _
    (Add _ _ (Add _ _ (Add _ _ (Add _ _ (Add _ _ (C _ _ ?_) (C _ _ ?_)) (C _ _ ?_)) (C _ _ ?_)) (C _ _ ?_))
      (C _ _ ?_))
    (Add _ _ (Add _ _ (Add _ _ (Add _ _ (Add _ _ (C _ _ ?_) (C _ _ ?_)) (C _ _ ?_)) (C _ _ ?_)) (C _ _ ?_))
      (C _ _ ?_))
  · rintro ⟨rfl, rfl⟩; exact ⟨10, by norm_num⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨12, by norm_num⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨24, by norm_num⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨3, by norm_num⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨6, by norm_num⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨9, by norm_num⟩
  · rintro ⟨h1, h2⟩; exact K _ _ 2 30 _ (by norm_num) (by omega) (by omega)
  · rintro ⟨h1, h2⟩; exact K _ _ 3 36 _ (by norm_num) (by omega) (by omega)
  · rintro ⟨h1, h2⟩; exact K _ _ 3 36 _ (by norm_num) (by omega) (by omega)
  · rintro ⟨h1, h2⟩; exact K _ _ 4 9 _ (by norm_num) (by omega) (by omega)
  · rintro ⟨h1, h2⟩; exact K _ _ 4 9 _ (by norm_num) (by omega) (by omega)
  · rintro ⟨h1, h2⟩; exact K _ _ 4 9 _ (by norm_num) (by omega) (by omega)

/-- `v_3(u_ij) ≥ i + j`. -/
theorem norm_u_le (i j : ℕ) : ‖(u i j : ℚ_[3])‖ ≤ (3 : ℝ) ^ (-((i : ℤ) + j)) := by
  obtain ⟨z, hz⟩ := u_dvd i j
  rw [hz]
  push_cast
  rw [norm_mul, norm_pow]
  have h3 : ‖(3 : ℚ_[3])‖ = 3⁻¹ := by
    have := Padic.norm_p (p := 3)
    simpa using this
  rw [h3]
  calc (3⁻¹ : ℝ) ^ (i + j) * ‖(z : ℚ_[3])‖ ≤ (3⁻¹ : ℝ) ^ (i + j) * 1 :=
        mul_le_mul_of_nonneg_left (Padic.norm_int_le_one z) (by positivity)
    _ = (3 : ℝ) ^ (-((i : ℤ) + j)) := by
        rw [mul_one, inv_pow, ← zpow_natCast, ← zpow_neg]
        push_cast
        rfl

/-! ## Generic ultrametric bounds in `ℚ_[3]` -/

/-- Helper: a product of powers of `3` with integer exponents. -/
theorem prod_zpow_three {ι : Type*} (s : Finset ι) (k : ι → ℤ) :
    ∏ a ∈ s, (3 : ℝ) ^ k a = (3 : ℝ) ^ (∑ a ∈ s, k a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]

theorem norm_prod_le_zpow {ι : Type*} (s : Finset ι) (x : ι → ℚ_[3]) (k : ι → ℤ)
    (h : ∀ a ∈ s, ‖x a‖ ≤ (3 : ℝ) ^ (-k a)) :
    ‖∏ a ∈ s, x a‖ ≤ (3 : ℝ) ^ (-∑ a ∈ s, k a) := by
  rw [norm_prod, ← Finset.sum_neg_distrib, ← prod_zpow_three]
  exact Finset.prod_le_prod₀ (fun a _ => norm_nonneg _) h

/-- Ultrametric Hadamard bound with row and column weights. -/
theorem norm_det_le_zpow {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℚ_[3]) (α β : ι → ℤ)
    (h : ∀ a b, ‖M a b‖ ≤ (3 : ℝ) ^ (-(α a + β b))) :
    ‖M.det‖ ≤ (3 : ℝ) ^ (-(∑ a, α a + ∑ b, β b)) := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun τ _ => ?_
  have hsm : ‖Equiv.Perm.sign τ • ∏ i, M (τ i) i‖ = ‖∏ i, M (τ i) i‖ := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> rw [h]
    · rw [one_smul]
    · rw [Units.neg_smul, one_smul, norm_neg]
  rw [hsm]
  calc ‖∏ i, M (τ i) i‖ ≤ (3 : ℝ) ^ (-∑ i, (α (τ i) + β i)) :=
        norm_prod_le_zpow _ _ _ fun i _ => h (τ i) i
    _ = (3 : ℝ) ^ (-(∑ a, α a + ∑ b, β b)) := by
        rw [Finset.sum_add_distrib, Equiv.sum_comp τ α]

/-- From W. Coram, `06_Slopes.lean`, `TateFredholm.norm_tsum_eq_of_dominant` (Apache 2.0). -/
theorem norm_tsum_eq_of_dominant {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    {ι : Type*} {f : ι → K} (hf : Summable f) (i₀ : ι)
    {c : ℝ} (hc : c < ‖f i₀‖) (h : ∀ i ≠ i₀, ‖f i‖ ≤ c) : ‖∑' i, f i‖ = ‖f i₀‖ := by
  classical
  rw [hf.tsum_eq_add_tsum_ite i₀]
  by_cases hall : ∀ i, i = i₀
  · rw [tsum_congr fun i => ite_eq_left (hall i), tsum_zero, add_zero]
  · obtain ⟨i₁, hi₁⟩ := not_forall.1 hall
    have hc0 : 0 ≤ c := (norm_nonneg (f i₁)).trans (h i₁ hi₁)
    have htail : ‖∑' i, if i = i₀ then (0 : K) else f i‖ ≤ c := by
      refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hc0 fun i => ?_
      by_cases hi : i = i₀
      · simpa [hi] using hc0
      · simpa [hi] using h i hi
    have hlt : ‖∑' i, if i = i₀ then (0 : K) else f i‖ < ‖f i₀‖ := htail.trans_lt hc
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]

/-- From W. Coram, `06_Slopes.lean`, `TateFredholm.norm_det_le_pow_of_row_bound` (Apache 2.0). -/
theorem norm_det_le_pow_of_row_bound {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    {σ : ℝ} (hσ0 : 0 ≤ σ) {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (w : n → ℕ) (hM : ∀ j i, ‖M j i‖ ≤ σ ^ w j) :
    ‖M.det‖ ≤ σ ^ (∑ j, w j) := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun τ _ => ?_
  have hsm : ‖Equiv.Perm.sign τ • ∏ i, M (τ i) i‖ = ‖∏ i, M (τ i) i‖ := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> rw [h]
    · rw [one_smul]
    · rw [Units.neg_smul, one_smul, norm_neg]
  rw [hsm]
  calc ‖∏ i, M (τ i) i‖ ≤ ∏ i, ‖M (τ i) i‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ i, σ ^ w (τ i) := Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => hM (τ i) i
    _ = ∏ j, σ ^ w j := Equiv.prod_comp τ fun j => σ ^ w j
    _ = σ ^ (∑ j, w j) := Finset.prod_pow_eq_pow_sum _ _ _

/-- Summability of the `n`-minors of an `ℕ+ × ℕ+` matrix over `ℚ_[3]` from a row bound `‖M i j‖ ≤ 3⁻ⁱ`. -/
theorem summable_minor_of_row_bound (M : ℕ+ → ℕ+ → ℚ_[3])
    (hM : ∀ i j, ‖M i j‖ ≤ (3⁻¹ : ℝ) ^ (i : ℕ)) (n : ℕ) :
    Summable (fun S : {S : Finset ℕ+ // S.card = n} =>
      (Matrix.of fun a b : S.1 => M (a : ℕ+) (b : ℕ+)).det) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  have hσ0 : (0 : ℝ) ≤ 3⁻¹ := by norm_num
  have hσ1 : (3⁻¹ : ℝ) < 1 := by norm_num
  have hb : ∀ S : Finset ℕ+, ‖(Matrix.of fun a b : S => M (a : ℕ+) (b : ℕ+)).det‖
      ≤ (3⁻¹ : ℝ) ^ (∑ a ∈ S, (a : ℕ)) := by
    intro S
    rw [← Finset.sum_coe_sort S (fun a : ℕ+ => (a : ℕ))]
    exact norm_det_le_pow_of_row_bound hσ0 _ (fun a : S => ((a : ℕ+) : ℕ)) fun a b => hM _ _
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hσ1
  rw [Filter.eventually_cofinite]
  obtain ⟨T, hTdef⟩ : ∃ T : Finset ℕ+, T = Finset.Iic N.succPNat := ⟨_, rfl⟩
  have hfin : {S : {S : Finset ℕ+ // S.card = n} | (S : Finset ℕ+) ⊆ T}.Finite := by
    have h1 : {S : Finset ℕ+ | S ⊆ T}.Finite :=
      T.powerset.finite_toSet.subset fun S hS => by simpa [Finset.mem_powerset] using hS
    exact h1.preimage Subtype.val_injective.injOn
  refine hfin.subset fun S hS => ?_
  simp only [Set.mem_ofPred_eq, dist_zero_right, not_lt] at hS ⊢
  intro a ha
  by_contra hT
  have haN : N < (a : ℕ) := by
    have hT' : N.succPNat < a := by
      rwa [hTdef, Finset.mem_Iic, not_le] at hT
    have := (PNat.coe_lt_coe _ _).2 hT'
    rw [Nat.succPNat_coe] at this
    omega
  have hsum : N ≤ ∑ b ∈ (S : Finset ℕ+), (b : ℕ) :=
    haN.le.trans (Finset.single_le_sum (f := fun b : ℕ+ => (b : ℕ)) (fun _ _ => Nat.zero_le _) ha)
  have := (hb S).trans (pow_le_pow_of_le_one hσ0 hσ1.le hsum)
  linarith

/-- The dominant-term principle read through `Padic.valuation`. -/
theorem valuation_tsum_of_dominant {ι : Type*} {f : ι → ℚ_[3]} (hf : Summable f) (i₀ : ι) {V : ℤ}
    (h0 : ‖f i₀‖ = (3 : ℝ) ^ (-V)) (h : ∀ i ≠ i₀, ‖f i‖ ≤ (3 : ℝ) ^ (-(V + 1))) :
    (∑' i, f i) ≠ 0 ∧ (∑' i, f i).valuation = V := by
  have hp1 : (1 : ℝ) < 3 := by norm_num
  have hc : (3 : ℝ) ^ (-(V + 1)) < ‖f i₀‖ := by
    rw [h0]; exact zpow_lt_zpow_right₀ hp1 (by omega)
  have ht := norm_tsum_eq_of_dominant hf i₀ hc h
  have hne : (∑' i, f i) ≠ 0 := by
    intro h'
    rw [h', norm_zero, h0] at ht
    exact (zpow_pos (by norm_num : (0 : ℝ) < 3) _).ne' ht.symm
  refine ⟨hne, ?_⟩
  have h2 := Padic.norm_eq_zpow_neg_valuation hne
  rw [ht, h0] at h2
  have h3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
  rw [h3] at h2
  have := zpow_right_injective₀ (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≠ 1) h2
  omega

/-! ## Expansion of a principal minor (proof of Lemma 7.2) -/

/-- Multilinearity of `det` in the rows: `det (X Y) = Σ_f (Π_a X_{a, f a}) det (Y_{f a, b})`. -/
theorem det_mul_eq_sum_fun {ι κ R : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (X : Matrix ι κ R) (Y : Matrix κ ι R) :
    (X * Y).det = ∑ f : ι → κ, (∏ a, X a (f a)) * (Matrix.of fun a b => Y (f a) b).det := by
  have hrows : (X * Y : Matrix ι ι R) = fun a => ∑ k, X a k • Y k := by
    funext a b
    simp [Matrix.mul_apply, Finset.sum_apply, smul_eq_mul]
  have h1 : (X * Y).det =
      (Matrix.detRowAlternating : (ι → R) [⋀^ι]→ₗ[R] R).toMultilinearMap
        (fun a => ∑ k, X a k • Y k) := by
    rw [Matrix.det, hrows]
    rfl
  rw [h1, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

/-- Theorem 2.3 on the block `S × S`, through any `K ⊇ [1, max S]`:
`U_SS = (A_sp D_p)_{s ∈ S, p ∈ K} (B_ps)_{p ∈ K, s ∈ S}`. -/
theorem minor_factor (hadb : ADBHyp) (S K : Finset ℕ+) (hK : ∀ s ∈ S, ∀ p : ℕ+, p ≤ s → p ∈ K) :
    (Matrix.of fun a b : S => (u ((a : ℕ+) : ℕ) ((b : ℕ+) : ℕ) : ℚ_[3])) =
      (Matrix.of fun (a : S) (p : K) =>
        ((A ((a : ℕ+) : ℕ) ((p : ℕ+) : ℕ) * D ((p : ℕ+) : ℕ) : ℚ) : ℚ_[3])) *
      (Matrix.of fun (p : K) (b : S) => (B ((p : ℕ+) : ℕ) ((b : ℕ+) : ℕ) : ℚ_[3])) := by
  classical
  ext a b
  simp only [Matrix.mul_apply, Matrix.of_apply]
  have ha := (a : ℕ+).pos
  have hb := (b : ℕ+).pos
  have key : ∑ p ∈ Finset.Icc 1 (min ((a : ℕ+) : ℕ) ((b : ℕ+) : ℕ)),
      A ((a : ℕ+) : ℕ) p * D p * B p ((b : ℕ+) : ℕ) =
      ∑ p : K, A ((a : ℕ+) : ℕ) ((p : ℕ+) : ℕ) * D ((p : ℕ+) : ℕ) * B ((p : ℕ+) : ℕ) ((b : ℕ+) : ℕ) := by
    rw [Finset.sum_coe_sort K
      (fun p : ℕ+ => A ((a : ℕ+) : ℕ) (p : ℕ) * D (p : ℕ) * B (p : ℕ) ((b : ℕ+) : ℕ)),
      ← Finset.sum_filter_of_ne
        (p := fun p : ℕ+ => (p : ℕ) ≤ min ((a : ℕ+) : ℕ) ((b : ℕ+) : ℕ))]
    · symm
      refine Finset.sum_nbij' (fun p : ℕ+ => (p : ℕ)) (fun n => Nat.toPNat' n) ?_ ?_ ?_ ?_ ?_
      · intro p hp
        rw [Finset.mem_filter] at hp
        rw [Finset.mem_Icc]
        exact ⟨p.pos, hp.2⟩
      · intro n hn
        rw [Finset.mem_Icc] at hn
        have hn' : ((Nat.toPNat' n : ℕ+) : ℕ) = n := PNat.toPNat'_coe (by omega)
        rw [Finset.mem_filter, hn']
        refine ⟨hK _ a.2 _ ?_, hn.2⟩
        rw [← PNat.coe_le_coe, hn']
        exact hn.2.trans (min_le_left _ _)
      · intro p _
        exact PNat.coe_toPNat' p
      · intro n hn
        rw [Finset.mem_Icc] at hn
        exact PNat.toPNat'_coe (by omega)
      · intro p _
        rfl
    · intro p _ hp
      by_contra hpm
      apply hp
      rcases le_or_gt ((p : ℕ)) ((a : ℕ+) : ℕ) with h1 | h1
      · have h2 : ((b : ℕ+) : ℕ) < (p : ℕ) := by omega
        rw [B_eq_zero_of_lt _ _ h2, mul_zero]
      · rw [A_eq_zero_of_lt _ _ h1, zero_mul, zero_mul]
  rw [← hadb _ _ ha hb, key]
  push_cast
  rfl

/-! ## Lemma 7.2: the bound on every principal minor -/

/-- The `f`-term of the expansion has valuation at least `2 sum(S) + W_n`, `n = |S|`, for injective `f`. -/
theorem norm_term_le (S K : Finset ℕ+) (f : S → K) (hf : Function.Injective f) :
    ‖(∏ a : S, ((A ((a : ℕ+) : ℕ) ((f a : ℕ+) : ℕ) * D ((f a : ℕ+) : ℕ) : ℚ) : ℚ_[3])) *
      (Matrix.of fun a b : S => (B ((f a : ℕ+) : ℕ) ((b : ℕ+) : ℕ) : ℚ_[3])).det‖ ≤
      (3 : ℝ) ^ (-(2 * (psum S : ℤ) + Wn S.card)) := by
  classical
  have hg1 : ∀ a : S, 1 ≤ ((f a : ℕ+) : ℕ) := fun a => (f a : ℕ+).pos
  have hs1 : ∀ a : S, 1 ≤ ((a : ℕ+) : ℕ) := fun a => (a : ℕ+).pos
  have hprod : ‖∏ a : S, ((A ((a : ℕ+) : ℕ) ((f a : ℕ+) : ℕ) * D ((f a : ℕ+) : ℕ) : ℚ) : ℚ_[3])‖ ≤
      (3 : ℝ) ^ (-∑ a : S, ((((a : ℕ+) : ℕ) : ℤ) - ((f a : ℕ+) : ℕ) + slope ((f a : ℕ+) : ℕ))) := by
    refine norm_prod_le_zpow _ _ _ fun a _ => ?_
    rw [Rat.cast_mul, norm_mul, neg_add, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    exact mul_le_mul (norm_A_le _ _ (hs1 a) (hg1 a)) (norm_D _).le (norm_nonneg _) (by positivity)
  have hdet : ‖(Matrix.of fun a b : S => (B ((f a : ℕ+) : ℕ) ((b : ℕ+) : ℕ) : ℚ_[3])).det‖ ≤
      (3 : ℝ) ^ (-(∑ a : S, (-((((f a : ℕ+) : ℕ)) : ℤ)) + ∑ b : S, ((((b : ℕ+) : ℕ)) : ℤ))) := by
    refine norm_det_le_zpow _ (fun a => -((((f a : ℕ+) : ℕ)) : ℤ)) (fun b => ((((b : ℕ+) : ℕ)) : ℤ))
      fun a b => ?_
    rw [Matrix.of_apply]
    calc ‖(B ((f a : ℕ+) : ℕ) ((b : ℕ+) : ℕ) : ℚ_[3])‖
        ≤ (3 : ℝ) ^ (-(((((b : ℕ+) : ℕ)) : ℤ) - (((f a : ℕ+) : ℕ) : ℤ))) := norm_B_le _ _ (hg1 a)
      _ = _ := by ring_nf
  have hinj : Function.Injective (fun a : S => (f a : ℕ+)) := Subtype.val_injective.comp hf
  have hw : (Wn S.card : ℤ) ≤ ∑ a : S, (wslope ((f a : ℕ+) : ℕ) : ℤ) := by
    have hT : (Finset.univ.image (fun a : S => (f a : ℕ+))).card = S.card := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe]
    have h1 := sum_Icc_le_sum (fun i => (wslope i : ℤ))
      (fun x y h => by simp only; exact_mod_cast wslope_mono h) (Finset.univ.image (fun a : S => (f a : ℕ+)))
    rw [hT, Finset.sum_image (fun x _ y _ h => hinj h)] at h1
    rw [Wn, Nat.cast_sum]
    exact h1
  have hps : (psum S : ℤ) = ∑ a : S, ((((a : ℕ+) : ℕ)) : ℤ) := by
    rw [psum, Nat.cast_sum]
    exact (Finset.sum_coe_sort S (fun x : ℕ+ => ((x : ℕ) : ℤ))).symm
  have hsl : ∀ t : ℕ, (slope t : ℤ) = 2 * t + wslope t := by
    intro t
    unfold slope wslope
    push_cast
    ring
  rw [norm_mul]
  calc _ ≤ (3 : ℝ) ^ (-∑ a : S, ((((a : ℕ+) : ℕ) : ℤ) - ((f a : ℕ+) : ℕ) + slope ((f a : ℕ+) : ℕ))) *
        (3 : ℝ) ^ (-(∑ a : S, (-((((f a : ℕ+) : ℕ)) : ℤ)) + ∑ b : S, ((((b : ℕ+) : ℕ)) : ℤ))) :=
        mul_le_mul hprod hdet (norm_nonneg _) (by positivity)
    _ = (3 : ℝ) ^ (-(2 * (psum S : ℤ) + ∑ a : S, (wslope ((f a : ℕ+) : ℕ) : ℤ))) := by
        rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
        congr 1
        rw [hps]
        simp only [hsl, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
          ← Finset.mul_sum]
        ring
    _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by linarith)

/-- Lemma 7.2: `v_3(det U_SS) ≥ 2 sum(S) + W_n`. -/
theorem norm_principalMinor_le (hadb : ADBHyp) (S : Finset ℕ+) :
    ‖principalMinor S‖ ≤ (3 : ℝ) ^ (-(2 * (psum S : ℤ) + Wn S.card)) := by
  classical
  have hK : ∀ s ∈ S, ∀ p : ℕ+, p ≤ s → p ∈ Ipn (psum S) := by
    intro s hs p hp
    rw [mem_Ipn]
    have h1 : (s : ℕ) ≤ psum S :=
      Finset.single_le_sum (f := fun s : ℕ+ => (s : ℕ)) (fun _ _ => Nat.zero_le _) hs
    have h2 : (p : ℕ) ≤ s := hp
    omega
  rw [principalMinor, minor_factor hadb S (Ipn (psum S)) hK, det_mul_eq_sum_fun]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun f _ => ?_
  by_cases hf : Function.Injective f
  · simpa only [Matrix.of_apply] using norm_term_le S _ f hf
  · obtain ⟨a, b, hab, hne⟩ : ∃ a b, f a = f b ∧ a ≠ b := by
      simp only [Function.Injective, not_forall] at hf
      obtain ⟨a, b, hab, hne⟩ := hf
      exact ⟨a, b, hab, hne⟩
    rw [Matrix.det_zero_of_row_eq hne (by ext c; simp [hab]), mul_zero, norm_zero]
    positivity

/-- Lemma 7.2, second part: `v_3(det U_SS) ≥ V_n + 2` for `S ≠ {1, ..., n}`. -/
theorem norm_principalMinor_le_of_ne (hadb : ADBHyp) (S : Finset ℕ+) (hS : S ≠ Ipn S.card) :
    ‖principalMinor S‖ ≤ (3 : ℝ) ^ (-((Vn S.card : ℤ) + 2)) := by
  refine (norm_principalMinor_le hadb S).trans (zpow_le_zpow_right₀ (by norm_num) ?_)
  have h1 := psum_ge_of_ne S hS
  have h2 := Vn_eq S.card
  have h1' : ((S.card : ℤ) * (S.card + 1) + 2 ≤ 2 * (psum S : ℤ)) := by exact_mod_cast h1
  have h2' : (Vn S.card : ℤ) = S.card * (S.card + 1) + Wn S.card := by exact_mod_cast h2
  linarith

/-! ## Lemma 7.2, last part: the principal block -/

/-- Lemma 7.2, last part: `det U_{[1,n]} = D_1 ⋯ D_n`. -/
theorem principalMinor_Ipn (hadb : ADBHyp) (n : ℕ) :
    principalMinor (Ipn n) = ∏ i ∈ Finset.Icc 1 n, (D i : ℚ_[3]) := by
  classical
  have hK : ∀ s ∈ Ipn n, ∀ p : ℕ+, p ≤ s → p ∈ Ipn n := by
    intro s hs p hp
    rw [mem_Ipn] at hs ⊢
    exact ((PNat.coe_le_coe _ _).2 hp).trans hs
  have hL : (Matrix.of fun (a : Ipn n) (p : Ipn n) =>
      ((A ((a : ℕ+) : ℕ) ((p : ℕ+) : ℕ) * D ((p : ℕ+) : ℕ) : ℚ) : ℚ_[3])).IsLowerTriangular := by
    intro a p hap
    have hap' : ((a : ℕ+) : ℕ) < ((p : ℕ+) : ℕ) := hap
    rw [Matrix.of_apply, A_eq_zero_of_lt _ _ hap', zero_mul, Rat.cast_zero]
  have hU : (Matrix.of fun (p : Ipn n) (b : Ipn n) =>
      (B ((p : ℕ+) : ℕ) ((b : ℕ+) : ℕ) : ℚ_[3])).IsUpperTriangular := by
    intro p b hbp
    have hbp' : ((b : ℕ+) : ℕ) < ((p : ℕ+) : ℕ) := hbp
    rw [Matrix.of_apply, B_eq_zero_of_lt _ _ hbp', Rat.cast_zero]
  rw [principalMinor, minor_factor hadb (Ipn n) (Ipn n) hK, Matrix.det_mul,
    Matrix.det_of_isLowerTriangular _ hL, Matrix.det_of_isUpperTriangular hU]
  simp only [Matrix.of_apply]
  have h1 : ∀ a : Ipn n, ((A ((a : ℕ+) : ℕ) ((a : ℕ+) : ℕ) * D ((a : ℕ+) : ℕ) : ℚ) : ℚ_[3]) =
      (D ((a : ℕ+) : ℕ) : ℚ_[3]) := by
    intro a
    rw [A_self _ (a : ℕ+).pos, one_mul]
  have h2 : ∀ a : Ipn n, (B ((a : ℕ+) : ℕ) ((a : ℕ+) : ℕ) : ℚ_[3]) = 1 := by
    intro a
    rw [B_self _ (a : ℕ+).pos, Rat.cast_one]
  simp only [h1, h2, Finset.prod_const_one, mul_one]
  rw [Finset.prod_coe_sort (Ipn n) (fun s : ℕ+ => (D (s : ℕ) : ℚ_[3])), Ipn, Finset.prod_map]
  simp only [Function.Embedding.coeFn_mk, Nat.succPNat_coe]
  rw [Finset.range_eq_Ico, Finset.prod_Ico_add' (fun i => (D i : ℚ_[3])) 0 n 1, zero_add,
    Finset.Ico_add_one_right_eq_Icc]

/-- `v_3(det U_{[1,n]}) = V_n`. -/
theorem norm_principalMinor_Ipn (hadb : ADBHyp) (n : ℕ) :
    ‖principalMinor (Ipn n)‖ = (3 : ℝ) ^ (-(Vn n : ℤ)) := by
  rw [principalMinor_Ipn hadb n, norm_prod, Finset.prod_congr rfl (fun i _ => norm_D i),
    prod_zpow_three, Vn, Nat.cast_sum, Finset.sum_neg_distrib]

/-! ## Assembly -/

/-- The `Summable` conjunct, from Lemma 3.1 (a) alone. -/
theorem summable_minors (n : ℕ) :
    Summable (fun S : {S : Finset ℕ+ // S.card = n} => principalMinor S.1) := by
  refine summable_minor_of_row_bound (fun i j => ((u i j : ℚ) : ℚ_[3])) (fun i j => ?_) n
  calc ‖((u i j : ℚ) : ℚ_[3])‖ ≤ (3 : ℝ) ^ (-(((i : ℕ) : ℤ) + ((j : ℕ) : ℤ))) := norm_u_le i j
    _ ≤ (3 : ℝ) ^ (-((i : ℕ) : ℤ)) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ = (3⁻¹ : ℝ) ^ (i : ℕ) := by rw [zpow_neg, zpow_natCast, inv_pow]

/-- The Newton step: Theorem 2.3 implies the conclusion of Corollary 7.1 for every `n`. -/
theorem newton (hadb : ADBHyp) (n : ℕ) :
    Summable (fun S : {S : Finset ℕ+ // S.card = n} => principalMinor S.1) ∧ c n ≠ 0 ∧
      Padic.valuation (c n) = ∑ i ∈ Finset.Icc 1 n, (slope i : ℤ) := by
  have hs := summable_minors n
  let i₀ : {S : Finset ℕ+ // S.card = n} := ⟨Ipn n, card_Ipn n⟩
  have hV : (Vn n : ℤ) = ∑ i ∈ Finset.Icc 1 n, (slope i : ℤ) := by
    rw [Vn]; push_cast; rfl
  have h0 : ‖principalMinor i₀.1‖ = (3 : ℝ) ^ (-(Vn n : ℤ)) := norm_principalMinor_Ipn hadb n
  have hoff : ∀ S ≠ i₀, ‖principalMinor S.1‖ ≤ (3 : ℝ) ^ (-((Vn n : ℤ) + 1)) := by
    intro S hS
    have hne : S.1 ≠ Ipn S.1.card := by
      rw [S.2]
      intro h
      exact hS (Subtype.ext h)
    calc ‖principalMinor S.1‖ ≤ (3 : ℝ) ^ (-((Vn S.1.card : ℤ) + 2)) :=
          norm_principalMinor_le_of_ne hadb S.1 hne
      _ = (3 : ℝ) ^ (-((Vn n : ℤ) + 2)) := by rw [S.2]
      _ ≤ (3 : ℝ) ^ (-((Vn n : ℤ) + 1)) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  obtain ⟨hne, hval⟩ := valuation_tsum_of_dominant hs i₀ h0 hoff
  exact ⟨hs, hne, by rw [c, hval, hV]⟩

end CalegariSlopes.Newton
