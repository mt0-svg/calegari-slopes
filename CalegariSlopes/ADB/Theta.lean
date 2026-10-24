/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.ADB.Defs

@[expose] public section

/-!
# Euler operators, box supports and the classes `Frac e dx dy` (for Lemma 5.3)

For the proof of Lemma 5.3 (the series of type `(e, d)` there are `Frac e d d`). On `MvPowerSeries (Fin 2) ℚ`
(variables `x = X 0`, `y = X 1`): coefficient multipliers `mulC`, the Euler operators `θ_x = x ∂_x`,
`θ_y = y ∂_y`, the property `Box dx dy f` (no monomial `x^a y^b` with `a > dx` or `b > dy`) and the class
`Frac e dx dy` of the series `f` with `f Q^e` a polynomial in the box `[0, dx] × [0, dy]`. A `θ` maps `Frac e dx dy`
into `Frac (e+1) (dx+3) (dy+3)`, and a series of `Frac e dx dy` whose coefficients vanish on that box is zero.
-/

open MvPowerSeries

namespace CalegariSlopes.ADB

/-- The exponent of `x^i y^j`. -/
noncomputable abbrev ex (i j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j

/-- `mulC φ f`: the coefficient of `x^a y^b` of `f` multiplied by `φ a b`. -/
noncomputable def mulC (φ : ℕ → ℕ → ℚ) (f : MvPowerSeries (Fin 2) ℚ) : MvPowerSeries (Fin 2) ℚ :=
  fun n => φ (n 0) (n 1) * coeff n f

/-- The Euler operator `θ_x = x ∂/∂x`. -/
noncomputable def thX (f : MvPowerSeries (Fin 2) ℚ) : MvPowerSeries (Fin 2) ℚ := mulC (fun a _ => (a : ℚ)) f

/-- The Euler operator `θ_y = y ∂/∂y`. -/
noncomputable def thY (f : MvPowerSeries (Fin 2) ℚ) : MvPowerSeries (Fin 2) ℚ := mulC (fun _ b => (b : ℚ)) f

/-- `f` has no monomial `x^a y^b` with `a > dx` or `b > dy`. -/
def Box (dx dy : ℕ) (f : MvPowerSeries (Fin 2) ℚ) : Prop :=
  ∀ n : Fin 2 →₀ ℕ, (dx < n 0 ∨ dy < n 1) → coeff n f = 0

/-- `f Q^e` is a polynomial supported in the box `[0, dx] × [0, dy]`. -/
def Frac (e dx dy : ℕ) (f : MvPowerSeries (Fin 2) ℚ) : Prop := Box dx dy (f * Q ^ e)

theorem coeff_mulC (φ : ℕ → ℕ → ℚ) (f : MvPowerSeries (Fin 2) ℚ) (n : Fin 2 →₀ ℕ) :
    coeff n (mulC φ f) = φ (n 0) (n 1) * coeff n f := rfl

theorem ex_apply_zero (i j : ℕ) : ex i j 0 = i := by simp [ex]

theorem ex_apply_one (i j : ℕ) : ex i j 1 = j := by simp [ex]

theorem eq_ex (n : Fin 2 →₀ ℕ) : n = ex (n 0) (n 1) := by
  ext v; fin_cases v <;> simp [ex]

/-! ## Coefficient multipliers -/

theorem mulC_mulC (φ ψ : ℕ → ℕ → ℚ) (f : MvPowerSeries (Fin 2) ℚ) :
    mulC φ (mulC ψ f) = mulC (fun a b => φ a b * ψ a b) f := by
  ext n
  simp only [coeff_mulC]
  ring

theorem mulC_add_fun (φ ψ : ℕ → ℕ → ℚ) (f : MvPowerSeries (Fin 2) ℚ) :
    mulC (fun a b => φ a b + ψ a b) f = mulC φ f + mulC ψ f := by
  ext n
  simp [coeff_mulC, add_mul]

theorem mulC_sub_fun (φ ψ : ℕ → ℕ → ℚ) (f : MvPowerSeries (Fin 2) ℚ) :
    mulC (fun a b => φ a b - ψ a b) f = mulC φ f - mulC ψ f := by
  ext n
  simp only [coeff_mulC, map_sub]
  ring

theorem mulC_const (c : ℚ) (f : MvPowerSeries (Fin 2) ℚ) : mulC (fun _ _ => c) f = C c * f := by
  ext n
  simp [coeff_mulC, MvPowerSeries.coeff_C_mul]

theorem mulC_add (φ : ℕ → ℕ → ℚ) (f g : MvPowerSeries (Fin 2) ℚ) :
    mulC φ (f + g) = mulC φ f + mulC φ g := by
  ext n
  simp [coeff_mulC, map_add, mul_add]

/-- `mulC` by a sum of functions over a finset. -/
theorem mulC_sum_fun {ι : Type*} (s : Finset ι) (φ : ι → ℕ → ℕ → ℚ) (f : MvPowerSeries (Fin 2) ℚ) :
    mulC (fun a b => ∑ k ∈ s, φ k a b) f = ∑ k ∈ s, mulC (φ k) f := by
  ext n
  simp [coeff_mulC, Finset.sum_mul]

/-- Leibniz rule for `θ_x`. -/
theorem thX_mul (f g : MvPowerSeries (Fin 2) ℚ) : thX (f * g) = thX f * g + f * thX g := by
  ext n
  simp only [thX, coeff_mulC, MvPowerSeries.coeff_mul, map_add]
  rw [Finset.mul_sum]
  have hsum : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (n 0 : ℚ) * (coeff p.1 f * coeff p.2 g)) =
             (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ((p.1 0 : ℚ) + (p.2 0 : ℚ)) * (coeff p.1 f * coeff p.2 g)) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have h := (Finset.HasAntidiagonal.mem_antidiagonal.mp hp)
    have h1 : (n : Fin 2 →₀ ℕ) 0 = (p.1 : Fin 2 →₀ ℕ) 0 + (p.2 : Fin 2 →₀ ℕ) 0 := by
      simpa [Finsupp.add_apply] using (congrArg (fun q : Fin 2 →₀ ℕ => q 0) h).symm
    rw [h1, Nat.cast_add]
  rw [hsum]
  simp only [add_mul, Finset.sum_add_distrib]
  simp [mul_comm, mul_left_comm]

/-- Leibniz rule for `θ_y`. -/
theorem thY_mul (f g : MvPowerSeries (Fin 2) ℚ) : thY (f * g) = thY f * g + f * thY g := by
  ext n
  simp only [thY, coeff_mulC, MvPowerSeries.coeff_mul, map_add]
  rw [Finset.mul_sum]
  have hsum : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (n 1 : ℚ) * (coeff p.1 f * coeff p.2 g)) =
             (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ((p.1 1 : ℚ) + (p.2 1 : ℚ)) * (coeff p.1 f * coeff p.2 g)) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have h := (Finset.HasAntidiagonal.mem_antidiagonal.mp hp)
    have h1 : (n : Fin 2 →₀ ℕ) 1 = (p.1 : Fin 2 →₀ ℕ) 1 + (p.2 : Fin 2 →₀ ℕ) 1 := by
      simpa [Finsupp.add_apply] using (congrArg (fun q : Fin 2 →₀ ℕ => q 1) h).symm
    rw [h1, Nat.cast_add]
  rw [hsum]
  simp only [add_mul, Finset.sum_add_distrib]
  simp [mul_comm, mul_left_comm]

/-- `θ_x` of a power. -/
theorem thX_pow (f : MvPowerSeries (Fin 2) ℚ) (e : ℕ) :
    thX (f ^ (e + 1)) = ((e : ℚ) + 1) • (f ^ e * thX f) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, thX_mul, ih, smul_eq_C_mul, smul_eq_C_mul]
    push_cast
    simp only [map_add, map_one]
    ring

/-- `θ_y` of a power. -/
theorem thY_pow (f : MvPowerSeries (Fin 2) ℚ) (e : ℕ) :
    thY (f ^ (e + 1)) = ((e : ℚ) + 1) • (f ^ e * thY f) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, thY_mul, ih, smul_eq_C_mul, smul_eq_C_mul]
    push_cast
    simp only [map_add, map_one]
    ring

/-! ## Box supports -/

theorem Box_mono {dx dy dx' dy' : ℕ} {f : MvPowerSeries (Fin 2) ℚ} (hx : dx ≤ dx') (hy : dy ≤ dy')
    (h : Box dx dy f) : Box dx' dy' f := by
  intro n hn
  apply h n
  rcases hn with (hnx | hny)
  · left; exact hx.trans_lt hnx
  · right; exact hy.trans_lt hny

theorem Box_add {dx dy : ℕ} {f g : MvPowerSeries (Fin 2) ℚ} (hf : Box dx dy f) (hg : Box dx dy g) :
    Box dx dy (f + g) := by
  intro n hn
  simp [hf n hn, hg n hn]

theorem Box_sub {dx dy : ℕ} {f g : MvPowerSeries (Fin 2) ℚ} (hf : Box dx dy f) (hg : Box dx dy g) :
    Box dx dy (f - g) := by
  intro n hn
  rw [map_sub (coeff n), hf n hn, hg n hn, sub_self]

theorem Box_smul {dx dy : ℕ} (c : ℚ) {f : MvPowerSeries (Fin 2) ℚ} (hf : Box dx dy f) :
    Box dx dy (c • f) := by
  intro n hn
  rw [MvPowerSeries.coeff_smul, hf n hn, mul_zero]

theorem Box_C_mul {dx dy : ℕ} (c : ℚ) {f : MvPowerSeries (Fin 2) ℚ} (hf : Box dx dy f) :
    Box dx dy (C c * f) := by
  intro n hn
  rw [MvPowerSeries.coeff_C_mul]
  rcases hn with (h | h)
  · have hzero := hf n (Or.inl h)
    simp [hzero]
  · have hzero := hf n (Or.inr h)
    simp [hzero]

theorem Box_mulC {dx dy : ℕ} (φ : ℕ → ℕ → ℚ) {f : MvPowerSeries (Fin 2) ℚ} (hf : Box dx dy f) :
    Box dx dy (mulC φ f) := by
  intro n hn
  rw [coeff_mulC, hf n hn, mul_zero]

/-- The supports add up under multiplication. -/
theorem Box_mul {dx dy ex' ey : ℕ} {f g : MvPowerSeries (Fin 2) ℚ} (hf : Box dx dy f)
    (hg : Box ex' ey g) : Box (dx + ex') (dy + ey) (f * g) := by
  intro n hn
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have hp_sum : p.1 + p.2 = n := by
    rwa [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hsum0 : p.1 0 + p.2 0 = n 0 := by
    simpa [Finsupp.add_apply] using congrArg (fun x : Fin 2 →₀ ℕ => x 0) hp_sum
  have hsum1 : p.1 1 + p.2 1 = n 1 := by
    simpa [Finsupp.add_apply] using congrArg (fun x : Fin 2 →₀ ℕ => x 1) hp_sum
  rcases hn with (hn | hn)
  · -- case (dx + ex') < n 0
    have h_cases : dx < p.1 0 ∨ ex' < p.2 0 := by
      omega
    rcases h_cases with (h | h)
    · have hf0 : coeff p.1 f = 0 := hf p.1 (Or.inl h)
      simp [hf0]
    · have hg0 : coeff p.2 g = 0 := hg p.2 (Or.inl h)
      simp [hg0]
  · -- case (dy + ey) < n 1
    have h_cases : dy < p.1 1 ∨ ey < p.2 1 := by
      omega
    rcases h_cases with (h | h)
    · have hf1 : coeff p.1 f = 0 := hf p.1 (Or.inr h)
      simp [hf1]
    · have hg1 : coeff p.2 g = 0 := hg p.2 (Or.inr h)
      simp [hg1]

theorem Box_one : Box 0 0 (1 : MvPowerSeries (Fin 2) ℚ) := by
  intro n hn
  rcases hn with (hx | hy)
  · have hn0 : n ≠ 0 := by
      intro heq
      have hzero : n 0 = 0 := by simp [heq]
      linarith
    rw [MvPowerSeries.coeff_one]
    simp [hn0]
  · have hn0 : n ≠ 0 := by
      intro heq
      have hzero : n 1 = 0 := by simp [heq]
      linarith
    rw [MvPowerSeries.coeff_one]
    simp [hn0]

theorem Box_X0 : Box 1 0 (X 0 : MvPowerSeries (Fin 2) ℚ) := by
  intro n hn
  simp [MvPowerSeries.coeff_X]
  by_cases h : n = Finsupp.single 0 1
  · subst h
    simp at hn
  · simp [h]

theorem Box_X1 : Box 0 1 (X 1 : MvPowerSeries (Fin 2) ℚ) := by
  intro n hn
  rw [MvPowerSeries.coeff_X]
  split_ifs with h
  · rcases hn with (hx | hy)
    · have h0 : (Finsupp.single 1 1 : Fin 2 →₀ ℕ) 0 = 0 := by simp
      rw [h] at hx
      rw [h0] at hx
      exact absurd hx (Nat.lt_irrefl _)
    · have h1 : (Finsupp.single 1 1 : Fin 2 →₀ ℕ) 1 = 1 := by simp
      rw [h] at hy
      rw [h1] at hy
      exact absurd hy (Nat.lt_irrefl _)
  · rfl

theorem Box_X_pow (a b : ℕ) : Box a b (X 0 ^ a * X 1 ^ b : MvPowerSeries (Fin 2) ℚ) := by
  intro n hn
  have hmono : (X 0 ^ a * X 1 ^ b : MvPowerSeries (Fin 2) ℚ) = MvPowerSeries.monomial (ex a b) (1 : ℚ) := by
    simp [MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, ex]
  rw [hmono, MvPowerSeries.coeff_monomial]
  split
  · rename_i h
    rcases hn with (h0 | h1)
    · have hval : (ex a b) 0 = a := by simp [ex]
      have hn0 : n 0 = a := by simp [h, hval]
      rw [hn0] at h0
      exact (lt_irrefl _ h0).elim
    · have hval : (ex a b) 1 = b := by simp [ex]
      have hn1 : n 1 = b := by simp [h, hval]
      rw [hn1] at h1
      exact (lt_irrefl _ h1).elim
  · rfl

theorem Box_Q : Box 3 3 Q := by
  have hQ : Q = 1 - C 270 * (X 0 ^ 1 * X 1 ^ 1) - C 972 * (X 0 ^ 2 * X 1 ^ 1) - C 972 * (X 0 ^ 1 * X 1 ^ 2)
      - C 729 * (X 0 ^ 3 * X 1 ^ 1) - C 729 * (X 0 ^ 2 * X 1 ^ 2) - C 729 * (X 0 ^ 1 * X 1 ^ 3) := by
    simp only [Q, x, y, map_ofNat]
    ring
  have hm : ∀ a b : ℕ, a ≤ 3 → b ≤ 3 → ∀ c : ℚ, Box 3 3 (C c * (X 0 ^ a * X 1 ^ b : MvPowerSeries (Fin 2) ℚ)) :=
    fun a b ha hb c => Box_C_mul c (Box_mono ha hb (Box_X_pow a b))
  rw [hQ]
  refine Box_sub (Box_sub (Box_sub (Box_sub (Box_sub (Box_sub (Box_mono (by norm_num) (by norm_num) Box_one)
    (hm 1 1 (by norm_num) (by norm_num) _)) (hm 2 1 (by norm_num) (by norm_num) _))
    (hm 1 2 (by norm_num) (by norm_num) _)) (hm 3 1 (by norm_num) (by norm_num) _))
    (hm 2 2 (by norm_num) (by norm_num) _)) (hm 1 3 (by norm_num) (by norm_num) _)

theorem Box_N : Box 3 3 N := by
  unfold N
  have h : (90 : MvPowerSeries (Fin 2) ℚ) * x * y + (324 : MvPowerSeries (Fin 2) ℚ) * x ^ 2 * y +
      (648 : MvPowerSeries (Fin 2) ℚ) * x * y ^ 2 + (243 : MvPowerSeries (Fin 2) ℚ) * x ^ 3 * y +
      (486 : MvPowerSeries (Fin 2) ℚ) * x ^ 2 * y ^ 2 + (729 : MvPowerSeries (Fin 2) ℚ) * x * y ^ 3 =
      C (90 : ℚ) * (X 0 ^ 1 * X 1 ^ 1) + C (324 : ℚ) * (X 0 ^ 2 * X 1 ^ 1) +
      C (648 : ℚ) * (X 0 ^ 1 * X 1 ^ 2) + C (243 : ℚ) * (X 0 ^ 3 * X 1 ^ 1) +
      C (486 : ℚ) * (X 0 ^ 2 * X 1 ^ 2) + C (729 : ℚ) * (X 0 ^ 1 * X 1 ^ 3) := by
    unfold x y
    ring_nf
    rfl
  rw [h]
  apply Box_add
  · apply Box_add
    · apply Box_add
      · apply Box_add
        · apply Box_add
          · have hx := Box_X_pow 1 1
            have hc := Box_C_mul (90 : ℚ) hx
            exact Box_mono (by decide) (by decide) hc
          · have hx := Box_X_pow 2 1
            have hc := Box_C_mul (324 : ℚ) hx
            exact Box_mono (by decide) (by decide) hc
        · have hx := Box_X_pow 1 2
          have hc := Box_C_mul (648 : ℚ) hx
          exact Box_mono (by decide) (by decide) hc
      · have hx := Box_X_pow 3 1
        have hc := Box_C_mul (243 : ℚ) hx
        exact Box_mono (by decide) (by decide) hc
    · have hx := Box_X_pow 2 2
      have hc := Box_C_mul (486 : ℚ) hx
      exact Box_mono (by decide) (by decide) hc
  · have hx := Box_X_pow 1 3
    have hc := Box_C_mul (729 : ℚ) hx
    exact Box_mono (by decide) (by decide) hc

/-- A series in the box whose coefficients vanish on the box is zero. -/
theorem eq_zero_of_Box {dx dy : ℕ} {f : MvPowerSeries (Fin 2) ℚ} (hf : Box dx dy f)
    (h0 : ∀ i j, i ≤ dx → j ≤ dy → coeff (ex i j) f = 0) : f = 0 := by
  ext n
  rw [eq_ex n]
  by_cases h : n 0 ≤ dx ∧ n 1 ≤ dy
  · rcases h with ⟨hn0, hn1⟩
    rw [h0 (n 0) (n 1) hn0 hn1, MvPowerSeries.coeff_zero]
  · rw [not_and_or] at h
    have h' : dx < (ex (n 0) (n 1)) 0 ∨ dy < (ex (n 0) (n 1)) 1 := by
      rw [ex_apply_zero, ex_apply_one]
      rcases h with (hx | hy)
      · left; exact Nat.lt_of_not_ge hx
      · right; exact Nat.lt_of_not_ge hy
    have hzero : coeff (ex (n 0) (n 1)) f = 0 := hf (ex (n 0) (n 1)) h'
    rw [hzero, MvPowerSeries.coeff_zero]

/-! ## The classes `Frac e dx dy` -/

theorem Frac_mono {e dx dy dx' dy' : ℕ} {f : MvPowerSeries (Fin 2) ℚ} (hx : dx ≤ dx') (hy : dy ≤ dy')
    (h : Frac e dx dy f) : Frac e dx' dy' f := by
  intro n hn
  rcases hn with (hnx | hny)
  · apply h n (Or.inl (lt_of_le_of_lt hx hnx))
  · apply h n (Or.inr (lt_of_le_of_lt hy hny))

theorem Frac_add {e dx dy : ℕ} {f g : MvPowerSeries (Fin 2) ℚ} (hf : Frac e dx dy f)
    (hg : Frac e dx dy g) : Frac e dx dy (f + g) := by
  unfold Frac
  rw [add_mul]
  exact Box_add hf hg

theorem Frac_sub {e dx dy : ℕ} {f g : MvPowerSeries (Fin 2) ℚ} (hf : Frac e dx dy f)
    (hg : Frac e dx dy g) : Frac e dx dy (f - g) := by
  dsimp [Frac] at hf hg ⊢
  rw [sub_mul]
  exact Box_sub hf hg

theorem Frac_smul {e dx dy : ℕ} (c : ℚ) {f : MvPowerSeries (Fin 2) ℚ} (hf : Frac e dx dy f) :
    Frac e dx dy (c • f) := by
  intro n hn
  have h := hf n hn
  calc
    coeff n ((c • f) * Q ^ e) = coeff n (c • (f * Q ^ e)) := by rw [smul_mul_assoc]
    _ = c * coeff n (f * Q ^ e) := by rw [MvPowerSeries.coeff_smul]
    _ = c * 0 := by rw [h]
    _ = 0 := by ring

theorem box_add {dx dy : ℕ} {f g : MvPowerSeries (Fin 2) ℚ} (hf : Box dx dy f) (hg : Box dx dy g) :
    Box dx dy (f + g) := by
  intro n hn
  rw [(MvPowerSeries.coeff n).map_add, hf n hn, hg n hn, add_zero]

theorem box_zero (dx dy : ℕ) : Box dx dy (0 : MvPowerSeries (Fin 2) ℚ) := by
  intro n hn
  simp

theorem frac_add {e dx dy : ℕ} {f g : MvPowerSeries (Fin 2) ℚ} (hf : Frac e dx dy f) (hg : Frac e dx dy g) :
    Frac e dx dy (f + g) := by
  unfold Frac at hf hg ⊢
  rw [add_mul]
  exact box_add hf hg


theorem Frac_sum {ι : Type*} (s : Finset ι) {e dx dy : ℕ} (f : ι → MvPowerSeries (Fin 2) ℚ)
    (hf : ∀ k ∈ s, Frac e dx dy (f k)) : Frac e dx dy (∑ k ∈ s, f k) := by
  classical
    induction' s using Finset.induction with a s has IH
    · -- empty sum
      simp [Frac, box_zero]
    · -- insert a into s
      rw [Finset.sum_insert has]
      apply frac_add
      · exact hf a (Finset.mem_insert_self a s)
      · exact IH fun k hk => hf k (Finset.mem_insert_of_mem hk)

/-- One more factor `Q`. -/
theorem Frac_up {e dx dy : ℕ} {f : MvPowerSeries (Fin 2) ℚ} (h : Frac e dx dy f) :
    Frac (e + 1) (dx + 3) (dy + 3) f := by
  unfold Frac at h ⊢
  have hQ : Box 3 3 Q := Box_Q
  simpa [pow_succ, mul_assoc] using Box_mul h hQ

/-- `Frac e dx dy ⊆ Frac (e + k) (dx + 3k) (dy + 3k)`. -/
theorem Frac_up' {e dx dy : ℕ} (k : ℕ) {f : MvPowerSeries (Fin 2) ℚ} (h : Frac e dx dy f) :
    Frac (e + k) (dx + 3 * k) (dy + 3 * k) f := by
  induction' k with k ih
  · simpa using h
  · have h1 : e + (k + 1) = (e + k) + 1 := by omega
    have h2 : dx + 3 * (k + 1) = (dx + 3 * k) + 3 := by omega
    have h3 : dy + 3 * (k + 1) = (dy + 3 * k) + 3 := by omega
    rw [h1, h2, h3]
    exact Frac_up ih

theorem Frac_mul_X_pow {e dx dy : ℕ} (a b : ℕ) {f : MvPowerSeries (Fin 2) ℚ} (h : Frac e dx dy f) :
    Frac e (dx + a) (dy + b) (X 0 ^ a * X 1 ^ b * f) := by
  unfold Frac
  have hbox := Box_mul (Box_X_pow a b) h
  simpa [add_comm, mul_assoc] using hbox

/-- `θ_x` raises `e` by one and the box by three. -/
theorem Frac_thX {e dx dy : ℕ} {f : MvPowerSeries (Fin 2) ℚ} (h : Frac e dx dy f) :
    Frac (e + 1) (dx + 3) (dy + 3) (thX f) := by
  dsimp [Frac] at h ⊢
  -- h : Box dx dy (f * Q ^ e)
  -- Goal: Box (dx + 3) (dy + 3) ((thX f) * Q ^ (e + 1))
  have hQ : Box 3 3 Q := Box_Q
  have hQthX : Box 3 3 (thX Q) := Box_mulC (fun a _ => (a : ℚ)) hQ
  have h_thX_one : thX (1 : MvPowerSeries (Fin 2) ℚ) = 0 := by
    ext n
    simp [thX, coeff_mulC, MvPowerSeries.coeff_one]
    intro h
    subst h
    simp
  have hkey : thX f * Q ^ (e + 1) = thX (f * Q ^ e) * Q - (e : ℚ) • ((f * Q ^ e) * thX Q) := by
    rcases Nat.eq_zero_or_pos e with (rfl | hpos)
    · -- e = 0
      simp
    · -- e = k + 1 for some k
      rcases Nat.exists_eq_succ_of_ne_zero hpos.ne' with ⟨k, rfl⟩
      have hcalc : thX (f * Q ^ (k + 1)) = thX f * Q ^ (k + 1) + f * thX (Q ^ (k + 1)) := thX_mul f (Q ^ (k + 1))
      have hpow : thX (Q ^ (k + 1)) = ((k : ℚ) + 1) • (Q ^ k * thX Q) := thX_pow Q k
      calc
        thX f * Q ^ (k + 1 + 1) = (thX f * Q ^ (k + 1)) * Q := by ring
        _ = (thX (f * Q ^ (k + 1)) - f * thX (Q ^ (k + 1))) * Q := by
          rw [hcalc]
          ring
        _ = thX (f * Q ^ (k + 1)) * Q - f * thX (Q ^ (k + 1)) * Q := by ring
        _ = thX (f * Q ^ (k + 1)) * Q - f * (((k : ℚ) + 1) • (Q ^ k * thX Q)) * Q := by rw [hpow]
        _ = thX (f * Q ^ (k + 1)) * Q - ((k : ℚ) + 1) • (f * (Q ^ k * thX Q) * Q) := by
          simp [MvPowerSeries.smul_eq_C_mul, mul_comm, mul_left_comm]
        _ = thX (f * Q ^ (k + 1)) * Q - ((k : ℚ) + 1) • (f * Q ^ k * thX Q * Q) := by ring
        _ = thX (f * Q ^ (k + 1)) * Q - ((k : ℚ) + 1) • (f * Q ^ k * Q * thX Q) := by ring
        _ = thX (f * Q ^ (k + 1)) * Q - ((k + 1 : ℕ) : ℚ) • (f * Q ^ (k + 1) * thX Q) := by
          push_cast
          ring
        _ = thX (f * Q ^ (k + 1)) * Q - ((k + 1 : ℕ) : ℚ) • ((f * Q ^ (k + 1)) * thX Q) := by ring
  rw [hkey]
  have hP : Box dx dy (f * Q ^ e) := h
  have hthXP : Box dx dy (thX (f * Q ^ e)) := Box_mulC (fun a _ => (a : ℚ)) hP
  have hprod1 : Box (dx + 3) (dy + 3) (thX (f * Q ^ e) * Q) := Box_mul hthXP hQ
  have hprod2 : Box (dx + 3) (dy + 3) ((f * Q ^ e) * thX Q) := Box_mul hP hQthX
  have hsmul : Box (dx + 3) (dy + 3) ((e : ℚ) • ((f * Q ^ e) * thX Q)) := Box_smul (e : ℚ) hprod2
  exact Box_sub hprod1 hsmul

/-- `θ_y` raises `e` by one and the box by three. -/
theorem Frac_thY {e dx dy : ℕ} {f : MvPowerSeries (Fin 2) ℚ} (h : Frac e dx dy f) :
    Frac (e + 1) (dx + 3) (dy + 3) (thY f) := by
  dsimp [Frac] at h ⊢
  -- h : Box dx dy (f * Q ^ e)
  -- Goal: Box (dx + 3) (dy + 3) ((thY f) * Q ^ (e + 1))
  have hQ : Box 3 3 Q := Box_Q
  have hQthY : Box 3 3 (thY Q) := Box_mulC (fun _ b => (b : ℚ)) hQ
  have h_thY_one : thY (1 : MvPowerSeries (Fin 2) ℚ) = 0 := by
    ext n
    simp [thY, coeff_mulC, MvPowerSeries.coeff_one]
    intro h
    subst h
    simp
  have hkey : thY f * Q ^ (e + 1) = thY (f * Q ^ e) * Q - (e : ℚ) • ((f * Q ^ e) * thY Q) := by
    rcases Nat.eq_zero_or_pos e with (rfl | hpos)
    · -- e = 0
      simp
    · -- e = k + 1 for some k
      rcases Nat.exists_eq_succ_of_ne_zero hpos.ne' with ⟨k, rfl⟩
      have hcalc : thY (f * Q ^ (k + 1)) = thY f * Q ^ (k + 1) + f * thY (Q ^ (k + 1)) := thY_mul f (Q ^ (k + 1))
      have hpow : thY (Q ^ (k + 1)) = ((k : ℚ) + 1) • (Q ^ k * thY Q) := thY_pow Q k
      calc
        thY f * Q ^ (k + 1 + 1) = (thY f * Q ^ (k + 1)) * Q := by ring
        _ = (thY (f * Q ^ (k + 1)) - f * thY (Q ^ (k + 1))) * Q := by
          rw [hcalc]
          ring
        _ = thY (f * Q ^ (k + 1)) * Q - f * thY (Q ^ (k + 1)) * Q := by ring
        _ = thY (f * Q ^ (k + 1)) * Q - f * (((k : ℚ) + 1) • (Q ^ k * thY Q)) * Q := by rw [hpow]
        _ = thY (f * Q ^ (k + 1)) * Q - ((k : ℚ) + 1) • (f * (Q ^ k * thY Q) * Q) := by
          simp [MvPowerSeries.smul_eq_C_mul, mul_comm, mul_left_comm]
        _ = thY (f * Q ^ (k + 1)) * Q - ((k : ℚ) + 1) • (f * Q ^ k * thY Q * Q) := by ring
        _ = thY (f * Q ^ (k + 1)) * Q - ((k : ℚ) + 1) • (f * Q ^ k * Q * thY Q) := by ring
        _ = thY (f * Q ^ (k + 1)) * Q - ((k + 1 : ℕ) : ℚ) • (f * Q ^ (k + 1) * thY Q) := by
          push_cast
          ring
        _ = thY (f * Q ^ (k + 1)) * Q - ((k + 1 : ℕ) : ℚ) • ((f * Q ^ (k + 1)) * thY Q) := by ring
  rw [hkey]
  have hP : Box dx dy (f * Q ^ e) := h
  have hthYP : Box dx dy (thY (f * Q ^ e)) := Box_mulC (fun _ b => (b : ℚ)) hP
  have hprod1 : Box (dx + 3) (dy + 3) (thY (f * Q ^ e) * Q) := Box_mul hthYP hQ
  have hprod2 : Box (dx + 3) (dy + 3) ((f * Q ^ e) * thY Q) := Box_mul hP hQthY
  have hsmul : Box (dx + 3) (dy + 3) ((e : ℚ) • ((f * Q ^ e) * thY Q)) := Box_smul (e : ℚ) hprod2
  exact Box_sub hprod1 hsmul

/-- A polynomial multiplier of degree `≤ n` in the first exponent acts like `n` operators `θ_x`. -/
theorem Frac_mulC_polyX {e dx dy n : ℕ} (P : Polynomial ℚ) (hP : P.natDegree ≤ n)
    {f : MvPowerSeries (Fin 2) ℚ} (h : Frac e dx dy f) :
    Frac (e + n) (dx + 3 * n) (dy + 3 * n) (mulC (fun a _ => P.eval (a : ℚ)) f) := by
  induction' n with n ih generalizing P
  · -- n = 0
    have h0 : P.natDegree = 0 := by omega
    have hdeg : P.degree ≤ 0 :=
      (Polynomial.natDegree_eq_zero_iff_degree_le_zero.mp h0)
    have hP_eq : P = Polynomial.C (P.coeff 0) :=
      (Polynomial.degree_le_zero_iff.mp hdeg)
    have h_mulC : mulC (fun a _ => P.eval (a : ℚ)) f = C (P.coeff 0) * f := by
      rw [hP_eq]
      ext n
      simp [coeff_mulC, MvPowerSeries.coeff_C_mul]
    rw [h_mulC]
    have h_smul : Frac e dx dy (C (P.coeff 0) * f) := by
      rw [← MvPowerSeries.smul_eq_C_mul]
      exact Frac_smul (P.coeff 0) h
    simpa [add_zero, mul_zero] using h_smul
  · -- n → n+1
    have hP_le : P.natDegree ≤ n + 1 := hP
    have h_divX_deg : P.divX.natDegree ≤ n := by
      rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
      omega
    have h_decomp : P = Polynomial.C (P.coeff 0) + Polynomial.X * P.divX := by
      calc
        P = Polynomial.X * P.divX + Polynomial.C (P.coeff 0) := (Polynomial.X_mul_divX_add P).symm
        _ = Polynomial.C (P.coeff 0) + Polynomial.X * P.divX := add_comm _ _
    have h_eval : ∀ a : ℕ, P.eval (a : ℚ) = P.coeff 0 + (a : ℚ) * P.divX.eval (a : ℚ) := by
      intro a
      have h := congrArg (fun q : Polynomial ℚ => q.eval (a : ℚ)) h_decomp
      simpa [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X] using h
    have h_mulC_eq : mulC (fun a _ => P.eval (a : ℚ)) f =
        C (P.coeff 0) * f + thX (mulC (fun a _ => P.divX.eval (a : ℚ)) f) := by
      ext n
      simp only [coeff_mulC, thX, coeff_mulC, MvPowerSeries.coeff_C_mul, map_add]
      rw [h_eval (n 0)]
      ring_nf
    rw [h_mulC_eq]
    have hC : Frac (e + n + 1) (dx + 3 * n + 3) (dy + 3 * n + 3) (C (P.coeff 0) * f) := by
      have h_base : Frac (e + n) (dx + 3 * n) (dy + 3 * n) f := Frac_up' n h
      have h_smul : Frac (e + n) (dx + 3 * n) (dy + 3 * n) ((P.coeff 0) • f) :=
        Frac_smul (P.coeff 0) h_base
      have h_up : Frac ((e + n) + 1) ((dx + 3 * n) + 3 * 1) ((dy + 3 * n) + 3 * 1)
          ((P.coeff 0) • f) := Frac_up' 1 h_smul
      simpa [MvPowerSeries.smul_eq_C_mul, mul_one] using h_up
    have h_thX : Frac (e + n + 1) (dx + 3 * n + 3) (dy + 3 * n + 3)
        (thX (mulC (fun a _ => P.divX.eval (a : ℚ)) f)) := by
      have ih_divX := ih P.divX h_divX_deg
      have h_thX' := Frac_thX ih_divX
      simpa [add_assoc] using h_thX'
    have hgoal := Frac_add hC h_thX
    have h_idx1 : e + (n + 1) = e + n + 1 := by omega
    have h_idx2 : dx + 3 * (n + 1) = dx + 3 * n + 3 := by omega
    have h_idx3 : dy + 3 * (n + 1) = dy + 3 * n + 3 := by omega
    simpa [h_idx1, h_idx2, h_idx3] using hgoal

/-- A polynomial multiplier of degree `≤ n` in the second exponent acts like `n` operators `θ_y`. -/
theorem Frac_mulC_polyY {e dx dy n : ℕ} (P : Polynomial ℚ) (hP : P.natDegree ≤ n)
    {f : MvPowerSeries (Fin 2) ℚ} (h : Frac e dx dy f) :
    Frac (e + n) (dx + 3 * n) (dy + 3 * n) (mulC (fun _ b => P.eval (b : ℚ)) f) := by
  induction' n with n ih generalizing P
  · -- base case n = 0
    have hP0 : P.natDegree = 0 := Nat.eq_zero_of_le_zero hP
    rcases (Polynomial.natDegree_eq_zero.mp hP0) with ⟨c, hc⟩
    have h_mulC : mulC (fun _ b => P.eval (b : ℚ)) f = MvPowerSeries.C c * f := by
      rw [← hc]
      ext n
      simp [mulC_const]
    rw [h_mulC]
    have h_up : Frac (e + 0) (dx + 3 * 0) (dy + 3 * 0) f := Frac_up' 0 h
    simpa [smul_eq_C_mul] using Frac_smul c h_up
  · -- inductive step: P.natDegree ≤ n+1
    have hPdiv : P.divX.natDegree ≤ n := by
      rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
      omega
    have h_eval : ∀ b : ℚ, P.eval (b : ℚ) = P.coeff 0 + (b : ℚ) * P.divX.eval (b : ℚ) := by
      intro b
      have h_eq : Polynomial.C (P.coeff 0) + Polynomial.X * P.divX = P := by
        rw [add_comm, Polynomial.X_mul_divX_add]
      have h_eval_eq : P.eval (b : ℚ) = ((Polynomial.C (P.coeff 0) + Polynomial.X * P.divX)).eval (b : ℚ) :=
        congrArg (fun q : Polynomial ℚ => q.eval (b : ℚ)) h_eq.symm
      calc
        P.eval (b : ℚ) = ((Polynomial.C (P.coeff 0) + Polynomial.X * P.divX)).eval (b : ℚ) := h_eval_eq
        _ = (Polynomial.C (P.coeff 0)).eval (b : ℚ) + (Polynomial.X * P.divX).eval (b : ℚ) := by rw [Polynomial.eval_add]
        _ = P.coeff 0 + ((b : ℚ) * P.divX.eval (b : ℚ)) := by
          rw [Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
    have h_mulC_decomp : mulC (fun a b => P.eval (b : ℚ)) f =
        MvPowerSeries.C (P.coeff 0) * f + thY (mulC (fun a b => P.divX.eval (b : ℚ)) f) := by
      ext n
      simp only [coeff_mulC, thY, map_add, MvPowerSeries.coeff_C_mul]
      rw [h_eval (n 1 : ℚ)]
      ring
    rw [h_mulC_decomp]
    apply Frac_add
    · -- first term: MvPowerSeries.C (P.coeff 0) * f
      have h_up : Frac (e + (n + 1)) (dx + 3 * (n + 1)) (dy + 3 * (n + 1)) f := Frac_up' (n + 1) h
      simpa [smul_eq_C_mul] using Frac_smul (P.coeff 0) h_up
    · -- second term: thY (mulC (fun a b => P.divX.eval (b : ℚ)) f)
      have h_ih : Frac (e + n) (dx + 3 * n) (dy + 3 * n)
          (mulC (fun a b => P.divX.eval (b : ℚ)) f) :=
        ih P.divX hPdiv
      have h_thY : Frac ((e + n) + 1) ((dx + 3 * n) + 3) ((dy + 3 * n) + 3)
          (thY (mulC (fun a b => P.divX.eval (b : ℚ)) f)) :=
        Frac_thY h_ih
      simpa [add_assoc, mul_add] using h_thY

theorem Q_mul_F : Q * F = N := by
  have hQconst : MvPowerSeries.constantCoeff Q = 1 := by
    dsimp [Q, x, y]
    simp
  have hQunit : MvPowerSeries.constantCoeff Q ≠ 0 := by
    rw [hQconst]
    norm_num
  dsimp [F]
  calc
    Q * (N * Q⁻¹) = (Q * Q⁻¹) * N := by ring
    _ = 1 * N := by rw [MvPowerSeries.mul_inv_cancel Q hQunit]
    _ = N := by simp

theorem Frac_F : Frac 1 3 3 F := by
  unfold Frac
  rw [pow_one, mul_comm, Q_mul_F]
  exact Box_N

/-- A series of `Frac e dx dy` whose coefficients vanish on the box `[0, dx] × [0, dy]` is zero. -/
theorem eq_zero_of_Frac {e dx dy : ℕ} {H : MvPowerSeries (Fin 2) ℚ} (hH : Frac e dx dy H)
    (h0 : ∀ i j, i ≤ dx → j ≤ dy → coeff (ex i j) H = 0) : H = 0 := by
  have hQconst : MvPowerSeries.constantCoeff Q = 1 := by
    simp [Q, x, y, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_one]
  have hQe_const_ne_zero : MvPowerSeries.constantCoeff (Q ^ e) ≠ 0 := by
    rw [map_pow, hQconst, one_pow]
    exact one_ne_zero
  have hPzero : H * Q ^ e = 0 := by
    apply eq_zero_of_Box hH
    intro i j hi hj
    rw [MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    have hp_sum : p.1 + p.2 = ex i j := (Finset.HasAntidiagonal.mem_antidiagonal.mp hp)
    have hsum0 : (p.1 0) + (p.2 0) = i := by
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) hp_sum
      simpa [ex_apply_zero] using this
    have hsum1 : (p.1 1) + (p.2 1) = j := by
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) hp_sum
      simpa [ex_apply_one] using this
    have h0le : (p.1 0) ≤ dx := by
      omega
    have h1le : (p.1 1) ≤ dy := by
      omega
    have hcoeffH : coeff p.1 H = 0 := by
      rw [eq_ex p.1]
      exact h0 (p.1 0) (p.1 1) h0le h1le
    rw [hcoeffH, zero_mul]
  calc
    H = H * 1 := by simp
    _ = H * ((Q ^ e) * (Q ^ e)⁻¹) := by rw [MvPowerSeries.mul_inv_cancel _ hQe_const_ne_zero]
    _ = (H * Q ^ e) * (Q ^ e)⁻¹ := by ring
    _ = 0 * (Q ^ e)⁻¹ := by rw [hPzero]
    _ = 0 := by simp

end CalegariSlopes.ADB
