/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.ADB.Defs

@[expose] public section

/-!
# Lemma 5.1, Loeffler's column recurrence, for every `p ≥ 1` (Appendix A)

`B p k = Σ_t β(k, t)` (`summand_eq_beta`); the certificate `φ` of Appendix A satisfies
`c0 β(k, t) + c1 β(k+1, t) + c2 β(k+2, t) = φ(k, t+1) - φ(k, t)` at every `t` (Lemma A.1, `cert`); the sum over `t`
telescopes. The binomial identities with natural boundaries reduce the certificate identity to one polynomial
identity (`claim_cleared`, `linear_combination`).
-/

namespace CalegariSlopes.ADB.Proof

open CalegariSlopes CalegariSlopes.ADB

theorem binZ_eq_w (t : ℕ) (m : ℤ) : binZ t m = w t m * ((m + 1) * (m + 2)) := by
  unfold binZ w invFac
  rcases lt_or_ge m 0 with hm | hm
  · -- `m < 0`: the binomial vanishes, and so does the right side.
    rw [if_neg (by omega)]
    rcases lt_or_ge (m + 2) 0 with hm2 | hm2
    · rw [if_neg (by omega)]; simp
    · have : m = -1 ∨ m = -2 := by omega
      rcases this with rfl | rfl <;> norm_num
  · rcases le_or_gt m t with hmt | hmt
    · -- `0 ≤ m ≤ t`
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n := ⟨m.toNat, by omega⟩
      have hnt : n ≤ t := by exact_mod_cast hmt
      rw [if_pos ⟨hm, hmt⟩, if_pos (by omega), if_pos (by omega)]
      have h1 : ((n : ℤ) + 2).toNat = n + 2 := by omega
      have h2 : ((t : ℤ) - n).toNat = t - n := by omega
      simp only [h1, h2, Int.toNat_natCast]
      rw [Nat.cast_choose ℚ hnt]
      rw [show n + 2 = (n + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      have : (n.factorial : ℚ) ≠ 0 := by positivity
      have : ((t - n).factorial : ℚ) ≠ 0 := by positivity
      field_simp
      ring
    · -- `m > t`
      rw [if_neg (by omega), if_neg (show ¬ (0 ≤ (t : ℤ) - m) by omega)]
      simp

/-- `binom(t, m + 1) = w(t, m) (m + 2) (t - m)`. -/
theorem binZ_succ_eq_w (t : ℕ) (m : ℤ) :
    binZ t (m + 1) = w t m * (((m : ℚ) + 2) * ((t : ℚ) - m)) := by
  unfold binZ w invFac
  by_cases hm : m + 1 < 0
  · -- m + 1 < 0, LHS = 0
    rw [if_neg (by omega)]
    by_cases hm2 : m + 2 < 0
    · rw [if_neg (by omega)]; simp
    · have hm2' : 0 ≤ m + 2 := by omega
      rw [if_pos hm2']
      have hm_eq : m = -2 := by omega
      subst hm_eq
      norm_num
  · -- 0 ≤ m + 1
    have hm' : 0 ≤ m + 1 := by omega
    by_cases hmt : m + 1 ≤ (t : ℤ)
    · -- 0 ≤ m + 1 ≤ t
      obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = m + 1 := by
        refine ⟨(m + 1).toNat, ?_⟩
        rw [Int.toNat_of_nonneg hm']
      have hm_eq : m = (n : ℤ) - 1 := by omega
      subst hm_eq
      have hn_le_t : n ≤ t := by omega
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
      have h1 : ((n : ℤ) + 1).toNat = n + 1 := by omega
      have h2 : ((t : ℤ) - ((n : ℤ) - 1)).toNat = t - n + 1 := by omega
      have h3 : ((n : ℤ) - 1 + 2).toNat = n + 1 := by omega
      simp [h2, h3]
      rw [Nat.cast_choose ℚ hn_le_t]
      have hfact_n : (n.factorial : ℚ) ≠ 0 := by positivity
      have hfact_tn : ((t - n).factorial : ℚ) ≠ 0 := by positivity
      have hfact_n1 : ((n + 1).factorial : ℚ) ≠ 0 := by positivity
      have hfact_tn1 : ((t - n + 1).factorial : ℚ) ≠ 0 := by positivity
      field_simp [hfact_n, hfact_tn, hfact_n1, hfact_tn1]
      have hfac_n1 : ((n + 1).factorial : ℚ) = (n + 1 : ℚ) * (n.factorial : ℚ) := by
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hfac_tn1 : ((t - n + 1).factorial : ℚ) = ((t - n + 1 : ℕ) : ℚ) * ((t - n).factorial : ℚ) := by
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      rw [hfac_n1, hfac_tn1]
      have hcast_tn1 : ((t - n + 1 : ℕ) : ℚ) = (t : ℚ) - (n : ℚ) + 1 := by
        rw [Nat.cast_add, Nat.cast_sub hn_le_t, Nat.cast_one]
      rw [hcast_tn1]
      ring
    · -- m + 1 > t
      rw [if_neg (by omega)]
      by_cases hm2 : m + 2 < 0
      · -- invFac(m+2) condition is false
        rw [if_neg (by omega)]
        simp
      · have hm2' : 0 ≤ m + 2 := by omega
        rw [if_pos hm2']
        by_cases htm : t - m < 0
        · -- invFac(t-m) condition is false
          rw [if_neg (by omega)]
          simp
        · have htm' : 0 ≤ t - m := by omega
          rw [if_pos htm']
          -- Both invFac nonzero, need (t:ℚ)-m = 0, i.e., m = t
          have h_eq : m = (t : ℤ) := by
            apply le_antisymm
            · omega
            · omega
          subst h_eq
          simp

/-- `binom(t, m + 2) = w(t, m) (t - m) (t - m - 1)`. -/
theorem binZ_add_two_eq_w (t : ℕ) (m : ℤ) :
    binZ t (m + 2) = w t m * (((t : ℚ) - m) * ((t : ℚ) - m - 1)) := by
  unfold binZ w invFac
  rcases lt_or_ge (m + 2) 0 with hm | hm
  · rw [if_neg (by omega), if_neg (by omega)]
    simp
  · rcases le_or_gt (m + 2) t with hmt | hmt
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = m + 2 := ⟨(m + 2).toNat, Int.toNat_of_nonneg hm⟩
      have hnt : n ≤ t := by omega
      obtain rfl : m = (n : ℤ) - 2 := by omega
      rw [if_pos ⟨by omega, by omega⟩, if_pos (by omega), if_pos (by omega)]
      have h1 : ((n : ℤ) - 2 + 2).toNat = n := by omega
      have h2 : ((t : ℤ) - ((n : ℤ) - 2)).toNat = (t - n) + 1 + 1 := by omega
      rw [h1, h2, Nat.cast_choose ℚ hnt, Nat.factorial_succ, Nat.factorial_succ]
      have : (n.factorial : ℚ) ≠ 0 := by positivity
      have : ((t - n).factorial : ℚ) ≠ 0 := by positivity
      have hc : ((t - n : ℕ) : ℚ) = (t : ℚ) - n := Nat.cast_sub hnt
      have hpos : (0 : ℚ) ≤ (t : ℚ) - n := by rw [← hc]; positivity
      have : (t : ℚ) - n + 1 ≠ 0 := by linarith
      have : (t : ℚ) - n + 1 + 1 ≠ 0 := by linarith
      push_cast [hc]
      field_simp
      ring
    · rw [if_neg (by omega)]
      rcases lt_or_ge ((t : ℤ) - m) 0 with h2 | h2
      · rw [if_neg (show ¬ (0 ≤ (t : ℤ) - m) by omega)]
        simp
      · have : (t : ℤ) - m = 0 ∨ (t : ℤ) - m = 1 := by omega
        rcases this with h | h
        · have hq : (t : ℚ) - m = 0 := by exact_mod_cast h
          rw [hq]; simp
        · have hq : (t : ℚ) - m - 1 = 0 := by
            have : (t : ℚ) - m = 1 := by exact_mod_cast h
            linarith
          rw [hq]; simp

theorem _root_.CalegariSlopes.ADB.invFac_succ_mul (k : ℤ) : invFac (k + 1) * ((k + 1 : ℤ) : ℚ) = invFac k := by
  unfold invFac
  by_cases hk : 0 ≤ k
  · have hk1 : 0 ≤ k + 1 := by omega
    have hk_eq : (k : ℚ) = (k.toNat : ℚ) := by
      exact_mod_cast (Int.toNat_of_nonneg hk).symm
    have htoNat_nat : (k + 1).toNat = k.toNat + 1 := by
      have h : ((k + 1).toNat : ℤ) = (k.toNat : ℤ) + 1 := by
        rw [Int.toNat_of_nonneg hk1, Int.toNat_of_nonneg hk]
      exact_mod_cast h
    simp [hk, hk1]
    rw [hk_eq, htoNat_nat]
    rw [Nat.factorial_succ]
    have hfact : ((k.toNat).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    field_simp [hfact]
    push_cast
    ring
  · -- k < 0
    by_cases hk1 : 0 ≤ k + 1
    · -- k = -1 (since k < 0 and k+1 ≥ 0)
      have hk_eq_neg1 : k = -1 := by omega
      subst hk_eq_neg1
      norm_num
    · -- k+1 < 0
      have hk1_lt : ¬ 0 ≤ k + 1 := by omega
      simp [hk, hk1_lt]


/-- `binom(t + 1, m + 1) = w(t, m) (t + 1) (m + 2)`. -/
theorem binZ_succ_succ_eq_w (t : ℕ) (m : ℤ) :
    binZ (t + 1) (m + 1) = w t m * (((t : ℚ) + 1) * ((m : ℚ) + 2)) := by
  unfold binZ w invFac
  by_cases h_cond : 0 ≤ m + 1 ∧ m + 1 ≤ ↑(t + 1)
  · rw [if_pos h_cond]
    rcases h_cond with ⟨hm1, hm1_le⟩
    by_cases hm_neg : m < 0
    · -- m = -1
      have hm_eq_neg1 : m = -1 := by omega
      subst hm_eq_neg1
      have hpos_t : 0 ≤ (t : ℤ) + 1 := by omega
      simp [hpos_t]
      have hfact_succ : ((t + 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      field_simp [hfact_succ]
      rw [Nat.factorial_succ]
      push_cast
      ring
    · -- m ≥ 0
      have hm_nonneg : 0 ≤ m := by omega
      have hm2 : 0 ≤ m + 2 := by omega
      have htm : 0 ≤ (t : ℤ) - m := by omega
      rw [if_pos hm2, if_pos htm]
      -- Convert m to ℕ
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n := ⟨Int.toNat m, by
        rw [Int.toNat_of_nonneg hm_nonneg]⟩
      have hnt : n ≤ t := by
        have : (n : ℤ) ≤ (t : ℤ) := by omega
        exact_mod_cast this
      have h1 : ((n : ℤ) + 2).toNat = n + 2 := by omega
      have h2 : ((t : ℤ) - n).toNat = t - n := by omega
      have hm1_toNat : ((n : ℤ) + 1).toNat = n + 1 := by omega
      rw [hm1_toNat, h1, h2]
      -- Goal: ↑((t+1).choose (n+1)) = ↑(t.factorial) * (↑(n+2).factorial)⁻¹ * (↑(t-n).factorial)⁻¹ * ((↑t + 1) * (↑n + 2))
      rw [Nat.cast_choose ℚ (show n + 1 ≤ t + 1 from by omega)]
      have hsub : (t + 1 : ℕ) - (n + 1 : ℕ) = t - n := by omega
      rw [hsub]
      push_cast
      -- Goal: (t+1)! / ((n+1)! * (t-n)!) = t! * ((n+2)!)⁻¹ * ((t-n)!)⁻¹ * (t+1) * (n+2)
      have hfact_tn : ((t - n).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hfact_n1 : ((n + 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hfact_n2 : ((n + 2).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      field_simp [hfact_tn, hfact_n1, hfact_n2]
      -- Goal: ↑(t+1).factorial * ↑(n+2).factorial = ↑(t.factorial) * ((↑t + 1) * (↑n + 2)) * ↑(n+1).factorial
      rw [Nat.factorial_succ, Nat.factorial_succ (n := n+1)]
      push_cast
      ring
  · -- condition false: binZ = 0
    rw [if_neg h_cond]
    -- Need to show RHS = 0
    -- h_cond: ¬ (0 ≤ m+1 ∧ m+1 ≤ ↑(t+1))
    -- So either m+1 < 0 or m+1 > ↑(t+1)
    rcases not_and_or.mp h_cond with (hm1_lt | hm1_gt)
    · -- m+1 < 0
      -- Then either m+2 < 0 (invFac(m+2)=0) or m = -2 ((m:ℚ)+2 = 0)
      by_cases hm2_lt : m + 2 < 0
      · -- m+2 < 0: invFac(m+2) = 0
        rw [if_neg (by omega : ¬ (0 ≤ m + 2))]
        simp
      · -- m+2 ≥ 0, so m = -2 (since m+1 < 0 and m+2 ≥ 0)
        have hm_eq_neg2 : m = -2 := by omega
        subst hm_eq_neg2
        norm_num
    · -- m+1 > ↑(t+1), i.e., m > t
      -- Then t-m < 0, so invFac(t-m) = 0
      rw [if_neg (by omega : ¬ (0 ≤ (t : ℤ) - m))]
      simp

/-- `g(k + 1) / g(k) = (k + 1)^2 / (k (p + k + 1))`, cleared. -/
theorem g_succ (p k : ℕ) :
    (k : ℚ) * ((k : ℚ) + p + 1) * g p (k + 1) = ((k : ℚ) + 1) ^ 2 * g p k := by
  dsimp [g]
  field_simp
  have h1 : ((k + 1 : ℕ).factorial : ℚ) = ((k : ℚ) + 1) * (k.factorial : ℚ) := by
    simpa [Nat.cast_add, Nat.cast_one] using congrArg (fun n : ℕ => (n : ℚ)) (Nat.factorial_succ k)
  have h2 : ((p + (k + 1) : ℕ).factorial : ℚ) = ((k : ℚ) + p + 1) * ((p + k : ℕ).factorial : ℚ) := by
    simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using congrArg (fun n : ℕ => (n : ℚ)) (Nat.factorial_succ (p + k))
  simp [h1, h2]
  ring

/-- `g(k + 2) / g(k) = (k + 1)(k + 2)^2 / (k (p + k + 1)(p + k + 2))`, cleared. -/
theorem g_add_two (p k : ℕ) :
    (k : ℚ) * ((k : ℚ) + p + 1) * ((k : ℚ) + p + 2) * g p (k + 2) =
      ((k : ℚ) + 1) * ((k : ℚ) + 2) ^ 2 * g p k := by
  unfold g
  have hfac1 : (k + 2).factorial = (k + 2) * (k + 1) * k.factorial := by
    calc
      (k + 2).factorial = (k + 2) * (k + 1).factorial := by rw [Nat.factorial_succ]
      _ = (k + 2) * ((k + 1) * k.factorial) := by rw [Nat.factorial_succ]
      _ = (k + 2) * (k + 1) * k.factorial := by ring
  have hfac2 : (p + (k + 2)).factorial = (p + k + 2) * (p + k + 1) * (p + k).factorial := by
    calc
      (p + (k + 2)).factorial = (p + k + 2).factorial := by ring
      _ = (p + k + 2) * (p + k + 1).factorial := by rw [Nat.factorial_succ]
      _ = (p + k + 2) * ((p + k + 1) * (p + k).factorial) := by rw [Nat.factorial_succ]
      _ = (p + k + 2) * (p + k + 1) * (p + k).factorial := by ring
  rw [hfac1, hfac2]
  push_cast
  field_simp [show (k.factorial : ℚ) ≠ 0 from by exact_mod_cast Nat.factorial_ne_zero _,
    show ((p + k).factorial : ℚ) ≠ 0 from by exact_mod_cast Nat.factorial_ne_zero _]
  ring

/-- The ratio `(t + 1) C_{t+1} = ρ(t) C_t` of Appendix A, cleared, for every `t ≥ 0` (`p ≥ 1`). -/
theorem Cc_succ (p t : ℕ) (hp : 1 ≤ p) :
    ((3 * t + 3 * p + 1) * (3 * t + 3 * p + 2) : ℚ) * ((t + 1) * Cc p (t + 1)) =
      -18 * ((t : ℚ) - p) * (t + 2 * p) * (2 * t + 2 * p + 1) * Cc p t := by
  unfold Cc
  rcases lt_trichotomy t p with htp | rfl | htp
  · rw [if_pos (by omega), if_pos htp.le]
    obtain ⟨d, rfl⟩ : ∃ d, p = t + 1 + d := ⟨p - (t + 1), by omega⟩
    have e1 : 2 * (t + 1 + d) + 2 * (t + 1) = (2 * (t + 1 + d) + 2 * t + 1) + 1 := by ring
    have e2 : 2 * (t + 1 + d) + (t + 1) - 1 = (2 * (t + 1 + d) + t - 1) + 1 := by omega
    have e3 : 3 * (t + 1 + d) + 3 * (t + 1) = (3 * (t + 1 + d) + 3 * t + 2) + 1 := by ring
    have e4 : t + 1 + d - t = (t + 1 + d - (t + 1)) + 1 := by omega
    rw [e1, e2, e3, e4, Nat.factorial_succ (2 * (t + 1 + d) + 2 * t + 1), Nat.factorial_succ,
      Nat.factorial_succ (2 * (t + 1 + d) + t - 1), Nat.factorial_succ (3 * (t + 1 + d) + 3 * t + 2),
      Nat.factorial_succ (3 * (t + 1 + d) + 3 * t + 1), Nat.factorial_succ (3 * (t + 1 + d) + 3 * t),
      Nat.factorial_succ (t + 1 + d - (t + 1)), Nat.factorial_succ t]
    have e5 : t + 1 + d - (t + 1) = d := by omega
    have e6 : 2 * (t + 1 + d) + t - 1 + 1 = 2 * (t + 1 + d) + t := by omega
    rw [e5, e6]
    have e7 : ((2 * (t + 1 + d) + t - 1 : ℕ) : ℚ) = 2 * (t + 1 + d) + t - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    push_cast [e7]
    have : ((2 * (t + 1 + d) + t - 1).factorial : ℚ) ≠ 0 := by positivity
    have : ((3 * (t + 1 + d) + 3 * t).factorial : ℚ) ≠ 0 := by positivity
    have : ((2 * (t + 1 + d) + 2 * t + 1 - 1).factorial : ℚ) ≠ 0 := by positivity
    have : (d.factorial : ℚ) ≠ 0 := by positivity
    have : (t.factorial : ℚ) ≠ 0 := by positivity
    have : ((2 * (t + 1 + d)).factorial : ℚ) ≠ 0 := by positivity
    have : ((2 * (t + 1 + d) + 2 * t).factorial : ℚ) ≠ 0 := by positivity
    field_simp
    ring
  · rw [if_neg (by omega)]; simp
  · rw [if_neg (by omega), if_neg (by omega)]; simp

/-- `ψ(k, t)` cleared of its denominator `k + p + 1`. -/
theorem psi_mul (p k t : ℕ) :
    ((k : ℚ) + p + 1) * psi p k t =
      -((k : ℚ) + 1) ^ 2 * ((k : ℚ) + 2) ^ 2 * ((k : ℚ) - p + 2) * (3 * (p : ℚ) + 3 * t - 1) *
        (3 * (p : ℚ) + 3 * t - 2) := by
  unfold psi
  have : ((k : ℚ) + p + 1) ≠ 0 := by positivity
  field_simp

theorem claim_cleared (k t p g g1 g2 C C1 w ψ0 ψ1 : ℚ) (hk : k ≠ 0) (h1 : k + p + 1 ≠ 0)
    (h2 : k + p + 2 ≠ 0) (h3 : 3*t + 3*p + 1 ≠ 0) (h4 : 3*t + 3*p + 2 ≠ 0)
    (hg1 : k * (k+p+1) * g1 = (k+1)^2 * g)
    (hg2 : k * (k+p+1) * (k+p+2) * g2 = (k+1) * (k+2)^2 * g)
    (hC : (3*t+3*p+1) * (3*t+3*p+2) * ((t+1) * C1) = -18 * (t-p) * (t+2*p) * (2*t+2*p+1) * C)
    (hψ0 : (k+p+1) * ψ0 = -(k+1)^2 * (k+2)^2 * (k-p+2) * (3*p+3*t-1) * (3*p+3*t-2))
    (hψ1 : (k+p+1) * ψ1 = -(k+1)^2 * (k+2)^2 * (k-p+2) * (3*p+3*t+2) * (3*p+3*t+1)) :
    let m := k - p - t
    9 * (k+1)^2 * (k+2)^2 * (k^2 - 9*p^2) * (g * C * (w * ((m+1) * (m+2))))
      + 18 * k * (k+2)^2 * ((k+1)^3 - p^2*(5*k+7)) * (g1 * C * (w * ((m+2) * (t-m))))
      + k * (k+1) * (3*k+4) * (3*k+5) * ((k+2)^2 - p^2) * (g2 * C * (w * ((t-m) * (t-m-1))))
      = ψ1 * g * C1 * (w * ((t+1) * (m+2))) - ψ0 * g * C * (w * ((t-m) * (t-m-1))) := by
  intro m
  have hD : k * (k+p+1) * (k+p+2) * ((3*t+3*p+1) * (3*t+3*p+2)) ≠ 0 := by
    have := mul_ne_zero h3 h4
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hk h1) h2) this
  refine mul_left_cancel₀ hD ?_
  simp only [m]
  linear_combination
    (18 * k * (k+2)^2 * ((k+1)^3 - p^2*(5*k+7)) * C * w * ((k-p-t+2) * (t-(k-p-t)))
        * (k+p+2) * ((3*t+3*p+1) * (3*t+3*p+2))) * hg1
    + (k * (k+1) * (3*k+4) * (3*k+5) * ((k+2)^2 - p^2) * C * w * ((t-(k-p-t)) * (t-(k-p-t)-1))
        * ((3*t+3*p+1) * (3*t+3*p+2))) * hg2
    - (k * (k+p+2) * g * w * (k-p-t+2) * ((k+p+1) * ψ1)) * hC
    - (k * (k+p+2) * g * w * (k-p-t+2) * (-18 * (t-p) * (t+2*p) * (2*t+2*p+1) * C)) * hψ1
    + (k * (k+p+2) * ((3*t+3*p+1) * (3*t+3*p+2)) * g * C * w * ((t-(k-p-t)) * (t-(k-p-t)-1))) * hψ0

/-- Lemma A.1, the certificate identity, at every `t`:
`c0 β(k, t) + c1 β(k+1, t) + c2 β(k+2, t) = φ(k, t+1) - φ(k, t)`, with `c_a = m_a + p^2 n_a`. -/
theorem cert (p k t : ℕ) (hp : 1 ≤ p) (hk : 1 ≤ k) :
    (mC 0 k + (p : ℚ) ^ 2 * nC 0 k) * beta p k t + (mC 1 k + (p : ℚ) ^ 2 * nC 1 k) * beta p (k + 1) t +
      (mC 2 k + (p : ℚ) ^ 2 * nC 2 k) * beta p (k + 2) t = phi p k (t + 1) - phi p k t := by
  set m : ℤ := (k : ℤ) - p - t with hm
  have e0 : ((k : ℤ) - p - t) = m := rfl
  have e1 : (((k + 1 : ℕ) : ℤ) - p - t) = m + 1 := by push_cast; ring
  have e2 : (((k + 2 : ℕ) : ℤ) - p - t) = m + 2 := by push_cast; ring
  have e3 : ((k : ℤ) + 2 - p - t) = m + 2 := by ring
  have e4 : ((k : ℤ) + 2 - p - ((t + 1 : ℕ) : ℤ)) = m + 1 := by push_cast; ring
  have hmq : (m : ℚ) = (k : ℚ) - p - t := by rw [hm]; push_cast; ring
  unfold beta phi
  rw [e0, e1, e2, e3, e4, binZ_eq_w, binZ_succ_eq_w, binZ_add_two_eq_w, binZ_succ_succ_eq_w]
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1 : (k : ℚ) + p + 1 ≠ 0 := by positivity
  have h2 : (k : ℚ) + p + 2 ≠ 0 := by positivity
  have h3 : 3 * (t : ℚ) + 3 * p + 1 ≠ 0 := by positivity
  have h4 : 3 * (t : ℚ) + 3 * p + 2 ≠ 0 := by positivity
  have hC := Cc_succ p t hp
  have hψ1 := psi_mul p k (t + 1)
  push_cast at hψ1
  have key := claim_cleared (k : ℚ) (t : ℚ) (p : ℚ) (g p k) (g p (k + 1)) (g p (k + 2)) (Cc p t)
    (Cc p (t + 1)) (w t m) (psi p k t) (psi p k (t + 1)) hk0 h1 h2 h3 h4
    (by linear_combination g_succ p k) (by linear_combination g_add_two p k)
    (by linear_combination hC) (by linear_combination psi_mul p k t) (by linear_combination hψ1)
  simp only [mC, nC]
  rw [hmq]
  linear_combination key

/-- The summand of `B` is `β` (Appendix A). -/
theorem summand_eq_beta (p k t : ℕ) (hp : 1 ≤ p) (ht : t ≤ p) :
    3 ^ (2 * t) * mu p k t / r t p = beta p k t := by
  unfold mu beta
  by_cases hg : k ≤ p + 2 * t ∧ p + t ≤ k ∧ t ≤ p
  · rw [if_pos hg]
    obtain ⟨s, rfl⟩ : ∃ s, k = p + t + s := ⟨k - (p + t), by omega⟩
    have hs : s ≤ t := by omega
    have e0 : ((p + t + s : ℕ) : ℤ) - p - t = (s : ℤ) := by push_cast; ring
    rw [e0]
    unfold binZ
    rw [if_pos ⟨by positivity, by exact_mod_cast hs⟩, Int.toNat_natCast, Nat.cast_choose ℚ hs]
    have e1 : p + 2 * t - (p + t + s) = t - s := by omega
    have e2 : p + t + s - p - t = s := by omega
    rw [e1, e2]
    unfold g Cc r
    rw [if_pos ht]
    have : ((p + (p + t + s)).factorial : ℚ) ≠ 0 := by positivity
    have : ((t - s).factorial : ℚ) ≠ 0 := by positivity
    have : ((2 * p).factorial : ℚ) ≠ 0 := by positivity
    have : (s.factorial : ℚ) ≠ 0 := by positivity
    have : ((p - t).factorial : ℚ) ≠ 0 := by positivity
    have : ((p + t).factorial : ℚ) ≠ 0 := by positivity
    have : ((3 * p + 3 * t).factorial : ℚ) ≠ 0 := by positivity
    have : (p.factorial : ℚ) ≠ 0 := by positivity
    have : ((3 * p).factorial : ℚ) ≠ 0 := by positivity
    have : (t.factorial : ℚ) ≠ 0 := by positivity
    field_simp
    ring
  · rw [if_neg hg]
    have hb : binZ t ((k : ℤ) - p - t) = 0 := by
      unfold binZ
      rw [if_neg]
      intro h
      apply hg
      refine ⟨?_, ?_, ht⟩ <;> omega
    rw [hb]
    simp

/-- `φ(k, 0) = 0`. -/
theorem phi_zero (p k : ℕ) (hp : 1 ≤ p) : phi p k 0 = 0 := by
  unfold phi
  by_cases h : (k : ℤ) + 2 = (p : ℤ)
  · -- (k : ℚ) - p + 2 = 0, so psi p k 0 = 0
    have hk : (k : ℚ) - (p : ℚ) + 2 = 0 := by
      have hk' : (k : ℚ) + 2 = (p : ℚ) := by exact_mod_cast h
      linarith
    have hpsi : psi p k 0 = 0 := by
      unfold psi
      simp [hk]
    rw [hpsi]
    simp
  · -- binZ 0 ((k : ℤ) + 2 - p - 0) = 0 because the guard fails
    have hbin : binZ 0 ((k : ℤ) + 2 - (p : ℤ) - (0 : ℤ)) = 0 := by
      unfold binZ
      split_ifs with hcond
      · rcases hcond with ⟨hle, hge⟩
        have heq : (k : ℤ) + 2 = (p : ℤ) := by omega
        exfalso
        exact h heq
      · rfl
    have hgoal : psi p k 0 * g p k * Cc p 0 * binZ 0 ((k : ℤ) + 2 - (p : ℤ) - (0 : ℤ)) = 0 := by
      rw [hbin]
      simp
    simpa using hgoal

/-- `B_pk = Σ_{0 ≤ t ≤ p + 1} β(k, t)` (the term `t = p + 1` is zero). -/
theorem B_eq_sum_beta (p k : ℕ) (hp : 1 ≤ p) :
    B p k = ∑ t ∈ Finset.range (p + 2), beta p k t := by
  rw [Finset.sum_range_succ, B]
  have hb : beta p k (p + 1) = 0 := by simp [beta, Cc]
  rw [hb, add_zero]
  exact Finset.sum_congr rfl fun t ht =>
    summand_eq_beta p k t hp (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht))

/-- Lemma 5.1: Loeffler's recurrence for the row `B_{p,.}`, for every `p ≥ 1` and `k ≥ 1`. -/
theorem P1 (p k : ℕ) (hp : 1 ≤ p) (hk : 1 ≤ k) : mOp (B p) k + (p : ℚ) ^ 2 * nOp (B p) k = 0 := by
  have hsplit : mOp (B p) k + (p : ℚ) ^ 2 * nOp (B p) k =
      ∑ t ∈ Finset.range (p + 2), ((mC 0 k + (p : ℚ) ^ 2 * nC 0 k) * beta p k t +
        (mC 1 k + (p : ℚ) ^ 2 * nC 1 k) * beta p (k + 1) t +
        (mC 2 k + (p : ℚ) ^ 2 * nC 2 k) * beta p (k + 2) t) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      ← B_eq_sum_beta p k hp, ← B_eq_sum_beta p (k + 1) hp, ← B_eq_sum_beta p (k + 2) hp]
    simp only [mOp, nOp, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero]
    ring
  rw [hsplit, Finset.sum_congr rfl (fun t (_ : t ∈ Finset.range (p + 2)) => cert p k t hp hk),
    Finset.sum_range_sub, phi_zero p k hp]
  simp [phi, Cc]

end CalegariSlopes.ADB.Proof
