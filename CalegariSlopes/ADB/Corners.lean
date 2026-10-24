/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.ADB.Defs
public import CalegariSlopes.ADB.URec

@[expose] public section

/-!
# Supports and corners, the columns `j = 1, 2`

Lemma 3.2 for `B`, Lemma 3.1 (b), (c) for `u` and Lemma 5.4: `B_pk = 0` outside `p ≤ k ≤ 3p`, `B_pp = 1`,
`D_p B_{p,3p} = 3^{6p}`; `u_ij = 0` for `i > 3j` and `u_{3j,j} = 3^{6j-1}` (weights, from the recurrence of `u`); the
same support and corner for `V`; and `S = V` on the columns `j = 1, 2` (exact values).
-/

namespace CalegariSlopes.ADB.Proof

open CalegariSlopes CalegariSlopes.ADB

theorem B_eq_zero_of_lt (p k : ℕ) (h : k < p) : B p k = 0 := by
  unfold B
  refine Finset.sum_eq_zero ?_
  intro t ht
  unfold mu
  split
  · case isTrue h =>
    rcases h with ⟨_, hptk, _⟩
    omega
  · simp

theorem B_eq_zero_of_gt (p k : ℕ) (h : 3 * p < k) : B p k = 0 := by
  unfold B
  apply Finset.sum_eq_zero
  intro t ht
  have ht_le_p : t ≤ p := by
    have ht_range : t < p + 1 := Finset.mem_range.1 ht
    omega
  have h_not_guard : ¬ (k ≤ p + 2 * t ∧ p + t ≤ k ∧ t ≤ p) := by
    intro hguard
    rcases hguard with ⟨h1, h2, h3⟩
    have hk_le_3p : k ≤ 3 * p := by
      calc
        k ≤ p + 2 * t := h1
        _ ≤ p + 2 * p := by omega
        _ = 3 * p := by omega
    omega
  unfold mu
  rw [ite_eq_right h_not_guard]
  simp

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

theorem D_mul_B_corner (p : ℕ) (hp : 1 ≤ p) : D p * B p (3 * p) = 3 ^ (6 * p) := by
  -- Since 1 ≤ p, we can write p = q+1 for some q, which helps with 3p-1 = 3q+2
  have hpos : p ≠ 0 := by omega
  rcases Nat.exists_eq_succ_of_ne_zero hpos with ⟨q, rfl⟩
  set i := q+1 with hi
  -- Step 1: B i (3*i) reduces to a single term at t = i
  have hsum : B i (3 * i) = 3 ^ (2 * i) * mu i (3 * i) i / r i i := by
    dsimp [B]
    apply Finset.sum_eq_single i
    · intro t ht hne
      have hmu : mu i (3 * i) t = 0 := by
        dsimp [mu]
        have ht_lt_i : t < i := by
          have := Finset.mem_range.1 ht
          omega
        have : ¬ (3 * i ≤ i + 2 * t) := by omega
        simp [this]
      simp [hmu]
    · simp
  rw [hsum]
  -- Step 2: Compute mu i (3*i) i explicitly (guard holds)
  have hguard : 3 * i ≤ i + 2 * i ∧ i + i ≤ 3 * i ∧ i ≤ i := by omega
  have hmu_val : mu i (3 * i) i =
      (6 * i : ℚ) * ((3 * i).factorial : ℚ) * ((3 * i - 1).factorial : ℚ) / (((2 * i).factorial : ℚ) * ((2 * i).factorial : ℚ)) := by
    dsimp [mu]
    rw [ite_eq_left hguard]
    -- Simplify the arithmetic in the factorial arguments
    have h1 : (2*i+2*i : ℕ) = 4*i := by omega
    have h2 : (2*i+i-1 : ℕ) = 3*i-1 := by omega
    have h3 : (i+3*i : ℕ) = 4*i := by omega
    have h4 : (i+2*i-3*i : ℕ) = 0 := by omega
    have h5 : (3*i-i-i : ℕ) = i := by omega
    have h6 : (i-i : ℕ) = 0 := by omega
    have h7 : (i+i : ℕ) = 2*i := by omega
    -- Rewrite the factorial arguments using these identities
    have h1' : ((2*i+2*i).factorial : ℚ) = ((4*i).factorial : ℚ) := by rw [h1]
    have h2' : ((2*i+i-1).factorial : ℚ) = ((3*i-1).factorial : ℚ) := by rw [h2]
    have h3' : ((i+3*i).factorial : ℚ) = ((4*i).factorial : ℚ) := by rw [h3]
    have h4' : ((i+2*i-3*i).factorial : ℚ) = ((0 : ℕ).factorial : ℚ) := by rw [h4]
    have h5' : ((3*i-i-i).factorial : ℚ) = (i.factorial : ℚ) := by rw [h5]
    have h6' : ((i-i).factorial : ℚ) = ((0 : ℕ).factorial : ℚ) := by rw [h6]
    have h7' : ((i+i).factorial : ℚ) = ((2*i).factorial : ℚ) := by rw [h7]
    rw [h1', h2', h3', h4', h5', h6', h7']
    simp [Nat.factorial_zero]
    field_simp
    ring
  -- Step 3: Compute r i i explicitly
  have hr_val : r i i = ((6 * i).factorial : ℚ) * (i.factorial : ℚ) / ((3 : ℚ) ^ i * ((3 * i).factorial : ℚ) * ((2 * i).factorial : ℚ)) := by
    dsimp [r]
    have h1 : 3 * i + 3 * i = 6 * i := by omega
    have h2 : i + i = 2 * i := by omega
    rw [h1, h2]
  rw [hmu_val, hr_val]
  -- Replace q.succ with i everywhere using hi: i = q+1
  have hi' : (q.succ : ℕ) = i := by omega
  rw [hi']
  dsimp [D]
  field_simp
  -- After clearing denominators, we get a polynomial equation in factorial terms
  -- Key identity: (3*i)! = (3*i) * (3*i-1)!
  have hfact : ((3 * i).factorial : ℚ) = (3 * i : ℚ) * ((3 * i - 1).factorial : ℚ) := by
    have h := Nat.factorial_succ (3 * i - 1)
    -- h : (3*i-1+1)! = (3*i-1+1) * (3*i-1)!
    have h' : ((3 * i - 1 + 1).factorial : ℚ) = ((3 * i - 1 + 1 : ℕ) : ℚ) * ((3 * i - 1).factorial : ℚ) := by
      exact_mod_cast h
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ 3 * i)] using h'
  rw [hfact]
  ring

theorem u_eq_zero_of_gt (i j : ℕ) (h : 3 * j < i) : u i j = 0 := by
  -- Strong induction on i + j
  have h_main : ∀ n, (∀ i j, i + j = n → (3 * j < i → u i j = 0)) := by
    intro n
    induction' n using Nat.strong_induction_on with n IH
    intro i j h_eq h_lt
    rw [u_rec i j]
    -- Now we have a sum of 12 terms; show each is 0
    have h0 : (if 1 = i ∧ 1 = j then (90 : ℚ) else 0) = 0 := by
      split_ifs with hcond
      · rcases hcond with ⟨rfl, rfl⟩
        omega
      · rfl
    have h1 : (if 2 = i ∧ 1 = j then (324 : ℚ) else 0) = 0 := by
      split_ifs with hcond
      · rcases hcond with ⟨rfl, rfl⟩
        omega
      · rfl
    have h2 : (if 1 = i ∧ 2 = j then (648 : ℚ) else 0) = 0 := by
      split_ifs with hcond
      · rcases hcond with ⟨rfl, rfl⟩
        omega
      · rfl
    have h3 : (if 3 = i ∧ 1 = j then (243 : ℚ) else 0) = 0 := by
      split_ifs with hcond
      · rcases hcond with ⟨rfl, rfl⟩
        omega
      · rfl
    have h4 : (if 2 = i ∧ 2 = j then (486 : ℚ) else 0) = 0 := by
      split_ifs with hcond
      · rcases hcond with ⟨rfl, rfl⟩
        omega
      · rfl
    have h5 : (if 1 = i ∧ 3 = j then (729 : ℚ) else 0) = 0 := by
      split_ifs with hcond
      · rcases hcond with ⟨rfl, rfl⟩
        omega
      · rfl
    have h6 : (if 1 ≤ i ∧ 1 ≤ j then (270 : ℚ) * u (i - 1) (j - 1) else 0) = 0 := by
      split_ifs with hcond
      · rcases hcond with ⟨hi, hj⟩
        have h_lt' : 3 * (j - 1) < i - 1 := by omega
        have h_sum_lt : (i - 1) + (j - 1) < n := by omega
        rw [IH ((i - 1) + (j - 1)) h_sum_lt (i - 1) (j - 1) rfl h_lt']
        simp
      · rfl
    have h7 : (if 2 ≤ i ∧ 1 ≤ j then (972 : ℚ) * u (i - 2) (j - 1) else 0) = 0 := by
      split_ifs with hcond
      · rcases hcond with ⟨hi, hj⟩
        have h_lt' : 3 * (j - 1) < i - 2 := by omega
        have h_sum_lt : (i - 2) + (j - 1) < n := by omega
        rw [IH ((i - 2) + (j - 1)) h_sum_lt (i - 2) (j - 1) rfl h_lt']
        simp
      · rfl
    have h8 : (if 1 ≤ i ∧ 2 ≤ j then (972 : ℚ) * u (i - 1) (j - 2) else 0) = 0 := by
      split_ifs with hcond
      · rcases hcond with ⟨hi, hj⟩
        have h_lt' : 3 * (j - 2) < i - 1 := by omega
        have h_sum_lt : (i - 1) + (j - 2) < n := by omega
        rw [IH ((i - 1) + (j - 2)) h_sum_lt (i - 1) (j - 2) rfl h_lt']
        simp
      · rfl
    have h9 : (if 3 ≤ i ∧ 1 ≤ j then (729 : ℚ) * u (i - 3) (j - 1) else 0) = 0 := by
      split_ifs with hcond
      · rcases hcond with ⟨hi, hj⟩
        have h_lt' : 3 * (j - 1) < i - 3 := by omega
        have h_sum_lt : (i - 3) + (j - 1) < n := by omega
        rw [IH ((i - 3) + (j - 1)) h_sum_lt (i - 3) (j - 1) rfl h_lt']
        simp
      · rfl
    have h10 : (if 2 ≤ i ∧ 2 ≤ j then (729 : ℚ) * u (i - 2) (j - 2) else 0) = 0 := by
      split_ifs with hcond
      · rcases hcond with ⟨hi, hj⟩
        have h_lt' : 3 * (j - 2) < i - 2 := by omega
        have h_sum_lt : (i - 2) + (j - 2) < n := by omega
        rw [IH ((i - 2) + (j - 2)) h_sum_lt (i - 2) (j - 2) rfl h_lt']
        simp
      · rfl
    have h11 : (if 1 ≤ i ∧ 3 ≤ j then (729 : ℚ) * u (i - 1) (j - 3) else 0) = 0 := by
      split_ifs with hcond
      · rcases hcond with ⟨hi, hj⟩
        have h_lt' : 3 * (j - 3) < i - 1 := by omega
        have h_sum_lt : (i - 1) + (j - 3) < n := by omega
        rw [IH ((i - 1) + (j - 3)) h_sum_lt (i - 1) (j - 3) rfl h_lt']
        simp
      · rfl
    simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  exact h_main (i + j) i j rfl h

theorem u_corner (j : ℕ) (hj : 1 ≤ j) : 3 * u (3 * j) j = 3 ^ (6 * j) := by
  have hpos : j ≠ 0 := by omega
  rcases Nat.exists_eq_succ_of_ne_zero hpos with ⟨k, hk⟩
  subst hk
  induction' k with n ih
  · -- j = 1
    rw [u_rec 3 1]
    simp [u_zero_right]
    ring
  · -- j = n + 2
    have hsub1 : 3 * (n + 2) - 1 = 3 * n + 5 := by omega
    have hsub2 : 3 * (n + 2) - 2 = 3 * n + 4 := by omega
    have hsub3 : 3 * (n + 2) - 3 = 3 * (n + 1) := by omega
    rw [u_rec (3 * (n + 2)) (n + 2)]
    simp only [hsub1, hsub2, hsub3]
    have h_ineq1 : 1 ≤ 3 * (n + 2) := by omega
    have h_ineq2 : 2 ≤ 3 * (n + 2) := by omega
    have h_not1 : 3 * (n + 2) ≠ 1 := by omega
    have h_not2 : 3 * (n + 2) ≠ 2 := by omega
    have h_not1' : 1 ≠ 3 * (n + 2) := by omega
    have h_not2' : 2 ≠ 3 * (n + 2) := by omega
    simp [h_ineq1, h_ineq2, h_not1', h_not2']
    have hu1 : u (3 * n + 5) (n + 1) = 0 := by
      apply u_eq_zero_of_gt; omega
    have hu2 : u (3 * n + 4) (n + 1) = 0 := by
      apply u_eq_zero_of_gt; omega
    have hu3 : u (3 * n + 5) n = 0 := by
      apply u_eq_zero_of_gt; omega
    have hu4 : u (3 * n + 4) n = 0 := by
      apply u_eq_zero_of_gt; omega
    rw [hu1, hu2, hu3, hu4]
    simp
    by_cases hn : n = 0
    · subst hn
      have hu3_1 : u 3 1 = 243 := by
        rw [u_rec 3 1]
        simp [u_zero_right]
      simp [hu3_1]
      norm_num
    · have h_ineq_n : 1 ≤ n := Nat.one_le_of_lt (Nat.pos_of_ne_zero hn)
      simp [h_ineq_n]
      have hu5 : u (3 * n + 5) (n - 1) = 0 := by
        apply u_eq_zero_of_gt; omega
      rw [hu5]
      simp
      have h_ih : 3 * u (3 * (n + 1)) (n + 1) = 3 ^ (6 * (n + 1)) := by
        apply ih (by omega) (by omega)
      calc
        3 * (729 * u (3 * (n + 1)) (n + 1)) = 729 * (3 * u (3 * (n + 1)) (n + 1)) := by ring
        _ = 729 * (3 ^ (6 * (n + 1))) := by rw [h_ih]
        _ = (3 ^ 6) * (3 ^ (6 * (n + 1))) := by norm_num
        _ = 3 ^ (6 + 6 * (n + 1)) := by rw [← pow_add]
        _ = 3 ^ (6 * (n + 2)) := by ring

theorem V_eq_sum (i j K : ℕ) (hK : min i j ≤ K) :
    V i j = ∑ p ∈ Finset.Icc 1 K, lam p * B p i * B p j := by
  dsimp [V]
  refine Finset.sum_subset ?_ ?_
  · intro p hp
    rcases Finset.mem_Icc.mp hp with ⟨hp1, hp2⟩
    exact Finset.mem_Icc.mpr ⟨hp1, le_trans hp2 hK⟩
  · intro p hp hnp
    rcases Finset.mem_Icc.mp hp with ⟨hp1, hp2⟩
    have hp_gt_min : min i j < p := by
      by_contra! hle
      apply hnp
      exact Finset.mem_Icc.mpr ⟨hp1, hle⟩
    rcases (min_lt_iff.mp hp_gt_min) with (h | h)
    · have hB : B p i = 0 := B_eq_zero_of_lt p i h
      simp [hB]
    · have hB : B p j = 0 := B_eq_zero_of_lt p j h
      simp [hB]

theorem V_eq_zero_of_gt (i j : ℕ) (h : 3 * j < i) : V i j = 0 := by
  unfold V
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.mem_Icc] at hp
  rcases hp with ⟨hp1, hp2⟩
  have hp_le_j : p ≤ j :=
    le_trans hp2 (min_le_right i j)
  have h3p_lt_i : 3 * p < i :=
    calc
      3 * p ≤ 3 * j := Nat.mul_le_mul_left 3 hp_le_j
      _ < i := h
  rw [B_eq_zero_of_gt p i h3p_lt_i]
  simp

theorem V_corner (j : ℕ) (hj : 1 ≤ j) : V (3 * j) j = j * 3 ^ (6 * j) := by
  have hmin : min (3 * j) j = j :=
    Nat.min_eq_right (by omega)
  rw [V, hmin]
  apply (Finset.sum_eq_single j ?_ ?_).trans ?_
  · intro p hp hne
    have hp_le_j : p ≤ j := (Finset.mem_Icc.mp hp).2
    have h3p_lt_3j : 3 * p < 3 * j := by
      have hp_lt_j : p < j := Nat.lt_of_le_of_ne hp_le_j hne
      omega
    have hBzero : B p (3 * j) = 0 := B_eq_zero_of_gt p (3 * j) h3p_lt_3j
    simp [hBzero]
  · intro hnotmem
    exfalso
    apply hnotmem
    exact Finset.mem_Icc.mpr ⟨hj, le_refl j⟩
  · calc
      lam j * B j (3 * j) * B j j = ((j : ℚ) * D j) * B j (3 * j) * B j j := rfl
      _ = ((j : ℚ) * D j) * B j (3 * j) * 1 := by rw [B_self j hj]
      _ = (j : ℚ) * (D j * B j (3 * j)) := by ring
      _ = (j : ℚ) * (3 ^ (6 * j)) := by rw [D_mul_B_corner j hj]
      _ = (j : ℚ) * 3 ^ (6 * j) := by ring

theorem S_col_one (i : ℕ) (hi : 1 ≤ i) : S i 1 = V i 1 := by
  unfold S V
  have hmin : min i 1 = 1 := by
    rw [Nat.min_eq_right hi]
  rw [hmin]
  simp [Finset.sum_singleton, lam]
  have hD1 : D 1 = 90 := by
    unfold D
    norm_num [Nat.factorial]
  have hB11 : B 1 1 = 1 := by
    have hp : 1 ≤ (1 : ℕ) := by decide
    exact B_self 1 hp
  rw [hD1, hB11]
  by_cases hi4 : i < 4
  · have hi_le_3 : i ≤ 3 := by omega
    interval_cases i
    · -- i = 1
      have hu11 : u 1 1 = 90 := by
        rw [u_rec 1 1]
        simp [u_zero_right]
      have hB11' : B 1 1 = 1 := hB11
      rw [hu11, hB11']
      norm_num
    · -- i = 2
      have hu21 : u 2 1 = 324 := by
        rw [u_rec 2 1]
        simp [u_zero_right]
      have hB12 : B 1 2 = 36/5 := by
        unfold B
        simp [Finset.sum_range_succ, mu, r, Nat.factorial]
        norm_num
      rw [hu21, hB12]
      norm_num
    · -- i = 3
      have hu31 : u 3 1 = 243 := by
        rw [u_rec 3 1]
        simp [u_zero_right]
      have hB13 : B 1 3 = 81/10 := by
        unfold B
        simp [Finset.sum_range_succ, mu, r, Nat.factorial]
        norm_num
      rw [hu31, hB13]
      norm_num
  · -- i ≥ 4
    have h3lt : 3 * 1 < i := by
      have : 4 ≤ i := by omega
      omega
    have hui : u i 1 = 0 := u_eq_zero_of_gt i 1 h3lt
    have hBi : B 1 i = 0 := B_eq_zero_of_gt 1 i h3lt
    simp [hui, hBi]

theorem S_col_two (i : ℕ) (hi : 1 ≤ i) : S i 2 = V i 2 := by
  -- Helper lemmas for D values
  have hD1 : D 1 = 90 := by unfold D; norm_num
  have hD2 : D 2 = 112266/5 := by unfold D; norm_num
  -- Helper lemmas for B values
  have hB11 : B 1 1 = 1 := by
    unfold B mu r
    have : (Finset.range 2 : Finset ℕ) = {0, 1} := by decide
    rw [this]; simp; norm_num
  have hB12 : B 1 2 = 36/5 := by
    unfold B mu r
    have : (Finset.range 2 : Finset ℕ) = {0, 1} := by decide
    rw [this]; simp; norm_num
  have hB13 : B 1 3 = 81/10 := by
    unfold B mu r
    have : (Finset.range 2 : Finset ℕ) = {0, 1} := by decide
    rw [this]; simp; norm_num
  have hB14 : B 1 4 = 0 := by
    unfold B mu r
    have : (Finset.range 2 : Finset ℕ) = {0, 1} := by decide
    rw [this]; simp
  have hB15 : B 1 5 = 0 := by
    unfold B mu r
    have : (Finset.range 2 : Finset ℕ) = {0, 1} := by decide
    rw [this]; simp
  have hB16 : B 1 6 = 0 := by
    unfold B mu r
    have : (Finset.range 2 : Finset ℕ) = {0, 1} := by decide
    rw [this]; simp
  have hB22 : B 2 2 = 1 := by
    unfold B mu r
    have : (Finset.range 3 : Finset ℕ) = {0, 1, 2} := by decide
    rw [this]; simp; norm_num
  have hB23 : B 2 3 = 81/7 := by
    unfold B mu r
    have : (Finset.range 3 : Finset ℕ) = {0, 1, 2} := by decide
    rw [this]; simp; norm_num
  have hB24 : B 2 4 = 3060/77 := by
    unfold B mu r
    have : (Finset.range 3 : Finset ℕ) = {0, 1, 2} := by decide
    rw [this]; simp; norm_num
  have hB25 : B 2 5 = 4050/77 := by
    unfold B mu r
    have : (Finset.range 3 : Finset ℕ) = {0, 1, 2} := by decide
    rw [this]; simp; norm_num
  have hB26 : B 2 6 = 3645/154 := by
    unfold B mu r
    have : (Finset.range 3 : Finset ℕ) = {0, 1, 2} := by decide
    rw [this]; simp; norm_num
  -- Helper lemmas for u values
  have hu00 : u 0 0 = 0 := u_zero_right 0
  have hu01 : u 0 1 = 0 := u_zero_left 1
  have hu10 : u 1 0 = 0 := u_zero_right 1
  have hu20 : u 2 0 = 0 := u_zero_right 2
  have hu30 : u 3 0 = 0 := u_zero_right 3
  have hu40 : u 4 0 = 0 := u_zero_right 4
  have hu50 : u 5 0 = 0 := u_zero_right 5
  have hu60 : u 6 0 = 0 := u_zero_right 6
  have hu11 : u 1 1 = 90 := by
    rw [u_rec 1 1]
    simp [u_zero_right]
  have hu21 : u 2 1 = 324 := by
    rw [u_rec 2 1]
    simp [u_zero_right]
  have hu31 : u 3 1 = 243 := by
    rw [u_rec 3 1]
    simp [u_zero_right]
  have hu41 : u 4 1 = 0 := u_eq_zero_of_gt 4 1 (by norm_num)
  have hu51 : u 5 1 = 0 := u_eq_zero_of_gt 5 1 (by norm_num)
  have hu61 : u 6 1 = 0 := u_eq_zero_of_gt 6 1 (by norm_num)
  have hu12 : u 1 2 = 648 := by
    rw [u_rec 1 2]
    simp [u_zero_left, u_zero_right]
  have hu22 : u 2 2 = 24786 := by
    rw [u_rec 2 2]
    simp [u_zero_left, u_zero_right, hu11]
    norm_num
  have hu32 : u 3 2 = 174960 := by
    rw [u_rec 3 2]
    simp [u_zero_left, u_zero_right, hu21, hu11]
    norm_num
  have hu42 : u 4 2 = 446148 := by
    rw [u_rec 4 2]
    simp [u_zero_right, hu31, hu21, hu11]
    norm_num
  have hu52 : u 5 2 = 472392 := by
    rw [u_rec 5 2]
    simp [u_zero_right, hu41, hu31, hu21]
    norm_num
  have hu62 : u 6 2 = 177147 := by
    rw [u_rec 6 2]
    simp [u_zero_right, hu51, hu41, hu31]
    norm_num
  by_cases h7 : i < 7
  · -- i ∈ {1,2,3,4,5,6}
    interval_cases i
    · -- i = 1
      have hV12 : V 1 2 = 648 := by
        unfold V
        have hmin : min 1 2 = 1 := by decide
        rw [hmin]
        have hIcc : Finset.Icc (1 : ℕ) 1 = {1} := by decide
        rw [hIcc]
        simp [lam, hD1, hB11, hB12]
        norm_num
      unfold S
      rw [hu12]
      rw [hV12]
      norm_num
    · -- i = 2
      have hV22 : V 2 2 = 49572 := by
        unfold V
        have hmin : min 2 2 = 2 := by decide
        rw [hmin]
        have hIcc : Finset.Icc (1 : ℕ) 2 = {1, 2} := by decide
        rw [hIcc]
        simp [lam, hD1, hD2, hB12, hB22]
        norm_num
      unfold S
      rw [hu22]
      -- S 2 2 = 2 * 24786 = 49572
      norm_num
      rw [hV22]
    · -- i = 3
      have hV32 : V 3 2 = 524880 := by
        unfold V
        have hmin : min 3 2 = 2 := by decide
        rw [hmin]
        have hIcc : Finset.Icc (1 : ℕ) 2 = {1, 2} := by decide
        rw [hIcc]
        simp [lam, hD1, hD2, hB12, hB13, hB22, hB23]
        norm_num
      unfold S
      rw [hu32]
      norm_num
      rw [hV32]
    · -- i = 4
      have hV42 : V 4 2 = 1784592 := by
        unfold V
        have hmin : min 4 2 = 2 := by decide
        rw [hmin]
        have hIcc : Finset.Icc (1 : ℕ) 2 = {1, 2} := by decide
        rw [hIcc]
        simp [lam, hD1, hD2, hB12, hB14, hB22, hB24]
        norm_num
      unfold S
      rw [hu42]
      norm_num
      rw [hV42]
    · -- i = 5
      have hV52 : V 5 2 = 2361960 := by
        unfold V
        have hmin : min 5 2 = 2 := by decide
        rw [hmin]
        have hIcc : Finset.Icc (1 : ℕ) 2 = {1, 2} := by decide
        rw [hIcc]
        simp [lam, hD1, hD2, hB12, hB15, hB22, hB25]
        norm_num
      unfold S
      rw [hu52]
      norm_num
      rw [hV52]
    · -- i = 6
      have hV62 : V 6 2 = 1062882 := by
        unfold V
        have hmin : min 6 2 = 2 := by decide
        rw [hmin]
        have hIcc : Finset.Icc (1 : ℕ) 2 = {1, 2} := by decide
        rw [hIcc]
        simp [lam, hD1, hD2, hB12, hB16, hB22, hB26]
        norm_num
      unfold S
      rw [hu62]
      norm_num
      rw [hV62]
  · -- i ≥ 7
    have h6lt : 6 < i := by omega
    have h3lt1 : 3 * 1 < i := by omega
    have h3lt2 : 3 * 2 < i := by omega
    have hi2 : 2 ≤ i := by omega
    have hui2 : u i 2 = 0 := u_eq_zero_of_gt i 2 h6lt
    have hB1i : B 1 i = 0 := B_eq_zero_of_gt 1 i h3lt1
    have hB2i : B 2 i = 0 := B_eq_zero_of_gt 2 i h3lt2
    unfold S V lam
    rw [hui2]
    have hmin : min i 2 = 2 := Nat.min_eq_right hi2
    rw [hmin]
    have hIcc : Finset.Icc (1 : ℕ) 2 = {1, 2} := by decide
    rw [hIcc]
    simp [hB1i, hB2i]

end CalegariSlopes.ADB.Proof
