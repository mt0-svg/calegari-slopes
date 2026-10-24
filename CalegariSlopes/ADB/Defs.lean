/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Target

@[expose] public section

/-!
# Loeffler's factors `A`, `D`, `B` and the objects of the proof of `ADB = U`

The objects of Theorem 2.3 and of its proof in Section 5: `A`, `B`, `D` (Section 2, Loeffler's factors), the
operators `M`, `N`, `R` (the paper's `L_0`, `L_1`, `R`, Section 5.1), the objects of the certificate of Lemma 5.1
(Appendix A).
All functions are over `ℚ`; indices are natural numbers.
-/

namespace CalegariSlopes.ADB

/-! ## Loeffler's factors (Section 2) -/

/-- `r_m(i) = (3i + 3m)! i! / (3^m (3i)! (i + m)!)`. -/
def r (m i : ℕ) : ℚ :=
  ((3 * i + 3 * m).factorial * i.factorial : ℚ) / (3 ^ m * (3 * i).factorial * (i + m).factorial)

/-- `μ(i, j, t) = 2j i! j! (2i + 2t)! (2i + t - 1)! / ((i + j)! (i - j + 2t)! (2i)! (j - i - t)! (i - t)! (i + t)!)`,
zero when `i - j + 2t`, `j - i - t` or `i - t` is negative (the guard); under the guard every natural subtraction
in the denominator is exact. `2i + t - 1` is used for `i ≥ 1` only. -/
def mu (i j t : ℕ) : ℚ :=
  if j ≤ i + 2 * t ∧ i + t ≤ j ∧ t ≤ i then
    (2 * j * i.factorial * j.factorial * (2 * i + 2 * t).factorial * (2 * i + t - 1).factorial : ℚ) /
      ((i + j).factorial * (i + 2 * t - j).factorial * (2 * i).factorial * (j - i - t).factorial *
        (i - t).factorial * (i + t).factorial)
  else 0

/-- `B_pk = Σ_t 3^{2t} μ(p, k, t) / r_t(p)`. The guard of `μ` forces `t ≤ p`, and its first two conditions
add up to `t ≥ 0`, so the sum over `0 ≤ t ≤ p` is Loeffler's sum over all integers `t`. -/
def B (p k : ℕ) : ℚ := ∑ t ∈ Finset.range (p + 1), 3 ^ (2 * t) * mu p k t / r t p

/-- `D_p = 3^{3p} (6p)! (2p)! p! / (2 (3p)!^3)`. -/
def D (p : ℕ) : ℚ :=
  3 ^ (3 * p) * (6 * p).factorial * (2 * p).factorial * p.factorial / (2 * (3 * p).factorial ^ 3)

/-- `A_ip = (p / i) B_pi` (used for `i ≥ 1`). -/
def A (i p : ℕ) : ℚ := (p : ℚ) / i * B p i

/-! ## The pencil `(M, N)` and the operator `R` (Section 5.1) -/

/-- The coefficients `m_0, m_1, m_2` of `M`. -/
def mC (a : ℕ) (k : ℚ) : ℚ :=
  match a with
  | 0 => 9 * k ^ 2 * (k + 1) ^ 2 * (k + 2) ^ 2
  | 1 => 18 * k * (k + 1) ^ 3 * (k + 2) ^ 2
  | _ => k * (k + 1) * (k + 2) ^ 2 * (3 * k + 4) * (3 * k + 5)

/-- The coefficients `n_0, n_1, n_2` of `N`. -/
def nC (a : ℕ) (k : ℚ) : ℚ :=
  match a with
  | 0 => -81 * (k + 1) ^ 2 * (k + 2) ^ 2
  | 1 => -18 * k * (k + 2) ^ 2 * (5 * k + 7)
  | _ => -k * (k + 1) * (3 * k + 4) * (3 * k + 5)

/-- `(M f)(k) = m_0(k) f(k) + m_1(k) f(k+1) + m_2(k) f(k+2)`. -/
def mOp (f : ℕ → ℚ) (k : ℕ) : ℚ := ∑ a ∈ Finset.range 3, mC a k * f (k + a)

/-- `(N f)(k) = n_0(k) f(k) + n_1(k) f(k+1) + n_2(k) f(k+2)`. Loeffler's recurrence for the row `B_{p,.}` is
`(M + p^2 N) B_{p,.} = 0`. -/
def nOp (f : ℕ → ℚ) (k : ℕ) : ℚ := ∑ a ∈ Finset.range 3, nC a k * f (k + a)

/-- `(R W)(i, j) = Σ_{a,b} (m_a(i) n_b(j) - n_a(i) m_b(j)) W(i + a, j + b)`, that is `R = M_1 N_2 - N_1 M_2`. -/
def R (W : ℕ → ℕ → ℚ) (i j : ℕ) : ℚ :=
  ∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3,
    (mC a i * nC b j - nC a i * mC b j) * W (i + a) (j + b)

/-! ## The two sides `S` and `V` of Theorem 2.3 (Section 5) -/

/-- `S_ij = i u_ij`. -/
noncomputable def S (i j : ℕ) : ℚ := i * u i j

/-- `λ_p = p D_p` (the paper's `κ_p`). -/
def lam (p : ℕ) : ℚ := p * D p

/-- `V_ij = Σ_p λ_p B_pi B_pj`, `i (ADB)_ij` written as a bilinear form. -/
def V (i j : ℕ) : ℚ := ∑ p ∈ Finset.Icc 1 (min i j), lam p * B p i * B p j

/-! ## The objects of the certificate of Lemma 5.1 (Appendix A) -/

/-- `C_t = 3^{3t} (3p)! (2p + 2t)! (2p + t - 1)! / ((3p + 3t)! (2p)! (p - t)! t!)` for `t ≤ p`, zero for
`t > p` (used for `p ≥ 1`). -/
def Cc (p t : ℕ) : ℚ :=
  if t ≤ p then
    (3 ^ (3 * t) * (3 * p).factorial * (2 * p + 2 * t).factorial * (2 * p + t - 1).factorial : ℚ) /
      ((3 * p + 3 * t).factorial * (2 * p).factorial * (p - t).factorial * t.factorial)
  else 0

/-- `g(k) = 2k k! / (p + k)!`. -/
def g (p k : ℕ) : ℚ := 2 * k * k.factorial / (p + k).factorial

/-- `binom(n, r)` for an integer `r`: zero unless `0 ≤ r ≤ n`. -/
def binZ (n : ℕ) (r : ℤ) : ℚ := if 0 ≤ r ∧ r ≤ n then (n.choose r.toNat : ℚ) else 0

/-- `1 / n!`, zero for `n < 0`. -/
def invFac (n : ℤ) : ℚ := if 0 ≤ n then ((n.toNat).factorial : ℚ)⁻¹ else 0

/-- The master term `w(t, m) = t! / ((m + 2)! (t - m)!)` (the paper's `ϖ`), with `1 / n! = 0` for `n < 0`. -/
def w (t : ℕ) (m : ℤ) : ℚ := t.factorial * invFac (m + 2) * invFac (t - m)

/-- The summand of `B_pk` in the form of Appendix A: `β(k, t) = g(k) C_t binom(t, k - p - t)` (`g` is the paper's
`γ`). -/
def beta (p k t : ℕ) : ℚ := g p k * Cc p t * binZ t ((k : ℤ) - p - t)

/-- The rational factor of the certificate,
`ψ(k, t) = -(k+1)^2 (k+2)^2 (k - p + 2) (3p + 3t - 1) (3p + 3t - 2) / (k + p + 1)`. -/
def psi (p k t : ℕ) : ℚ :=
  -((k : ℚ) + 1) ^ 2 * ((k : ℚ) + 2) ^ 2 * ((k : ℚ) - p + 2) * (3 * (p : ℚ) + 3 * t - 1) *
    (3 * (p : ℚ) + 3 * t - 2) / ((k : ℚ) + p + 1)

/-- The certificate `φ(k, t) = ψ(k, t) g(k) C_t binom(t, k + 2 - p - t)`. -/
def phi (p k t : ℕ) : ℚ := psi p k t * g p k * Cc p t * binZ t ((k : ℤ) + 2 - p - t)

end CalegariSlopes.ADB
