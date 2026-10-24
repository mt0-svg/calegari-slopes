/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Newton.Proofs
public import CalegariSlopes.ADB.Main

@[expose] public section

/-!
# Corollary 7.1, the characteristic series

The statement of `CalegariSlopes/ChallengeMatrix.lean`, over the definitions of `CalegariSlopes/Target.lean`:
`newton` (module `CalegariSlopes.Newton.Proofs`) applied to Loeffler's identity `CalegariSlopes.ADB.adb`
(Theorem 2.3, module `CalegariSlopes.ADB.Main`). `CalegariSlopes/SolutionMatrix.lean` proves it under the name of
the challenge, for Comparator (`config-matrix.json`).
-/

namespace CalegariSlopes.Newton

/-- **Corollary 7.1**: the principal minors of order `n` of `u` are summable, their sum `c n` is nonzero and has
valuation `slope 1 + ... + slope n`; from Theorem 2.3 (`CalegariSlopes.ADB.adb`). -/
theorem calegari_conjecture (n : ℕ) :
    Summable (fun S : {S : Finset ℕ+ // S.card = n} => principalMinor S.1) ∧ c n ≠ 0 ∧
      Padic.valuation (c n) = ∑ i ∈ Finset.Icc 1 n, (slope i : ℤ) :=
  newton CalegariSlopes.ADB.adb n

end CalegariSlopes.Newton
