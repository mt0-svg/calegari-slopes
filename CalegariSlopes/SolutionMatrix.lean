/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Newton.Proofs
public import CalegariSlopes.ADB.Main

@[expose] public section

/-! Solution module of the Comparator check of `config-matrix.json`: the theorem of
`CalegariSlopes/ChallengeMatrix.lean` (Corollary 7.1), under its name there, with the proof of
`CalegariSlopes.Newton.calegari_conjecture`: `newton` applied to `CalegariSlopes.ADB.adb`. The statement is the one
of the challenge, verbatim. -/

open MvPowerSeries

namespace CalegariSlopes

theorem calegari_conjecture (n : ℕ) :
    Summable (fun S : {S : Finset ℕ+ // S.card = n} => principalMinor S.1) ∧ c n ≠ 0 ∧
      Padic.valuation (c n) = ∑ i ∈ Finset.Icc 1 n, (slope i : ℤ) :=
  CalegariSlopes.Newton.newton CalegariSlopes.ADB.adb n

end CalegariSlopes
