/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Spectral.Main
public import CalegariSlopes.Bridge.C4Main
public import CalegariSlopes.Bridge.JMain

@[expose] public section

/-!
# Calegari's conjecture at p = 3 on overconvergent forms (Theorem 1.2)

The statement of `CalegariSlopes/Challenge.lean`, over the definitions of `CalegariSlopes/Statement.lean`, proved as in
Section 2: `CalegariSlopes.Spectral.calegari_conjecture_overconvergent_of`, the proof of Theorem 1.2 for any series
`G` with the two properties of Theorem 2.1, applied to `G = Sol a2 27` (the paper's `g`), with Theorem 2.1 (b) from
`CalegariSlopes.Bridge.c4_Sol` and Theorem 2.1 (a) from `CalegariSlopes.Bridge.jhyp_Sol`.

The term of the statement differs from the one of the challenge in its instances, definitionally equal: with the
imports of the proof modules, instance search finds `NormedField.instCompletableTopField` where the statement file
finds `Valued.completable` for the completion of `PadicAlgCl 3`. `CalegariSlopes/Solution.lean` proves the statement
as elaborated in the challenge, for Comparator (`config.json`). `slope` is written `Overconvergent.slope`: the bare
name would resolve to `CalegariSlopes.slope` of `CalegariSlopes/Target.lean` (the same function).
-/

namespace CalegariSlopes.Final

open CalegariSlopes.Overconvergent

/-- **Calegari's conjecture at p = 3** (Theorem 1.2): the nonzero eigenvalues of
`U_3` on the 3-adic overconvergent cusp forms of tame level 1 and weight 0, counted with algebraic multiplicity, are
`ev 1, ev 2, ...` with `‖ev i‖ = 3 ^ (-slope i)`. -/
theorem calegari_conjecture_overconvergent :
    ∃ ev : ℕ+ → K, (∀ i, ‖ev i‖ = (3 : ℝ) ^ (-(Overconvergent.slope i : ℤ))) ∧
      ∀ μ : K, μ ≠ 0 → FiniteDimensional K (genEig μ) ∧
        Module.finrank K (genEig μ) = Nat.card {i : ℕ+ // ev i = μ} :=
  Spectral.calegari_conjecture_overconvergent_of (Bridge.Sol Bridge.a2 27) Bridge.c4_Sol Bridge.jhyp_Sol

end CalegariSlopes.Final
