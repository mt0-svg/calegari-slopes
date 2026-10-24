/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.Statement

@[expose] public section

/-! The statement of `CalegariSlopes/Challenge.lean` elaborated in the environment of the challenge. This module
depends only on `CalegariSlopes/Statement.lean`, the definitions of the challenge without its theorem, so the
statement below, the one of the challenge verbatim, elaborates to the same term as in `Challenge.lean` (the same
instances are found; with the imports of the proof modules, instance search takes other paths, for instance
`NormedField.instCompletableTopField` for the completion of `PadicAlgCl 3`, definitionally equal but a different
term). `Solution.lean` states its theorem as `type_of% (stmt_of _)`, which is this term. -/

open PowerSeries Filter Topology

namespace CalegariSlopes.Overconvergent.FrozenType

/-- The statement of the challenge, as a hypothesis and as a conclusion. -/
theorem stmt_of
    (h : ∃ ev : ℕ+ → K, (∀ i, ‖ev i‖ = (3 : ℝ) ^ (-(slope i : ℤ))) ∧
      ∀ μ : K, μ ≠ 0 → FiniteDimensional K (genEig μ) ∧
        Module.finrank K (genEig μ) = Nat.card {i : ℕ+ // ev i = μ}) :
    ∃ ev : ℕ+ → K, (∀ i, ‖ev i‖ = (3 : ℝ) ^ (-(slope i : ℤ))) ∧
      ∀ μ : K, μ ≠ 0 → FiniteDimensional K (genEig μ) ∧
        Module.finrank K (genEig μ) = Nat.card {i : ℕ+ // ev i = μ} :=
  h

end CalegariSlopes.Overconvergent.FrozenType
