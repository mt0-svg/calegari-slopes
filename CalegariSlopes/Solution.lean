/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import CalegariSlopes.SolutionStatement
public import CalegariSlopes.Spectral.Main
public import CalegariSlopes.Bridge.C4Main
public import CalegariSlopes.Bridge.JMain

@[expose] public section

/-! Solution module of the Comparator check of `config.json`: the theorem of `CalegariSlopes/Challenge.lean`
(Theorem 1.2), under its name there, with the proof of `CalegariSlopes.Final.calegari_conjecture_overconvergent`:
the proof of Theorem 1.2 in Section 2, applied to `G = Sol a2 27` with Theorem 2.1 (a) and (b). The type is
`type_of% (stmt_of _)`, the statement as elaborated in the environment of the challenge (`SolutionStatement.lean`). -/

namespace CalegariSlopes.Overconvergent

theorem calegari_conjecture_overconvergent :
    type_of% (FrozenType.stmt_of (Spectral.calegari_conjecture_overconvergent_of (Bridge.Sol Bridge.a2 27)
      Bridge.c4_Sol Bridge.jhyp_Sol)) :=
  FrozenType.stmt_of (Spectral.calegari_conjecture_overconvergent_of (Bridge.Sol Bridge.a2 27) Bridge.c4_Sol
    Bridge.jhyp_Sol)

end CalegariSlopes.Overconvergent
