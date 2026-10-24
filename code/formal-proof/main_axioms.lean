import CalegariSlopes.Main
import CalegariSlopes.Solution
import CalegariSlopes.SolutionMatrix

-- The axioms of the two main theorems, under their names in the development and in the solution modules of
-- config.json and config-matrix.json, then of the theorems of config-conj5.json (Lemma 8.1 and Theorem 8.2) and of
-- config-conj5-spectral.json (Corollaries 8.3 and 8.4).
-- Run from the package root: lake env lean code/formal-proof/main_axioms.lean

#print axioms CalegariSlopes.Final.calegari_conjecture_overconvergent
#print axioms CalegariSlopes.Newton.calegari_conjecture
#print axioms CalegariSlopes.Overconvergent.calegari_conjecture_overconvergent
#print axioms CalegariSlopes.calegari_conjecture
#print axioms CalegariSlopes.Conj5.factorization
#print axioms CalegariSlopes.Conj5.factors_unitTriangular
#print axioms CalegariSlopes.Conj5.factorization_unique
#print axioms CalegariSlopes.Conj5.integral_iff
#print axioms CalegariSlopes.Conj5.congr_maximal_iff
#print axioms CalegariSlopes.Conj5.valuation_B_ge
#print axioms CalegariSlopes.Conj5.valuation_A_ge
#print axioms CalegariSlopes.Conj5.valuation_uniform
#print axioms CalegariSlopes.Conj5.congr_three_iff
#print axioms CalegariSlopes.Conj5.B_two_four
#print axioms CalegariSlopes.Conj5.A_four_two
#print axioms CalegariSlopes.Conj5.padicValRat_B_two_four
#print axioms CalegariSlopes.Conj5.padicValRat_A_four_two
#print axioms CalegariSlopes.Conj5.exists_gamma
#print axioms CalegariSlopes.Conj5.spectral_expansion
#print axioms CalegariSlopes.Conj5.x_mem_L
#print axioms CalegariSlopes.Conj5.norm_x_le
