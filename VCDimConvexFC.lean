import VCDimConvex.BoundOne
import VCDimConvex.Bound123
import VCDimConvex.FCStatement
import VCDimConvex.FinalBound

/-!
# A finite additive VC_n bound for convex sets

This file imports the local proof. The theorem below repeats the complete binders
and conclusion of the Formal Conjectures target
`VCDimConvex.exists_hasAddVCNDimAtMost_n_of_convex_rn_add_one` and
discharges it using the explicit bound proved in `VCDimConvex.FinalBound`.
For `n = 2` it also records the much smaller witness `123` from `VCDimConvex.Bound123`.
-/

namespace VCDimConvexFC

/-- The exact uniform finite-bound existence target registered in Formal Conjectures. -/
theorem vcdim_convex_uniform_bound_solved (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : ℕ, ∀ C : Set (Fin (n + 1) → ℝ), Convex ℝ C → HasAddVCNDimAtMost C n d :=
  VCDimConvex.fc_exists_hasAddVCNDimAtMost_n_of_convex_rn_add_one n hn

/-- Every convex set in `ℝ²` has additive VC dimension at most `3`. -/
theorem vcdim_convex_one_le_three :
    ∀ C : Set (Fin 2 → ℝ), Convex ℝ C → HasAddVCDimLE 3 C :=
  VCDimConvex.explicit_bound_one

/-- Every convex set in `ℝ³` has additive VC₂ dimension at most `123`. -/
theorem vcdim_convex_two_le_123 :
    ∀ C : Set (Fin 3 → ℝ), Convex ℝ C → HasAddVCNDimAtMost C 2 123 :=
  VCDimConvex.explicit_bound_123

#print axioms vcdim_convex_uniform_bound_solved
#print axioms vcdim_convex_one_le_three
#print axioms vcdim_convex_two_le_123

end VCDimConvexFC
