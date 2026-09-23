import VCDimConvexBound.FCStatement
import VCDimConvexBound.FinalBound

/-!
# A finite additive VC_n bound for convex sets

This file imports the local proof. The theorem below repeats the complete binders
and conclusion of the Formal Conjectures target
`VCDimConvex.exists_hasAddVCNDimAtMost_n_of_convex_rn_add_one` and
discharges it using the Janson bound proved in `VCDimConvexBound.JansonBound`.
The original bound from `VCDimConvexBound.FinalBound` is still built and checked.
-/

namespace VCDimConvexBoundFC

/-- The exact uniform finite-bound existence target registered in Formal Conjectures. -/
theorem vcdim_convex_uniform_bound_solved (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : ℕ, ∀ C : Set (Fin (n + 1) → ℝ), Convex ℝ C → HasAddVCNDimAtMost C n d :=
  VCDimConvexBound.fc_exists_hasAddVCNDimAtMost_n_of_convex_rn_add_one n hn

#check VCDimConvexBound.explicit_bound
#check VCDimConvexBound.janson_bound
#check vcdim_convex_uniform_bound_solved
#print axioms VCDimConvexBound.explicit_bound
#print axioms VCDimConvexBound.janson_bound
#print axioms vcdim_convex_uniform_bound_solved

end VCDimConvexBoundFC
