import VCDimConvex.FCStatement
import VCDimConvex.FinalBound

/-!
# A finite additive VC_n bound for convex sets

This file imports the local proof. The theorem below repeats the complete binders
and conclusion of the Formal Conjectures target
`VCDimConvex.exists_hasAddVCNDimAtMost_n_of_convex_rn_add_one` and
discharges it using the explicit bound proved in `VCDimConvex.FinalBound`.
-/

namespace VCDimConvexFC

/-- The exact uniform finite-bound existence target registered in Formal Conjectures. -/
theorem vcdim_convex_uniform_bound_solved (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : ℕ, ∀ C : Set (Fin (n + 1) → ℝ), Convex ℝ C → HasAddVCNDimAtMost C n d :=
  VCDimConvex.fc_exists_hasAddVCNDimAtMost_n_of_convex_rn_add_one n hn

#check VCDimConvex.explicit_bound
#check vcdim_convex_uniform_bound_solved
#print axioms VCDimConvex.explicit_bound
#print axioms vcdim_convex_uniform_bound_solved

end VCDimConvexFC
