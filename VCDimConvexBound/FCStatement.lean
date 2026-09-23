import VCDimConvexBound.JansonBound

/-!
# The exact pinned Formal Conjectures existence statement

The statement below is copied from
`FormalConjectures/Other/VCDimConvex.lean` at the pinned revision.
`HasAddVCNDimAtMost` is the local copy in `VCDimConvexBound.Basic`. The proof uses only the local
proved Janson bound (`JansonBound`), not the conjecture declaration from the upstream file.
-/

namespace VCDimConvexBound

theorem fc_exists_hasAddVCNDimAtMost_n_of_convex_rn_add_one (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : ℕ, ∀ C : Set (Fin (n + 1) → ℝ), Convex ℝ C → HasAddVCNDimAtMost C n d :=
  exists_bound_janson n hn

end VCDimConvexBound
