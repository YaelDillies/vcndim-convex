import VCDimConvex.BoundGeneral
import VCDimConvex.FCStatement
import VCDimConvex.InfiniteDim
import VCDimConvex.SideThree
import VCDimConvex.LowDim

/-!
# A finite additive VC_n bound for convex sets

This file imports the local proof. The theorem below repeats the complete binders
and conclusion of the Formal Conjectures target
`VCDimConvex.exists_hasAddVCNDimAtMost_n_of_convex_rn_add_one` and
discharges it using the explicit bound `2^(2^(n+1)+2) - 1` from `VCDimConvex.BoundGeneral`. It also
records the much smaller witnesses `3` for `n = 1` (`VCDimConvex.BoundOne`) and `123` for `n = 2`
(`VCDimConvex.Bound123`), a convex set in `ℝⁿ⁺²` of infinite VCₙ dimension
(`VCDimConvex.InfiniteDim`), and the bound `2` in `ℝⁿ` (`VCDimConvex.SideThree`).
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

/-- Every convex set in `ℝ^(n+1)` has additive VCₙ dimension at most `2^(2^(n+1)+2) - 1`. -/
theorem vcdim_convex_le_general (n : ℕ) (hn : n ≠ 0) :
    ∀ C : Set (Fin (n + 1) → ℝ), Convex ℝ C → HasAddVCNDimAtMost C n (2 ^ (2 ^ (n + 1) + 2) - 1) :=
  VCDimConvex.explicit_bound_general n hn

/-- There exists a convex set in `ℝⁿ⁺²` of infinite `VCₙ` dimension. -/
theorem exists_convex_rn_add_two_forall_not_hasAddVCNDimAtMost (n : ℕ) :
    ∃ C : Set (Fin (n + 2) → ℝ), Convex ℝ C ∧ ∀ d, ¬ HasAddVCNDimAtMost C n d :=
  VCDimConvex.exists_convex_forall_not_hasAddVCNDimAtMost n

/-- Every convex set in `ℝⁿ` has additive VCₙ dimension at most `2`. -/
theorem vcdim_convex_rn_le_two (n : ℕ) (hn : 1 ≤ n) :
    ∀ C : Set (Fin n → ℝ), Convex ℝ C → HasAddVCNDimAtMost C n 2 :=
  fun C hC => VCDimConvex.hasAddVCNDimAtMost_two_of_convex hn C hC

/-- The bound `2` in `ℝⁿ` is attained for `n = 1`, by the unit interval. -/
theorem exists_convex_r1_not_hasAddVCNDimAtMost_one :
    ∃ C : Set (Fin 1 → ℝ), Convex ℝ C ∧ ¬ HasAddVCNDimAtMost C 1 1 :=
  ⟨_, VCDimConvex.convex_unitInterval1, VCDimConvex.not_hasAddVCNDimAtMost_unitInterval1⟩

/-- Every convex set in `ℝ²` has additive VC₂ dimension at most `1`. -/
theorem vcdim_convex_r2_le_one :
    ∀ C : Set (Fin 2 → ℝ), Convex ℝ C → HasAddVCNDimAtMost C 2 1 :=
  VCDimConvex.hasAddVCNDimAtMost_two_one_of_convex

end VCDimConvexFC

#print axioms VCDimConvexFC.vcdim_convex_rn_le_two
#print axioms VCDimConvexFC.exists_convex_r1_not_hasAddVCNDimAtMost_one
#print axioms VCDimConvexFC.vcdim_convex_r2_le_one
