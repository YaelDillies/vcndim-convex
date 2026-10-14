import VCDimConvex.BoundOne

/-!
# Small `VCₙ` dimension in `ℝⁿ` for `n ≤ 2`

In `ℝ¹`, the interval `[0, 1]` has `VC₁` dimension exactly `2`: its translates shatter `{0, 1}`.
In `ℝ²` no convex set has `VC₂` dimension `2`: a shattered grid of side `2` would be four points
shattered by translates, which `not_shatter_four` rules out.
-/

namespace VCDimConvex

/-- The unit interval in `ℝ¹`. -/
def unitInterval1 : Set (Point 1) := {p | 0 ≤ p 0 ∧ p 0 ≤ 1}

theorem convex_unitInterval1 : Convex ℝ unitInterval1 := by
  intro p hp q hq a b ha hb hab
  simp only [unitInterval1, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  constructor <;> nlinarith

/-- Translates of `[0, 1]` shatter the grid `{0, 1}`, so its `VC₁` dimension is not at most `1`. -/
theorem not_hasAddVCNDimAtMost_unitInterval1 : ¬ HasAddVCNDimAtMost unitInterval1 1 1 := by
  classical
  intro h
  let z : Fin 1 → Fin 2 := fun _ => 0
  let o : Fin 1 → Fin 2 := fun _ => 1
  let y : Set (Fin 1 → Fin 2) → Point 1 := fun s => fun _ =>
    if z ∈ s then (if o ∈ s then 0 else 1) else (if o ∈ s then -1 else 5)
  refine h (fun _ j _ => (j : ℝ)) y fun i s => ?_
  have hi : i = z ∨ i = o := by
    rcases Fin.exists_fin_two.mp ⟨i 0, rfl⟩ with h0 | h0
    · exact .inl (funext fun k => by rw [Subsingleton.elim k 0, h0])
    · exact .inr (funext fun k => by rw [Subsingleton.elim k 0, h0])
  rcases hi with rfl | rfl <;> by_cases hz : z ∈ s <;> by_cases ho : o ∈ s <;>
    simp [unitInterval1, y, z, o, hz, ho] at *

/-- No convex set in `ℝ²` has `VC₂` dimension `2`: grids of side `2` are never shattered. -/
theorem hasAddVCNDimAtMost_two_one_of_convex (C : Set (Point 2)) (hC : Convex ℝ C) :
    HasAddVCNDimAtMost C 2 1 := by
  intro x y hxy
  let e : Fin 4 ≃ (Fin 2 → Fin 2) := (finFunctionFinEquiv (m := 2) (n := 2)).symm
  refine not_shatter_four hC (a := fun j => ∑ k, x k (e j k)) fun s => ⟨y (e '' s), fun j => ?_⟩
  exact (hxy (e j) (e '' s)).trans e.injective.mem_set_image

end VCDimConvex
