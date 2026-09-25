import VCDimConvex.Basic

/-!
# From counting additive arrays to a VCₙ bound

This is the final reduction of section 7 of the paper argument. Shattering
an `n`-dimensional grid realizes every label on an `(n + 1)`-dimensional
array. We place the new translation coordinate first; permuting coordinates
gives the presentation with the translation coordinate last.

The counting inequality is a hypothesis here. It is proved in `BoundOne`, `Bound123` and
`BoundGeneral`.
-/

namespace VCDimConvex

/-- Slice an arbitrary label by its first coordinate, and use the shattering
translations as the first sequence of a larger additive array. -/
theorem realizes_of_shattering {G : Type*} [AddCommGroup G]
    {n m : ℕ} {C : Set G}
    (x : Fin n → Fin m → G) (y : Set (Grid n m) → G)
    (hxy : ∀ i s, y s + ∑ k, x k (i k) ∈ C ↔ i ∈ s)
    (S : Set (Grid (n + 1) m)) : Realizes C S := by
  let z : Fin (n + 1) → Fin m → G :=
    Fin.cons (fun j => y {i | Fin.cons j i ∈ S}) x
  refine ⟨z, fun i => ?_⟩
  simpa [gridSum, z, Fin.sum_univ_succ, Fin.tail, Fin.cons_self_tail] using
    hxy (Fin.tail i) {j | Fin.cons (i 0) j ∈ S}

/-- Shattering forces all labels to occur, even while keeping `C` fixed. -/
theorem convexLabels_eq_univ_of_shattering {n m : ℕ}
    {C : Set (Point (n + 1))} (hC : Convex ℝ C)
    (x : Fin n → Fin m → Point (n + 1))
    (y : Set (Grid n m) → Point (n + 1))
    (hxy : ∀ i s, y s + ∑ k, x k (i k) ∈ C ↔ i ∈ s) :
    convexLabels (n + 1) m = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro S
  exact mem_convexLabels.mpr ⟨C, hC, realizes_of_shattering x y hxy S⟩

/-- A strict count of convex labels gives the actual FC predicate. -/
theorem hasAddVCNDimAtMost_of_label_count (n d : ℕ)
    (hcount : (convexLabels (n + 1) (d + 1)).card < 2 ^ ((d + 1) ^ (n + 1)))
    (C : Set (Point (n + 1))) (hC : Convex ℝ C) :
    HasAddVCNDimAtMost C n d := by
  intro x y hxy
  have hfull := convexLabels_eq_univ_of_shattering hC x y hxy
  simp [hfull] at hcount

/-- The side-length version keeps the off-by-one conversion explicit. -/
theorem hasAddVCNDimAtMost_of_label_count_side (n m : ℕ) (hm : 0 < m)
    (hcount : (convexLabels (n + 1) m).card < 2 ^ (m ^ (n + 1)))
    (C : Set (Point (n + 1))) (hC : Convex ℝ C) :
    HasAddVCNDimAtMost C n (m - 1) := by
  cases m with
  | zero => omega
  | succ d =>
    simpa only [Nat.succ_sub_one] using
      hasAddVCNDimAtMost_of_label_count n d hcount C hC

end VCDimConvex
