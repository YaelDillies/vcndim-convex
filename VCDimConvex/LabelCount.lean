import VCDimConvex.MinorHullRecovery
import VCDimConvex.MinorSignPatterns

/-!
# Count convex labels by minor signs and representative subsets

An additive array is recorded by its minor sign vector together with a representative subset
of indices. Equal minor signs give equal hull memberships, so the encoding is injective.
-/

namespace VCDimConvex

/-- The minor sign vector of an additive array. -/
noncomputable def arrayMinorSigns {D m : ℕ} (z : Fin D → Fin m → Point D) :
    MinorIndex D m → Fin 3 :=
  fun j => signCode (MvPolynomial.eval (arrayAssignment z) (minorPolynomial j))

theorem arrayMinorSigns_mem {D m : ℕ} (z : Fin D → Fin m → Point D) :
    arrayMinorSigns z ∈ minorSignPatterns D m := by
  classical
  simp only [minorSignPatterns, ternaryPatterns, Finset.mem_filter, Finset.mem_univ,
    true_and]
  exact ⟨arrayAssignment z, fun _ => rfl⟩

/-- Any family of representative subsets covering all labels gives a product bound. -/
theorem card_convexLabels_le_signs_mul_generators {D m : ℕ}
    (G : Finset (Finset (Grid D m)))
    (hgen : ∀ S ∈ convexLabels D m,
      ∃ (z : Fin D → Fin m → Point D) (V : Finset (Grid D m)),
        V ∈ G ∧ ∀ i, i ∈ S ↔ gridSum z i ∈ indexedHull (gridSum z) V) :
    (convexLabels D m).card ≤ (minorSignPatterns D m).card * G.card := by
  classical
  choose z V hV hlabels using fun S : ↑(convexLabels D m) => hgen S S.property
  let encode : ↑(convexLabels D m) → ↑(minorSignPatterns D m) × ↑G :=
    fun S => (⟨arrayMinorSigns (z S), arrayMinorSigns_mem (z S)⟩, ⟨V S, hV S⟩)
  have hinj : Function.Injective encode := by
    intro S T he
    have hs : arrayMinorSigns (z S) = arrayMinorSigns (z T) :=
      congrArg (fun e => e.1.val) he
    have hv : V S = V T := congrArg (fun e => e.2.val) he
    apply Subtype.ext
    ext i
    rw [hlabels S i, hlabels T i, ← hv]
    exact same_signs_same_hull_membership (z S) (z T) (fun j => congrFun hs j) (V S) i
  simpa only [Fintype.card_prod, Fintype.card_coe] using Fintype.card_le_of_injective encode hinj

end VCDimConvex
