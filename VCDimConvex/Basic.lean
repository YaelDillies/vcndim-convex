import Mathlib.Analysis.Convex.Hull
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic
import VCDimConvex.Mathlib.Combinatorics.Additive.VCDim

/-!
# Finite additive arrays and convex labels

These definitions implement the array-counting setup in section 1 of the
VCₙ argument in `FCreportv1.html`, exploration 30. The additive VCₙ predicate
is defined here with the same statement as `HasAddVCNDimAtMost` in Formal Conjectures
(`FormalConjecturesForMathlib/Combinatorics/Additive/VCDim.lean`).
-/

section VCNDim

variable {G : Type*} [AddCommGroup G]

/-- A set `A` in an abelian group has VCₙ dimension at most `d` iff one cannot find two sequences
`x` and `y` of elements indexed by `[n] × [d + 1]` and `2 ^ [d + 1]ⁿ` respectively such that
`y s + ∑ k, x (k, i k) ∈ A ↔ i ∈ s` for all `i ∈ [d + 1]ⁿ`, `s ⊆ [d + 1]ⁿ`. -/
def HasAddVCNDimAtMost (A : Set G) (n d : ℕ) : Prop :=
  ∀ (x : Fin n → Fin (d + 1) → G) (y : Set (Fin n → Fin (d + 1)) → G),
    ¬ ∀ i s, y s + ∑ k, x k (i k) ∈ A ↔ i ∈ s

theorem HasAddVCNDimAtMost.mono {A : Set G} {n d d' : ℕ} (h : HasAddVCNDimAtMost A n d)
    (hdd' : d ≤ d') : HasAddVCNDimAtMost A n d' := by
  intro x y hxy
  let e : Fin (d + 1) → Fin (d' + 1) := Fin.castLE (by omega)
  refine h (fun k j => x k (e j)) (fun S => y ((fun i => e ∘ i) '' S)) fun i S =>
    (hxy (e ∘ i) _).trans ?_
  exact ((Fin.castLE_injective _).comp_left).mem_set_image

open scoped Pointwise in
/-- If the translates of `A` shatter `S`, then any injective family of points of `S` is shattered
in the explicit sense. -/
theorem exists_translate_of_shatters {A S : Set G} (hS : Shatters {t +ᵥ A | t : G} S) {ι : Type*}
    {a : ι → G} (ha : Function.Injective a) (haS : ∀ j, a j ∈ S) (s : Set ι) :
    ∃ t, ∀ j, t + a j ∈ A ↔ j ∈ s := by
  obtain ⟨_, ⟨t, rfl⟩, hD⟩ := hS (show a '' s ⊆ S by rintro _ ⟨j, -, rfl⟩; exact haS j)
  refine ⟨-t, fun j => ?_⟩
  have := congrArg (a j ∈ ·) hD
  simp only [Set.inf_eq_inter, Set.mem_inter_iff, haS j, true_and, ha.mem_set_image] at this
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] at this
  exact Iff.of_eq this

open scoped Pointwise in
/-- A family of points shattered in the explicit sense is shattered by the translates of `A`. -/
theorem shatters_range_of_forall_exists_translate {A : Set G} {ι : Type*} {a : ι → G}
    (hshat : ∀ s : Set ι, ∃ t, ∀ j, t + a j ∈ A ↔ j ∈ s) :
    Function.Injective a ∧ Shatters {t +ᵥ A | t : G} (Set.range a) := by
  refine ⟨fun j j' hjj' => ?_, fun B hB => ?_⟩
  · obtain ⟨t, ht⟩ := hshat {j}
    simpa [eq_comm] using ((ht j').symm.trans (by rw [← hjj'])).trans (ht j)
  obtain ⟨t, ht⟩ := hshat (a ⁻¹' B)
  refine ⟨-t +ᵥ A, ⟨-t, rfl⟩, Set.ext fun z => ?_⟩
  simp only [Set.inf_eq_inter, Set.mem_inter_iff, Set.mem_range, Set.mem_vadd_set_iff_neg_vadd_mem,
    neg_neg, vadd_eq_add]
  constructor
  · rintro ⟨⟨j, rfl⟩, hj⟩
    exact (ht j).mp hj
  · intro hz
    obtain ⟨j, rfl⟩ := hB hz
    exact ⟨⟨j, rfl⟩, (ht j).mpr hz⟩

/-- The VC₁ dimension is at most the VC dimension. -/
theorem HasAddVCDimLE.hasAddVCNDimAtMost_one {A : Set G} {d : ℕ} (h : HasAddVCDimLE d A) :
    HasAddVCNDimAtMost A 1 d := by
  intro x y hxy
  obtain ⟨hinj, hS⟩ := shatters_range_of_forall_exists_translate (A := A) (a := fun j => x 0 j)
    fun s => ⟨y {i | i 0 ∈ s}, fun j => by simpa using hxy (fun _ => j) {i | i 0 ∈ s}⟩
  have := h (Set.finite_range _) hS
  rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

end VCNDim

namespace VCDimConvex

abbrev Grid (D m : ℕ) := Fin D → Fin m

abbrev Point (D : ℕ) := Fin D → ℝ

/-- The point associated with an index of an additive array. -/
def gridSum {D m : ℕ} {G : Type*} [AddCommMonoid G]
    (z : Fin D → Fin m → G) (i : Grid D m) : G :=
  ∑ k, z k (i k)

/-- A label set is realized by one additive array in a fixed set `C`. -/
def Realizes {D m : ℕ} {G : Type*} [AddCommMonoid G]
    (C : Set G) (S : Set (Grid D m)) : Prop :=
  ∃ z : Fin D → Fin m → G, ∀ i, gridSum z i ∈ C ↔ i ∈ S

/-- All labels realized by convex sets and additive arrays in ambient dimension `D`. -/
noncomputable def convexLabels (D m : ℕ) : Finset (Set (Grid D m)) := by
  classical
  exact Finset.univ.filter fun S =>
    ∃ C : Set (Point D), Convex ℝ C ∧ Realizes C S

@[simp] theorem mem_convexLabels {D m : ℕ} {S : Set (Grid D m)} :
    S ∈ convexLabels D m ↔ ∃ C : Set (Point D), Convex ℝ C ∧ Realizes C S := by
  classical
  simp [convexLabels]

@[simp] theorem card_grid (D m : ℕ) : Fintype.card (Grid D m) = m ^ D := by
  simp [Grid]

@[simp] theorem card_label_sets (D m : ℕ) :
    Fintype.card (Set (Grid D m)) = 2 ^ (m ^ D) := by
  simp

/-- The explicit bound proposed in the paper argument. -/
def bound (n : ℕ) : ℕ := 2 ^ (8 * (n + 2) ^ n) - 1

end VCDimConvex
