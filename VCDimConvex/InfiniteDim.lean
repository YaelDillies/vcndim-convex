import Mathlib.Analysis.Convex.Basic
import VCDimConvex.Basic

/-!
# A convex set in `ℝⁿ⁺²` of infinite `VCₙ` dimension

We construct a convex set `C ⊆ ℝ^(n+2)` which has infinite additive VCₙ dimension. Write points of
`ℝ^(n+2)` as `(u, h)` with `u ∈ ℝ^(n+1)` and `h ∈ ℝ`, and lift `u` to the paraboloid point
`(u, ∑ⱼ uⱼ²)`. Fix an injection `α` from the pairs `(d, S)`, where `S` is a set of grid indices
`Fin n → Fin (d + 1)`, into `ℝ`, and let `C` be the convex hull of the lifts of `(i, α (d, S))`
for all `d`, `S` and `i ∈ S`.

A lifted point `(q, ∑ⱼ qⱼ²)` lies strictly above the tangent hyperplane at `q` except at `q`
itself, so it lies in `C` only if it is one of the generators. Hence the grid
`x k j = (j eₖ, j²)`, translated by `y S = (α (d, S) eₙ, α (d, S)²)`, is shattered by `C`.
-/

open Finset

namespace VCDimConvex

variable {n : ℕ}

/-- The lift of `u ∈ ℝ^(n+1)` to the paraboloid `h = ∑ⱼ uⱼ²` in `ℝ^(n+2)`. -/
noncomputable def paraboloidLift (u : Fin (n + 1) → ℝ) : Fin (n + 2) → ℝ :=
  Fin.snoc (α := fun _ => ℝ) u (∑ j, u j ^ 2)

/-- A lifted point lies in the convex hull of a set of lifted points only if it is one of them. -/
lemma paraboloidLift_mem_convexHull {T : Set (Fin (n + 1) → ℝ)} {q : Fin (n + 1) → ℝ}
    (hq : paraboloidLift q ∈ convexHull ℝ (paraboloidLift '' T)) : q ∈ T := by
  by_contra hqT
  -- The tangent functional at `q`: `ψ (u, h) = h - 2 ⟪q, u⟫ + ‖q‖²`.
  let L : (Fin (n + 2) → ℝ) →ₗ[ℝ] ℝ :=
    LinearMap.proj (Fin.last (n + 1)) - ∑ j, (2 * q j) • LinearMap.proj j.castSucc
  have hL : ∀ u, L (paraboloidLift u) + ∑ j, q j ^ 2 = ∑ j, (u j - q j) ^ 2 := by
    intro u
    simp only [L, paraboloidLift, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, Fin.snoc_last, Fin.snoc_castSucc, smul_eq_mul]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsub : paraboloidLift '' T ⊆ {p | -∑ j, q j ^ 2 < L p} := by
    rintro _ ⟨u, hu, rfl⟩
    have hne : u ≠ q := by rintro rfl; exact hqT hu
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
    have hpos : 0 < ∑ j, (u j - q j) ^ 2 :=
      Finset.sum_pos' (fun _ _ => sq_nonneg _)
        ⟨j, mem_univ _, by have := sub_ne_zero.mpr hj; positivity⟩
    simp only [Set.mem_ofPred_eq]
    linarith [hL u]
  have := convexHull_min hsub (convex_halfSpace_gt L.isLinear _) hq
  simp only [Set.mem_ofPred_eq] at this
  linarith [hL q, show ∑ j, (q j - q j) ^ 2 = 0 by simp]

/-- The index set of the shattering configurations: a side length and a set of grid indices. -/
abbrev ShatterIndex (n : ℕ) := Σ d : ℕ, Set (Fin n → Fin (d + 1))

/-- An injection of the shattering configurations into `ℝ`. -/
noncomputable def shatterLabel (n : ℕ) : ShatterIndex n → ℝ :=
  fun p => (Classical.choose (Countable.exists_injective_nat (ShatterIndex n)) p : ℝ)

lemma shatterLabel_injective : Function.Injective (shatterLabel n) :=
  (Nat.cast_injective (R := ℝ)).comp
    (Classical.choose_spec (Countable.exists_injective_nat (ShatterIndex n)))

/-- The base point `(i, α (d, S)) ∈ ℝ^(n+1)`. -/
noncomputable def shatterBase (d : ℕ) (S : Set (Fin n → Fin (d + 1))) (i : Fin n → Fin (d + 1)) :
    Fin (n + 1) → ℝ :=
  Fin.snoc (α := fun _ => ℝ) (fun k => (i k : ℝ)) (shatterLabel n ⟨d, S⟩)

/-- The convex set of infinite VCₙ dimension. -/
noncomputable def infiniteVCNSet (n : ℕ) : Set (Fin (n + 2) → ℝ) :=
  convexHull ℝ (paraboloidLift ''
    {u | ∃ d S i, i ∈ S ∧ u = shatterBase (n := n) d S i})

lemma paraboloidLift_shatterBase_mem_iff (d : ℕ) (S : Set (Fin n → Fin (d + 1)))
    (i : Fin n → Fin (d + 1)) :
    paraboloidLift (shatterBase d S i) ∈ infiniteVCNSet n ↔ i ∈ S := by
  refine ⟨fun h => ?_, fun h => subset_convexHull ℝ _ ⟨_, ⟨d, S, i, h, rfl⟩, rfl⟩⟩
  obtain ⟨d', S', i', hi', he⟩ := paraboloidLift_mem_convexHull h
  have hlast := congrFun he (Fin.last n)
  simp only [shatterBase, Fin.snoc_last] at hlast
  obtain ⟨rfl, hS⟩ := Sigma.mk.inj_iff.mp (shatterLabel_injective hlast)
  obtain rfl := eq_of_heq hS
  have hinit := congrArg (Fin.init (α := fun _ => ℝ)) he
  simp only [shatterBase, Fin.init_snoc] at hinit
  convert hi'
  funext k
  exact Fin.ext (by exact_mod_cast congrFun hinit k)

/-- There is a convex set in `ℝ^(n+2)` of infinite additive VCₙ dimension. -/
theorem exists_convex_forall_not_hasAddVCNDimAtMost (n : ℕ) :
    ∃ C : Set (Fin (n + 2) → ℝ), Convex ℝ C ∧ ∀ d, ¬ HasAddVCNDimAtMost C n d := by
  refine ⟨infiniteVCNSet n, convex_convexHull ℝ _, fun d hd => hd
    (fun k j => Pi.single k.castSucc.castSucc (j : ℝ) + Pi.single (Fin.last (n + 1)) ((j : ℝ) ^ 2))
    (fun S => Pi.single (Fin.last n).castSucc (shatterLabel n ⟨d, S⟩) +
      Pi.single (Fin.last (n + 1)) (shatterLabel n ⟨d, S⟩ ^ 2))
    fun i S => ?_⟩
  rw [← paraboloidLift_shatterBase_mem_iff]
  convert Iff.rfl using 2
  funext c
  induction c using Fin.lastCases with
  | last =>
    simp [paraboloidLift, shatterBase, Fin.sum_univ_castSucc, Finset.sum_add_distrib, add_comm]
  | cast c =>
    induction c using Fin.lastCases with
    | last => simp [paraboloidLift, shatterBase]
    | cast c => simp [paraboloidLift, shatterBase, Pi.single_apply, Fin.castSucc_inj]

end VCDimConvex
