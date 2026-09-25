import VCDimConvex.Basic
import Mathlib.Analysis.Convex.Radon
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Additive VC dimension at most 3 for convex sets in ℝ²

Suppose translates of a convex set `C ⊆ ℝ²` shatter four points `x₀, …, x₃`. By Radon's lemma,
either one of the points lies in the convex hull of the other three, or two of the segments
`[xᵢ, xⱼ]` and `[xₖ, xₗ]` with `{i, j, k, l} = {0, 1, 2, 3}` meet. In the first case the translate
cutting out the other three points contains the fourth one as well. In the second case let `y`
and `y'` be the translates cutting out `{i, j}` and `{k, l}`. Depending on the quadrant of
`y - y'` in the basis `xⱼ - xᵢ`, `xₗ - xₖ`, one of the four points that should be outside `C` is
a convex combination of three points that should be inside `C`. When the two segments are
parallel, an endpoint of one segment lies in the other.
-/

open Set

namespace VCDimConvex

section Combination

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {K : Set E}

/-- A convex combination of three points, with weights that need not be normalized. -/
theorem mem_of_smul_eq_add_three (hK : Convex ℝ K) {x y z q : E} (hx : x ∈ K) (hy : y ∈ K)
    (hz : z ∈ K) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : 0 < a + b + c)
    (hq : (a + b + c) • q = a • x + b • y + c • z) : q ∈ K := by
  have hq' : q = (a / (a + b + c)) • x + (b / (a + b + c)) • y + (c / (a + b + c)) • z := by
    have : q = (a + b + c)⁻¹ • ((a + b + c) • q) := by
      rw [smul_smul, inv_mul_cancel₀ habc.ne', one_smul]
    rw [this, hq]
    simp only [smul_add, smul_smul, div_eq_inv_mul]
  have := hK.sum_mem (t := Finset.univ)
    (w := ![a / (a + b + c), b / (a + b + c), c / (a + b + c)]) (z := ![x, y, z])
    (fun i _ => by fin_cases i <;> simp <;> positivity)
    (by simp [Fin.sum_univ_three]; field_simp)
    (fun i _ => by fin_cases i <;> simpa)
  simpa [Fin.sum_univ_three, hq'] using this

/-- A convex combination of two points, with weights that need not be normalized. -/
theorem mem_segment_of_smul_eq_add {x y q : E} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a + b) (hq : (a + b) • q = a • x + b • y) : q ∈ segment ℝ x y :=
  mem_of_smul_eq_add_three (convex_segment x y) (left_mem_segment ℝ x y)
    (right_mem_segment ℝ x y) (left_mem_segment ℝ x y) ha hb le_rfl (by simpa using hab)
    (by simpa using hq)

/-- The core of the crossing case. The segments `[a₁, a₃]` and `[a₂, a₄]` meet, the points
`v + a₁`, `v + a₃`, `a₂`, `a₄` lie in `K`, and `v` is in the closed positive quadrant spanned by
`a₃ - a₁` and `a₄ - a₂`. Then `v + a₂` or `a₃` lies in `K`. -/
theorem add_mem_or_mem_of_crossing (hK : Convex ℝ K) {a₁ a₂ a₃ a₄ v : E} {t u α β : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hp : (1 - t) • a₁ + t • a₃ = (1 - u) • a₂ + u • a₄)
    (hv : v = α • (a₃ - a₁) + β • (a₄ - a₂))
    (h₁ : v + a₁ ∈ K) (h₃ : v + a₃ ∈ K) (h₂ : a₂ ∈ K) (h₄ : a₄ ∈ K) :
    v + a₂ ∈ K ∨ a₃ ∈ K := by
  subst hv
  have case₁ (hD : 0 < β + u) (h : α * u ≤ β * (1 - t)) :
      α • (a₃ - a₁) + β • (a₄ - a₂) + a₂ ∈ K :=
    mem_of_smul_eq_add_three hK h₁ h₃ h₂ (a := β * (1 - t) - α * u) (b := α * u + t * β)
      (c := u) (sub_nonneg.mpr h) (by positivity) hu₀ (by linarith)
      (by linear_combination (norm := module) (-β) • hp)
  have case₂ (hD : 0 < α + 1 - t) (h : β * (1 - t) ≤ α * u) : a₃ ∈ K :=
    mem_of_smul_eq_add_three hK h₃ h₂ h₄ (a := 1 - t) (b := α * (1 - u) + (1 - t) * β)
      (c := α * u - (1 - t) * β) (by linarith) (by nlinarith) (by linarith) (by linarith)
      (by linear_combination (norm := module) α • hp)
  have case₃ (ht : t = 1) (hu : u = 0) : a₃ ∈ K := by
    subst ht hu
    simp only [sub_self, zero_smul, one_smul, zero_add, sub_zero, add_zero] at hp
    exact hp ▸ h₂
  rcases le_total (α * u) (β * (1 - t)) with h | h
  · by_cases hD : 0 < β + u
    · exact Or.inl (case₁ hD h)
    obtain ⟨rfl, rfl⟩ : β = 0 ∧ u = 0 := by constructor <;> linarith
    by_cases hD' : 0 < α + 1 - t
    · exact Or.inr (case₂ hD' (by simp))
    exact Or.inr (case₃ (by linarith) rfl)
  · by_cases hD' : 0 < α + 1 - t
    · exact Or.inr (case₂ hD' h)
    obtain ⟨rfl, rfl⟩ : α = 0 ∧ t = 1 := by constructor <;> linarith
    by_cases hD : 0 < β + u
    · exact Or.inl (case₁ hD (by simp))
    exact Or.inr (case₃ rfl (by linarith))

end Combination

section Shattering

variable {ι E : Type*} [AddCommGroup E] [Module ℝ E] {C : Set E} {a : ι → E}

/-- If translates of a convex set shatter the points `a`, then no point `a k` lies in the convex
hull of points `a j` with `j ≠ k`. -/
theorem not_mem_convexHull_of_shatter (hC : Convex ℝ C)
    (hshat : ∀ s : Set ι, ∃ y, ∀ j, y + a j ∈ C ↔ j ∈ s) {J : Set ι} {k : ι} (hk : k ∉ J) :
    a k ∉ convexHull ℝ (a '' J) := by
  intro h
  obtain ⟨y, hy⟩ := hshat J
  have hsub : convexHull ℝ (a '' J) ⊆ (fun z => y + z) ⁻¹' C :=
    convexHull_min (by rintro _ ⟨m, hm, rfl⟩; exact (hy m).mpr hm)
      (hC.translate_preimage_right y)
  exact hk ((hy k).mp (hsub h))

theorem not_mem_segment_of_shatter (hC : Convex ℝ C)
    (hshat : ∀ s : Set ι, ∃ y, ∀ j, y + a j ∈ C ↔ j ∈ s) {i j k : ι} (hki : k ≠ i)
    (hkj : k ≠ j) : a k ∉ segment ℝ (a i) (a j) := by
  rw [← convexHull_pair, ← Set.image_pair]
  exact not_mem_convexHull_of_shatter hC hshat (by simp [hki, hkj])

end Shattering

/-- Two vectors of `ℝ²` with nonzero determinant form a basis. -/
theorem exists_eq_smul_add_smul (e f v : Point 2) (h : e 0 * f 1 - e 1 * f 0 ≠ 0) :
    ∃ α β : ℝ, v = α • e + β • f := by
  refine ⟨(v 0 * f 1 - v 1 * f 0) / (e 0 * f 1 - e 1 * f 0),
    (e 0 * v 1 - e 1 * v 0) / (e 0 * f 1 - e 1 * f 0), funext fun r => ?_⟩
  have h' : f 1 * e 0 - f 0 * e 1 ≠ 0 := by rwa [mul_comm, mul_comm (f 0)]
  fin_cases r <;> simp <;> field_simp <;> ring

/-- A vector of `ℝ²` with zero determinant against a nonzero vector `e` is a multiple of `e`. -/
theorem exists_eq_smul_of_det_eq_zero (e f : Point 2) (he : e ≠ 0)
    (h : e 0 * f 1 - e 1 * f 0 = 0) : ∃ c : ℝ, f = c • e := by
  have hpos : 0 < e 0 ^ 2 + e 1 ^ 2 := by
    by_contra! hle
    refine he (funext fun r => ?_)
    fin_cases r <;> simp <;> nlinarith [sq_nonneg (e 0), sq_nonneg (e 1)]
  refine ⟨(f 0 * e 0 + f 1 * e 1) / (e 0 ^ 2 + e 1 ^ 2), funext fun r => ?_⟩
  fin_cases r <;> simp <;> field_simp
  · linear_combination (-e 1) * h
  · linear_combination e 0 * h

variable {C : Set (Point 2)} {a : Fin 4 → Point 2}

/-- If translates of a convex set in `ℝ²` shatter four points, then the segments joining two
disjoint pairs of them do not meet. -/
theorem not_segments_meet_of_shatter (hC : Convex ℝ C)
    (hshat : ∀ s : Set (Fin 4), ∃ y, ∀ j, y + a j ∈ C ↔ j ∈ s) {i j k l : Fin 4}
    (hki : k ≠ i) (hkj : k ≠ j) (hli : l ≠ i) (hlj : l ≠ j) {q : Point 2}
    (hq : q ∈ segment ℝ (a i) (a j)) (hq' : q ∈ segment ℝ (a k) (a l)) : False := by
  obtain ⟨s₁, t, hs₁, ht₀, hst, rfl⟩ := hq
  obtain ⟨s₂, u, hs₂, hu₀, hsu, hq'⟩ := hq'
  obtain rfl : s₁ = 1 - t := by linarith
  obtain rfl : s₂ = 1 - u := by linarith
  have hp : (1 - t) • a i + t • a j = (1 - u) • a k + u • a l := hq'.symm
  have ht₁ : t ≤ 1 := by linarith
  have hu₁ : u ≤ 1 := by linarith
  have hseg {i j k : Fin 4} (hki : k ≠ i) (hkj : k ≠ j) : a k ∉ segment ℝ (a i) (a j) :=
    not_mem_segment_of_shatter hC hshat hki hkj
  obtain ⟨y₁, hy₁⟩ := hshat {i, j}
  obtain ⟨y₂, hy₂⟩ := hshat {k, l}
  -- Translate so that the label `{k, l}` is cut out by `K` itself.
  let K := (fun z => y₂ + z) ⁻¹' C
  have hK : Convex ℝ K := hC.translate_preimage_right y₂
  have hvK (m : Fin 4) : y₁ - y₂ + a m ∈ K ↔ m ∈ ({i, j} : Set (Fin 4)) := by
    show y₂ + (y₁ - y₂ + a m) ∈ C ↔ _
    rw [show y₂ + (y₁ - y₂ + a m) = y₁ + a m by abel]
    exact hy₁ m
  have hK' (m : Fin 4) : a m ∈ K ↔ m ∈ ({k, l} : Set (Fin 4)) := hy₂ m
  have hi : y₁ - y₂ + a i ∈ K := (hvK i).2 (by simp)
  have hj : y₁ - y₂ + a j ∈ K := (hvK j).2 (by simp)
  have hk : a k ∈ K := (hK' k).2 (by simp)
  have hl : a l ∈ K := (hK' l).2 (by simp)
  have hk' : y₁ - y₂ + a k ∉ K := fun h => by simp at hvK; simp_all
  have hl' : y₁ - y₂ + a l ∉ K := fun h => by simp at hvK; simp_all
  have hi' : a i ∉ K := fun h => by simp at hK'; simp_all [eq_comm]
  have hj' : a j ∉ K := fun h => by simp at hK'; simp_all [eq_comm]
  by_cases hdet : (a j - a i) 0 * (a l - a k) 1 - (a j - a i) 1 * (a l - a k) 0 = 0
  · -- The two segments are parallel.
    by_cases he : a j - a i = 0
    · rw [sub_eq_zero] at he
      refine hseg (i := k) (j := l) (k := i) hki.symm hli.symm ⟨1 - u, u, by linarith, hu₀,
        by ring, ?_⟩
      rw [← hp, he]
      module
    obtain ⟨c, hf⟩ := exists_eq_smul_of_det_eq_zero _ _ he hdet
    rcases lt_or_ge (t - u * c) 0 with h₀ | h₀
    · have hc : 0 < c := by
        by_contra! hc
        nlinarith
      refine hseg (i := k) (j := l) (k := i) hki.symm hli.symm
        (mem_segment_of_smul_eq_add (a := c * (1 - u) + t) (b := u * c - t) (by nlinarith)
          (by linarith) (by linarith) ?_)
      linear_combination (norm := module) c • hp + t • hf
    rcases le_or_gt (t - u * c) 1 with h₁ | h₁
    · refine hseg (i := i) (j := j) (k := k) hki hkj
        (mem_segment_of_smul_eq_add (a := 1 - t + u * c) (b := t - u * c) (by linarith)
          h₀ (by linarith) ?_)
      linear_combination (norm := module) (-1 : ℝ) • hp + (-u) • hf
    · have hc : c < 0 := by
        by_contra! hc
        nlinarith
      refine hseg (i := k) (j := l) (k := j) hkj.symm hlj.symm
        (mem_segment_of_smul_eq_add (a := -c * (1 - u) + 1 - t) (b := t - 1 - u * c)
          (by nlinarith) (by linarith) (by linarith) ?_)
      linear_combination (norm := module) (-c) • hp + (1 - t) • hf
  · -- The segments cross: write `y₁ - y₂` in the basis of the two directions.
    obtain ⟨α, β, hv⟩ := exists_eq_smul_add_smul _ _ (y₁ - y₂) hdet
    rcases le_total 0 α with hα | hα <;> rcases le_total 0 β with hβ | hβ
    · rcases add_mem_or_mem_of_crossing hK ht₀ ht₁ hu₀ hu₁ hα hβ hp hv hi hj hk hl with h | h
      exacts [hk' h, hj' h]
    · rcases add_mem_or_mem_of_crossing hK ht₀ ht₁ (a₂ := a l) (a₄ := a k) (u := 1 - u)
        (β := -β) (by linarith) (by linarith) hα (by linarith)
        (by rw [hp]; module) (by rw [hv]; module) hi hj hl hk with h | h
      exacts [hl' h, hj' h]
    · rcases add_mem_or_mem_of_crossing hK (a₁ := a j) (a₃ := a i) (t := 1 - t) (α := -α)
        (by linarith) (by linarith) hu₀ hu₁ (by linarith) hβ
        (by rw [← hp]; module) (by rw [hv]; module) hj hi hk hl with h | h
      exacts [hk' h, hi' h]
    · rcases add_mem_or_mem_of_crossing hK (a₁ := a j) (a₃ := a i) (a₂ := a l) (a₄ := a k)
        (t := 1 - t) (u := 1 - u) (α := -α) (β := -β) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith)
        (by
          rw [(show (1 - (1 - t)) • a j + (1 - t) • a i = (1 - t) • a i + t • a j by module), hp]
          module)
        (by rw [hv]; module) hj hi hl hk with h | h
      exacts [hl' h, hi' h]

/-- Translates of a convex set in `ℝ²` do not shatter four points. -/
theorem not_shatter_four (hC : Convex ℝ C)
    (hshat : ∀ s : Set (Fin 4), ∃ y, ∀ j, y + a j ∈ C ↔ j ∈ s) : False := by
  classical
  have hdep : ¬ AffineIndependent ℝ a := by
    intro h
    have h₁ := h.card_le_finrank_succ
    have h₂ := Submodule.finrank_le (vectorSpan ℝ (Set.range a))
    simp only [Fintype.card_fin, Module.finrank_fin_fun] at h₁ h₂
    omega
  obtain ⟨I, q, hq₁, hq₂⟩ := Convex.radon_partition hdep
  -- One side of the partition has at most one point.
  have hsingle (I : Set (Fin 4)) (k : Fin 4) (hI : I ⊆ {k}) (h₁ : q ∈ convexHull ℝ (a '' I))
      (h₂ : q ∈ convexHull ℝ (a '' Iᶜ)) : False := by
    by_cases hk : k ∈ I
    · have hsub : a '' I ⊆ {a k} := by
        rintro _ ⟨m, hm, rfl⟩
        rw [hI hm]
        rfl
      have hq : q = a k := by
        simpa using convexHull_min hsub (convex_singleton (a k)) h₁
      exact not_mem_convexHull_of_shatter hC hshat (J := Iᶜ) (by simpa using hk) (hq ▸ h₂)
    · have : I = ∅ := eq_empty_of_forall_notMem fun m hm => hk (hI hm ▸ hm)
      simp [this] at h₁
  have hcases : ∀ T : Finset (Fin 4),
      T.card ≤ 1 ∨ Tᶜ.card ≤ 1 ∨ ∃ i j k l : Fin 4, T = {i, j} ∧ Tᶜ = {k, l} := by
    decide
  rcases hcases I.toFinset with h | h | ⟨i, j, k, l, hT, hTc⟩
  · obtain ⟨k, hk⟩ := Finset.card_le_one_iff_subset_singleton.mp h
    exact hsingle I k (fun m hm => by simpa using hk (Set.mem_toFinset.mpr hm)) hq₁ hq₂
  · obtain ⟨k, hk⟩ := Finset.card_le_one_iff_subset_singleton.mp h
    refine hsingle Iᶜ k (fun m hm => by simpa using hk (by simpa using hm)) hq₂
      (by rwa [compl_compl])
  · have hI : I = {i, j} := Set.ext fun m => by simpa using Finset.ext_iff.mp hT m
    have hIc : Iᶜ = {k, l} := Set.ext fun m => by simpa using Finset.ext_iff.mp hTc m
    have hk : k ∉ I := by simp [← mem_compl_iff, hIc]
    have hl : l ∉ I := by simp [← mem_compl_iff, hIc]
    rw [hI, Set.image_pair, convexHull_pair] at hq₁
    rw [hIc, Set.image_pair, convexHull_pair] at hq₂
    rw [hI] at hk hl
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hk hl
    exact not_segments_meet_of_shatter hC hshat hk.1 hk.2 hl.1 hl.2 hq₁ hq₂

/-- Every convex set in `ℝ²` has additive VC dimension at most `3`. -/
theorem explicit_bound_one (C : Set (Point 2)) (hC : Convex ℝ C) : HasAddVCDimLE 3 C := by
  intro S hSfin hS
  by_contra! hlt
  have := hSfin.fintype
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card] at hlt
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 4) (β := S)
    (by rw [Fintype.card_fin]; omega)
  exact not_shatter_four hC (a := fun j => e j)
    (exists_translate_of_shatters hS (Subtype.val_injective.comp e.injective) fun j => (e j).2)

end VCDimConvex
