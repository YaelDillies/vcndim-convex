import VCDimConvex.ConvexIndependentGeneral

/-!
# VCₙ dimension at most 2 for convex sets in `ℝⁿ`

Let `z : Fin n → Fin 3 → ℝⁿ` be an additive array. We show that the `3ⁿ` points `gridSum z i` are
not convexly independent, by running the fibre induction of `ConvexIndependentGeneral` on the full
grid. Two fibres of the full grid over the first family share *all* their tails, so no counting is
needed, and with `r + 1` families and `W` of codimension at most `r + 1` the induction ends with a
single family and three points exposed by multiples of one functional.

If translates of a convex `C` shattered the grid, one of its points `q i` would lie in the hull of
the others, and the translate cutting out all the others would contain `q i` too.
-/

namespace VCDimConvex

open Finset Module

/-- In a full grid of side three, with `r + 1` families and `W` of codimension at most `r + 1`,
the points cannot all be strictly exposed by functionals annihilating `W`. -/
theorem not_forall_exposed_full {d : ℕ} :
    ∀ (r : ℕ) (a : Fin (r + 1) → Fin 3 → Point d) (W : Submodule ℝ (Point d)),
      d ≤ r + 1 + finrank ℝ W →
      ¬ ∀ x : Fin (r + 1) → Fin 3, ∃ ν : Dual ℝ (Point d), (∀ w ∈ W, ν w = 0) ∧
        ∀ y, y ≠ x → ν (pt a y) < ν (pt a x)
  | 0, a, W, hW, hexp => by
    have := card_le_two_of_exposed_annihilating (pt a) W (by omega) univ
      fun x _ => by
        obtain ⟨ν, hν, h⟩ := hexp x
        exact ⟨ν, hν, fun y _ hy => h y hy⟩
    simp at this
  | r + 1, a, W, hW, hexp => by
    set u := a 0 1 - a 0 0 with hu
    have hne (t : Fin (r + 1) → Fin 3) :
        (Fin.cons 1 t : Fin (r + 2) → Fin 3) ≠ Fin.cons 0 t :=
      fun h => absurd (Fin.cons_injective2 h).1 (by decide)
    have htail {t t' : Fin (r + 1) → Fin 3} (c : Fin 3) (h : t' ≠ t) :
        (Fin.cons c t' : Fin (r + 2) → Fin 3) ≠ Fin.cons c t :=
      fun h' => h (Fin.cons_injective2 h').2
    have hopp (t : Fin (r + 1) → Fin 3) :
        ∃ ν ν' : Dual ℝ (Point d), (∀ w ∈ W, ν w = 0) ∧ (∀ w ∈ W, ν' w = 0) ∧
          ν u < 0 ∧ 0 < ν' u ∧ ∀ t', t' ≠ t →
            ν (pt (Fin.tail a) t') < ν (pt (Fin.tail a) t) ∧
              ν' (pt (Fin.tail a) t') < ν' (pt (Fin.tail a) t) := by
      obtain ⟨ν, hνW, hν⟩ := hexp (Fin.cons 0 t)
      obtain ⟨ν', hν'W, hν'⟩ := hexp (Fin.cons 1 t)
      refine ⟨ν, ν', hνW, hν'W, ?_, ?_, fun t' htt' => ⟨?_, ?_⟩⟩
      · have := hν _ (hne t)
        simp only [pt_cons, u, map_add, map_sub] at this ⊢
        linarith
      · have := hν' _ (hne t).symm
        simp only [pt_cons, u, map_add, map_sub] at this ⊢
        linarith
      · have := hν _ (htail 0 htt')
        simp only [pt_cons, map_add] at this
        linarith
      · have := hν' _ (htail 1 htt')
        simp only [pt_cons, map_add] at this
        linarith
    obtain ⟨ν, -, hνW, -, hνu, -, -⟩ := hopp fun _ => 0
    have huW : u ∉ W := fun hu => hνu.ne (hνW u hu)
    have hu0 : u ≠ 0 := fun h => by simp [h] at hνu
    have hW' : finrank ℝ ↥(W ⊔ ℝ ∙ u) = finrank ℝ W + 1 := by
      have := Submodule.finrank_sup_add_finrank_inf_eq W (ℝ ∙ u)
      rw [finrank_span_singleton hu0, ((Submodule.disjoint_span_singleton' hu0).mpr huW).eq_bot,
        finrank_bot] at this
      omega
    refine not_forall_exposed_full r (Fin.tail a) (W ⊔ ℝ ∙ u) (by omega) fun t => ?_
    obtain ⟨ν, ν', hνW, hν'W, hνu, hν'u, hν⟩ := hopp t
    obtain ⟨ν₀, hν₀u, hν₀, hν₀W⟩ := exists_combination_annihilating ν ν' u hνu hν'u
    refine ⟨ν₀, fun w hw => ?_, fun t' htt' => hν₀ _ _ (hν t' htt').1 (hν t' htt').2⟩
    obtain ⟨y, hy, v, hv, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    simp [hν₀W y (hνW y hy) (hν'W y hy), hν₀u]

/-- Among the `3ⁿ` points of an additive array in `ℝⁿ` with three points per family, one lies in
the hull of the others. -/
theorem not_convexIndependentOn_univ_side_three {n : ℕ} (hn : 1 ≤ n)
    (z : Fin n → Fin 3 → Point n) : ¬ ConvexIndependentOn (gridSum z) (univ : Finset (Grid n 3)) := by
  classical
  intro hV
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  refine not_forall_exposed_full r z ⊥ (by simp) fun x => ?_
  obtain ⟨ν, hν⟩ := exists_exposing_of_convexIndependentOn hV (mem_univ x)
  exact ⟨ν, by simp, fun y hy => hν y (mem_erase.mpr ⟨hy, mem_univ y⟩)⟩

/-- **Every convex set in `ℝⁿ` has `VCₙ` dimension at most `2`.** -/
theorem hasAddVCNDimAtMost_two_of_convex {n : ℕ} (hn : 1 ≤ n) (C : Set (Point n))
    (hC : Convex ℝ C) : HasAddVCNDimAtMost C n 2 := by
  classical
  intro x y hxy
  have h := not_convexIndependentOn_univ_side_three hn x
  simp only [ConvexIndependentOn, not_forall, not_not] at h
  obtain ⟨i, -, hi⟩ := h
  have hsub : indexedHull (gridSum x) (univ.erase i) ⊆
      (fun p => y {j | j ≠ i} + p) ⁻¹' C := by
    refine convexHull_min ?_ (hC.translate_preimage_right _)
    rintro _ ⟨j, hj, rfl⟩
    have hji : j ≠ i := by simpa using hj
    exact (hxy j {j | j ≠ i}).mpr hji
  exact ((hxy i {j | j ≠ i}).mp (hsub hi)) rfl

end VCDimConvex
