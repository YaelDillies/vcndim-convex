import VCDimConvex.ConvexIndependentBound

/-!
# Convexly independent subsets of an additive array in any dimension

For an additive array with `r + 1` families of `m` points each, a set of indices whose points are
all strictly exposed has at most `vertexBound r m` elements. The proof inducts on the number of
families. It keeps track of a subspace `W` that all exposing functionals annihilate. Two fibres over
the first family differ by a fixed offset `u`. Opposite exposing functionals combine into one that
also annihilates `u`, so the shared tails form an instance with one family fewer and `W ⊔ ℝ ∙ u` in
place of `W`. Once a single family is left, `W` is a hyperplane, and its annihilating functionals
are proportional, so they expose at most two points. Sanyal's obstruction is not used.
-/

namespace VCDimConvex

open Finset Module

/-! ### The vertex bound -/

/-- A bound for the number of strictly exposed points of an array with `r + 1` families of `m`
points each: `2` for one family, and `m^(r+1) + √(m^(r+1) · m² · vertexBound r m)` for `r + 2`
families. -/
def vertexBound : ℕ → ℕ → ℕ
  | 0, _ => 2
  | r + 1, m => m ^ (r + 1) + Nat.sqrt (m ^ (r + 1) * m ^ 2 * vertexBound r m)

/-- A natural number `s` with `s² ≤ U s + B` is at most `U + √B`. -/
theorem le_add_sqrt_of_sq_le (s U B : ℕ) (h : s ^ 2 ≤ U * s + B) : s ≤ U + Nat.sqrt B := by
  rcases le_or_gt s U with hs | hs
  · omega
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs.le
  have : t ≤ Nat.sqrt B := by
    rw [Nat.le_sqrt']
    nlinarith
  omega

/-! ### Arrays with any number of families -/

/-- The point of the index `x` of an array `a` with `r` families in `ℝ^d`. -/
def pt {d r m : ℕ} (a : Fin r → Fin m → Point d) (x : Fin r → Fin m) : Point d :=
  ∑ k, a k (x k)

theorem pt_cons {d r m : ℕ} (a : Fin (r + 1) → Fin m → Point d) (j : Fin m) (t : Fin r → Fin m) :
    pt a (Fin.cons j t) = a 0 j + pt (Fin.tail a) t := by
  simp [pt, Fin.sum_univ_succ, Fin.tail]

/-- **Base case**: functionals annihilating a hyperplane strictly expose at most two points. -/
theorem card_le_two_of_exposed_annihilating {ι : Type*} {d : ℕ} (q : ι → Point d)
    (W : Submodule ℝ (Point d)) (hW : d ≤ finrank ℝ W + 1) (S : Finset ι)
    (hexp : ∀ x ∈ S, ∃ ν : Dual ℝ (Point d), (∀ w ∈ W, ν w = 0) ∧
      ∀ y ∈ S, y ≠ x → ν (q y) < ν (q x)) :
    S.card ≤ 2 := by
  obtain ⟨φ, hφ⟩ := exists_forall_eq_smul_of_finrank W hW
  by_contra! hlt
  obtain ⟨x0, x1, x2, h0, h1, h2, h01, h02, h12⟩ := Finset.two_lt_card_iff.mp hlt
  let x : Fin 3 → ι := ![x0, x1, x2]
  have hx : Function.Injective x := by
    intro k l hkl
    fin_cases k <;> fin_cases l <;> first | rfl | (exfalso; simp [x] at hkl; tauto)
  have hmem (k : Fin 3) : x k ∈ S := by
    fin_cases k
    exacts [h0, h1, h2]
  choose ν hνW hν using fun k => hexp (x k) (hmem k)
  choose c hc using fun k => hφ (ν k) (hνW k)
  refine not_three_exposed_of_smul φ (fun k => q (x k)) c fun k l hl => ?_
  simpa [hc k] using hν k (x l) (hmem l) (hx.ne hl)

/-- **G**: if every index of `S` is strictly exposed by a functional annihilating `W`, and `W` has
codimension at most the number of families, then `S` has at most `vertexBound r m` elements. -/
theorem card_le_vertexBound_of_exposed_annihilating {d m : ℕ} :
    ∀ (r : ℕ) (a : Fin (r + 1) → Fin m → Point d) (W : Submodule ℝ (Point d)),
      d ≤ r + 1 + finrank ℝ W → ∀ S : Finset (Fin (r + 1) → Fin m),
      (∀ x ∈ S, ∃ ν : Dual ℝ (Point d), (∀ w ∈ W, ν w = 0) ∧
        ∀ y ∈ S, y ≠ x → ν (pt a y) < ν (pt a x)) →
      S.card ≤ vertexBound r m
  | 0, a, W, hW, S, hexp => card_le_two_of_exposed_annihilating (pt a) W (by omega) S hexp
  | r + 1, a, W, hW, S, hexp => by
    classical
    let F : Fin m → Finset (Fin (r + 1) → Fin m) := fun i => univ.filter fun t => Fin.cons i t ∈ S
    have hF : ∑ i, (F i).card = S.card := by
      calc
        ∑ i, (F i).card =
            ∑ i, ∑ t, if (Fin.cons i t : Fin (r + 2) → Fin m) ∈ S then 1 else 0 := by
          simp only [F, Finset.card_filter]
        _ = ∑ p : Fin m × (Fin (r + 1) → Fin m),
            if (Fin.cons p.1 p.2 : Fin (r + 2) → Fin m) ∈ S then 1 else 0 :=
          (Fintype.sum_prod_type fun p =>
            if (Fin.cons p.1 p.2 : Fin (r + 2) → Fin m) ∈ S then 1 else 0).symm
        _ = ∑ x, if x ∈ S then 1 else 0 :=
          (Fin.consEquiv fun _ => Fin m).sum_comp fun x => if x ∈ S then 1 else 0
        _ = S.card := by simp
    have hinter (i i' : Fin m) (hii' : i ≠ i') : (F i ∩ F i').card ≤ vertexBound r m := by
      set T := F i ∩ F i'
      have hmem (t : Fin (r + 1) → Fin m) (ht : t ∈ T) :
          (Fin.cons i t : Fin (r + 2) → Fin m) ∈ S ∧ (Fin.cons i' t : Fin (r + 2) → Fin m) ∈ S := by
        simpa [T, F] using ht
      have hne (t : Fin (r + 1) → Fin m) :
          (Fin.cons i' t : Fin (r + 2) → Fin m) ≠ Fin.cons i t :=
        fun h => hii' (Fin.cons_injective2 h).1.symm
      have htail {t t' : Fin (r + 1) → Fin m} (c : Fin m) (h : t' ≠ t) :
          (Fin.cons c t' : Fin (r + 2) → Fin m) ≠ Fin.cons c t :=
        fun h' => h (Fin.cons_injective2 h').2
      set u := a 0 i' - a 0 i
      -- The two copies of a shared tail are exposed by functionals of opposite signs on `u`.
      have hopp (t : Fin (r + 1) → Fin m) (ht : t ∈ T) :
          ∃ ν ν' : Dual ℝ (Point d), (∀ w ∈ W, ν w = 0) ∧ (∀ w ∈ W, ν' w = 0) ∧
            ν u < 0 ∧ 0 < ν' u ∧ ∀ t' ∈ T, t' ≠ t →
              ν (pt (Fin.tail a) t') < ν (pt (Fin.tail a) t) ∧
                ν' (pt (Fin.tail a) t') < ν' (pt (Fin.tail a) t) := by
        obtain ⟨ν, hνW, hν⟩ := hexp _ (hmem t ht).1
        obtain ⟨ν', hν'W, hν'⟩ := hexp _ (hmem t ht).2
        refine ⟨ν, ν', hνW, hν'W, ?_, ?_, fun t' ht' htt' => ⟨?_, ?_⟩⟩
        · have := hν _ (hmem t ht).2 (hne t)
          simp only [pt_cons, u, map_add, map_sub] at this ⊢
          linarith
        · have := hν' _ (hmem t ht).1 (hne t).symm
          simp only [pt_cons, u, map_add, map_sub] at this ⊢
          linarith
        · have := hν _ (hmem t' ht').1 (htail i htt')
          simp only [pt_cons, map_add] at this
          linarith
        · have := hν' _ (hmem t' ht').2 (htail i' htt')
          simp only [pt_cons, map_add] at this
          linarith
      rcases T.eq_empty_or_nonempty with hT | ⟨t₀, ht₀⟩
      · simp [hT]
      obtain ⟨ν, -, hνW, -, hνu, -, -⟩ := hopp t₀ ht₀
      have huW : u ∉ W := fun hu => hνu.ne (hνW u hu)
      have hu0 : u ≠ 0 := fun h => by simp [h] at hνu
      have hW' : finrank ℝ ↥(W ⊔ ℝ ∙ u) = finrank ℝ W + 1 := by
        have := Submodule.finrank_sup_add_finrank_inf_eq W (ℝ ∙ u)
        rw [finrank_span_singleton hu0, ((Submodule.disjoint_span_singleton' hu0).mpr huW).eq_bot,
          finrank_bot] at this
        omega
      refine card_le_vertexBound_of_exposed_annihilating r (Fin.tail a) (W ⊔ ℝ ∙ u) (by omega) T
        fun t ht => ?_
      obtain ⟨ν, ν', hνW, hν'W, hνu, hν'u, hν⟩ := hopp t ht
      obtain ⟨ν₀, hν₀u, hν₀, hν₀W⟩ := exists_combination_annihilating ν ν' u hνu hν'u
      refine ⟨ν₀, fun w hw => ?_, fun t' ht' htt' => hν₀ _ _ (hν t' ht' htt').1 (hν t' ht' htt').2⟩
      obtain ⟨y, hy, v, hv, rfl⟩ := Submodule.mem_sup.mp hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
      simp [hν₀W y (hνW y hy) (hν'W y hy), hν₀u]
    have hcs := sum_card_sq_le_of_card_inter_le F _ hinter
    rw [hF] at hcs
    simp only [Fintype.card_fun, Fintype.card_fin] at hcs
    have hm : m * (m - 1) ≤ m ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    refine le_add_sqrt_of_sq_le _ _ _ (hcs.trans ?_)
    calc
      m ^ (r + 1) * (S.card + m * (m - 1) * vertexBound r m) =
          m ^ (r + 1) * S.card + m ^ (r + 1) * (m * (m - 1)) * vertexBound r m := by ring
      _ ≤ m ^ (r + 1) * S.card + m ^ (r + 1) * m ^ 2 * vertexBound r m := by gcongr

/-- **T1**: a convexly independent set of indices of an array with `n + 1` families in `ℝ^(n+1)`
has at most `vertexBound n m` elements. -/
theorem card_le_vertexBound_of_convexIndependentOn {n m : ℕ}
    (z : Fin (n + 1) → Fin m → Point (n + 1)) (V : Finset (Grid (n + 1) m))
    (hV : ConvexIndependentOn (gridSum z) V) :
    V.card ≤ vertexBound n m := by
  classical
  refine card_le_vertexBound_of_exposed_annihilating n z ⊥ (by simp) V fun x hx => ?_
  obtain ⟨ν, hν⟩ := exists_exposing_of_convexIndependentOn hV hx
  exact ⟨ν, by simp, fun y hy hyx => hν y (mem_erase.mpr ⟨hyx, hy⟩)⟩

end VCDimConvex
