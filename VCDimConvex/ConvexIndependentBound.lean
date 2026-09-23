import VCDimConvex.HullEncoding
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Convexly independent subsets of a three-dimensional additive array

For an additive array `z : Fin 3 → Fin m → Point 3`, a convexly independent set of indices has
at most `R m` elements. The proof slices the grid into the layers `i 0 = j`. Two layers share at
most `mu m` tails (a planar fibre bound, proved by exposing functionals that kill the layer offset),
and a Cauchy–Schwarz count over the layers turns this into the bound on `V`.
-/

namespace VCDimConvex

open Finset Module

/-! ### Arithmetic of the bounds -/

/-- Planar fibre bound: `⌊(m + √(m² + 8m²(m-1)))/2⌋`. -/
def mu (m : ℕ) : ℕ := (m + Nat.sqrt (m ^ 2 + 8 * m ^ 2 * (m - 1))) / 2

/-- Vertex bound for a convexly independent subset of a three-dimensional array of side `m`. -/
def R (m : ℕ) : ℕ := (m ^ 2 + Nat.sqrt (m ^ 4 + 4 * m ^ 3 * (m - 1) * mu m)) / 2

/-- A natural number below the positive root of `X² - aX - b` is below its floor. -/
theorem nat_le_of_sq_le_linear (s a b : ℕ) (h : s ^ 2 ≤ a * s + b) :
    s ≤ (a + Nat.sqrt (a ^ 2 + 4 * b)) / 2 := by
  rcases le_or_gt (2 * s) a with has | has
  · omega
  obtain ⟨t, hst⟩ : ∃ t, 2 * s = a + t := ⟨2 * s - a, by omega⟩
  have ht : t ≤ Nat.sqrt (a ^ 2 + 4 * b) := by
    rw [Nat.le_sqrt']
    nlinarith [congrArg (· ^ 2) hst]
  omega

theorem mu_spec (m s : ℕ) (h : s ^ 2 ≤ m * (s + 2 * m * (m - 1))) : s ≤ mu m := by
  have := nat_le_of_sq_le_linear s m (2 * m ^ 2 * (m - 1)) (by nlinarith)
  unfold mu
  convert this using 4
  ring

theorem R_spec (m s : ℕ) (h : s ^ 2 ≤ m ^ 2 * (s + m * (m - 1) * mu m)) : s ≤ R m := by
  have := nat_le_of_sq_le_linear s (m ^ 2) (m ^ 3 * (m - 1) * mu m) (by nlinarith)
  unfold R
  convert this using 4
  ring

/-! ### Double counting -/

/-- If the members of a family of finsets pairwise meet in at most `K` elements, then the square of
their total size is controlled by Cauchy–Schwarz. -/
theorem sum_card_sq_le_of_card_inter_le {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    [DecidableEq α] (F : ι → Finset α) (K : ℕ)
    (hK : ∀ i j, i ≠ j → (F i ∩ F j).card ≤ K) :
    (∑ i, (F i).card) ^ 2 ≤
      Fintype.card α * (∑ i, (F i).card + Fintype.card ι * (Fintype.card ι - 1) * K) := by
  let d : α → ℕ := fun a => (univ.filter fun i => a ∈ F i).card
  have hcard (s : Finset α) : s.card = ∑ a, if a ∈ s then 1 else 0 := by
    simp
  have hd (a : α) : d a = ∑ i, if a ∈ F i then 1 else 0 := by
    simp [d, Finset.sum_boole]
  have hsum : ∑ a, d a = ∑ i, (F i).card := by
    simp_rw [hd, hcard]
    exact Finset.sum_comm
  have hsq : ∑ a, d a ^ 2 = ∑ i, ∑ j, (F i ∩ F j).card := by
    simp_rw [hd, sq, Finset.sum_mul_sum, hcard, Finset.mem_inter, ite_and, ite_mul, one_mul,
      zero_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have hpair : ∑ i, ∑ j, (F i ∩ F j).card ≤
      ∑ i, (F i).card + Fintype.card ι * (Fintype.card ι - 1) * K := by
    have hrow (i : ι) :
        ∑ j, (F i ∩ F j).card ≤ (F i).card + (Fintype.card ι - 1) * K := by
      rw [← Finset.add_sum_erase _ _ (mem_univ i), Finset.inter_self]
      gcongr
      calc
        _ ≤ ∑ _j ∈ univ.erase i, K :=
          Finset.sum_le_sum fun j hj => hK i j (Finset.ne_of_mem_erase hj).symm
        _ = _ := by simp [Finset.card_erase_of_mem]
    calc
      _ ≤ ∑ i, ((F i).card + (Fintype.card ι - 1) * K) := Finset.sum_le_sum fun i _ => hrow i
      _ = _ := by simp [Finset.sum_add_distrib, mul_assoc]
  calc
    (∑ i, (F i).card) ^ 2 = (∑ a, d a) ^ 2 := by rw [hsum]
    _ ≤ Fintype.card α * ∑ a, d a ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := univ) (f := d)
    _ ≤ _ := by rw [hsq]; gcongr

/-! ### Exposing functionals -/

/-- **L0**: every point of a convexly independent family is strictly exposed. -/
theorem exists_exposing_of_convexIndependentOn {ι : Type*} [DecidableEq ι] {D : ℕ}
    {q : ι → Point D} {V : Finset ι} (hV : ConvexIndependentOn q V) {i : ι} (hi : i ∈ V) :
    ∃ ν : Dual ℝ (Point D), ∀ j ∈ V.erase i, ν (q j) < ν (q i) := by
  have hfin : (q '' ((V.erase i : Finset ι) : Set ι)).Finite :=
    (V.erase i).finite_toSet.image q
  obtain ⟨f, u, hf, hu⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _)
    (hfin.isCompact_convexHull ℝ).isClosed (hV i hi)
  exact ⟨f.toLinearMap, fun j hj =>
    (hf _ (subset_convexHull ℝ _ ⟨j, hj, rfl⟩)).trans hu⟩

/-- Two functionals of opposite signs on `w` combine into one annihilating `w`, preserving every
strict inequality they share and every vector they both annihilate. -/
theorem exists_combination_annihilating {E : Type*} [AddCommGroup E] [Module ℝ E]
    (ν ν' : Dual ℝ E) (w : E) (h : ν w < 0) (h' : 0 < ν' w) :
    ∃ ν₀ : Dual ℝ E, ν₀ w = 0 ∧ (∀ x y, ν x < ν y → ν' x < ν' y → ν₀ x < ν₀ y) ∧
      ∀ v, ν v = 0 → ν' v = 0 → ν₀ v = 0 := by
  refine ⟨ν' w • ν - ν w • ν', by simp [mul_comm], fun x y hxy hxy' => ?_,
    fun v hv hv' => by simp [hv, hv']⟩
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  nlinarith

/-- In `ℝ³`, the functionals annihilating two independent vectors form a line. -/
theorem exists_forall_eq_smul_of_annihilate {u w : Point 3}
    (hind : LinearIndependent ℝ ![u, w]) :
    ∃ φ : Dual ℝ (Point 3), ∀ ν : Dual ℝ (Point 3), ν u = 0 → ν w = 0 → ∃ c : ℝ, ν = c • φ := by
  let W : Submodule ℝ (Point 3) := Submodule.span ℝ (Set.range ![u, w])
  have hW : Module.finrank ℝ W = 2 := by simpa [W] using finrank_span_eq_card hind
  have hann : Module.finrank ℝ W.dualAnnihilator = 1 := by
    have := Subspace.finrank_add_finrank_dualAnnihilator_eq W
    simp only [hW, Module.finrank_fin_fun] at this
    omega
  have : Module.Free ℝ W.dualAnnihilator := Module.Free.of_divisionRing ℝ W.dualAnnihilator
  obtain ⟨φ, -, hφ⟩ := (finrank_eq_one_iff' (K := ℝ) (V := W.dualAnnihilator)).mp (by convert hann)
  refine ⟨φ, fun ν hu hw => ?_⟩
  have hν : ν ∈ W.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      fin_cases k <;> simpa
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  obtain ⟨c, hc⟩ := hφ ⟨ν, hν⟩
  exact ⟨c, by simpa using congrArg Subtype.val hc.symm⟩

/-- **L1**: the six points `b k`, `b k + u` cannot all be strictly exposed by functionals
annihilating a fixed nonzero vector `w`. -/
theorem not_all_exposed_segment_add_triangle
    (b : Fin 3 → Point 3) (u w : Point 3) (hw : w ≠ 0)
    (ν ν' : Fin 3 → Dual ℝ (Point 3))
    (hνw : ∀ k, ν k w = 0) (hν'w : ∀ k, ν' k w = 0)
    (hν : ∀ k l, l ≠ k → ν k (b l) < ν k (b k))
    (hνu : ∀ k, ν k (b k + u) < ν k (b k))
    (hν' : ∀ k l, l ≠ k → ν' k (b l) < ν' k (b k))
    (hν'u : ∀ k, ν' k (b k) < ν' k (b k + u)) :
    False := by
  have hu (k : Fin 3) : ν k u < 0 := by simpa using hνu k
  have hu' (k : Fin 3) : 0 < ν' k u := by simpa using hν'u k
  have hind : LinearIndependent ℝ ![u, w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h0 := congrArg (ν 0) hst
    simp only [map_add, map_smul, hνw, smul_eq_mul, mul_zero, add_zero, map_zero] at h0
    have hs : s = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h (hu 0).ne
    subst hs
    simp only [zero_smul, zero_add, smul_eq_zero] at hst
    exact ⟨rfl, hst.resolve_right hw⟩
  obtain ⟨φ, hφ⟩ := exists_forall_eq_smul_of_annihilate hind
  -- For each `k`, combine `ν k` and `ν' k` into a functional killing `u` and `w`.
  have hcomb (k : Fin 3) : ∃ c : ℝ, ∀ l, l ≠ k → c * φ (b l) < c * φ (b k) := by
    obtain ⟨ν₀, hν₀u, hν₀, hν₀w⟩ :=
      exists_combination_annihilating (ν k) (ν' k) u (hu k) (hu' k)
    obtain ⟨c, rfl⟩ := hφ ν₀ hν₀u (hν₀w w (hνw k) (hν'w k))
    exact ⟨c, fun l hl => by simpa using hν₀ _ _ (hν k l hl) (hν' k l hl)⟩
  choose c hc using hcomb
  have hne (k : Fin 3) : c k ≠ 0 := by
    rintro h0
    have := hc k (k + 1) (by fin_cases k <;> decide)
    simp [h0] at this
  -- Two of the three coefficients have the same sign, which gives opposite strict inequalities.
  have key (k l : Fin 3) (hkl : k ≠ l) (hpos : 0 < c k * c l) : False := by
    have h1 := hc k l hkl.symm
    have h2 := hc l k hkl
    have h3 : 0 < c k * (φ (b k) - φ (b l)) := by linarith
    have h4 : 0 < c l * (φ (b l) - φ (b k)) := by linarith
    nlinarith [mul_pos h3 h4, mul_nonneg hpos.le (sq_nonneg (φ (b k) - φ (b l)))]
  rcases (hne 0).lt_or_gt with h0 | h0 <;> rcases (hne 1).lt_or_gt with h1 | h1 <;>
    rcases (hne 2).lt_or_gt with h2 | h2
  all_goals first
    | exact key 0 1 (by decide) (by nlinarith)
    | exact key 0 2 (by decide) (by nlinarith)
    | exact key 1 2 (by decide) (by nlinarith)

/-! ### The fibre bound along a fixed direction -/

/-- **L2**: if every point `a i + b l` of an index set `S` is strictly exposed by a functional
annihilating a fixed nonzero `w`, then two fibres of `S` share at most two points, and hence `S`
is small. -/
theorem card_sq_le_of_exposed_annihilating {m : ℕ} (a b : Fin m → Point 3) (w : Point 3)
    (hw : w ≠ 0) (S : Finset (Fin m × Fin m))
    (hexp : ∀ x ∈ S, ∃ ν : Dual ℝ (Point 3), ν w = 0 ∧
      ∀ y ∈ S, y ≠ x → ν (a y.1 + b y.2) < ν (a x.1 + b x.2)) :
    S.card ^ 2 ≤ m * (S.card + 2 * m * (m - 1)) := by
  let F : Fin m → Finset (Fin m) := fun i => univ.filter fun l => (i, l) ∈ S
  have hS : ∑ i, (F i).card = S.card := by
    calc
      ∑ i, (F i).card = ∑ i, ∑ l, if (i, l) ∈ S then 1 else 0 := by
        simp only [F, Finset.card_filter]
      _ = ∑ p : Fin m × Fin m, if p ∈ S then 1 else 0 :=
        (Fintype.sum_prod_type fun p => if p ∈ S then 1 else 0).symm
      _ = S.card := by simp
  have hinter (i i' : Fin m) (hii' : i ≠ i') : (F i ∩ F i').card ≤ 2 := by
    by_contra! hlt
    obtain ⟨l0, l1, l2, h0, h1, h2, h01, h02, h12⟩ := Finset.two_lt_card_iff.mp hlt
    let l : Fin 3 → Fin m := ![l0, l1, l2]
    have hl : Function.Injective l := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> first | rfl | (exfalso; simp [l] at hxy; tauto)
    simp only [F, mem_inter, mem_filter, mem_univ, true_and] at h0 h1 h2
    have hmem (k : Fin 3) : (i, l k) ∈ S ∧ (i', l k) ∈ S := by
      fin_cases k
      exacts [h0, h1, h2]
    choose ν hνw hν using fun k => hexp (i, l k) (hmem k).1
    choose ν' hν'w hν' using fun k => hexp (i', l k) (hmem k).2
    have hshift (k : Fin 3) : a i + b (l k) + (a i' - a i) = a i' + b (l k) := by abel
    refine not_all_exposed_segment_add_triangle (fun k => a i + b (l k)) (a i' - a i) w hw
      ν ν' hνw hν'w (fun k k' hk => ?_) (fun k => ?_) (fun k k' hk => ?_) (fun k => ?_)
    · exact hν k (i, l k') (hmem k').1 (by simp [hl.ne hk])
    · simpa [hshift] using hν k (i', l k) (hmem k).2 (by simp [hii'.symm])
    · have := hν' k (i', l k') (hmem k').2 (by simp [hl.ne hk])
      simp only [map_add] at this ⊢
      linarith
    · simpa [hshift] using hν' k (i, l k) (hmem k).1 (by simp [hii'])
  have := sum_card_sq_le_of_card_inter_le F 2 hinter
  rw [hS, Fintype.card_fin] at this
  calc
    _ ≤ _ := this
    _ = _ := by ring

theorem card_le_mu_of_exposed_annihilating {m : ℕ} (a b : Fin m → Point 3) (w : Point 3)
    (hw : w ≠ 0) (S : Finset (Fin m × Fin m))
    (hexp : ∀ x ∈ S, ∃ ν : Dual ℝ (Point 3), ν w = 0 ∧
      ∀ y ∈ S, y ≠ x → ν (a y.1 + b y.2) < ν (a x.1 + b x.2)) :
    S.card ≤ mu m :=
  mu_spec m _ (card_sq_le_of_exposed_annihilating a b w hw S hexp)

/-! ### Layers of a convexly independent set -/

/-- The tails of the indices of `V` whose first coordinate is `j`. -/
def layer {m : ℕ} (V : Finset (Grid 3 m)) (j : Fin m) : Finset (Fin m × Fin m) :=
  univ.filter fun x => ![j, x.1, x.2] ∈ V

theorem gridSum_three {m : ℕ} (z : Fin 3 → Fin m → Point 3) (j k l : Fin m) :
    gridSum z ![j, k, l] = z 0 j + (z 1 k + z 2 l) := by
  simp [gridSum, Fin.sum_univ_three, add_assoc]

theorem sum_card_layer {m : ℕ} (V : Finset (Grid 3 m)) : ∑ j, (layer V j).card = V.card := by
  let e : Fin m × (Fin m × Fin m) ≃ Grid 3 m :=
    { toFun := fun p => ![p.1, p.2.1, p.2.2]
      invFun := fun i => (i 0, i 1, i 2)
      left_inv := fun p => rfl
      right_inv := fun i => by ext k; fin_cases k <;> rfl }
  calc
    ∑ j, (layer V j).card = ∑ j, ∑ x, if e (j, x) ∈ V then 1 else 0 := by
      simp only [layer, Finset.card_filter]
      rfl
    _ = ∑ p, if e p ∈ V then 1 else 0 :=
      (Fintype.sum_prod_type fun p => if e p ∈ V then 1 else 0).symm
    _ = ∑ i, if i ∈ V then 1 else 0 := e.sum_comp fun i => if i ∈ V then 1 else 0
    _ = V.card := by simp

/-- **L3**: two layers of a convexly independent set share at most `mu m` tails. -/
theorem card_inter_layer_le_mu {m : ℕ} (z : Fin 3 → Fin m → Point 3) {V : Finset (Grid 3 m)}
    (hV : ConvexIndependentOn (gridSum z) V)
    (hinj : Set.InjOn (gridSum z) (V : Set (Grid 3 m))) {j j' : Fin m} (hjj' : j ≠ j') :
    (layer V j ∩ layer V j').card ≤ mu m := by
  set S := layer V j ∩ layer V j'
  have hmem (x : Fin m × Fin m) (hx : x ∈ S) : ![j, x.1, x.2] ∈ V ∧ ![j', x.1, x.2] ∈ V := by
    simpa [S, layer] using hx
  have hne (x : Fin m × Fin m) : (![j', x.1, x.2] : Grid 3 m) ≠ ![j, x.1, x.2] :=
    fun h => hjj' (by simpa using (congrFun h 0).symm)
  have htail {x y : Fin m × Fin m} (c : Fin m) (hyx : y ≠ x) :
      (![c, y.1, y.2] : Grid 3 m) ≠ ![c, x.1, x.2] :=
    fun h => hyx (Prod.ext (by simpa using congrFun h 1) (by simpa using congrFun h 2))
  rcases S.eq_empty_or_nonempty with hS | ⟨x₀, hx₀⟩
  · simp [hS]
  set w := z 0 j' - z 0 j
  have hw : w ≠ 0 := by
    intro h
    refine hne x₀ (hinj (hmem x₀ hx₀).2 (hmem x₀ hx₀).1 ?_)
    rw [gridSum_three, gridSum_three, sub_eq_zero.mp h]
  refine card_le_mu_of_exposed_annihilating (z 1) (z 2) w hw S fun x hx => ?_
  obtain ⟨hxj, hxj'⟩ := hmem x hx
  obtain ⟨ν, hν⟩ := exists_exposing_of_convexIndependentOn hV hxj
  obtain ⟨ν', hν'⟩ := exists_exposing_of_convexIndependentOn hV hxj'
  have h1 : ν w < 0 := by
    have := hν _ (mem_erase.mpr ⟨hne x, hxj'⟩)
    simp only [gridSum_three, w, map_add, map_sub] at this ⊢
    linarith
  have h2 : 0 < ν' w := by
    have := hν' _ (mem_erase.mpr ⟨(hne x).symm, hxj⟩)
    simp only [gridSum_three, w, map_add, map_sub] at this ⊢
    linarith
  obtain ⟨ν₀, hν₀w, hν₀, -⟩ := exists_combination_annihilating ν ν' w h1 h2
  refine ⟨ν₀, hν₀w, fun y hy hyx => hν₀ _ _ ?_ ?_⟩
  · have := hν _ (mem_erase.mpr ⟨htail j hyx, (hmem y hy).1⟩)
    simp only [gridSum_three, map_add] at this ⊢
    linarith
  · have := hν' _ (mem_erase.mpr ⟨htail j' hyx, (hmem y hy).2⟩)
    simp only [gridSum_three, map_add] at this ⊢
    linarith

/-! ### The vertex bound -/

/-- **T1**: a convexly independent set of indices of a three-dimensional array of side `m` has at
most `R m` elements. -/
theorem card_le_R_of_convexIndependentOn {m : ℕ} (z : Fin 3 → Fin m → Point 3)
    (V : Finset (Grid 3 m)) (hV : ConvexIndependentOn (gridSum z) V)
    (hinj : Set.InjOn (gridSum z) (V : Set (Grid 3 m))) :
    V.card ≤ R m := by
  apply R_spec
  have := sum_card_sq_le_of_card_inter_le (layer V) (mu m)
    fun j j' h => card_inter_layer_le_mu z hV hinj h
  rw [sum_card_layer] at this
  simp only [Fintype.card_prod, Fintype.card_fin] at this
  calc
    _ ≤ _ := this
    _ = _ := by ring

end VCDimConvex
