import VCDimConvex.ConvexIndependentBound
import VCDimConvex.LabelCount
import VCDimConvex.Shattering

/-!
# Additive VC₂ dimension at most 123 for convex sets in ℝ³

Every label realized by a convex set on a `124 × 124 × 124` array is cut out by a convexly
independent set of at most `R 124` indices. Counting these subsets with a weighted binomial
estimate, and the minor sign patterns with the direct polynomial sign count, leaves fewer labels
than subsets of the grid. The Sanyal obstruction is not used.
-/

namespace VCDimConvex

open Finset

/-- Generator family: all index sets of size at most `R m`. -/
noncomputable def smallSubsets (m : ℕ) : Finset (Finset (Grid 3 m)) := by
  classical exact univ.filter fun V => V.card ≤ R m

theorem mem_smallSubsets {m : ℕ} {V : Finset (Grid 3 m)} : V ∈ smallSubsets m ↔ V.card ≤ R m := by
  classical
  simp [smallSubsets]

theorem mu_124 : mu 124 = 2007 := by norm_num [mu]

theorem R_124 : R 124 = 693785 := by norm_num [R, mu_124]

/-- Every realized label is cut out by a small convexly independent set. -/
theorem exists_small_generator {m : ℕ} {S : Set (Grid 3 m)} (hS : S ∈ convexLabels 3 m) :
    ∃ (z : Fin 3 → Fin m → Point 3) (V : Finset (Grid 3 m)),
      V ∈ smallSubsets m ∧ ∀ i, i ∈ S ↔ gridSum z i ∈ indexedHull (gridSum z) V := by
  obtain ⟨z, V, hV, -, hinj, -, rfl⟩ := exists_hull_encoding_of_mem_convexLabels hS
  exact ⟨z, V, mem_smallSubsets.mpr (card_le_R_of_convexIndependentOn z V hV hinj),
    fun _ => Iff.rfl⟩

theorem card_convexLabels_le_signs_mul_small (m : ℕ) :
    (convexLabels 3 m).card ≤ (minorSignPatterns 3 m).card * (smallSubsets m).card :=
  card_convexLabels_le_signs_mul_generators _ fun _ hS => exists_small_generator hS

/-- For `a ≤ b`, lowering the size of a subset raises its weight `a ^ |V| * b ^ (n - |V|)`. -/
theorem weight_anti {a b n r s : ℕ} (hab : a ≤ b) (hrs : r ≤ s) (hs : s ≤ n) :
    a ^ s * b ^ (n - s) ≤ a ^ r * b ^ (n - r) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hrs
  rw [show n - r = n - (r + t) + t by omega]
  calc
    a ^ (r + t) * b ^ (n - (r + t)) = a ^ r * b ^ (n - (r + t)) * a ^ t := by ring
    _ ≤ a ^ r * b ^ (n - (r + t)) * b ^ t := by gcongr
    _ = _ := by ring

/-- A weighted binomial count of the subsets of size at most `K`. -/
theorem card_filter_card_le_mul_weight_le {α : Type*} [Fintype α] [DecidableEq α] (K a b : ℕ)
    (hab : a ≤ b) (hK : K ≤ Fintype.card α) :
    (univ.filter fun V : Finset α => V.card ≤ K).card * (a ^ K * b ^ (Fintype.card α - K)) ≤
      (a + b) ^ Fintype.card α := by
  calc
    _ = ∑ _V ∈ univ.filter fun V : Finset α => V.card ≤ K, a ^ K * b ^ (Fintype.card α - K) := by
      simp
    _ ≤ ∑ V ∈ univ.filter fun V : Finset α => V.card ≤ K,
        a ^ V.card * b ^ (Fintype.card α - V.card) :=
      sum_le_sum fun V hV => weight_anti hab (mem_filter.mp hV).2 hK
    _ ≤ ∑ V : Finset α, a ^ V.card * b ^ (Fintype.card α - V.card) :=
      sum_le_sum_of_subset (subset_univ _)
    _ = (a + b) ^ Fintype.card α := Fintype.sum_pow_mul_eq_add_pow α a b

/-- **N0**: a weighted binomial count of the small subsets. -/
theorem card_smallSubsets_mul_weight_le (m : ℕ) (h : R m ≤ m ^ 3) :
    (smallSubsets m).card * (4 ^ R m * 7 ^ (m ^ 3 - R m)) ≤ 11 ^ (m ^ 3) := by
  classical
  simpa [smallSubsets] using
    card_filter_card_le_mul_weight_le (α := Grid 3 m) (R m) 4 7 (by norm_num) (by simpa using h)

/-- **N1**: the numerical certificate at `m = 124`, checked by kernel arithmetic. -/
theorem certificate_124 :
    (192 * 124 ^ 12 + 2) ^ 1118 * 11 ^ 1906624 <
      2 ^ 1906624 * (4 ^ 693785 * 7 ^ (1906624 - 693785)) := by
  decide +kernel

/-- The shape of the final count, kept abstract so that no large number is ever unfolded. -/
theorem lt_of_le_mul_of_weight {L N G P E T W : ℕ} (hL : L ≤ N * G) (hN : N ≤ P)
    (hG : G * W ≤ E) (hcert : P * E < T * W) : L < T := by
  refine Nat.lt_of_mul_lt_mul_right (a := W) ?_
  calc
    L * W ≤ N * G * W := Nat.mul_le_mul_right _ hL
    _ = N * (G * W) := Nat.mul_assoc _ _ _
    _ ≤ P * E := Nat.mul_le_mul hN hG
    _ < T * W := hcert

/-- **T2**: fewer labels than subsets of the `124 × 124 × 124` grid are realized by convex sets. -/
theorem card_convexLabels_lt_124 : (convexLabels 3 124).card < 2 ^ (124 ^ 3) := by
  have hsigns := card_minorSignPatterns_le_direct 3 124 (by norm_num) (by norm_num)
  rw [show 4 * 3 * (2 ^ (3 + 1) * (124 ^ 3) ^ (3 + 1)) + 2 = 192 * 124 ^ 12 + 2 by norm_num,
    show 3 ^ 2 * 124 + 2 = 1118 by norm_num] at hsigns
  have hsmall := card_smallSubsets_mul_weight_le 124 (by rw [R_124]; norm_num)
  rw [R_124, show 124 ^ 3 = 1906624 by norm_num] at hsmall
  rw [show 124 ^ 3 = 1906624 by norm_num]
  exact lt_of_le_mul_of_weight (card_convexLabels_le_signs_mul_small 124) hsigns hsmall
    certificate_124

/-- Every convex set in `ℝ³` has additive VC₂ dimension at most `123`. -/
theorem explicit_bound_123 (C : Set (Point 3)) (hC : Convex ℝ C) :
    HasAddVCNDimAtMost C 2 123 :=
  hasAddVCNDimAtMost_of_label_count_side 2 124 (by norm_num)
    (by rw [show 2 + 1 = 3 from rfl]; exact card_convexLabels_lt_124) C hC

end VCDimConvex
