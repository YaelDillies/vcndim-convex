import VCDimConvex.Bound123
import VCDimConvex.BoundOne
import VCDimConvex.ConvexIndependentGeneral

/-!
# Additive VCₙ dimension at most `2^(2^(n+1)+2) - 1` for convex sets in `ℝ^(n+1)`

Take the side length `m = 2^(2^(n+1)+2)`. Every label realized by a convex set on the grid of side
`m` is cut out by a convexly independent set of at most `vertexBound n m` indices, which is at most
a quarter of the grid. Counting these subsets with the weights `1` and `2`, and the minor sign
patterns with the direct polynomial sign count, leaves fewer labels than subsets of the grid. The
Sanyal obstruction is not used.
-/

namespace VCDimConvex

open Finset

/-! ### Density of the vertex bound -/

/-- One step of the density induction, with `p = m^r` and `T² = 2^(2^(D-r))`. -/
theorem density_step (p m T M : ℕ) (hT : 4 ≤ T) (h : (M + p) * T ^ 2 ≤ p * m) :
    (2 * p * m + Nat.sqrt (p * m ^ 3 * M)) * T ≤ p * m ^ 2 := by
  set s := Nat.sqrt (p * m ^ 3 * M)
  have hs : s ^ 2 ≤ p * m ^ 3 * M := by
    rw [sq]
    exact Nat.sqrt_le _
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have hM : M = 0 := by
      have : M * T ^ 2 = 0 := by simpa using h
      simpa [show T ≠ 0 by omega] using this
    simp [s, hM]
  have hTm : T ^ 2 ≤ m := Nat.le_of_mul_le_mul_left (by nlinarith) hp
  obtain ⟨X, rfl⟩ := Nat.exists_eq_add_of_le (show 2 * T ≤ m by nlinarith)
  have h1 : p * (2 * T + X) ^ 3 * (M * T ^ 2 + p * T ^ 2) ≤
      p * (2 * T + X) ^ 3 * (p * (2 * T + X)) := by
    gcongr
    nlinarith
  have h2 : (2 * T + X) ^ 2 ≤ X ^ 2 + (2 * T + X) * T ^ 2 := by
    nlinarith [Nat.mul_le_mul_left (T ^ 2) (show 4 ≤ 2 * T by omega),
      Nat.mul_le_mul_left (T * X) hT]
  have h3 := Nat.mul_le_mul_left (p ^ 2 * (2 * T + X) ^ 2) h2
  have hsq : (s * T) ^ 2 ≤ (p * (2 * T + X) * X) ^ 2 := by
    calc
      (s * T) ^ 2 = s ^ 2 * T ^ 2 := by ring
      _ ≤ p * (2 * T + X) ^ 3 * M * T ^ 2 := by gcongr
      _ ≤ _ := by nlinarith
  have := (Nat.pow_le_pow_iff_left (by norm_num)).mp hsq
  nlinarith

/-- **N1**: at the side length `m = 2^(2^D+2)`, the vertex bound for `r + 1 ≤ D` families is at
most `m^(r+1) / 2^(2^(D-r)) - m^r`. -/
theorem vertexBound_density (D : ℕ) :
    ∀ r, r + 1 ≤ D → (vertexBound r (2 ^ (2 ^ D + 2)) + (2 ^ (2 ^ D + 2)) ^ r) *
      2 ^ (2 ^ (D - r)) ≤ (2 ^ (2 ^ D + 2)) ^ (r + 1)
  | 0, _ => by
    simp only [vertexBound, pow_zero, Nat.sub_zero, pow_one, pow_add]
    omega
  | r + 1, hD => by
    have ih := vertexBound_density D r (by omega)
    set m := 2 ^ (2 ^ D + 2)
    set T := 2 ^ (2 ^ (D - (r + 1)))
    have hT2 : 2 ^ (2 ^ (D - r)) = T ^ 2 := by
      simp only [T]
      rw [← pow_mul, show D - r = D - (r + 1) + 1 by omega, pow_succ]
    have hT : 4 ≤ T :=
      calc
        4 = 2 ^ 2 ^ 1 := rfl
        _ ≤ T := Nat.pow_le_pow_right (by norm_num)
          (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [hT2, pow_succ] at ih
    have := density_step (m ^ r) m T (vertexBound r m) hT ih
    rw [vertexBound, show m ^ (r + 1) * m ^ 2 * vertexBound r m =
      m ^ r * m ^ 3 * vertexBound r m by ring]
    calc
      _ = (2 * m ^ r * m + Nat.sqrt (m ^ r * m ^ 3 * vertexBound r m)) * T := by ring
      _ ≤ m ^ r * m ^ 2 := this
      _ = _ := by ring

/-- At the side length `2^(2^(n+1)+2)`, a convexly independent set covers at most a quarter of
the grid. -/
theorem four_mul_vertexBound_le (n : ℕ) :
    4 * vertexBound n (2 ^ (2 ^ (n + 1) + 2)) ≤ (2 ^ (2 ^ (n + 1) + 2)) ^ (n + 1) := by
  have := vertexBound_density (n + 1) n (le_refl _)
  rw [show n + 1 - n = 1 by omega] at this
  calc
    _ ≤ (vertexBound n (2 ^ (2 ^ (n + 1) + 2)) + (2 ^ (2 ^ (n + 1) + 2)) ^ n) * 2 ^ 2 ^ 1 := by
      rw [add_mul, mul_comm]
      exact Nat.le_add_right _ _
    _ ≤ _ := this

/-! ### Counting the small subsets -/

/-- Generator family: all index sets of size at most `vertexBound n m`. -/
noncomputable def vertexSubsets (n m : ℕ) : Finset (Finset (Grid (n + 1) m)) := by
  classical exact univ.filter fun V => V.card ≤ vertexBound n m

theorem mem_vertexSubsets {n m : ℕ} {V : Finset (Grid (n + 1) m)} :
    V ∈ vertexSubsets n m ↔ V.card ≤ vertexBound n m := by
  classical
  simp [vertexSubsets]

/-- Every realized label is cut out by a small convexly independent set. -/
theorem exists_vertex_generator {n m : ℕ} {S : Set (Grid (n + 1) m)}
    (hS : S ∈ convexLabels (n + 1) m) :
    ∃ (z : Fin (n + 1) → Fin m → Point (n + 1)) (V : Finset (Grid (n + 1) m)),
      V ∈ vertexSubsets n m ∧ ∀ i, i ∈ S ↔ gridSum z i ∈ indexedHull (gridSum z) V := by
  obtain ⟨z, V, hV, -, -, -, rfl⟩ := exists_hull_encoding_of_mem_convexLabels hS
  exact ⟨z, V, mem_vertexSubsets.mpr (card_le_vertexBound_of_convexIndependentOn z V hV),
    fun _ => Iff.rfl⟩

theorem card_convexLabels_le_signs_mul_vertexSubsets (n m : ℕ) :
    (convexLabels (n + 1) m).card ≤
      (minorSignPatterns (n + 1) m).card * (vertexSubsets n m).card :=
  card_convexLabels_le_signs_mul_generators _ fun _ hS => exists_vertex_generator hS

/-- A weighted binomial count of the small subsets. -/
theorem card_vertexSubsets_mul_weight_le (n m a b : ℕ) (hab : a ≤ b)
    (h : vertexBound n m ≤ m ^ (n + 1)) :
    (vertexSubsets n m).card * (a ^ vertexBound n m * b ^ (m ^ (n + 1) - vertexBound n m)) ≤
      (a + b) ^ (m ^ (n + 1)) := by
  classical
  simpa [vertexSubsets] using card_filter_card_le_mul_weight_le (α := Grid (n + 1) m)
    (vertexBound n m) a b hab (by simpa using h)

/-- **N2**: if the small subsets cover at most a quarter of the grid, they are few. -/
theorem card_vertexSubsets_pow_le (n m : ℕ) (h : 4 * vertexBound n m ≤ m ^ (n + 1)) :
    (vertexSubsets n m).card ^ 4 * 2 ^ (3 * m ^ (n + 1)) ≤ 3 ^ (4 * m ^ (n + 1)) := by
  have hcount := card_vertexSubsets_mul_weight_le n m 1 2 (by norm_num) (by omega)
  rw [one_pow, one_mul] at hcount
  calc
    _ ≤ (vertexSubsets n m).card ^ 4 * 2 ^ (4 * (m ^ (n + 1) - vertexBound n m)) := by
      have : 3 * m ^ (n + 1) ≤ 4 * (m ^ (n + 1) - vertexBound n m) := by
        generalize m ^ (n + 1) = N at h ⊢
        omega
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) this)
    _ = ((vertexSubsets n m).card * 2 ^ (m ^ (n + 1) - vertexBound n m)) ^ 4 := by ring
    _ ≤ (3 ^ (m ^ (n + 1))) ^ 4 := Nat.pow_le_pow_left hcount 4
    _ = _ := by ring

/-! ### The sign-pattern budget -/

theorem add_two_le_two_pow {n : ℕ} (hn : 2 ≤ n) : n + 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

/-- **N3**: the exponent of the sign-pattern count is small against the grid size. -/
theorem sign_budget (n : ℕ) (hn : 2 ≤ n) :
    20 * (4 * (2 ^ (n + 1) + 2) * (n + 1 + 1) ^ 4 * 2 ^ (2 ^ (n + 1) + 2)) <
      (2 ^ (2 ^ (n + 1) + 2)) ^ (n + 1) := by
  set L := 2 ^ (n + 1) + 2
  have h8 : 8 ≤ 2 ^ (n + 1) :=
    calc
      8 = 2 ^ 3 := rfl
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hL : L ≤ 2 ^ (n + 2) := by
    rw [pow_succ 2 (n + 1)]
    omega
  have hexp : 5 * n + 9 ≤ L * n := by
    show 5 * n + 9 ≤ (2 ^ (n + 1) + 2) * n
    nlinarith [Nat.mul_le_mul_right n h8]
  have hpos : 0 < L * (n + 2) ^ 4 := by positivity
  have key : 80 * L * (n + 2) ^ 4 < (2 ^ L) ^ n := by
    calc
      80 * L * (n + 2) ^ 4 < 2 ^ 7 * L * (n + 2) ^ 4 := by
        rw [mul_assoc, mul_assoc (2 ^ 7)]
        exact Nat.mul_lt_mul_of_pos_right (by norm_num) hpos
      _ ≤ 2 ^ 7 * 2 ^ (n + 2) * (2 ^ n) ^ 4 := by
        gcongr
        exact add_two_le_two_pow hn
      _ = 2 ^ (5 * n + 9) := by ring
      _ ≤ 2 ^ (L * n) := Nat.pow_le_pow_right (by norm_num) hexp
      _ = (2 ^ L) ^ n := pow_mul _ _ _
  calc
    _ = 80 * L * (n + 2) ^ 4 * 2 ^ L := by ring
    _ < (2 ^ L) ^ n * 2 ^ L := Nat.mul_lt_mul_of_pos_right key (by positivity)
    _ = _ := (pow_succ _ _).symm

/-! ### The final count -/

/-- The shape of the final count, kept abstract. -/
theorem lt_two_pow_of_counts {L P G N : ℕ} (hL : L ≤ P * G) (hP : P ^ 20 < 2 ^ N)
    (hG : G ^ 4 * 2 ^ (3 * N) ≤ 3 ^ (4 * N)) : L < 2 ^ N := by
  have h3 : 3 ^ (20 * N) ≤ 2 ^ (32 * N) := by
    rw [show 20 * N = 5 * (4 * N) by ring, show 32 * N = 8 * (4 * N) by ring,
      pow_mul 3 5, pow_mul 2 8]
    exact Nat.pow_le_pow_left (show 3 ^ 5 ≤ 2 ^ 8 by norm_num) _
  have hPG : (P * G) ^ 20 * 2 ^ (15 * N) < (2 ^ N) ^ 20 * 2 ^ (15 * N) := by
    calc
      (P * G) ^ 20 * 2 ^ (15 * N) = P ^ 20 * (G ^ 4 * 2 ^ (3 * N)) ^ 5 := by ring
      _ ≤ P ^ 20 * (3 ^ (4 * N)) ^ 5 := by gcongr
      _ < 2 ^ N * (3 ^ (4 * N)) ^ 5 := Nat.mul_lt_mul_of_pos_right hP (by positivity)
      _ = 2 ^ N * 3 ^ (20 * N) := by ring
      _ ≤ 2 ^ N * 2 ^ (32 * N) := by gcongr
      _ ≤ 2 ^ N * 2 ^ (34 * N) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ = _ := by ring
  have hlt : L ^ 20 < (2 ^ N) ^ 20 :=
    (Nat.pow_le_pow_left hL 20).trans_lt (Nat.lt_of_mul_lt_mul_right hPG)
  exact lt_of_pow_lt_pow_left₀ 20 (by positivity) hlt

/-- **T2**: fewer labels than subsets of the grid of side `2^(2^(n+1)+2)` are realized by convex
sets in `ℝ^(n+1)`. -/
theorem card_convexLabels_lt_general (n : ℕ) (hn : 2 ≤ n) :
    (convexLabels (n + 1) (2 ^ (2 ^ (n + 1) + 2))).card <
      2 ^ ((2 ^ (2 ^ (n + 1) + 2)) ^ (n + 1)) := by
  have h8 : 8 ≤ 2 ^ (n + 1) + 2 := by
    have : 8 ≤ 2 ^ (n + 1) :=
      calc
        8 = 2 ^ 3 := rfl
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hsigns := card_minorSignPatterns_le_two_pow_direct (n + 1) _ (by omega) h8
  refine lt_two_pow_of_counts (card_convexLabels_le_signs_mul_vertexSubsets n _) ?_
    (card_vertexSubsets_pow_le n _ (four_mul_vertexBound_le n))
  calc
    _ ≤ (2 ^ (4 * (2 ^ (n + 1) + 2) * (n + 1 + 1) ^ 4 * 2 ^ (2 ^ (n + 1) + 2))) ^ 20 :=
      Nat.pow_le_pow_left hsigns 20
    _ = 2 ^ (20 * (4 * (2 ^ (n + 1) + 2) * (n + 1 + 1) ^ 4 * 2 ^ (2 ^ (n + 1) + 2))) := by
      rw [← pow_mul, mul_comm]
    _ < _ := Nat.pow_lt_pow_right (by norm_num) (sign_budget n hn)

/-- Every convex set in `ℝ^(n+1)`, `n ≥ 1`, has additive VCₙ dimension at most
`2^(2^(n+1)+2) - 1`. For `n = 1` this follows from the planar bound `3`. -/
theorem explicit_bound_general (n : ℕ) (hn : n ≠ 0) (C : Set (Point (n + 1)))
    (hC : Convex ℝ C) : HasAddVCNDimAtMost C n (2 ^ (2 ^ (n + 1) + 2) - 1) := by
  obtain rfl | hn := (show n = 1 ∨ 2 ≤ n by omega)
  · exact (explicit_bound_one C hC).hasAddVCNDimAtMost_one.mono (by norm_num)
  exact hasAddVCNDimAtMost_of_label_count_side n _ (by positivity)
    (card_convexLabels_lt_general n hn) C hC

end VCDimConvex
