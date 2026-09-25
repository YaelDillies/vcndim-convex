import VCDimConvex.DirectSignCount
import VCDimConvex.Minors

/-!
# Counting all-minor sign patterns

This applies the direct polynomial sign count to the polynomial encoding of additive arrays. The
geometric assertion that minor signs determine convex-hull membership is proved separately in
`MinorHullRecovery`.
-/

namespace VCDimConvex

/-- All ternary sign vectors of the polynomial minor family. -/
noncomputable def minorSignPatterns (D m : ℕ) : Finset (MinorIndex D m → Fin 3) :=
  ternaryPatterns (fun j x => MvPolynomial.eval x (minorPolynomial j))

/-- The number of minor sign patterns. -/
theorem card_minorSignPatterns_le_direct (D m : ℕ) (hD : 1 ≤ D) (hm : 0 < m) :
    (minorSignPatterns D m).card ≤
      (4 * D * (2 ^ (D + 1) * (m ^ D) ^ (D + 1)) + 2) ^ (D ^ 2 * m + 2) := by
  have h := card_ternaryPatterns_le_coarse_direct D hD
    (minorPolynomial (D := D) (m := m)) totalDegree_minorPolynomial_le
  simp only [card_arrayVar] at h
  change (minorSignPatterns D m).card ≤ _ at h
  exact h.trans (by gcongr; exact card_minorIndex_le D m hm)

/-- The base of the sign count fits inside a power of two. -/
theorem minor_base_le_two_pow (D L : ℕ) (hD : 1 ≤ D) (hL : 8 ≤ L) :
    4 * D * (2 ^ (D + 1) * ((2 ^ L) ^ D) ^ (D + 1)) + 2 ≤
      2 ^ (2 * L * (D + 1) ^ 2) := by
  have hpos : 0 < D * (2 ^ (D + 1) * ((2 ^ L) ^ D) ^ (D + 1)) := by positivity
  have hexp : 4 + 2 * D + L * D * (D + 1) ≤ 2 * L * (D + 1) ^ 2 := by
    nlinarith
  calc
    _ ≤ 8 * D * (2 ^ (D + 1) * ((2 ^ L) ^ D) ^ (D + 1)) := by nlinarith
    _ ≤ 8 * (2 ^ D) * (2 ^ (D + 1) * ((2 ^ L) ^ D) ^ (D + 1)) := by
      gcongr
      exact (Nat.lt_two_pow_self (n := D)).le
    _ = 2 ^ (4 + 2 * D + L * D * (D + 1)) := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
      simp only [← pow_mul, ← pow_add]
      congr 1
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hexp

/-- The number of minor sign patterns at a side length that is a power of two. -/
theorem card_minorSignPatterns_le_two_pow_direct (D L : ℕ) (hD : 1 ≤ D) (hL : 8 ≤ L) :
    (minorSignPatterns D (2 ^ L)).card ≤ 2 ^ (4 * L * (D + 1) ^ 4 * 2 ^ L) := by
  have hm : 0 < (2 : ℕ) ^ L := by positivity
  have hp : D ^ 2 * 2 ^ L + 2 ≤ 2 * (D + 1) ^ 2 * 2 ^ L := by
    calc
      _ ≤ (D ^ 2 + 2) * 2 ^ L := by nlinarith
      _ ≤ _ := Nat.mul_le_mul_right _ (by nlinarith : D ^ 2 + 2 ≤ 2 * (D + 1) ^ 2)
  have he : (2 * L * (D + 1) ^ 2) * (D ^ 2 * 2 ^ L + 2) ≤
      4 * L * (D + 1) ^ 4 * 2 ^ L := by
    calc
      _ ≤ (2 * L * (D + 1) ^ 2) * (2 * (D + 1) ^ 2 * 2 ^ L) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ _ := card_minorSignPatterns_le_direct D (2 ^ L) hD hm
    _ ≤ (2 ^ (2 * L * (D + 1) ^ 2)) ^ (D ^ 2 * 2 ^ L + 2) :=
      Nat.pow_le_pow_left (minor_base_le_two_pow D L hD hL) _
    _ = 2 ^ ((2 * L * (D + 1) ^ 2) * (D ^ 2 * 2 ^ L + 2)) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) he

end VCDimConvex
