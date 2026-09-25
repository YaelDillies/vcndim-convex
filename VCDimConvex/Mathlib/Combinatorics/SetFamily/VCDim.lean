/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice

/-!
# VC dimension

This file defines the VC dimension of set families.
-/

variable {α : Type*}

section SemilatticeInf
variable [SemilatticeInf α] {𝒜 ℬ : Set α} {A B : α}

/-- A set family `𝒜` shatters a set `A` if all subsets of `A` can be obtained as the intersection
of `A` with some element of the set family. We also say that `A` is *traced* by `𝒜`. -/
def Shatters (𝒜 : Set α) (A : α) : Prop := ∀ ⦃B⦄, B ≤ A → ∃ C ∈ 𝒜, A ⊓ C = B

@[gcongr]
lemma Shatters.mono (h : 𝒜 ⊆ ℬ) (h𝒜 : Shatters 𝒜 A) : Shatters ℬ A :=
  fun _B hBA ↦ let ⟨C, hC, hCB⟩ := h𝒜 hBA; ⟨C, h hC, hCB⟩

end SemilatticeInf

section Set
variable {d d₁ d₂ : ℕ} {𝒜 ℬ : Set (Set α)}

/-- A set family `𝒜` has VC dimension at most `d` if all the sets it shatters have size at most
`d`. -/
def HasVCDimLE (d : ℕ) (𝒜 : Set (Set α)) : Prop :=
  ∀ ⦃A : Set α⦄, A.Finite → Shatters 𝒜 A → A.ncard ≤ d

@[gcongr]
lemma HasVCDimLE.anti (hℬ𝒜 : ℬ ⊆ 𝒜) (hd : HasVCDimLE d 𝒜) : HasVCDimLE d ℬ :=
  fun _A hA h𝒜A ↦ hd hA <| h𝒜A.mono hℬ𝒜

@[gcongr]
lemma HasVCDimLE.mono (hd : d₁ ≤ d₂) : HasVCDimLE d₁ 𝒜 → HasVCDimLE d₂ 𝒜 := by
  grw [HasVCDimLE, HasVCDimLE, hd]; exact id

end Set
