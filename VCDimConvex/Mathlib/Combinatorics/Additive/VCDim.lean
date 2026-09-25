/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import VCDimConvex.Mathlib.Combinatorics.SetFamily.VCDim

/-!
# VC dimension of a set in a group

This file defines the VC dimension of a set in a group as the VC dimension of its set of translates.
-/

open scoped Pointwise

variable {G : Type*} [Group G] {A B : Set G} {d₁ d₂ : ℕ}

/-- A set `A` in a group `G` has VC dimension at most `d` if all the sets that `{t • A | t : G}`
shatters have size at most `d`. -/
@[to_additive
/-- A set `A` in a group `G` has VC dimension at most `d` if all the sets that `{t +ᵥ A | t : G}`
shatters have size at most `d`. -/]
def HasMulVCDimLE (d : ℕ) (A : Set G) : Prop := HasVCDimLE d {t • A | t : G}

@[to_additive (attr := gcongr)]
lemma HasMulVCDimLE.mono (hd : d₁ ≤ d₂) (hA : HasMulVCDimLE d₁ A) : HasMulVCDimLE d₂ A :=
  HasVCDimLE.mono hd hA
