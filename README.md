# VC_n dimension of convex sets in ℝⁿ⁺¹

This repository contains a Lean proof of the uniform finite-bound target registered in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/b86fdb9a8f2f83d2bb2b4281586705896c0c8208/FormalConjectures/Other/VCDimConvex.lean).
For every `n ≥ 1` and every convex set `C ⊆ ℝ^(n+1)`, it proves the explicit estimate

```text
VC_n(C) ≤ 2^(8 (n + 2)^n) - 1.
```

Consequently, it proves the complete binder and conclusion of the Formal Conjectures theorem
`VCDimConvex.exists_hasAddVCNDimAtMost_n_of_convex_rn_add_one`:

```lean
theorem vcdim_convex_uniform_bound_solved (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : ℕ, ∀ C : Set (Fin (n + 1) → ℝ),
      Convex ℝ C → HasAddVCNDimAtMost C n d
```

The witness is `d = 2^(8 * (n + 2)^n) - 1`.

The upstream Formal Conjectures declaration is still marked `research open` at the pinned
revision.

## Formal Conjectures target

The root Lake project depends only on mathlib.  It defines `HasAddVCNDimAtMost` locally, with
the same statement as the pinned Formal Conjectures definition, and restates the target.  Its
public entry point is:

```lean
theorem VCDimConvexFC.vcdim_convex_uniform_bound_solved
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : ℕ, ∀ C : Set (Fin (n + 1) → ℝ),
      Convex ℝ C → HasAddVCNDimAtMost C n d
```

The stronger explicit theorem is:

```lean
theorem VCDimConvex.explicit_bound
    (n : ℕ) (hn : 1 ≤ n)
    (C : Set (Fin (n + 1) → ℝ)) (hC : Convex ℝ C) :
    HasAddVCNDimAtMost C n (VCDimConvex.bound n)
```

Here `VCDimConvex.bound n` is defined as `2^(8 * (n + 2)^n) - 1`.

The project is pinned to mathlib `v4.33.1` and Lean `v4.33.1`.  Exact dependency revisions are
recorded in `lake-manifest.json`.

## Mathematical Explanation (AI generated)

The proof has two main parts.

First, it proves the geometric sparsification needed for the convex-label count.  A finite
hexagon complex, mod-two boundary identities, and a general-position removal argument give the
specialized odd-map zero statement required by the Sanyal obstruction.  This produces small
representative subsets for all relevant convex-hull labels.

Second, it bounds polynomial sign patterns directly.  For polynomials `f_i`, let `P = ∏ i, f_i`
and consider

```text
G(x) = P(x)^2 - ε (1 + ∑_j x_j^(2d+2)).
```

A common positive `ε` assigns a positive local maximum of `G` to every realized strict sign
word.  At a local maximum, the derivative equations have the form

```text
x_j^(2d+1) = R_j(x),    degree R_j < 2d+1.
```

Total-degree reduction and finite-point polynomial interpolation show that such a system has at
most `(2d+1)^p` distinct solutions in `p` variables.  Hence `N` polynomials of degree at most `k`
realize at most `(2kN+1)^p` strict sign words.  Introducing one shared variable handles zero
signs and gives the ternary bound `(4kN+1)^(p+1)`.  Applied to the determinant polynomials, this
fits the numerical budget above.

No general Warren theorem, hypersurface-component theorem, Sard theorem, or nondegeneracy of
critical points is assumed by the final theorem.

## Status boundary

What this repository proves:

```text
For every n ≥ 1, there is one finite d(n) that works for every convex
C ⊆ ℝ^(n+1), with d(n) = 2^(8(n+2)^n) - 1.
```

What it does not prove:

```text
Every convex C ⊆ ℝ^3 has additive VC_2 dimension at most 2.

Every convex C ⊆ ℝ^(n+1) has additive VC_n dimension at most 3.
```

Those are separate open declarations in the same Formal Conjectures file.  The large explicit
bound proves the uniform-existence target, but does not imply either sharper bound.

## Files

| Directory | Dependency | Purpose |
|---|---|---|
| repository root | mathlib + Lean 4.33.1 | Source modules (`VCDimConvex/`) and the FC-target entry point |

## Verification

```bash
lake exe cache get
lake build
```

The entry file contains `#print axioms` commands for the final explicit and existence theorems.
The build succeeds under Lean 4.33.1, and the reported dependencies are Lean's standard
foundations:

```text
[propext, Classical.choice, Quot.sound]
```

The project sources contain no `sorry`, `admit`, custom axiom, or `unsafe` theorem.

## Sources and attribution

- [Pinned Formal Conjectures target](https://github.com/google-deepmind/formal-conjectures/blob/b86fdb9a8f2f83d2bb2b4281586705896c0c8208/FormalConjectures/Other/VCDimConvex.lean)
- [Additive VC_n definition](https://github.com/google-deepmind/formal-conjectures/blob/b86fdb9a8f2f83d2bb2b4281586705896c0c8208/FormalConjecturesForMathlib/Combinatorics/Additive/VCDim.lean)
- [Repository layout used as a model](https://github.com/KitaKen1/erdos-361-asymptotic)

`VCDimConvex/Basic.lean` reproduces the relevant Formal Conjectures
definition under the repository's Apache-2.0 license and record the pinned source above.

## AI usage disclosure

This formalization and repository packaging were developed under the direction of Kenta Kitamura ([KitaKen1 on GitHub](https://github.com/KitaKen1)), with assistance from OpenAI's ChatGPT GPT-6 Astra and Codex GPT-6 Astra.
