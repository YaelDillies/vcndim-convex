# VCₙ dimension of convex sets in ℝⁿ⁺¹

This repository investigates the VCₙ dimension of convex sets in ℝⁿ⁺¹.

For every convex set `C ⊆ ℝ^(n+1)`, it proves the explicit estimates

```text
VC(C)   ≤ 3                          for n = 1,
VC_2(C) ≤ 123                        for n = 2,
VC_n(C) ≤ 2 ^ (8 * (n + 2) ^ n) - 1  for n ≥ 1.
```

### The bound VC ≤ 3

The planar case has a direct geometric proof (`VCDimConvex/BoundOne.lean`).  Suppose translates of
a convex set `C ⊆ ℝ²` shatter four points `x₁, …, x₄`.  If one point lies in the convex hull of the
other three, the translate that cuts out those three also contains the fourth.  Otherwise, by
Radon's lemma, two segments meet, say `[x₁, x₃]` and `[x₂, x₄]`.  Let `y₁₃` and `y₂₄` be the
translates cutting out `{1, 3}` and `{2, 4}`.  Of the eight points `y₁₃ + aᵢ` and `y₂₄ + aᵢ`,
exactly four lie in `C`.  Write `y₁₃ - y₂₄` in the basis `x₃ - x₁`, `x₄ - x₂`.  Its quadrant, and
one linear inequality, determine a point that should lie outside `C` but is a convex combination
of three points that lie in `C`.  When the two segments are parallel, an endpoint of one segment
lies in the other.

### The bound VC₂ ≤ 123

In `ℝ³` there is a direct bound on convexly independent index sets
(`VCDimConvex/ConvexIndependentBound.lean`).  Slice an `m × m × m` array into the layers
`i₀ = j`.  If two layers share three tails, the six corresponding points `b_k`, `b_k + u` would all
be strictly exposed by functionals annihilating the layer offset `w`.  This is impossible, because
such functionals form a line in the dual of `ℝ³`.  Two Cauchy–Schwarz counts then show that two
layers share at most `mu m` tails, and that a convexly independent set has at most `R m`
elements, where

```text
mu m = ⌊(m + √(m² + 8m²(m-1)))/2⌋,   R m = ⌊(m² + √(m⁴ + 4m³(m-1)·mu m))/2⌋.
```

At `m = 124`, `R 124 = 693785`.  A weighted binomial count (weights `4` and `7`) bounds the number
of such subsets, and the direct sign-pattern count bounds the rest.  The resulting inequality
between two numbers of about 3.6 million bits is checked by kernel arithmetic
(`VCDimConvex/Bound123.lean`).

## Status boundary

What this repository proves:

```text
For every n ≥ 1, there is one finite d(n) that works for every convex
C ⊆ ℝ^(n+1), with d(n) = 2^(8(n+2)^n) - 1.

Every convex C ⊆ ℝ^3 has additive VC_2 dimension at most 123.
```

What it does not prove:

```text
Every convex C ⊆ ℝ^3 has additive VC_2 dimension at most 2.

Every convex C ⊆ ℝ^(n+1) has additive VC_n dimension at most 3.
```

Those are separate open declarations in the same Formal Conjectures file.  The large explicit
bounds prove the uniform-existence target, but do not imply either sharper bound.

## Files

| Directory | Dependency | Purpose |
|---|---|---|
| repository root | mathlib + Lean 4.33.1 | Source modules (`VCDimConvex/`) and the FC-target entry point |

## Verification

```bash
lake exe cache get
lake build
```

The entry file contains `#print axioms` commands for the final explicit, existence and VC_2
theorems.
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
