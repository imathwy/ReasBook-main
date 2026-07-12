import Mathlib.Analysis.Convex.Basic
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_3_0_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Pointwise

universe u v w

/-
Source/core/bridge triage:
- `source-facing`: Text 3.1.3 says that a finite linear combination of convex sets is convex.
- `core/canonical`: the owner abstraction is `Convex 𝕜` on sets. Mathlib's finite-sum theorem
  `convex_sum` is canonical but currently requires the stronger `[Module 𝕜 E]` layer.
- `bridge/view`: the textbook expression `∑ i ∈ s, w i • C i` is already the weighted
  Minkowski-sum expression in the pointwise additive structure on sets.
- Primitive data vs derived API: primitive data are a finite family of sets and coefficients;
  scalar-image convexity and binary-sum convexity come from upstream chapter bridges
  (`Convex.smul_set` in `Theorem_3_0_2` and `Convex.add_set` in
  `Theorem_3_1`); finite-sum convexity is then rebuilt below.
- Domain-style sampling: this item aligns with finite pointwise set sums and
  `Set.addCommMonoid`.
- Layer target: `core/canonical` with a source-facing theorem surface by direct owner reuse.

Abstraction audit (canonicalize):
- Codomain/ambient layer over-concrete? `No`: this item is codomain-free and lives at set convexity.
- Scalar/ambient structure stronger than needed? `Yes` in the old version: requiring
  `[Module 𝕜 E]` came from `convex_sum`, but the finite weighted-set-sum argument only needs
  `[DistribSMul 𝕜 E]` plus commuting scalar actions.
- Owner tied to a concrete model? `No`: owner remains intrinsic `Convex 𝕜`.
- Ambient-vs-intrinsic topology mismatch? `Not applicable`.
- Owner name/notation too heavy or too concrete? `No`: theorem surface stays in the textbook
  notation `∑ i ∈ s, w i • C i`.
- Upstream over-specialization to repair first? `Yes`: reuse the upstream weak scalar-image and
  binary-sum bridges, then expose finite-sum closure at the same weak layer.
-/

section

variable {ι : Type u} {𝕜 : Type v} {E : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [DistribSMul 𝕜 E]

/-- Finite Minkowski-sum closure for convex sets at the same primitive scalar-action layer as
scalar-image convexity at this weak action layer, reusing the upstream binary closure theorem
`Convex.add_set` from `Theorem_3_1`. This owner theorem avoids exposing
`[Module 𝕜 E]` on downstream theorem surfaces. -/
theorem Convex.sum_set (s : Finset ι) (t : ι → Set E)
    (h : ∀ i ∈ s, Convex 𝕜 (t i)) :
    Convex 𝕜 (∑ i ∈ s, t i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro h x hx y hy a b ha hb hab
    have hx0 : x = 0 := by simpa using hx
    have hy0 : y = 0 := by simpa using hy
    subst hx0
    subst hy0
    simp [smul_zero]
  · intro i s hi hs h
    have hiConv : Convex 𝕜 (t i) := h i (by simp [hi])
    have hsConv : Convex 𝕜 (∑ j ∈ s, t j) := hs (by
      intro j hj
      exact h j (by simp [hj]))
    simpa [Finset.sum_insert, hi] using hiConv.add_set hsConv

variable [SMulCommClass 𝕜 𝕜 E]

/-- Text 3.1.3 in source-facing weighted-set notation: a finite weighted Minkowski sum of convex
sets is convex. The theorem surface is now at the primitive scalar-action layer
`[DistribSMul 𝕜 E]`, using the weak scalar-image convexity bridge and `Convex.sum_set`
rather than the stronger `[Module 𝕜 E]`-based `convex_sum`. -/
theorem Convex.sum_smul (s : Finset ι) (w : ι → 𝕜) (C : ι → Set E)
    (hC : ∀ i ∈ s, Convex 𝕜 (C i)) :
    Convex 𝕜 (∑ i ∈ s, w i • C i) := by
  refine Convex.sum_set (s := s) (t := fun i ↦ w i • C i) ?_
  intro i hi
  exact (hC i hi).smul_set

end
