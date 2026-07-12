import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap07.Lemma33_0_22

noncomputable section

universe u v w z

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 33.1 sends a convex bifunction `F` to the saddle kernel
  `lowerPairing F`, sends a concave-convex kernel `K` back to the bifunction `lowerPairing K`
  under the swapped pairing, and gives the reconstruction formulas
  `lowerPairing (lowerPairing F) = cl₂ F` and `lowerPairing (lowerPairing K) = cl₂ K`.
- `core/canonical`: the chapter already owns the operators and predicates needed for that
  statement: `lowerPairing`, the bifunction closure owner `cl₂`, graph convexity
  `(Function.uncurry F).IsConvex 𝕜`, second-variable closedness
  `Bifunction.IsConvexClosed`, and saddle shape `SaddleFunction.IsConcaveConvex 𝕜`.
- `bridge/view`: the inverse-on-closed-classes theorem
  `lowerPairing_invOn_admissibleClasses` belongs to the corollary layer rather than
  to Theorem 33.1 itself.

Domain-style sampling used here:
- `lowerPairing` from `Defn_34_2`;
- `Function.isConvex_convexConjugate` and
  `lowerSemicontinuous_convexConjugate_of_pairingSlices` from Chapter 12;
- `cl(·)` and `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull` from Chapter 12;
- `cl₂` and `Bifunction.IsConvexClosed` from Definition 33.0.4;
- `lowerPairing_isConcaveConvex_of_uncurry_isConvex` from Lemma 33.0.22.

Primitive data vs derived API:
- primitive owners: `lowerPairing`, `cl(·)`, `cl₂`, graph convexity, and saddle concave-convexity;
- derived API here: forward second-variable closedness, reverse graph convexity, and the two
  reconstruction formulas.

Layer target: clause `(1)` is an exact `core/canonical` recall; the remaining declarations are
`source-facing`. The one-to-one correspondence under additional closedness hypotheses is deferred
to Corollary 33.1.2.
-/

section ForwardShape

variable {𝕜 : Type z} {U : Type u} {X : Type v} {XStar : Type w}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid XStar] [Module 𝕜 XStar]
variable [HasLinearPairing X XStar 𝕜]

/- Theorem33.1 (1): if the graph function of `F` is jointly convex, then the lower
representative `lowerPairing XStar F` is a concave-convex saddle bifunction. This clause is
already formalized upstream as the canonical owner theorem
`lowerPairing_isConcaveConvex_of_uncurry_isConvex`. -/
recall lowerPairing_isConcaveConvex_of_uncurry_isConvex

end ForwardShape

section ForwardClosedness

variable {𝕜 : Type z} {U : Type u} {X : Type v} {XStar : Type w}
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable [TopologicalSpace XStar] [Sub (WithTopBot 𝕜)] [HasPairing X XStar 𝕜]

/-- Theorem33.1 (1): partial Fenchel conjugation in the second variable
is closed in that variable once the dual pairing slices are lower semicontinuous; this is the
slice-wise Chapter 12 owner theorem lifted to the bifunction layer. -/
-- Proof sketch: apply the slice-wise Chapter 12 lower-semicontinuity theorem for convex
-- conjugates to each fixed `u`, then rewrite the result as the Chapter 33 owner predicate
-- `IsConvexClosed`.
theorem lowerPairing_isConvexClosed
    (F : U → X → WithTopBot 𝕜)
    (hpair : ∀ x : X,
      LowerSemicontinuous (fun xStar : XStar ↦ ⟪x, xStar⟫ₚ)) :
    IsConvexClosed (lowerPairing XStar F) := sorry

end ForwardClosedness

section ReverseShape

variable {𝕜 : Type z} {U : Type u} {X : Type v} {XStar : Type w}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid XStar] [Module 𝕜 XStar]
variable [HasLinearPairing XStar X 𝕜]

/-- Theorem33.1 (2): if `K` is concave-convex, then its reverse partial Fenchel
conjugate is jointly convex. -/
-- Proof sketch: combine the Chapter 33 saddle-shape hypothesis on `K` with the reverse
-- conjugation convexity theorem for concave-convex kernels, then rewrite the conclusion on the
-- uncurried graph function.
theorem lowerPairing_uncurry_isConvex_of_isConcaveConvex
    (K : U → XStar → WithTopBot 𝕜) (hK : SaddleFunction.IsConcaveConvex 𝕜 K) :
    (Function.uncurry (lowerPairing X K)).IsConvex 𝕜 := sorry

end ReverseShape

section Reconstruction

variable {𝕜 : Type z} {U : Type u} {X : Type v} {XStar : Type w}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]

/-- Theorem33.1 (3): applying reverse partial Fenchel conjugation to
`lowerPairing F` recovers the intrinsic second-variable closure `cl₂ F`. -/
-- Proof sketch: apply the Chapter 12 biconjugation formula to each second-variable slice of `F`,
-- using the finite-dimensional continuous pairing hypotheses to identify the iterated partial
-- conjugation with slice-wise biconjugation and then with `cl₂ F`.
theorem lowerPairing_lowerPairing_eq_closure2_of_uncurry_isConvex
    [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X] [FiniteDimensional 𝕜 X]
    [TopologicalSpace XStar] [AddCommMonoid XStar] [Module 𝕜 XStar]
    [HasLinearPairing X XStar 𝕜] [HasContinuousPairing X XStar 𝕜]
    [HasLinearPairing XStar X 𝕜] [HasContinuousPairing XStar X 𝕜]
    (F : U → X → WithTopBot 𝕜) (hF : (Function.uncurry F).IsConvex 𝕜) :
    lowerPairing X (lowerPairing XStar F) = cl₂ F := sorry

/-- Theorem33.1 (4): for a concave-convex kernel `K`, the forward
partial conjugate of its reverse partial conjugate is the second-variable closure `cl₂ K`. -/
-- Proof sketch: apply the previous biconjugation argument to the swapped pairing orientation for
-- the concave-convex kernel `K`, using the reverse-shape clause to supply the convexity input for
-- the reconstructed graph function.
theorem lowerPairing_lowerPairing_eq_closure2_of_isConcaveConvex
    [TopologicalSpace X] [AddCommMonoid X] [Module 𝕜 X]
    [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar] [FiniteDimensional 𝕜 XStar]
    [HasLinearPairing X XStar 𝕜] [HasContinuousPairing X XStar 𝕜]
    [HasLinearPairing XStar X 𝕜] [HasContinuousPairing XStar X 𝕜]
    (K : U → XStar → WithTopBot 𝕜) (hK : SaddleFunction.IsConcaveConvex 𝕜 K) :
    lowerPairing XStar (lowerPairing X K) = cl₂ K := sorry

end Reconstruction

end Bifunction
