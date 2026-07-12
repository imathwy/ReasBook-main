import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_8
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_36_4_1

noncomputable section

universe u v w z

open scoped Rockafellar
open Function

namespace Rockafellar

local notation "IsClosedProperConvex[" 𝕜 "]" =>
  Function.IsClosedProperConvex (𝕜 := 𝕜)

local notation "IsClosedProperConcave[" 𝕜 "]" =>
  Function.IsClosedProperConcave (𝕜 := 𝕜)

/-- Source-facing closed-proper-convex owner for a bifunction graph function. -/
scoped[Rockafellar] notation:70 "cpconvᵇ[" 𝕜 "](" F ")" =>
  IsClosedProperConvex[𝕜] (Function.uncurry F)

/-- Source-facing closed-proper-concave owner for a bifunction graph function. -/
scoped[Rockafellar] notation:70 "cpconcᵇ[" 𝕜 "](" F ")" =>
  IsClosedProperConcave[𝕜] (Function.uncurry F)

end Rockafellar

namespace Bifunction

section Convexity

variable {𝕜 : Type z} {U : Type u} {X : Type v} {α : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [AddCommGroup α] [SMul 𝕜 α] [LE α]

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 36.4.2 studies the inverse bifunction `F_*`, owned in this chapter
  by `Bifunction.inverse`.
- `core/canonical`: the natural owner layer for the convexity clauses is the graph-function API
  `Function.uncurry`, together with the Chapter 6 convex/concave source notations
  `convᵇ[𝕜](F)` and `concᵇ[𝕜](F)`, and the closed-proper source notations
  `cpconvᵇ[𝕜](F)` and `cpconcᵇ[𝕜](F)` on
  `WithTopBot α`.
- `bridge/view`: the source-facing inverse object `F _*` is studied directly through those
  existing owners, with no file-local convex-bifunction wrapper alias.

Domain-style sampling used here:
- `Function.uncurry`;
- `Bifunction.inverse`;
- `convᵇ[𝕜](F)`;
- `concᵇ[𝕜](F)`.
- `cpconvᵇ[𝕜](F)`;
- `cpconcᵇ[𝕜](F)`.

Primitive data vs derived API:
- primitive datum: a bifunction `F : U → X → WithTopBot α`;
- source-facing inverse object: `F _*`;
- derived clauses: convexity/concavity exchange, preservation of the closed-proper classes, and
  involutivity.

Layer target: `source-facing`, using the chapter owners and source notation.
-/

-- Proof sketch: `Function.uncurry (inverse F)` is obtained from `Function.uncurry F` by
-- precomposing with coordinate swap and negating values; swapping preserves affine combinations,
-- while negation exchanges convexity and concavity.
/-- Proposition 36.4.2 (1): if a bifunction is convex through its graph-function owner, then its
inverse bifunction is concave. -/
theorem inverse_isConcave_of_isConvex
    {F : U → X → WithTopBot α} (hF : convᵇ[𝕜](F)) :
    concᵇ[𝕜](F _*) := sorry

-- Proof sketch: apply the same swap-and-negation transformation in the opposite direction:
-- concavity of the graph function becomes convexity after negation, and the coordinate swap keeps
-- the affine structure of the product domain.
/-- Second clause: if a bifunction is concave, then its inverse bifunction is convex through the
canonical graph-function owner. -/
theorem inverse_isConvex_of_isConcave
    {F : U → X → WithTopBot α} (hF : concᵇ[𝕜](F)) :
    convᵇ[𝕜](F _*) := sorry

/-- Involution bridge for Proposition 36.4.2 (1)-(2): inverse concavity and original graph
convexity are equivalent. -/
theorem inverse_isConcave_iff_isConvex
    {F : U → X → WithTopBot α} :
    concᵇ[𝕜](F _*) ↔ convᵇ[𝕜](F) := by
  constructor
  · intro hFstar
    simpa [inverse_inverse] using
      (inverse_isConvex_of_isConcave (F := F _*) hFstar)
  · intro hF
    exact inverse_isConcave_of_isConvex (F := F) hF

/-- Involution bridge for Proposition 36.4.2 (1)-(2): inverse graph convexity and original
concavity are equivalent. -/
theorem inverse_isConvex_iff_isConcave
    {F : U → X → WithTopBot α} :
    convᵇ[𝕜](F _*) ↔ concᵇ[𝕜](F) := by
  constructor
  · intro hFstar
    simpa [inverse_inverse] using
      (inverse_isConcave_of_isConvex (F := F _*) hFstar)
  · intro hF
    exact inverse_isConvex_of_isConcave (F := F) hF

end Convexity

section ClosedProper

variable {𝕜 : Type z} {U : Type u} {X : Type v} {α : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [TopologicalSpace U] [AddCommMonoid U] [SMul 𝕜 U]
variable [TopologicalSpace X] [AddCommMonoid X] [SMul 𝕜 X]
variable [TopologicalSpace (WithTopBot α)] [AddCommGroup α] [SMul 𝕜 α] [Preorder α]

-- Proof sketch: the inverse bifunction is the negated swapped graph function, so the closed proper
-- convex owner on `F` is transported to the closed proper concave owner on
-- the inverse by the same sign-swap transformation as in the convexity clauses.
/-- Third clause: if `F` has closed-proper-convex graph function, then its inverse bifunction has
closed-proper-concave graph function. -/
theorem inverse_isClosedProperConcave_of_isClosedProperConvex
    {F : U → X → WithTopBot α}
    (hF : cpconvᵇ[𝕜](F)) :
    cpconcᵇ[𝕜](F _*) := sorry

-- Proof sketch: rewrite closed proper concavity of `F` as closed proper convexity of `-uncurry F`,
-- then apply the same sign-swap transport to the inverse bifunction.
/-- Fourth clause: if `F` has closed-proper-concave graph function, then its inverse bifunction has
closed-proper-convex graph function. -/
theorem inverse_isClosedProperConvex_of_isClosedProperConcave
    {F : U → X → WithTopBot α}
    (hF : cpconcᵇ[𝕜](F)) :
    cpconvᵇ[𝕜](F _*) := sorry

/-- Involution bridge for Proposition 36.4.2 (3)-(4): inverse closed-proper concavity and
original closed-proper convexity are equivalent. -/
theorem inverse_isClosedProperConcave_iff_isClosedProperConvex
    {F : U → X → WithTopBot α} :
    cpconcᵇ[𝕜](F _*) ↔ cpconvᵇ[𝕜](F) := by
  constructor
  · intro hFstar
    simpa [inverse_inverse] using
      (inverse_isClosedProperConvex_of_isClosedProperConcave (F := F _*) hFstar)
  · intro hF
    exact inverse_isClosedProperConcave_of_isClosedProperConvex (F := F) hF

/-- Involution bridge for Proposition 36.4.2 (3)-(4): inverse closed-proper convexity and
original closed-proper concavity are equivalent. -/
theorem inverse_isClosedProperConvex_iff_isClosedProperConcave
    {F : U → X → WithTopBot α} :
    cpconvᵇ[𝕜](F _*) ↔ cpconcᵇ[𝕜](F) := by
  constructor
  · intro hFstar
    simpa [inverse_inverse] using
      (inverse_isClosedProperConcave_of_isClosedProperConvex (F := F _*) hFstar)
  · intro hF
    exact inverse_isClosedProperConvex_of_isClosedProperConcave (F := F) hF

end ClosedProper

section Involution

variable {U : Type u} {X : Type v} {α : Type w}
variable [InvolutiveNeg (WithTopBot α)]

/- Fifth clause: the inverse-bifunction operation `F ↦ -Function.swap F` is already the canonical
involution theorem `inverse_inverse`. -/
recall inverse_inverse

end Involution

end Bifunction
