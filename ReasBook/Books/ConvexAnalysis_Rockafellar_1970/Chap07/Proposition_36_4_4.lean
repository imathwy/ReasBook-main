import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_30_11
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_36_4_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Proposition_36_4_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Proposition_36_4_3

noncomputable section

universe u v

open scoped Rockafellar
open Function

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 36.4.4 says that for a convex bifunction `F`, the source operator
  `F_*^*` is again convex, and that applying the same source operator once more yields the usual
  bifunction biconjugate `F^{**}` on the paired-space Chapter 36 owner surface. In the stronger
  self-dual finite-dimensional setting over an ordered scalar field, Chapter 6 then identifies
  this ordinary biconjugate with `cl F`.
- `core/canonical`: the relevant owner layer is already present in the project:
  `Function.IsConvex 𝕜 (uncurry F)`, the Chapter 6 adjoint owner `F⋆`,
  the Chapter 7 inverse owner `F _*`, and the self-dual biconjugate surface
  `(F⋆⋆ : U → X → L)` for the specialization `F^{**}`. On the general paired-space
  layer, the ordinary biconjugate owner is `concaveAdjoint U X (F⋆)`.
- `bridge/view`: the textbook object `F_*^*` is the existing source-facing owner `((F⋆) _*)`,
  while its iterate is `((((F⋆) _*)⋆) _*)`. Proposition 36.4.3 already identifies that iterate
  with the canonical paired-space biconjugate owner `concaveAdjoint U X (F⋆)`, so this
  file stays on those owners rather than rebuilding the same construction through a local wrapper.

Domain-style sampling used here:
- `Function.IsConvex` on the graph-function owner from `Definition33_0_28`;
- the Chapter 12 convex-conjugate convexity owner theorem;
- the Chapter 6 owner `Bifunction.concaveAdjoint`;
- the Chapter 7 commutation theorem
  `Bifunction.adjoint_inverse_eq_inverse_concaveAdjoint`;
- the stable self-dual closure theorem `Bifunction.biadjointFunction_eq_closure`.

Primitive data vs derived API:
- primitive input: a convex bifunction `F : U → X → WithBotTop 𝕜`;
- primitive source-facing owner expression for `F_*^*`: `((F⋆) _*)`;
- derived API: convexity of that source object on the linear-pairing layer, its identification
  with the ordinary paired-space bifunction biconjugate after one more application of
  `G ↦ G_*^*`, the stronger self-dual `(F⋆⋆ : U → X → L)` specialization, and the recalled
  closure formula for that self-dual biconjugate.

Layer target: `bridge/view`, stated directly on the canonical chapter owners.
-/

section

variable {𝕜 : Type*} {α : Type*} {U : Type u} {X : Type v} {UStar : Type*} {XStar : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid UStar] [SMul 𝕜 UStar]
variable [AddCommMonoid XStar] [SMul 𝕜 XStar]
variable [ConditionallyCompleteLinearOrder α] [AddCommGroup α] [SMul 𝕜 α] [LE α]
variable [Neg UStar]
variable [HasPairing U UStar α] [HasPairing X XStar α]

variable (F : U → X → WithBotTop α)

local notation "F⋆" => (adjoint XStar UStar F : XStar → UStar → WithBotTop α)

/-- Primitive owner bridge for Proposition 36.4.4 (1): concavity of the adjoint owner `F⋆`
implies convexity of the source owner `F_*^*`. -/
theorem isConvex_inverse_adjoint_of_isConcave_adjoint
    (hFstar : concᵇ[𝕜](F⋆)) :
    convᵇ[𝕜]((F _*^*) : UStar → XStar → WithBotTop α) := by
  simpa using
    (inverse_isConvex_of_isConcave (𝕜 := 𝕜) (F := F⋆) hFstar)

end

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {UStar : Type*} {XStar : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup UStar] [Module 𝕜 UStar]
variable [AddCommGroup XStar] [Module 𝕜 XStar]
variable [HasLinearPairing U UStar 𝕜] [HasLinearPairing X XStar 𝕜]

variable (F : U → X → WithBotTop 𝕜)

local notation "F⋆" => (adjoint XStar UStar F : XStar → UStar → WithBotTop 𝕜)

-- Proof sketch: `- uncurry (F⋆)` is a Fenchel conjugate of `uncurry F` after the linear
-- coordinate change `(x⋆, u⋆) ↦ (-u⋆, x⋆)`, so Chapter 12 convexity of conjugates gives
-- concavity of `F⋆`. Proposition 36.4.2 then turns that concavity into convexity of its inverse
-- bifunction, which is exactly the source object `F_*^* = ((F⋆) _*)`.
/-- Proposition 36.4.4 (1): if `F` is a convex bifunction, then the source bifunction `F_*^*`,
rendered here as `((F⋆) _*)`, is again convex. -/
theorem isConvex_inverse_adjointFunction_of_isConvex
    (hF : convᵇ[𝕜](F)) :
    convᵇ[𝕜]((F _*^*) : UStar → XStar → WithBotTop 𝕜) := sorry

end

section

variable {α : Type*} {U : Type u} {X : Type v} {UStar : Type*} {XStar : Type*}
variable [ConditionallyCompleteLinearOrder α] [AddCommGroup α]
variable [Neg U] [Neg UStar]
variable [HasPairing U UStar α] [HasPairing X XStar α]
variable [HasPairing XStar X α] [HasPairing UStar U α]
variable [HasPairingNegRight UStar U α]

variable (F : U → X → WithBotTop α)

local notation "F⋆" => (adjoint XStar UStar F : XStar → UStar → WithBotTop α)

-- Proof sketch: Proposition 36.4.3 already says that adjoint-after-inverse equals
-- inverse-after-concave-adjoint. Applying that owner theorem to `F⋆` and then using the inverse
-- involution collapses the second iterate of `G ↦ G_*^*` to the ordinary paired-space
-- biconjugate owner `concaveAdjoint U X (F⋆)`.
/-- Proposition 36.4.4 (2), paired-space owner form: applying `G ↦ G_*^*` to
`G = F_*^* = ((F⋆) _*)` yields the ordinary bifunction biconjugate `F^{**}`, rendered on the
general paired-space owner layer as `concaveAdjoint U X (F⋆)`. -/
theorem iteratedInverseAdjoint_eq_concaveAdjoint_adjoint
    : ((((F⋆) _*)⋆) _*) = concaveAdjoint U X F⋆ := sorry

end

section

variable {U : Type u} {X : Type v} {L : Type*}
variable [Sub L] [Neg L] [SupSet L]
variable [Neg U] [Neg X]
variable [HasPairing (U × X) (U × X) L]
variable [HasPairing (X × U) (X × U) L]

variable (F : U → X → L)

-- Proof sketch: on the self-dual owner layer, the source iterate `G ↦ G_*^*` evaluated twice is
-- exactly the same owner-level object as `(F⋆⋆ : U → X → L)`, so this identity is independent of
-- convexity hypotheses and of any specific ordered-codomain specialization.
/-- Self-dual owner identity: for bifunctions on the primitive adjoint/inverse codomain layer,
the iterated source operator is the stable Chapter 6 bifunction biconjugate owner `F⋆⋆`. -/
theorem biadjointFunction_eq_iteratedInverseAdjointFunction
    : adjoint U X (adjoint X U F) = ((adjoint X U ((adjoint X U F) _*)) _*) := sorry

end

section

variable {𝕜 : Type*} {U : Type u} {X : Type v}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [IsTopologicalAddGroup U] [ContinuousSMul 𝕜 U] [FiniteDimensional 𝕜 U] [T2Space U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [IsTopologicalAddGroup X] [ContinuousSMul 𝕜 X] [FiniteDimensional 𝕜 X] [T2Space X]
variable [HasLinearPairing U U 𝕜] [HasContinuousPairing U U 𝕜]
variable [HasLinearPairing X X 𝕜] [HasContinuousPairing X X 𝕜]

/- Proposition 36.4.4 (3): for a convex bifunction, the bifunction biconjugate `F^{**}` equals
the source-facing bifunction closure `closure F` on the self-dual finite-dimensional owner layer. -/
recall biadjointFunction_eq_closure

end

end Bifunction
