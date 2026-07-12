import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_38
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2

noncomputable section

universe u v u' v' w z

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem33.0.39 characterizes fully closed concave-convex saddle-functions by
  closed-convex generators whose lower representative is `K` and whose lower and upper
  adjoint-side representatives coincide pointwise through the global Chapter 33 pairing equation.
- `core/canonical`: the relevant owner layer is the Chapter 34 closed-convex surface
  `Bifunction.IsClosedConvex` together with `Bifunction.lowerPairing`,
  `Bifunction.upperAdjointPairing`, `Bifunction.omegaAdjoint`,
  `SaddleFunction.IsConcaveConvex`, and `Bifunction.IsFullyClosed`.
- `bridge/view`: the source-facing pairing equation is rendered directly by the canonical
  representative equality `lowerPairing XStar F = upperAdjointPairing XStar UStar F`, rather than
  by a separate wrapper predicate.

Domain-style sampling used here:
- `SaddleFunction.IsConcaveConvex`;
- `Bifunction.IsFullyClosed`;
- `Bifunction.IsClosedConvex`;
- `Bifunction.lowerPairing`;
- `Bifunction.upperAdjointPairing`;
- `Bifunction.omegaAdjoint`;

Primitive vs derived API:
- primitive source data: a saddle-function `K : U → XStar → WithBotTop 𝕜`;
- primitive generator data: a closed convex bifunction `F : U → X → WithBotTop 𝕜`;
- primitive owner conditions: `IsClosedConvex F`, `K = lowerPairing XStar F`, and
  `lowerPairing XStar F = upperAdjointPairing XStar UStar F`;
- derived source-facing reformulation: the pointwise Chapter 33 pairing equation recovered from
  that representative equality, equivalently the singleton degeneration of
  `omegaAdjoint XStar UStar F`.
-/

namespace SaddleFunction

section Representation

open Bifunction

variable {𝕜 : Type z} {U : Type u} {UStar : Type u'} {X : Type v} {XStar : Type v'}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology 𝕜]
variable [Module 𝕜 (WithBotTop 𝕜)] [PosSMulMono 𝕜 (WithBotTop 𝕜)]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [IsTopologicalAddGroup U] [ContinuousSMul 𝕜 U] [FiniteDimensional 𝕜 U] [T2Space U]
variable [TopologicalSpace UStar] [AddCommGroup UStar] [Module 𝕜 UStar]
variable [IsTopologicalAddGroup UStar] [ContinuousSMul 𝕜 UStar]
variable [FiniteDimensional 𝕜 UStar] [T2Space UStar]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [IsTopologicalAddGroup X] [ContinuousSMul 𝕜 X] [FiniteDimensional 𝕜 X] [T2Space X]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar]
variable [IsTopologicalAddGroup XStar] [ContinuousSMul 𝕜 XStar]
variable [FiniteDimensional 𝕜 XStar] [T2Space XStar]
variable [HasLinearPairing U UStar 𝕜] [HasContinuousPairing U UStar 𝕜]
variable [HasLinearPairing X XStar 𝕜] [HasContinuousPairing X XStar 𝕜]
variable [HasLinearPairing XStar X 𝕜] [HasContinuousPairing XStar X 𝕜]

-- Proof sketch: apply the Chapter 33/34 lower-pairing reconstruction for fully closed
-- concave-convex kernels to obtain a closed convex generator whose lower representative is `K`.
/-- Theorem33.0.39 (1): a fully closed concave-convex saddle-function on `U × XStar` is the
lower pairing representative of some closed convex bifunction on `U × X`. -/
theorem exists_closedConvex_bifunction_eq_lowerPairing_of_isConcaveConvex_of_isFullyClosed
    {K : U → XStar → WithBotTop 𝕜} :
    IsConcaveConvex 𝕜 K →
      IsFullyClosed K →
        ∃ F : U → X → WithBotTop 𝕜, IsClosedConvex F ∧ K = lowerPairing XStar F := sorry

-- Proof sketch: once `K` is known to be fully closed and realized as the lower representative of
-- a closed convex generator `F`, upper closedness identifies `cl₁ K` with the adjoint-side
-- representative, yielding the global pairing equation for `F`.
/-- Theorem33.0.39 (2): if a fully closed saddle-function is the lower pairing representative of a
closed convex bifunction, then that generator satisfies the global Chapter 33 pairing equation. -/
theorem lowerPairing_eq_upperAdjointPairing_of_isFullyClosed_of_eq_lowerPairing
    {K : U → XStar → WithBotTop 𝕜} {F : U → X → WithBotTop 𝕜} :
    IsFullyClosed K →
      IsClosedConvex F →
        K = lowerPairing XStar F →
          lowerPairing XStar F = upperAdjointPairing XStar UStar F := sorry

-- Proof sketch: closed convexity gives the canonical lower representative `lowerPairing XStar F`
-- the concave-convex owner, and the pairing equation identifies the adjoint-side representative
-- with the same kernel, forcing full closedness as well.
/-- Theorem33.0.39 (3): if `K` is the lower pairing representative of a closed convex bifunction
whose lower and adjoint-upper representatives coincide, then `K` is concave-convex and fully
closed. -/
theorem isConcaveConvex_isFullyClosed_of_eq_lowerPairing_of_pairingEquation
    {K : U → XStar → WithBotTop 𝕜} {F : U → X → WithBotTop 𝕜} :
    IsClosedConvex F →
      K = lowerPairing XStar F →
        lowerPairing XStar F = upperAdjointPairing XStar UStar F →
          IsConcaveConvex 𝕜 K ∧ IsFullyClosed K := sorry

end Representation

end SaddleFunction
