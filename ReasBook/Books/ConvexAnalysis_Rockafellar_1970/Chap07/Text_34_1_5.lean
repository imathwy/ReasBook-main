import ConvexAnalysis_Rockafellar_1970.Chap07.Theorem_34_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Corollary33_3_1

noncomputable section

universe u v w w' z

namespace Bifunction

open scoped Rockafellar
open SaddleFunction

section

variable {𝕜 : Type z} {U : Type u} {X : Type v} {XStar : Type w} {UStar : Type w'}
variable [Field 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U] [FiniteDimensional 𝕜 U]
variable [IsTopologicalAddGroup U] [ContinuousConstSMul 𝕜 U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X] [FiniteDimensional 𝕜 X]
variable [IsTopologicalAddGroup X] [ContinuousConstSMul 𝕜 X]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar]
variable [FiniteDimensional 𝕜 XStar]
variable [IsTopologicalAddGroup XStar] [ContinuousConstSMul 𝕜 XStar]
variable [TopologicalSpace UStar] [AddCommGroup UStar] [Module 𝕜 UStar]
variable [FiniteDimensional 𝕜 UStar]
variable [IsTopologicalAddGroup UStar] [ContinuousConstSMul 𝕜 UStar]
variable [HasLinearPairing U UStar 𝕜] [HasContinuousPairing U UStar 𝕜]
variable [HasLinearPairing X XStar 𝕜] [HasContinuousPairing X XStar 𝕜]
variable [HasLinearPairing XStar X 𝕜] [HasContinuousPairing XStar X 𝕜]
variable [Module 𝕜 (WithBotTop 𝕜)] [PosSMulMono 𝕜 (WithBotTop 𝕜)]

local notation:50 F " represents_closed_convex_pair[" K ", " Kbar "]" =>
  IsClosedConvex F ∧
    K = lowerPairing XStar F ∧
    Kbar = upperAdjointPairing XStar UStar F

/-!
Source/core/bridge triage:

- `source-facing`: Text 34.1.5 says that for a concave-convex saddle-function `K`, there exists a
  unique closed-convex bifunction `F` whose lower and upper representatives are the iterated
  closures `cl₂ (cl₁ K)` and `cl₁ (cl₂ K)`.
- `core/canonical`: those owners are already the Chapter 34 canonical API:
  `Bifunction.lowerClosure`, `Bifunction.upperClosure`,
  `Bifunction.IsClosedConvex`, `Bifunction.lowerPairing`, and
  `Bifunction.upperAdjointPairing`.
- `bridge/view`: the unique-generator statement is a thin bridge through the existing closure
  relation theorem
  `SaddleFunction.existsUnique_closedConvex_bifunction_iff_closure_relations`, applied to the
  canonical representatives `K̲` and `K̅`.

Domain-style sampling used here:
- `Bifunction.lowerClosure_isConcaveConvex` from `Theorem_34_1`;
- `Bifunction.closure1_lowerClosure_eq_upperClosure` from `Text_34_1_4`;
- `Bifunction.closure2_upperClosure_eq_lowerClosure` from `Text_34_1_4`;
- `SaddleFunction.existsUnique_closedConvex_bifunction_iff_closure_relations` from
  `Corollary33_3_1`.

Layer target: `source-facing`, using the canonical Chapter 34 owner names.
-/

/-- Text 34.1.5: for a concave-convex saddle-function `K : U → XStar → WithBotTop 𝕜`, there
exists a unique closed-convex bifunction `F : U → X → WithBotTop 𝕜` whose canonical
representatives are the iterated closures of `K`:
`K̲ = lowerPairing XStar F` and `K̅ = upperAdjointPairing XStar UStar F`. -/
theorem existsUnique_closedConvex_bifunction_generating_closure_representatives
    {K : U → XStar → WithBotTop 𝕜}
    (hK : IsConcaveConvex 𝕜 K) :
    ∃! F : U → X → WithBotTop 𝕜,
      F represents_closed_convex_pair[K̲, K̅] := by
  have hKlower : IsConcaveConvex 𝕜 K̲ :=
    lowerClosure_isConcaveConvex hK
  have hclosure :
      cl₁ K̲ = K̅ ∧ cl₂ K̅ = K̲ :=
    ⟨closure1_lowerClosure_eq_upperClosure hK, closure2_upperClosure_eq_lowerClosure hK⟩
  exact (existsUnique_closedConvex_bifunction_iff_closure_relations UStar hKlower).2 hclosure

end

end Bifunction
