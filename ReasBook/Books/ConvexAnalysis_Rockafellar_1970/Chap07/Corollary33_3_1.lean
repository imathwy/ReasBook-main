import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_42
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_6

noncomputable section

universe u v w w'

open scoped Rockafellar

namespace SaddleFunction

section

open Bifunction

variable {𝕜 : Type*} {U : Type u} {X : Type v} {XStar : Type w}
variable (UStar : Type w')
variable [Field 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U] [FiniteDimensional 𝕜 U]
variable [IsTopologicalAddGroup U] [ContinuousConstSMul 𝕜 U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X] [FiniteDimensional 𝕜 X]
variable [IsTopologicalAddGroup X] [ContinuousConstSMul 𝕜 X]
variable [TopologicalSpace UStar] [AddCommGroup UStar] [Module 𝕜 UStar]
variable [FiniteDimensional 𝕜 UStar]
variable [IsTopologicalAddGroup UStar] [ContinuousConstSMul 𝕜 UStar]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar]
variable [FiniteDimensional 𝕜 XStar]
variable [IsTopologicalAddGroup XStar] [ContinuousConstSMul 𝕜 XStar]
variable [HasLinearPairing U UStar 𝕜] [HasContinuousPairing U UStar 𝕜]
variable [HasLinearPairing X XStar 𝕜] [HasContinuousPairing X XStar 𝕜]
variable [HasLinearPairing XStar X 𝕜] [HasContinuousPairing XStar X 𝕜]
variable [Module 𝕜 (WithBotTop 𝕜)] [PosSMulMono 𝕜 (WithBotTop 𝕜)]

/-!
Source/core/bridge triage:

- `source-facing`: a helper reconstruction criterion characterizes when a concave-convex
  saddle-function
  `K : U → XStar → WithBotTop 𝕜` and a second representative
  `Kbar : U → XStar → WithBotTop 𝕜` arise as the lower and upper representatives of a unique
  closed convex bifunction `F : U → X → WithBotTop 𝕜`; the closure relations then force `Kbar`
  to be concave-convex as well.
- `core/canonical`: the chapter owners for that statement are `Bifunction.IsClosedConvex`,
  `Bifunction.lowerPairing`, `Bifunction.upperAdjointPairing`, the partial closures `cl₁`, `cl₂`,
  and the fixed-point owners `SaddleFunction.IsLowerClosed` and
  `SaddleFunction.IsUpperClosed`.
- `bridge/view`: the adjoint-side representative is expressed directly by the chapter owner
  `upperAdjointPairing XStar UStar`, and the textbook relations `cl₁ K = Kbar` and
  `cl₂ Kbar = K` stay on the source closure-operator surface rather than being hidden in a local
  wrapper.

Domain-style sampling used here:
- `Bifunction.lowerPairing_bijOn_admissibleClasses` from `Corollary33_1_2`;
- `Bifunction.lowerPairing_lowerPairing_eq_closure2_of_isConcaveConvex` from `Theorem33_1`;
- `Bifunction.upperAdjointPairing` from `Defn_34_2`;
- `Bifunction.closure1_lowerPairing_eq_upperAdjointPairing_of_uncurry_isConvex_or_isConcave`
  from `Corollary33_2_1`;
- `Function.IsClosedConcave` from `Definition33_0_27`;
- `Bifunction.upperConcavePairing` from `Defn_34_6`;
- `SaddleFunction.IsLowerClosed` and `SaddleFunction.IsUpperClosed`.

Layer target: `source-facing`, stated directly on the chapter's representative and closure-owner
APIs at the finite-dimensional continuous-pairing owner layer already used upstream for the
explicit paired-space Chapter 33 partial-conjugation correspondences.
-/

local notation:50 F " represents_closed_convex_pair[" K ", " Kbar "]" =>
  IsClosedConvex F ∧
    K = lowerPairing XStar F ∧
    Kbar = upperAdjointPairing XStar UStar F

-- Proof sketch: for the forward implication, the lower representative and upper adjoint-side
-- representative formulas for a closed convex bifunction identify the two partial closures via
-- the Chapter 34 reconstruction machinery. For the reverse implication, the closure relations
-- reconstruct the closed representatives of `K`, and the Chapter 34 unique-generator theorem
-- yields the unique `F` whose lower and upper adjoint-side representatives are `K` and `Kbar`.
/-- Corollary33.3.1: a concave-convex saddle-function `K : U → XStar → WithBotTop 𝕜` and a
second representative `Kbar : U → XStar → WithBotTop 𝕜` arise as the lower and upper
adjoint-side representatives of a unique closed convex bifunction `F : U → X → WithBotTop 𝕜`
exactly when they satisfy the closure relations `cl₁ K = Kbar` and `cl₂ Kbar = K`. -/
theorem existsUnique_closedConvex_bifunction_iff_closure_relations
    {K Kbar : U → XStar → WithBotTop 𝕜}
    (hK : IsConcaveConvex 𝕜 K) :
    (∃! F : U → X → WithBotTop 𝕜,
      F represents_closed_convex_pair[K, Kbar]) ↔
      cl₁ K = Kbar ∧ cl₂ Kbar = K := sorry

-- Proof sketch: `cl₁` preserves the concave-convex saddle shape, so `hK.closure1` identifies the
-- closure representative `cl₁ K` as concave-convex; then rewrite along `hcl₁`.
/-- The first closure relation forces the upper representative `Kbar` to be concave-convex. -/
theorem isConcaveConvex_of_closure1_eq
    {K Kbar : U → XStar → WithBotTop 𝕜}
    (hK : IsConcaveConvex 𝕜 K)
    (hcl₁ : cl₁ K = Kbar) :
    IsConcaveConvex 𝕜 Kbar := sorry

end

section

open Bifunction

variable {𝕜 : Type*} {U : Type u} {XStar : Type w}
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [AddCommGroup 𝕜]
variable [TopologicalSpace U] [TopologicalSpace XStar]

-- Proof sketch: `IsLowerClosed K` is the owner equation `K̲ = K`, and
-- `K̲ = cl₂ (cl₁ K) = cl₂ Kbar = K` by `hcl₁` and `hcl₂`.
/-- The closure relations force the lower representative `K` to be lower closed. -/
theorem isLowerClosed_of_closure_relations
    {K Kbar : U → XStar → WithBotTop 𝕜}
    (hcl₁ : cl₁ K = Kbar)
    (hcl₂ : cl₂ Kbar = K) :
    IsLowerClosed K := sorry

-- Proof sketch: `IsUpperClosed Kbar` is the owner equation `Kbar̅ = Kbar`, and
-- `Kbar̅ = cl₁ (cl₂ Kbar) = cl₁ K = Kbar` by `hcl₂` and `hcl₁`.
/-- The same closure relations force the upper representative `Kbar` to be upper closed. -/
theorem isUpperClosed_of_closure_relations
    {K Kbar : U → XStar → WithBotTop 𝕜}
    (hcl₁ : cl₁ K = Kbar)
    (hcl₂ : cl₂ Kbar = K) :
    IsUpperClosed Kbar := sorry

end

section

open Bifunction

variable {𝕜 : Type*} {U : Type u} {XStar : Type w}
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [AddCommGroup 𝕜]
variable [TopologicalSpace XStar]

-- Proof sketch: `K = cl₂ Kbar` by `hcl₂`, and the second-variable closure is pointwise bounded
-- above by the original slice, so `K ≤ Kbar`.
/-- The closure relations place the lower representative below the upper representative. -/
theorem le_of_closure_relations
    {K Kbar : U → XStar → WithBotTop 𝕜}
    (hcl₂ : cl₂ Kbar = K) :
    K ≤ Kbar := sorry

end

end SaddleFunction

namespace Bifunction

section LowerPairingTheorem33_3

open SaddleFunction

variable {𝕜 : Type*} {U : Type u} {X : Type v} {XStar : Type w}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [OrderTopology 𝕜] [NoBotOrder 𝕜] [NoMinOrder 𝕜] [Nonempty 𝕜]
variable [IsOrderedAddMonoid 𝕜]
variable [TopologicalSpace U] [AddCommMonoid U] [Module 𝕜 U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X] [FiniteDimensional 𝕜 X]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar]
variable [FiniteDimensional 𝕜 XStar]
variable [Module 𝕜 (WithBotTop 𝕜)] [PosSMulMono 𝕜 (WithBotTop 𝕜)]
variable [HasLinearPairing X XStar 𝕜] [HasContinuousPairing X XStar 𝕜]
variable [HasLinearPairing XStar X 𝕜] [HasContinuousPairing XStar X 𝕜]

-- Proof sketch: combine Corollary 33.1.2's finite-dimensional continuous-pairing
-- partial-conjugation bijection with Theorem 33.2's criterion identifying lower closedness of the
-- kernel `K(u, xStar) = (F u)⋆ xStar` with closedness of the convex generator `F`.
/-- Theorem33.3 (1): partial Fenchel conjugation in the second variable,
`F ↦ fun u xStar ↦ (F u)⋆ xStar`, gives a one-to-one correspondence between closed convex
bifunctions and lower closed concave-convex saddle-functions; equivalently,
`K(u, x^*) = (F u)⋆ x^*` and `F u = (K u)⋆` determine each other on these two classes. -/
theorem lowerPairing_bijOn_closedConvex_lowerClosed :
    Set.BijOn
      (lowerPairing XStar)
      {F : U → X → WithBotTop 𝕜 | IsClosedConvex F}
      {K : U → XStar → WithBotTop 𝕜 | IsConcaveConvex 𝕜 K ∧ IsLowerClosed K} := sorry

end LowerPairingTheorem33_3

section UpperConcavePairingTheorem33_3

open SaddleFunction

variable {𝕜 : Type*} {U : Type u} {UStar : Type w'} {X : Type v} {XStar : Type w}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [OrderTopology 𝕜] [NoBotOrder 𝕜] [NoMinOrder 𝕜] [Nonempty 𝕜]
variable [IsOrderedAddMonoid 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U] [FiniteDimensional 𝕜 U]
variable [TopologicalSpace UStar] [AddCommGroup UStar] [Module 𝕜 UStar]
variable [FiniteDimensional 𝕜 UStar]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X] [FiniteDimensional 𝕜 X]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar]
variable [FiniteDimensional 𝕜 XStar]
variable [Module 𝕜 (WithBotTop 𝕜)] [PosSMulMono 𝕜 (WithBotTop 𝕜)]
variable [HasLinearPairing U UStar 𝕜] [HasContinuousPairing U UStar 𝕜]
variable [HasLinearPairing UStar U 𝕜] [HasContinuousPairing UStar U 𝕜]
variable [HasLinearPairing X XStar 𝕜] [HasContinuousPairing X XStar 𝕜]
variable [HasLinearPairing XStar X 𝕜] [HasContinuousPairing XStar X 𝕜]

-- Proof sketch: apply the same finite-dimensional continuous-pairing correspondence on the
-- concave side. The domain owner is the bifunction-level closed-concavity predicate on
-- `XStar × UStar`, and the bridge map is the canonical Chapter 34 owner
-- `upperConcavePairing`; Theorem 33.2 identifies its image exactly as the upper closed
-- concave-convex kernels.
/-- Theorem33.3 (2): partial concave conjugation on the adjoint side,
`G ↦ upperConcavePairing G`, equivalently `G ↦ fun u xStar ↦ concaveConjugate (G xStar) u`,
gives a one-to-one correspondence between closed concave bifunctions on `XStar × UStar` and upper
closed concave-convex saddle-functions on `U × XStar`. -/
theorem upperConcavePairing_bijOn_closedConcave_upperClosed :
    Set.BijOn
      (upperConcavePairing :
        (XStar → UStar → WithBotTop 𝕜) → U → XStar → WithBotTop 𝕜)
      {G : XStar → UStar → WithBotTop 𝕜 |
        Function.IsClosedConcave (EStar := X × U) (Function.uncurry G)}
      {K : U → XStar → WithBotTop 𝕜 | IsConcaveConvex 𝕜 K ∧ IsUpperClosed K} := sorry

end UpperConcavePairingTheorem33_3

end Bifunction
