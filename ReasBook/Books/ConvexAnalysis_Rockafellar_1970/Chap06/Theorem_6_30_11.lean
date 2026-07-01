import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_24
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14

noncomputable section

universe u v u' v'

open Function
open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 6.30.11 studies the adjoint bifunction `F⋆` and its biconjugate `F⋆⋆`,
  together with the closure/properness consequences of Fenchel duality for bifunctions.
- `core/canonical`: the relevant upstream owners are the Chapter 6 adjoint owner `adjoint`
  with notation `F⋆`, the Chapter 6 concave-bifunction notation `concᵇ[𝕜](F)`, the
  bifunction closure owner `cl F`, the Chapter 12 owners `f.IsClosedProperConvex` and
  `g.IsClosedProperConcave`, and the Chapter 19 owner `f.HasPolyhedralEpigraph`.
- `bridge/view`: this file should therefore stay on the bifunction surface, but phrase its public
  API through those owners and the graph-function bridge `uncurry F`, rather than through parallel
  local wrapper names.

Domain-style sampling used here:
- `Bifunction.adjoint` and the scoped notation `F⋆` from `Definition_6_30_14`;
- the scoped biconjugate notation `F⋆⋆` from `Definition_6_30_14`, with type ascriptions where
  needed for disambiguation;
- `concᵇ[𝕜](F)` from `Definition_6_30_8`;
- `Bifunction.closure` from `Definition_6_29_24`;
- `Function.IsClosedProperConvex` from `Chap03.Text_12_3_6`;
- `Function.IsClosedProperConcave` from `Definition_6_30_2`;
- `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull`,
  `Function.IsClosedProperConvex.biconjugate_eq`, and
  `Function.HasPolyhedralEpigraph.convexConjugate` from the Chapter 12 and Chapter 19 closure.

Primitive data vs derived API:
- primitive data for the closed-concavity owner theorem:
  a bifunction `F : U → X → WithBotTop 𝕜`;
- primitive source-facing owners reused directly: `F⋆`, `F⋆⋆`, and `cl F`;
- derived API in this file: closed-concavity, properness equivalence, closed-proper-concavity,
  biconjugacy, and the resulting bijection/polyhedrality statements.

Layer target: `bridge/view`, stated directly on the canonical chapter owners.
-/

section ClosedConcave

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [TopologicalSpace U] [TopologicalSpace X]
variable [TopologicalSpace UStar] [TopologicalSpace XStar]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup UStar] [Module 𝕜 UStar]
variable [AddCommGroup XStar] [Module 𝕜 XStar]
variable [HasLinearPairing U UStar 𝕜] [HasLinearPairing X XStar 𝕜]
variable [HasContinuousPairing U UStar 𝕜] [HasContinuousPairing X XStar 𝕜]

-- Proof sketch: identify `Function.uncurry (F⋆)` with the sign-twisted conjugate
-- of `Function.uncurry F`, then apply the Chapter 12 theorem that conjugates of convex functions
-- are closed and convex after negation.
/-- The adjoint of a convex bifunction is closed of the opposite type, rendered on the graph
function as bifunction concavity together with lower semicontinuity of the negated adjoint
graph. -/
theorem adjointFunction_isClosedConcave
    (F : U → X → WithBotTop 𝕜) (hF_convex : (uncurry F).IsConvex 𝕜) :
    concᵇ[𝕜]((F⋆ : XStar → UStar → WithBotTop 𝕜)) ∧
      LowerSemicontinuous (-uncurry (F⋆ : XStar → UStar → WithBotTop 𝕜)) := sorry

end ClosedConcave

section ClosedProperAndBiconjugacy

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology 𝕜]
variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [IsTopologicalAddGroup U] [ContinuousSMul 𝕜 U] [FiniteDimensional 𝕜 U] [T2Space U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [IsTopologicalAddGroup X] [ContinuousSMul 𝕜 X] [FiniteDimensional 𝕜 X] [T2Space X]
variable [TopologicalSpace UStar] [AddCommGroup UStar] [Module 𝕜 UStar]
variable [IsTopologicalAddGroup UStar] [ContinuousSMul 𝕜 UStar]
variable [FiniteDimensional 𝕜 UStar] [T2Space UStar]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar]
variable [IsTopologicalAddGroup XStar] [ContinuousSMul 𝕜 XStar]
variable [FiniteDimensional 𝕜 XStar] [T2Space XStar]
variable [HasLinearPairing U UStar 𝕜] [HasContinuousPairing U UStar 𝕜]
variable [HasLinearPairing X XStar 𝕜] [HasContinuousPairing X XStar 𝕜]

local instance : HasPairing XStar X 𝕜 :=
  HasPairing.swap (X := X) (Y := XStar) (L := 𝕜)

local instance : HasPairing UStar U 𝕜 :=
  HasPairing.swap (X := U) (Y := UStar) (L := 𝕜)

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)
local notation "IsClosedProperConcave[" 𝕜 "]" => Function.IsClosedProperConcave (𝕜 := 𝕜)
local postfix:max "⋆⋆" =>
  fun F : U → X → WithBotTop 𝕜 ↦
    (Bifunction.adjoint (F⋆ : XStar → UStar → WithBotTop 𝕜) : U → X → WithBotTop 𝕜)

-- Proof sketch: the graph function of `adjoint F` is obtained from the Fenchel conjugate
-- of `uncurry F` by the sign-twisted swap map, so Chapter 12 properness preservation for
-- convex conjugates gives the equivalence.
/-- The adjoint bifunction is proper on the opposite, concave side exactly when the original
convex bifunction is proper on the graph-function side. -/
theorem adjointFunction_isProper_iff
    (F : U → X → WithBotTop 𝕜) (hF_convex : (uncurry F).IsConvex 𝕜) :
    (-uncurry (F⋆ : XStar → UStar → WithBotTop 𝕜)).IsProper ↔ (uncurry F).IsProper := sorry

-- Proof sketch: combine `adjointFunction_isClosedConcave` with
-- `adjointFunction_isProper_iff`, then package the three fields of
-- `Function.IsClosedProperConvex` for the negated graph function of `F⋆`.
/-- If the graph function of `F` is closed proper convex, then the graph function of its adjoint
is closed proper concave. -/
theorem adjointFunction_isClosedProperConcave
    (F : U → X → WithBotTop 𝕜)
    (hF : IsClosedProperConvex[𝕜] (uncurry F)) :
    IsClosedProperConcave[𝕜]
      (uncurry (show XStar → UStar → WithBotTop 𝕜 from F⋆)) := sorry

-- Proof sketch: pass from the bifunction `F` to its graph function `uncurry F`, apply
-- the Chapter 12 biconjugacy theorem `f⋆⋆ = cl(f)` for convex functions on the product space, and
-- identify the resulting graph closure with the source-facing bifunction owner `cl F`.
/-- Theorem 6.30.11: for a convex bifunction `F`, the paired-space biconjugate owner
`F⋆⋆` recovers the canonical bifunction closure `cl F`, i.e. the bifunction form of the source
identity `F⋆⋆ = cl F`. -/
theorem biadjointFunction_eq_closure
    (F : U → X → WithBotTop 𝕜) (hF_convex : (uncurry F).IsConvex 𝕜) :
    (F⋆⋆ : U → X → WithBotTop 𝕜) = cl F := sorry

-- Proof sketch: combine `biadjointFunction_eq_closure` with the assumed fixed-point
-- identity for the canonical closure owner.
/-- If a convex bifunction already equals its closure, then the paired-space bifunction biconjugate
`F⋆⋆` reduces back to `F`; this is the source involutivity statement `F⋆⋆ = F`. -/
theorem biadjointFunction_eq_self_of_closure_eq_self
    (F : U → X → WithBotTop 𝕜) (hF_convex : (uncurry F).IsConvex 𝕜)
    (hF_closed : cl F = F) :
    (F⋆⋆ : U → X → WithBotTop 𝕜) = F := sorry

-- Proof sketch: `adjointFunction_isClosedProperConcave` gives the forward maps-to statement, and
-- `biadjointFunction_eq_closure` together with the fixed-point identity for closed
-- proper convex bifunctions gives the inverse-on-class relation, hence a bijection.
/-- Fenchel adjunction gives a one-to-one correspondence between closed proper convex bifunctions
and closed proper concave bifunctions, with the source and target spaces exchanged. -/
theorem adjointFunction_bijOn_closedProperConvex_bifunctions :
    Set.BijOn
      (fun F : U → X → WithBotTop 𝕜 ↦
        (((F : U → X → WithBotTop 𝕜)⋆) : XStar → UStar → WithBotTop 𝕜))
      {F : U → X → WithBotTop 𝕜 |
        IsClosedProperConvex[𝕜] (uncurry F)}
      {G : XStar → UStar → WithBotTop 𝕜 | IsClosedProperConcave[𝕜] (uncurry G)} := sorry

end ClosedProperAndBiconjugacy

section PolyhedralAdjoint

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [IsTopologicalAddGroup U] [ContinuousSMul 𝕜 U] [FiniteDimensional 𝕜 U] [T2Space U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [IsTopologicalAddGroup X] [ContinuousSMul 𝕜 X] [FiniteDimensional 𝕜 X] [T2Space X]
variable [TopologicalSpace UStar] [AddCommGroup UStar] [Module 𝕜 UStar]
variable [IsTopologicalAddGroup UStar] [ContinuousSMul 𝕜 UStar]
variable [FiniteDimensional 𝕜 UStar] [T2Space UStar]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar]
variable [IsTopologicalAddGroup XStar] [ContinuousSMul 𝕜 XStar]
variable [FiniteDimensional 𝕜 XStar] [T2Space XStar]
variable [HasLinearPairing U UStar 𝕜] [HasContinuousPairing U UStar 𝕜]
variable [HasLinearPairing X XStar 𝕜] [HasContinuousPairing X XStar 𝕜]

-- Proof sketch: identify the negated adjoint graph with the Fenchel conjugate of `uncurry F`
-- on the explicit dual product `UStar × XStar`, then apply the Chapter 19 conjugate-polyhedral
-- owner theorem and the linear sign/swap change of variables on the product space.
/-- If the graph function of a convex bifunction has polyhedral epigraph, then the negated graph
function of its adjoint bifunction also has polyhedral epigraph. The owner is stated on explicit
dual spaces `XStar` and `UStar`, using the chapter's source-facing notation `F⋆`. -/
theorem adjointFunction_hasPolyhedralEpigraph
    (F : U → X → WithBotTop 𝕜)
    (hF_poly : (uncurry F).HasPolyhedralEpigraph) :
    (-uncurry (F⋆ : XStar → UStar → WithBotTop 𝕜)).HasPolyhedralEpigraph := sorry

end PolyhedralAdjoint

end Bifunction
