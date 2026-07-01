import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_0_3
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_8
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_28

noncomputable section

universe u v u' v' w

open scoped Rockafellar

namespace Bifunction

section

variable {𝕜 : Type w} {U : Type u} {X : Type v} {XStar : Type v'}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [IsTopologicalAddGroup U] [ContinuousSMul 𝕜 U] [FiniteDimensional 𝕜 U] [T2Space U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [IsTopologicalAddGroup X] [ContinuousSMul 𝕜 X] [FiniteDimensional 𝕜 X] [T2Space X]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar]
variable [IsTopologicalAddGroup XStar] [ContinuousSMul 𝕜 XStar]
variable [FiniteDimensional 𝕜 XStar] [T2Space XStar]
variable [HasLinearPairing X XStar 𝕜] [HasContinuousPairing X XStar 𝕜]

/-!
Source/core/bridge triage:

- Primary mathematical domain: the Chapter 33 pairing-equation surface for convex bifunctions,
  with the Corollary 33.2.2 polyhedral upgrade supplied by the finite-dimensional ordered-field
  Chapter 19/33 epigraph/conjugacy owners actually available in the project.
- `source-facing`: this file records the convex-side owner form of Corollary33.2.2, namely that a
  proper bifunction with polyhedral epigraph satisfies the displayed Chapter 33 pairing equation
  away from the exceptional case `u ∉ dom F` and
  `x⋆ ∉ dom (-adjoint XStar UStar F)`.
- `core/canonical`: the chapter owner surface for this statement is
  `Function.IsProper (Function.uncurry F)`, the finite-half-space description of the epigraph
  `epi (Function.uncurry F)`, `dom F`, `dom (-adjoint XStar UStar F)`, and the displayed equality
  `⟪F u, x⋆⟫ᶠ = ⟪u, F⋆ x⋆⟫ᶜ`.
- `bridge/view`: the polyhedral hypothesis is kept as the direct finite intersection of closed
  half-spaces, avoiding an unstable duplicate wrapper import.

Domain-style sampling used here:
- `Function.IsProper` from `Chap01.Definition_4_6`;
- `epi` from `Chap01.Definition_4_1`;
- `closedHalfSpaceLE` from `Chap01.Definition_2_0_3`;
- `Bifunction.dom` from `Chap06.Definition_6_29_8`;
- `Bifunction.adjoint` and the chapter pairing notations from `Definition33_0_28`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → WithBotTop 𝕜`;
- primitive owner hypotheses: graph properness and the explicit finite-half-space description of
  the graph epigraph `epi (Function.uncurry F)`;
- derived API here: the nonexceptional displayed pairing equation itself.

Ambient refinement:
- unlike Corollary33.2.1 from `Corollary33_2_1`, the polyhedral upgrade here still needs the
  finite-dimensional ordered-field polyhedral layer, but it now stays on the explicit pairing
  spaces `U`, `UStar`, `X`, `XStar` rather than collapsing to a self-dual realization.

Layer target: `source-facing`, stated directly on the canonical Chapter 33 owner surface at that
finite-dimensional paired topological-module layer.
-/

-- Proof sketch: sharpen Corollary 33.2.1 using the polyhedral improvement that the relevant
-- Chapter 33 slices agree with their closures on their whole effective domains. If either
-- `u ∈ dom F` or `x⋆ ∈ dom (-F⋆)`, the point is outside the
-- exceptional case, so the displayed Chapter 33 pairing equality holds.
section PairingEquation

variable (UStar : Type u')
variable [TopologicalSpace UStar] [AddCommGroup UStar] [Module 𝕜 UStar]
variable [IsTopologicalAddGroup UStar] [ContinuousSMul 𝕜 UStar]
variable [FiniteDimensional 𝕜 UStar] [T2Space UStar]
variable [HasLinearPairing U UStar 𝕜] [HasContinuousPairing U UStar 𝕜]
variable (F : U → X → WithBotTop 𝕜)

local notation "F⋆" => adjoint XStar UStar F
local instance : HasPairing UStar U (WithBotTop 𝕜) := HasPairing.swap

-- Proof sketch: combine the source properness hypothesis with the explicit polyhedral epigraph
-- hypothesis to place `F` in the polyhedral Chapter 33 regime, then use the nonexceptional-domain
-- alternative `u ∈ dom F ∨ x⋆ ∈ dom (-F⋆)` to force equality of the two chapter pairings.
/-- Corollary33.2.2: if `F` is proper and its epigraph is a finite intersection of closed
half-spaces, then the Chapter 33 pairing equation holds at every point with `u ∈ dom F` or
`xStar ∈ dom (-F⋆)`, written directly as the displayed equality
`⟪F u, x⋆⟫ᶠ = ⟪u, F⋆ x⋆⟫ᶜ`. -/
theorem pairingEquationAt_of_mem_dom_or_mem_dom_neg_adjoint_of_proper_polyhedral
    (hF_proper : Function.IsProper (Function.uncurry F))
    (hF_poly : ∃ S : Finset ((((U × X) × 𝕜) →ₗ[𝕜] 𝕜) × 𝕜),
      epi (Function.uncurry F) = ⋂ y ∈ S, closedHalfSpaceLE y.1 y.2)
    (u : U) (xStar : XStar)
    (hdom : u ∈ dom F ∨ xStar ∈ dom (-F⋆)) :
    ⟪F u, xStar⟫ᶠ = ⟪u, F⋆ xStar⟫ᶜ := sorry

end PairingEquation

end

end Bifunction
