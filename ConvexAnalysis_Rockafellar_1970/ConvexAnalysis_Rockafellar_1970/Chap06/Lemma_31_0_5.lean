import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_31_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [LinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} {EStar : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable [AddCommGroup EStar] [Module 𝕜 EStar] [TopologicalSpace EStar]
variable [HasPairing E EStar 𝕜]
variable {f g : E → WithBotTop 𝕜}

local instance : HasPairing E EStar (WithBotTop 𝕜) := instHasPairingWithBotTop

local notation "IsClosedProperConvex[" 𝕜 "]" => @Function.IsClosedProperConvex 𝕜
local notation "IsClosedProperConcave[" 𝕜 "]" => @Function.IsClosedProperConcave 𝕜
local notation "primalObjective" => fun x : E ↦ f x - g x
local notation "convexDual" => (f⋆ : EStar → WithBotTop 𝕜)
local notation "concaveDual" => (g∗ : EStar → WithBotTop 𝕜)
local notation "dualRiQualification" =>
  Set.Nonempty (riDom[𝕜](-concaveDual) ∩ riDom[𝕜](convexDual))
local notation "primalValue" => (⨅ x : E, primalObjective x)
local notation "dualObjective" => fun xStar : EStar ↦ concaveDual xStar - convexDual xStar
local notation "dualValue" => (⨆ xStar : EStar, dualObjective xStar)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 31.0.5 is the closed-case Fenchel duality statement for the identity
  pairing configuration, with the dual qualification written as a common relative-interior point of
  the dual effective domains.
- `core/canonical`: the chapter owner theorems are already
  `iInf_sub_eq_iSup_concaveConjugate_sub_convexConjugate_of_fenchel_qualification` and
  `exists_isMinOn_sub_of_dual_riDom_inter_nonempty` from `Theorem_31_1`, built on the core owners
  `Function.IsClosedProperConvex`, the Fenchel conjugate `(·)⋆`, the Chapter 6 concave-conjugate
  notation `(·)∗`, `riDom[𝕜](·)`, and `IsMinOn`.
- `bridge/view`: this file should therefore keep only the source-facing closed-owner specialization
  of those existing Chapter 31 results, with the source phrase "closed proper concave" rendered by
  the chapter owner `g.IsClosedProperConcave`.

Layer target: pairing-based source-facing API over `WithBotTop 𝕜`, stated directly on the chapter
owners rather than on a new duality-package wrapper or a parallel local proof payload.
-/

-- Proof sketch: specialize the Chapter 31 identity-map owner theorem
-- `iInf_sub_eq_iSup_concaveConjugate_sub_convexConjugate_of_fenchel_qualification` to the closed
-- qualification branch by packaging `hf`, `hg`, and `hri` into the branch-(b) owner
-- qualification, then pair that equality with the canonical
-- primal-attainment theorem `exists_isMinOn_sub_of_dual_riDom_inter_nonempty`.
/-- Lemma 31.0.5: if `f` is closed proper convex and `g` is closed proper concave, recorded
canonically as `hf : f.IsClosedProperConvex` and `hg : g.IsClosedProperConcave`, and if the
dual relative interiors `riDom[𝕜](-g∗)` and `riDom[𝕜](f⋆)` meet, then the primal value
`⨅ x, f x - g x` equals the dual value `⨆ xStar, g∗ xStar - f⋆ xStar`, and the primal infimum is
attained. -/
theorem fenchelDuality_eq_and_primalAttainment_of_dual_riDom_inter_nonempty
    (hf : IsClosedProperConvex[𝕜] f)
    (hg : IsClosedProperConcave[𝕜] g)
    (hri : dualRiQualification) :
    (primalValue = dualValue) ∧
      ∃ x : E, IsMinOn primalObjective Set.univ x := by
  refine ⟨?_, ?_⟩
  · exact
      iInf_sub_eq_iSup_concaveConjugate_sub_convexConjugate_of_fenchel_qualification
        (Or.inr ⟨hf, hg, hri⟩)
  · exact exists_isMinOn_sub_of_dual_riDom_inter_nonempty hf hg hri

end
