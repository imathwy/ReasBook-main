import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_12_1
import StacksProject_2024.stacks_project.Chap30.Lemma_30_9_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_4_1
import StacksProject_2024.stacks_project.Chap31.Lemma_31_2_9

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable (ℱ : X.Modules) [ℱ.IsCoherent]

-- Semantic recall: `lean_leansearch` surfaced the sober/generic-point API
-- `genericPoints.ofComponent` and `genericPoints.isGenericPoint_ofComponent`; for the closed
-- support `Supp(ℱ)`, the source phrase “generic points of irreducible components” is recorded here
-- by the existing project owner `X.minimalSpecializationPoints (moduleSupport ℱ)`.

/-- Helper for Lemma 31.4.2: in this file, a coherent `\mathcal O_X`-module is used through its
quasi-coherent Chapter 31 interfaces. -/
local instance instIsQuasicoherentOfIsCoherentForLemma3142 : ℱ.IsQuasicoherent := by
  let _ : ℱ.IsFinitePresentation :=
    (isCoherent_iff_isFinitePresentation (X := X) ℱ).mp inferInstance
  infer_instance

/-- Lemma 31.4.2 (1): let `X` be a locally Noetherian scheme and let `\mathcal F` be a coherent
`\mathcal O_X`-module. Then the generic points of the irreducible components of `Supp(\mathcal F)`
are associated points of `\mathcal F`, formalized here as the coherent specialization of
`Lemma_31_2_9 (1)`. -/
@[stacks 05AL]
theorem minimalSpecializationPoints_moduleSupport_subset_associatedPoints :
    X.minimalSpecializationPoints (moduleSupport ℱ) ⊆ associatedPoints ℱ :=
  Scheme.Modules.minimalSpecializationPoints_support_subset_associatedPoints (ℱ := ℱ)

/-- Lemma 31.4.2 (2): let `X` be a locally Noetherian scheme and let `\mathcal F` be a coherent
`\mathcal O_X`-module. Then an associated point of `\mathcal F` is embedded if and only if it is
not a generic point of an irreducible component of `Supp(\mathcal F)`, formalized here as not
lying in `X.minimalSpecializationPoints (moduleSupport ℱ)`. -/
@[stacks 05AL]
theorem embeddedAssociatedAt_iff_mem_associatedPoints_and_not_mem_minimalSpecializationPoints_moduleSupport
    (x : X) :
    ℱ.embeddedAssociatedAt x ↔
      x ∈ associatedPoints ℱ ∧
        x ∉ X.minimalSpecializationPoints (moduleSupport ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- Lemma 31.4.2 (3): an embedded point of a locally Noetherian scheme `X` is an associated point
of `X` if and only if it is not a generic point of an irreducible component of `X`. -/
@[stacks 05AL]
theorem embeddedPoint_iff_mem_associatedPoints_and_not_mem_genericPointsOfIrreducibleComponents
    (x : X) :
    X.embeddedPoint x ↔
      x ∈ X.associatedPoints ∧
        x ∉ genericPointsOfIrreducibleComponents X := sorry

end AlgebraicGeometry.Scheme
