import StacksProject_2024.Chap28.Lemma_28_9_2
import StacksProject_2024.Chap17.Definition_17_14_1
import StacksProject_2024.Chap30.Lemma_30_9_1
import StacksProject_2024.Chap31.Definition_31_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry
open scoped ENat

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced the canonical ring-level owner
-- `Module.IsReflexive`; local Chapter 31 precedent fixes the scheme-side owner as
-- `Scheme.Modules.IsReflexive`, the source phrase "regular scheme" as `Scheme.Regular`, and
-- finite local freeness as `SheafOfModules.IsFiniteLocallyFree`. The stalkwise regular-local
-- formulation remains as a thin bridge via
-- `Scheme.regular_iff_isLocallyNoetherian_and_forall_isRegularLocalRing_stalk`.

section

variable {X : Scheme.{u}} [IsIntegral X]
variable [MonoidalCategory X.Modules] [BraidedCategory X.Modules] [MonoidalClosed X.Modules]
variable (ℱ : X.Modules) [ℱ.IsCoherent]

/-- In this file, coherent modules are used through the Chapter 17 finite-locally-free owner,
which is stated for quasi-coherent modules. -/
local instance instIsQuasicoherentOfIsCoherentForLemma311215 [IsLocallyNoetherian X] :
    ℱ.IsQuasicoherent := by
  let _ : ℱ.IsFinitePresentation :=
    (isCoherent_iff_isFinitePresentation ℱ).mp inferInstance
  infer_instance

/-- Lemma 31.12.15: let `X` be a regular scheme of dimension `≤ 2`, and let `ℱ` be a coherent
`\mathcal O_X`-module. Then the following are equivalent: `ℱ` is reflexive, and `ℱ` is finite
locally free. The regularity hypothesis uses the project owner `Scheme.Regular X`, and the
dimension hypothesis is encoded by `topologicalKrullDim X ≤ 2`.
-/
@[stacks 0B3N]
theorem isReflexive_iff_isFiniteLocallyFree_of_regular_and_topologicalKrullDim_le_two
    [Scheme.Regular X] (hdim : topologicalKrullDim X ≤ 2) :
    IsReflexive ℱ ↔ SheafOfModules.IsFiniteLocallyFree ℱ := sorry

/-- Stalkwise regular-locality is a source-faithful bridge to the regular-scheme form of
Lemma 31.12.15. -/
theorem isReflexive_iff_isFiniteLocallyFree_of_regular_stalk_and_topologicalKrullDim_le_two
    [IsLocallyNoetherian X]
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : topologicalKrullDim X ≤ 2) :
    IsReflexive ℱ ↔ SheafOfModules.IsFiniteLocallyFree ℱ := by
  let hX : Scheme.Regular X :=
    (Scheme.regular_iff_isLocallyNoetherian_and_forall_isRegularLocalRing_stalk X).2
      ⟨inferInstance, hreg⟩
  letI : Scheme.Regular X := hX
  exact isReflexive_iff_isFiniteLocallyFree_of_regular_and_topologicalKrullDim_le_two ℱ hdim

end

end AlgebraicGeometry.Scheme.Modules
