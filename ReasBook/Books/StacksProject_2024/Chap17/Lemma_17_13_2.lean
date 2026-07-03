import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.Definition_17_13_1
import StacksProject_2024.Chap17.Remark_17_13_5

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 17.13.2:
- primary domain: quasi-coherent sheaves of modules on ringed spaces and pushforward along a
  closed immersion of ringed spaces;
- inspected owner declarations:
  `RingedSpace.IsClosedImmersion`,
  `ringedSpaceModulePushforward_isLeftAdjoint_of_isClosedImmersion`,
  `RingedSpace.ringCatSheaf`,
  `RingedSpace.Modules`,
  `SheafOfModules.IsQuasicoherent`,
  `AlgebraicGeometry.RingedSpace.Hom.pushforward`;
- best owner abstraction: the chapter source-facing owner `RingedSpace.IsClosedImmersion i`,
  together with the ambient owner categories `X.Modules` and `Z.Modules`, the canonical owner
  predicate `SheafOfModules.IsQuasicoherent`, the pushforward functor `i _*`, and the canonical
  left-adjoint owner layer on `i _*` supplied by the closed-immersion instance
  `ringedSpaceModulePushforward_isLeftAdjoint_of_isClosedImmersion`;
- primitive data: a closed immersion `i : Z ⟶ X` and a quasi-coherent module `ℱ : Z.Modules`;
- derived API: the quasi-coherence of `(i _*).obj (SheafOfModules.unit Z.ringCatSheaf)` supplied
  by the closed-immersion hypothesis, the colimit-preservation of `i _*` supplied by its
  left-adjoint structure, and then the quasi-coherence of `((i _*).obj ℱ)`.

Source/core/bridge triage:
- `source-facing`: the Stacks assertion that for a closed immersion `i`, the pushforward `i_* ℱ`
  of a quasi-coherent `\mathcal O_Z`-module is quasi-coherent;
- `core/canonical`: `X.Modules`, `Z.Modules`, `SheafOfModules.IsQuasicoherent`, and `i _*`,
  together with the owner-level left-adjoint structure on `i _*` and the explicit hypothesis that
  `i_* \mathcal O_Z` is quasi-coherent;
- `bridge/view`: the theorem that a closed immersion supplies that explicit structure-sheaf
  quasi-coherence hypothesis and the left-adjoint structure on `i_*`.

This file therefore keeps the numbered item at the `source-facing` layer and records the
closed-embedding plus owner-level left-adjoint / `i_* \mathcal O_Z` formulation as a companion
core theorem. -/

variable {X Z : RingedSpace.{u}}

local notation "𝒪Z" => SheafOfModules.unit Z.ringCatSheaf

-- Proof sketch: choose local quasi-coherent presentations of `ℱ` on `Z`; the closed-embedding
-- hypothesis identifies neighbourhoods on the image, and quasi-coherence of `i_* \mathcal O_Z`
-- makes the pushed-forward free terms quasi-coherent on `X`. The canonical left-adjoint owner
-- layer on `i_*` then supplies the coproduct-preservation needed by `Presentation.map`, so
-- pushing forward those local presentations yields local cokernel presentations of `i_* ℱ`.
/-- Core companion: if `i : (Z, \mathcal{O}_Z) \to (X, \mathcal{O}_X)` has underlying map a
closed embedding, if pushforward on module sheaves along `i` is a left adjoint, and if the
pushed-forward structure sheaf `i_* \mathcal O_Z` is quasi-coherent, then for any quasi-coherent
`\mathcal{O}_Z`-module `\mathcal{F}`, the pushforward `i_* \mathcal{F}` is quasi-coherent. -/
theorem ringedSpaceModulePushforward_isQuasicoherent_of_closedEmbedding_of_isLeftAdjoint_of_pushforwardUnit_isQuasicoherent
    (i : Z ⟶ X)
    (hi : Topology.IsClosedEmbedding i.hom.base)
    [(i _*).IsLeftAdjoint]
    (hOZ : ((i _*).obj 𝒪Z).IsQuasicoherent)
    (ℱ : Z.Modules) [ℱ.IsQuasicoherent] :
    ((i _*).obj ℱ).IsQuasicoherent := sorry

-- Proof sketch: a closed immersion is defined by local surjectivity of
-- `\mathcal O_X \to i_* \mathcal O_Z` with locally generated kernel ideal sheaf, so
-- `i_* \mathcal O_Z` is locally the cokernel of a map between locally free modules and hence is
-- quasi-coherent.
/-- Closed-immersion bridge: the source-facing owner `RingedSpace.IsClosedImmersion i` supplies
the quasi-coherence of the pushed-forward structure sheaf `i_* \mathcal O_Z`. -/
theorem ringedSpaceModulePushforward_unit_isQuasicoherent_of_isClosedImmersion
    (i : Z ⟶ X) [RingedSpace.IsClosedImmersion i] :
    ((i _*).obj 𝒪Z).IsQuasicoherent := sorry

/-- Lemma 17.13.2: if `i : (Z, \mathcal{O}_Z) \to (X, \mathcal{O}_X)` is a closed immersion, then
for any quasi-coherent `\mathcal{O}_Z`-module `\mathcal{F}`, the pushforward `i_* \mathcal{F}` is
quasi-coherent. -/
theorem ringedSpaceModulePushforward_isQuasicoherent_of_isClosedImmersion
    (i : Z ⟶ X) [RingedSpace.IsClosedImmersion i]
    (ℱ : Z.Modules) [ℱ.IsQuasicoherent] :
    ((i _*).obj ℱ).IsQuasicoherent := by
  let hi : RingedSpace.IsClosedImmersion i := inferInstance
  let _ : (i _*).IsLeftAdjoint := inferInstance
  exact
    ringedSpaceModulePushforward_isQuasicoherent_of_closedEmbedding_of_isLeftAdjoint_of_pushforwardUnit_isQuasicoherent
      i hi.isClosedEmbedding
      (ringedSpaceModulePushforward_unit_isQuasicoherent_of_isClosedImmersion i) ℱ

end AlgebraicGeometry
