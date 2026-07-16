import Mathlib
import StacksProject_2024.stacks_project.Chap17.Lemma_17_20_2
import StacksProject_2024.stacks_project.Chap18.Lemma_18_31_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.RingedSpace.Hom

/- Domain-style sampling for Lemma 17.22.5:
- primary domain: pullback of internal-Hom sheaves along a morphism of ringed spaces;
- inspected owner declarations:
  `RingedSite.ofCommRingSheaf`,
  `RingedSite.Hom.pullbackInternalHomComparison`,
  `RingedSite.Hom.isIso_pullbackInternalHomComparison`,
  `exactFunctor`,
  `AlgebraicGeometry.RingedSpace.Hom.IsFlat.pullback_exact`;
- best owner abstraction:
  the source-facing ringed-space comparison is a thin specialization of the ringed-site owner
  `RingedSite.Hom.pullbackInternalHomComparison`; the chapter-level public surface should remain
  the pullback owner `f^*` and the flatness owner `RingedSpace.Hom.IsFlat`;
- primitive data:
  a morphism `f : X ⟶ Y` and sheaves `ℱ 𝒢 : Y.Modules`;
- derived API:
  the ringed-space bridge `pullbackInternalHomComparison`, together with its flat/finitely
  presented isomorphism criterion obtained from the ringed-site owner theorem.

Source/core/bridge triage:
- `source-facing`: `pullbackInternalHomComparison`;
- `core/canonical`: `RingedSite.Hom.pullbackInternalHomComparison`,
  `RingedSite.Hom.isIso_pullbackInternalHomComparison`,
  `exactFunctor _ _ ((opensRingedSiteHom f)^*)`, `RingedSpace.Hom.IsFlat`, and the pullback owner
  `f^*`;
- `bridge/view`: the ringed-space specialization along the site of opens and
  `RingedSpace.Hom.toRingCatSheafHom`.
-/

variable {X Y : RingedSpace} (f : X ⟶ Y)
variable [MonoidalCategory Y.Modules] [MonoidalClosed Y.Modules]
variable [MonoidalCategory X.Modules] [MonoidalClosed X.Modules]
variable [(f^*).Monoidal]

private abbrev opensRingedSite (X : RingedSpace) : RingedSite :=
  RingedSite.ofCommRingSheaf (Opens.grothendieckTopology X) X.sheaf

private noncomputable abbrev opensRingedSiteHom (f : X ⟶ Y) :
    opensRingedSite X ⟶ opensRingedSite Y where
  base := Opens.map f.hom.base
  structureSheafMap := RingedSpace.Hom.toRingCatSheafHom f

private instance instExactFunctor_modulePullback_opensRingedSiteHom
    [RingedSpace.Hom.IsFlat f] :
    exactFunctor _ _ (opensRingedSiteHom f).modulePullback := by
  simpa [RingedSpace.Hom.pullback, opensRingedSiteHom] using
    (IsFlat.pullback_exact f)

/-- The canonical pullback-to-internal-Hom comparison morphism associated to a morphism of
ringed spaces. This is the ringed-space specialization of the ringed-site owner
`RingedSite.Hom.pullbackInternalHomComparison`. -/
noncomputable abbrev pullbackInternalHomComparison (ℱ 𝒢 : Y.Modules) :
    (f^*).obj ((ihom ℱ).obj 𝒢) ⟶
      (ihom ((f^*).obj ℱ)).obj ((f^*).obj 𝒢) :=
  RingedSite.Hom.pullbackInternalHomComparison (opensRingedSiteHom f) ℱ 𝒢

-- Proof sketch: transport the ringed-space morphism `f` to the ringed site of opens with its
-- structure sheaf. The Chapter 17 flatness bridge gives exactness of `f^*`, hence a
-- canonical `exactFunctor` instance on that ringed-site morphism. The result is then
-- exactly the Chapter 18 owner theorem specialized back to ringed spaces.
/-- Lemma 17.22.5: for a flat morphism of ringed spaces `f : (X, \mathcal O_X) ⟶
`(Y, \mathcal O_Y)` and an `\mathcal O_Y`-module `\mathcal F` of finite presentation, the
canonical map
`f^*\mathcal H\!\mathit{om}_{\mathcal O_Y}(\mathcal F, \mathcal G) ⟶
\mathcal H\!\mathit{om}_{\mathcal O_X}(f^*\mathcal F, f^*\mathcal G)`
is an isomorphism. -/
theorem isIso_pullbackInternalHomComparison
    (ℱ 𝒢 : Y.Modules) [ℱ.IsFinitePresentation] [RingedSpace.Hom.IsFlat f] :
    IsIso (pullbackInternalHomComparison f ℱ 𝒢) := by
  let X' : RingedSite := opensRingedSite X
  let Y' : RingedSite := opensRingedSite Y
  let g : X' ⟶ Y' := opensRingedSiteHom f
  let ℱ' : SheafOfModules Y'.structureSheaf := ℱ
  let 𝒢' : SheafOfModules Y'.structureSheaf := 𝒢
  have hg : IsIso (RingedSite.Hom.pullbackInternalHomComparison g ℱ' 𝒢') := by
    exact RingedSite.Hom.isIso_pullbackInternalHomComparison g ℱ' 𝒢'
  simpa [X', Y', g, ℱ', 𝒢', pullbackInternalHomComparison] using hg

end AlgebraicGeometry.RingedSpace.Hom
