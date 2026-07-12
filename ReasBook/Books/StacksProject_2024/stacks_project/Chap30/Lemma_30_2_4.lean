import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}}

-- Semantic recall: `lean_leansearch` and the local Chapter 20/30 precedent point to terminal-open
-- sheaf cohomology of the underlying additive sheaf, expressed here through the canonical
-- `SheafOfModules.toSheaf` owner to avoid importing the proof-heavy project bridge
-- `RingedSpace.moduleUnderlyingSheaf`, together with the Leray-degeneration bridge
-- `RingedSpace.globalCohomology_iso_pushforward_of_higherDirectImageModule_isZero`. This item is
-- the affine specialization where Lemma `30.2.3` supplies the higher direct image vanishing.

/-- Lemma 30.2.4: let `f : X ⟶ S` be an affine morphism of schemes. Let `\mathcal F` be a
quasi-coherent `\mathcal O_X`-module. Then `H^i(X, \mathcal F) = H^i(S, f_*\mathcal F)` for all
`i ≥ 0`. -/
@[stacks 089W]
theorem globalCohomology_iso_pushforward_of_isAffineHom
    (f : X ⟶ S) [IsAffineHom f]
    [HasInjectiveResolutions X.Modules]
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    [HasSheafify (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u})]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (i : ℕ) :
    IsIsomorphic
      (((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' i (⊤ : Opens X))
      (((SheafOfModules.toSheaf S.ringCatSheaf).obj
        ((Scheme.Modules.pushforward f).obj ℱ)).H' i (⊤ : Opens S)) := sorry

end AlgebraicGeometry.Scheme
