import Mathlib
import stacks_project.Chap20.Lemma_20_10_2
import stacks_project.Chap20.Lemma_20_11_11

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (RingedSpace.Modules X)]
variable (U : Opens X.carrier) {ι : Type u} (𝒰 : ι → Over U)
variable [HasFiniteProducts (Over U)]
variable [HasProducts (ModuleCat.{u} (X.presheaf.obj (op U)))]

/-- The canonical inclusion `Mod(\mathcal O_X) ⥤ PMod(\mathcal O_X)` is additive. -/
instance sheafOfModules_forget_additive (X : RingedSpace.{u}) :
    (SheafOfModules.forget (RingedSpace.ringCatSheaf X)).Additive := by
  infer_instance

/-- The sections functor of `\mathcal O_X`-modules over an open subset `U`. -/
abbrev moduleSectionsEvaluation (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (RingedSpace.Modules X) ⥤ ModuleCat.{u} (X.presheaf.obj (op U)) :=
  SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)

/-- The sections functor on `U` is additive. -/
instance moduleSectionsEvaluation_additive (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleSectionsEvaluation X U).Additive where
  map_add := by
    intro M N f g
    change
      (PresheafOfModules.evaluation (RingedSpace.ringCatSheaf X).obj (op U)).map
          ((SheafOfModules.forget (RingedSpace.ringCatSheaf X)).map (f + g)) =
        (PresheafOfModules.evaluation (RingedSpace.ringCatSheaf X).obj (op U)).map
            ((SheafOfModules.forget (RingedSpace.ringCatSheaf X)).map f) +
          (PresheafOfModules.evaluation (RingedSpace.ringCatSheaf X).obj (op U)).map
            ((SheafOfModules.forget (RingedSpace.ringCatSheaf X)).map g)
    rw [(SheafOfModules.forget (RingedSpace.ringCatSheaf X)).map_add,
      (PresheafOfModules.evaluation (RingedSpace.ringCatSheaf X).obj (op U)).map_add]

/-- The `E_2^{p,q}` term in the Čech-to-cohomology spectral sequence for an
`\mathcal O_X`-module `ℱ`, computed as Čech cohomology of the `q`-th cohomology presheaf. -/
abbrev moduleCechToCohomologyPageTwoTerm
    (ℱ : (RingedSpace.Modules X)) (p q : ℕ) :
    ModuleCat.{u} (X.presheaf.obj (op U)) :=
  ((ringedSpaceCechCohomologyDegree U 𝒰 p).obj.obj
    (((SheafOfModules.forget (RingedSpace.ringCatSheaf X)).rightDerived q).obj ℱ))

/-- The degree-`n` cohomology of an `\mathcal O_X`-module on the open subset `U`, viewed as the
`n`-th right derived functor of sections on `U`. -/
abbrev moduleCohomologyAtOpen
    (ℱ : (RingedSpace.Modules X)) (n : ℕ) :
    ModuleCat.{u} (X.presheaf.obj (op U)) :=
  ((moduleSectionsEvaluation X U).rightDerived n).obj ℱ

/-- A functorial package for the spectral sequence computing the cohomology of an
`\mathcal O_X`-module on `U` from the Čech cohomology of its cohomology presheaves with respect
to the cover `𝒰`. -/
structure CechToModuleCohomologySpectralSequence
    (X : RingedSpace.{u})
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    [HasInjectiveResolutions (RingedSpace.Modules X)]
    (U : Opens X.carrier) [HasFiniteProducts (Over U)] {ι : Type u} (𝒰 : ι → Over U)
    [HasProducts (ModuleCat.{u} (X.presheaf.obj (op U)))] where
  /-- The cohomological spectral sequence attached to each `\mathcal O_X`-module, functorially
  in the module and starting on the `E₂`-page. -/
  spectralSequenceFunctor :
    (RingedSpace.Modules X) ⥤
      E₂CohomologicalSpectralSequenceNat (ModuleCat.{u} (X.presheaf.obj (op U)))
  /-- The `E₂`-page is the Čech cohomology of the cohomology presheaf
  `\underline{H}^q(\mathcal F)`. -/
  pageTwoIso :
    ∀ (ℱ : (RingedSpace.Modules X)) (p q : ℕ),
      ((spectralSequenceFunctor.obj ℱ).page 2).X (p, q) ≅
        moduleCechToCohomologyPageTwoTerm U 𝒰 ℱ p q
  /-- The chosen abutment objects of the spectral sequence. -/
  abutment :
    (RingedSpace.Modules X) → ℕ →
      ModuleCat.{u} (X.presheaf.obj (op U))
  /-- The abutment identifies with the degree-`n` module cohomology of `ℱ` on `U`. -/
  targetIso :
    ∀ (ℱ : (RingedSpace.Modules X)) (n : ℕ),
      abutment ℱ n ≅ moduleCohomologyAtOpen U ℱ n

-- Proof sketch: apply the Grothendieck spectral sequence to the composite of the left exact
-- inclusion `Mod(\mathcal O_X) ⥤ PMod(\mathcal O_X)` with degree-zero Čech cohomology for the
-- cover `𝒰`. Lemma `20.9.2` identifies degree-zero Čech cohomology with sections on `U`, Lemma
-- `20.11.1` shows that injective `\mathcal O_X`-modules are Čech-acyclic for the cover, and
-- Lemmas `20.10.5` and `20.11.4` identify the `E₂`-page with Čech cohomology of the cohomology
-- presheaves `\underline{H}^q(\mathcal F)`. Naturality of the Grothendieck construction gives
-- functoriality in `\mathcal F`.
/-- Lemma 20.11.5: for a ringed space `X`, an open subset `U`, and an open covering `𝒰` of `U`,
there is a cohomological spectral sequence functorial in an `\mathcal O_X`-module `\mathcal F`
whose `E_2^{p,q}`-term is `\check H^p(\mathcal U, \underline{H}^q(\mathcal F))` and whose
abutment is the degree-`p + q` cohomology of `\mathcal F` on `U`. -/
theorem exists_cechToModuleCohomologySpectralSequence :
    Nonempty (CechToModuleCohomologySpectralSequence X U 𝒰) := sorry

end AlgebraicGeometry.RingedSpace
