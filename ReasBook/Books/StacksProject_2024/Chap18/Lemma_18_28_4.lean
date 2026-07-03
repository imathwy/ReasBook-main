import Mathlib
import StacksProject_2024.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite Limits

noncomputable section

universe u

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]

/- Domain-style sampling for Lemma 18.28.4:
- primary domain: sheafification of locally flat presheaves of modules, with the core
  sheafification machinery owned by the Chapter 18 flatness API for sheaves of modules;
- sampled owner declarations:
  `SheafOfModules.RingedSite.IsFlat`,
  `PresheafOfModules.moduleSheafification`,
  `PresheafOfModules.sheafificationRingMap`,
  `sheafModuleTensorRightFunctor`,
  `exactFunctor`;
- best owner abstraction: the source-facing result should be stated directly in the chapter owner
  `SheafOfModules.RingedSite.IsFlat` for the sheafified module
  `((moduleSheafification J 𝒪).obj ℱ)` over `commRingSheafification J 𝒪`; exactness of tensoring
  is then derived API via the field `IsFlat.exact_tensor`;
- primitive data: a presheaf of commutative rings `𝒪`, a presheaf module
  `ℱ : PresheafOfModules (ringPresheaf 𝒪)`, and the local sectionwise flatness hypothesis;
- derived API: exactness of the sheaf tensor-right functor on
  `SheafOfModules (ringSheaf J (commRingSheafification J 𝒪))`.

Layer triage:
- `source-facing`: the local-flatness criterion for the sheafified module;
- `core/canonical`: `SheafOfModules.RingedSite.IsFlat`;
- `bridge/view`: the exactness consequence expressed by `IsFlat.exact_tensor`.
-/

-- Proof sketch: use the local-flatness hypothesis to reduce injectivity of tensoring with
-- `\mathcal F^\#` to injectivity after passing to a covering on which the section modules of
-- `\mathcal F` are flat; then apply exactness of module sheafification and the local criterion
-- that a morphism of presheaves which is injective on a cover sheafifies to a monomorphism.
/-- Lemma 18.28.4: if every object of the site has a covering on which the section modules of a
presheaf `\mathcal F` are flat over the corresponding sections of `\mathcal O`, then the
associated sheaf `\mathcal F^\#` is flat over the sheafified structure sheaf `\mathcal O^\#`,
expressed in the chapter's canonical owner `SheafOfModules.RingedSite.IsFlat`. -/
theorem sheafification_isFlat_of_locally_flat
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    (hlocal :
      ∀ U : C, ∃ R : Presieve U, Sieve.generate R ∈ J U ∧
        ∀ ⦃V : C⦄ (f : V ⟶ U), R f → Module.Flat (𝒪.obj (op V)) (ℱ.obj (op V))) :
    SheafOfModules.RingedSite.IsFlat
      (commRingSheafification J 𝒪) ((moduleSheafification J 𝒪).obj ℱ) := sorry

/-- Exactness companion to Lemma 18.28.4: the canonical flatness statement implies that
tensoring on the right by `\mathcal F^\#` is exact on sheaves of `\mathcal O^\#`-modules. -/
theorem sheafification_exact_tensor_of_locally_flat
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    (hlocal :
      ∀ U : C, ∃ R : Presieve U, Sieve.generate R ∈ J U ∧
        ∀ ⦃V : C⦄ (f : V ⟶ U), R f → Module.Flat (𝒪.obj (op V)) (ℱ.obj (op V))) :
    exactFunctor
      (SheafOfModules (ringSheaf J (commRingSheafification J 𝒪)))
      (SheafOfModules (ringSheaf J (commRingSheafification J 𝒪)))
      (sheafModuleTensorRightFunctor ((moduleSheafification J 𝒪).obj ℱ)) :=
  (sheafification_isFlat_of_locally_flat J 𝒪 ℱ hlocal).exact_tensor

end PresheafOfModules
