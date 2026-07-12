import StacksProject_2024.Chap18.Lemma_18_30_3
import StacksProject_2024.Chap18.Definition_18_17_1
import StacksProject_2024.Chap07.Definition_7_17_1
import StacksProject_2024.Chap07.Lemma_7_40_1
import StacksProject_2024.Chap21.Lemma_21_51_1
import StacksProject_2024.Chap21.Lemma_21_52_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Limits
open Opposite
open scoped SheafOfModules.RingedSite.LocalizedStructureModuleExtensionByZero

noncomputable section

universe u w

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasBinaryProducts C]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable {𝒪 : Sheaf J CommRingCat.{u}}

variable [modAbelian : Abelian (SheafOfModules (ringSheaf J 𝒪))]

local notation "Mod𝒪" => Mod(ringSheaf J 𝒪)
local notation "single0" => DerivedCategory.singleFunctor Mod𝒪 (0 : ℤ)

omit [HasBinaryProducts C] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})] modAbelian in
private theorem cohomologyPresheafFunctor_preserves_coproducts_of_isZero
    (U : C) (p : ℕ)
    (hzero :
      ∀ ℱ : Mod𝒪,
        IsZero (((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).H' p U))
    (ι : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete ι)
      (SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙
        Sheaf.cohomologyPresheafFunctor J p ⋙
          (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat).obj (op U)) := by
  let F : Mod𝒪 ⥤ AddCommGrpCat :=
    SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙
      Sheaf.cohomologyPresheafFunctor J p ⋙
        (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat).obj (op U)
  let hF : IsZero F := Functor.isZero _ fun ℱ ↦ by
    simpa [F] using hzero ℱ
  simpa [F] using F.preservesColimitsOfShape_of_isZero hF (Discrete ι)

omit [HasBinaryProducts C] [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})] modAbelian in
private theorem cohomologyPresheafFunctor_preserves_coproducts_of_weaklyContractible
    (U : C) [J.IsWeaklyContractible U] (p : ℕ) (hp : 0 < p) (ι : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete ι)
      (SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙
        Sheaf.cohomologyPresheafFunctor J p ⋙
          (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat).obj (op U)) := by
  exact
    cohomologyPresheafFunctor_preserves_coproducts_of_isZero
      U p
      (fun ℱ ↦
        weaklyContractible_higherCohomology_isZero U
          ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ) p hp)
      ι

omit [HasBinaryProducts C] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})] modAbelian in
private theorem cohomologyPresheafFunctor_preserves_coproducts_zero
    (U : C) (hUqc : J.QuasiCompactObject U) (ι : Type w) :
    PreservesColimitsOfShape (Discrete ι)
      (SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙
        Sheaf.cohomologyPresheafFunctor J 0 ⋙
          (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat).obj (op U)) := by
  let F : Mod𝒪 ⥤ AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙ siteAbelianSectionsFunctor J U
  let eSections :
      siteAbelianSectionsFunctor J U ≅
        Sheaf.cohomologyPresheafFunctor J 0 ⋙
          (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U) := by
    let e :=
      Classical.choice
        (Sheaf.abelianSheafInclusion_rightDerived_eval_is_cohomologyAtObject J U 0)
    exact
      (Functor.isoWhiskerRight
        (Functor.rightDerivedZeroIsoSelf (sheafToPresheaf J AddCommGrpCat.{u}))
        ((CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))).symm ≪≫ e
  let e :
      F ≅ SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙
        Sheaf.cohomologyPresheafFunctor J 0 ⋙
          (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U) :=
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf (ringSheaf J 𝒪)) eSections
  let _ : PreservesColimitsOfShape (Discrete ι) F := by
    simpa [F, siteAbelianSectionsFunctor, sheafSections, SheafOfModules.evaluation] using
      quasiCompactObject_module_sections_preserves_direct_sums
        (ringSheaf J 𝒪) U hUqc ι
  simpa [F] using
    (CategoryTheory.Limits.preservesColimitsOfShape_of_natIso e :
      PreservesColimitsOfShape (Discrete ι)
        (SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙
          Sheaf.cohomologyPresheafFunctor J 0 ⋙
            (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)))

omit [HasBinaryProducts C] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})] modAbelian in
/-- Degree-zero cohomology over a quasi-compact object `U` commutes with arbitrary coproducts,
because `R^0Γ(U, -)` identifies with ordinary sections over `U`. -/
theorem cohomologyAtObjectFunctor_preserves_coproducts_zero
    (U : C) (hUqc : J.QuasiCompactObject U) (ι : Type w) :
    PreservesColimitsOfShape (Discrete ι)
      (SheafOfModules.cohomologyAtObjectFunctor (ringSheaf J 𝒪) 0 U) := by
  exact
    cohomologyAtObjectFunctor_preservesColimitsOfShape_of_source U 0 ι
      (cohomologyPresheafFunctor_preserves_coproducts_zero U hUqc ι)

/- Domain-style sampling for Lemma 21.52.6:
- primary domain: compactness of the standard derived generators `(single0).obj (j![𝒪, U])` on a
  ringed site, specialized from the finite-cohomological-dimension criterion of `21.52.5`;
- sampled owner declarations:
  `CategoryTheory.IsCompactObject`,
  `DerivedCategory.singleFunctor`,
  `SheafOfModules.RingedSite.localizedStructureModuleExtensionByZeroDegreeZero_isCompactObject_of_finiteCohomologicalDimension_and_directSumCompatibility`,
  `CategoryTheory.weaklyContractible_higherCohomology_isZero`,
  `quasiCompactObject_module_sections_preserves_direct_sums`;
- best owner abstraction: the source-facing object is the canonical degree-zero derived object
  `((single0).obj (j![𝒪, U]))`, and this lemma should specialize the compactness theorem
  `21.52.5` directly on that owner;
- primitive vs derived:
  primitive data are the object `U`, quasi-compactness of `U`, and weak contractibility of `U`;
  the finite-cohomological-dimension hypothesis package and compactness are derived API.

Source/core/bridge triage:
- `source-facing`: the quasi-compact weakly-contractible specialization in Lemma `21.52.6`;
- `core/canonical`: `CategoryTheory.IsCompactObject` applied to
  `((single0).obj (j![𝒪, U]))`;
- `bridge/view`: the vanishing and direct-sum hypotheses supplied to `21.52.5`. -/

-- Proof sketch: apply Lemma `21.52.5` to the degree-zero derived object attached to
-- `j![𝒪, U]`. Weak contractibility gives vanishing of higher cohomology over `U` via
-- Lemma `21.51.1`, while quasi-compactness gives direct-sum compatibility of sections over `U`
-- via Modules on Sites, Lemma `18.30.3`.
/-- Lemma 21.52.6: if `U` is quasi-compact and weakly contractible in a ringed site
`(C, 𝒪)`, then the degree-zero derived object attached to `j![𝒪, U]` is a compact object
of the derived category of `𝒪`-modules. -/
@[stacks 094E]
theorem localizedStructureModuleExtensionByZero_degreeZero_isCompactObject_of_quasiCompact_weaklyContractible
    (U : C) (hUqc : J.QuasiCompactObject U) [J.IsWeaklyContractible U] :
    IsCompactObject ((single0).obj (j![𝒪, U])) := by
  refine
    localizedStructureModuleExtensionByZeroDegreeZero_isCompactObject_of_finiteCohomologicalDimension_and_directSumCompatibility
      U ?_ ?_
  · refine ⟨0, fun p hp ℱ ↦ ?_⟩
    exact
      weaklyContractible_higherCohomology_isZero U
        ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ) p (by exact_mod_cast hp)
  · intro p ι
    by_cases hp : p = 0
    · subst hp
      exact cohomologyPresheafFunctor_preserves_coproducts_zero U hUqc ι
    · have hp' : 0 < p := Nat.pos_of_ne_zero hp
      exact
        cohomologyPresheafFunctor_preserves_coproducts_of_weaklyContractible
          U p hp' ι

end

end SheafOfModules.RingedSite
