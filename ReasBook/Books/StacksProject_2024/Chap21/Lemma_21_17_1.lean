import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap13.Remark_13_10_9
import stacks_project.Chap18.Lemma_18_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits ComplexShape HomotopyCategory MonoidalCategory

noncomputable section

universe u

set_option checkBinderAnnotations false

namespace CategoryTheory

/-
Domain-style sampling for Lemma 21.17.1:
- primary domain: triangulated tensor-totalization functors on homotopy categories of cochain
  complexes in a preadditive monoidal category;
- sampled owner declarations:
  `Functor.map₂CochainComplex`,
  `Functor.mapHomotopyCategory`,
  `Functor.IsTriangulated`;
- best owner abstraction: the Chapter 13 owner theorem
  `Functor.mapHomotopyCategory` on the fixed-factor tensor-complex functors for a bilinear
  bifunctor;
- primitive data: the bilinear tensor bifunctor `curriedTensor (ringedSiteModuleCategory J 𝒪)` and
  a fixed complex in each variable;
- derived API here: the ringed-site specialization to the homotopy-category endofunctors
  `𝒜 ↦ Tot (𝒢 ⊗ 𝒜)` and `𝒜 ↦ Tot (𝒜 ⊗ 𝒢)`.

Source/core/bridge triage:
- `source-facing`: exactness of tensoring on either side by a fixed complex of `𝒪`-modules on a
  ringed site;
- `core/canonical`: the two fixed-factor tensor functors
  `((curriedTensor (ringedSiteModuleCategory J 𝒪)).map₂CochainComplex.obj 𝒢).mapHomotopyCategory
    (up ℤ)` and
  `((curriedTensor (ringedSiteModuleCategory J 𝒪)).map₂CochainComplex.flip.obj 𝒢).mapHomotopyCategory
    (up ℤ)`;
- `bridge/view`: specializing the Chapter 13 owner theorem to
  `curriedTensor (ringedSiteModuleCategory J 𝒪)`.

This file adds no ringed-site-specific primitive tensor data beyond that specialization, so the
correct refinement is direct recall/use of the Chapter 13 owner theorem rather than a duplicate
Chapter 21 wrapper.
-/

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})

variable [Preadditive (ringedSiteModuleCategory J 𝒪)]
variable [HasZeroObject (ringedSiteModuleCategory J 𝒪)]
variable [HasBinaryBiproducts (ringedSiteModuleCategory J 𝒪)]
variable [HasCountableCoproducts (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ F : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj F).Additive]
variable [∀ (F G : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ),
  CochainComplex.HasMapBifunctor F G (curriedTensor (ringedSiteModuleCategory J 𝒪))]

variable (𝒢 : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)

/- Lemma 21.17.1 is the ringed-site specialization of the canonical fixed-factor
tensor-totalization functors on the homotopy category, given by the Chapter 13 exactness
theorems specialized to `curriedTensor (ringedSiteModuleCategory J 𝒪)`. -/
example :
    let F : HomotopyCategory (ringedSiteModuleCategory J 𝒪) (up ℤ) ⥤
        HomotopyCategory (ringedSiteModuleCategory J 𝒪) (up ℤ) :=
      CategoryTheory.Quotient.lift (homotopic (ringedSiteModuleCategory J 𝒪) (up ℤ))
        ((((curriedTensor (ringedSiteModuleCategory J 𝒪)).map₂CochainComplex).obj 𝒢) ⋙
          HomotopyCategory.quotient (ringedSiteModuleCategory J 𝒪) (up ℤ))
        (fun _ _ _ _ ⟨h⟩ ↦
          HomotopyCategory.eq_of_homotopy _ _
            (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 𝒢) h
              (curriedTensor (ringedSiteModuleCategory J 𝒪)) (up ℤ)))
    let _ : F.CommShift ℤ := by
      change (CategoryTheory.Quotient.lift (homotopic (ringedSiteModuleCategory J 𝒪) (up ℤ))
        ((((curriedTensor (ringedSiteModuleCategory J 𝒪)).map₂CochainComplex).obj 𝒢) ⋙
          HomotopyCategory.quotient (ringedSiteModuleCategory J 𝒪) (up ℤ))
        (fun _ _ _ _ ⟨h⟩ ↦
          HomotopyCategory.eq_of_homotopy _ _
            (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 𝒢) h
              (curriedTensor (ringedSiteModuleCategory J 𝒪)) (up ℤ)))).CommShift ℤ
      infer_instance
    Functor.IsTriangulated F := by
  sorry

example :
    let F : HomotopyCategory (ringedSiteModuleCategory J 𝒪) (up ℤ) ⥤
        HomotopyCategory (ringedSiteModuleCategory J 𝒪) (up ℤ) :=
      CategoryTheory.Quotient.lift (homotopic (ringedSiteModuleCategory J 𝒪) (up ℤ))
        ((((curriedTensor (ringedSiteModuleCategory J 𝒪)).map₂CochainComplex).flip.obj 𝒢) ⋙
          HomotopyCategory.quotient (ringedSiteModuleCategory J 𝒪) (up ℤ))
        (fun _ _ _ _ ⟨h⟩ ↦
          HomotopyCategory.eq_of_homotopy _ _
            (HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 𝒢)
              (curriedTensor (ringedSiteModuleCategory J 𝒪)) (up ℤ)))
    let _ : F.CommShift ℤ := by
      change (CategoryTheory.Quotient.lift (homotopic (ringedSiteModuleCategory J 𝒪) (up ℤ))
        ((((curriedTensor (ringedSiteModuleCategory J 𝒪)).map₂CochainComplex).flip.obj 𝒢) ⋙
          HomotopyCategory.quotient (ringedSiteModuleCategory J 𝒪) (up ℤ))
        (fun _ _ _ _ ⟨h⟩ ↦
          HomotopyCategory.eq_of_homotopy _ _
            (HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 𝒢)
              (curriedTensor (ringedSiteModuleCategory J 𝒪)) (up ℤ)))).CommShift ℤ
      infer_instance
    Functor.IsTriangulated F := by
  sorry

end

end CategoryTheory
