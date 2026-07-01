import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap17.Definition_17_5_1
import stacks_project.Chap13.Remark_13_10_9

open CategoryTheory CategoryTheory.Limits ComplexShape HomotopyCategory MonoidalCategory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

set_option checkBinderAnnotations false

/-
Domain-style sampling for Lemma 20.26.1:
- primary domain: triangulated tensor-totalization functors on homotopy categories of cochain
  complexes in a preadditive monoidal category;
- sampled owner declarations:
  `Functor.map₂CochainComplex`,
  `Functor.mapHomotopyCategory`,
  `Functor.IsTriangulated`;
- best owner abstraction: the Chapter 13 owner theorem
  `Functor.mapHomotopyCategory` on the fixed-factor tensor-complex functors for a bilinear
  bifunctor;
- primitive data: a bilinear bifunctor `tensor : 𝒜 ⥤ ℬ ⥤ 𝒞` together with fixed complexes in the
  source variables;
- derived API here: the specialization `tensor := curriedTensor (RingedSpace.Modules X)` on the homotopy
  category of `\mathcal O_X`-modules.

Source/core/bridge triage:
- `source-facing`: the exactness of the two endofunctors
  `\mathcal F^\bullet ↦ \mathrm{Tot}(\mathcal G^\bullet \otimes_{\mathcal O_X}
  \mathcal F^\bullet)` and
  `\mathcal F^\bullet ↦ \mathrm{Tot}(\mathcal F^\bullet \otimes_{\mathcal O_X}
  \mathcal G^\bullet)`;
- `core/canonical`: the two fixed-factor tensor functors
  `((curriedTensor (RingedSpace.Modules X)).map₂CochainComplex.obj 𝒢).mapHomotopyCategory
    (up ℤ)` and
  `((curriedTensor (RingedSpace.Modules X)).map₂CochainComplex.flip.obj 𝒢).mapHomotopyCategory
    (up ℤ)`;
- `bridge/view`: specializing the bilinear owner theorem to the ringed-space tensor bifunctor
  `curriedTensor (RingedSpace.Modules X)`.

This file carries no ringed-space-specific primitive tensor data beyond that specialization, so the
correct refinement is to recall the Chapter 13 owner theorem directly rather than keep a duplicate
Chapter 20 wrapper with the same interface.
-/

section

variable {X : RingedSpace.{u}}

variable [Preadditive (RingedSpace.Modules X)]
variable [HasZeroObject (RingedSpace.Modules X)]
variable [HasBinaryBiproducts (RingedSpace.Modules X)]
variable [HasCountableCoproducts (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [(curriedTensor (RingedSpace.Modules X)).Additive]
variable [∀ ℱ : (RingedSpace.Modules X), ((curriedTensor (RingedSpace.Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (RingedSpace.Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (RingedSpace.Modules X))]

variable (𝒢 : CochainComplex (RingedSpace.Modules X) ℤ)

/- Lemma 20.26.1: for a ringed space `(X, \mathcal O_X)` and a complex `\mathcal G^\bullet`, the
two fixed-factor tensor-totalization functors on the homotopy category are exactly the Chapter 13
triangulated tensor functors specialized to `curriedTensor (RingedSpace.Modules X)`. -/
example :
    let F : HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤
        HomotopyCategory (RingedSpace.Modules X) (up ℤ) :=
      CategoryTheory.Quotient.lift (homotopic (RingedSpace.Modules X) (up ℤ))
        ((((curriedTensor (RingedSpace.Modules X)).map₂CochainComplex).obj 𝒢) ⋙
          HomotopyCategory.quotient (RingedSpace.Modules X) (up ℤ))
        (fun _ _ _ _ ⟨h⟩ ↦
          HomotopyCategory.eq_of_homotopy _ _
            (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 𝒢) h
              (curriedTensor (RingedSpace.Modules X)) (up ℤ)))
    let _ : F.CommShift ℤ := by
      change (CategoryTheory.Quotient.lift (homotopic (RingedSpace.Modules X) (up ℤ))
        ((((curriedTensor (RingedSpace.Modules X)).map₂CochainComplex).obj 𝒢) ⋙
          HomotopyCategory.quotient (RingedSpace.Modules X) (up ℤ))
        (fun _ _ _ _ ⟨h⟩ ↦
          HomotopyCategory.eq_of_homotopy _ _
            (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 𝒢) h
              (curriedTensor (RingedSpace.Modules X)) (up ℤ)))).CommShift ℤ
      infer_instance
    Functor.IsTriangulated F := by
  sorry

example :
    let F : HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤
        HomotopyCategory (RingedSpace.Modules X) (up ℤ) :=
      CategoryTheory.Quotient.lift (homotopic (RingedSpace.Modules X) (up ℤ))
        ((((curriedTensor (RingedSpace.Modules X)).map₂CochainComplex).flip.obj 𝒢) ⋙
          HomotopyCategory.quotient (RingedSpace.Modules X) (up ℤ))
        (fun _ _ _ _ ⟨h⟩ ↦
          HomotopyCategory.eq_of_homotopy _ _
            (HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 𝒢)
              (curriedTensor (RingedSpace.Modules X)) (up ℤ)))
    let _ : F.CommShift ℤ := by
      change (CategoryTheory.Quotient.lift (homotopic (RingedSpace.Modules X) (up ℤ))
        ((((curriedTensor (RingedSpace.Modules X)).map₂CochainComplex).flip.obj 𝒢) ⋙
          HomotopyCategory.quotient (RingedSpace.Modules X) (up ℤ))
        (fun _ _ _ _ ⟨h⟩ ↦
          HomotopyCategory.eq_of_homotopy _ _
            (HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 𝒢)
              (curriedTensor (RingedSpace.Modules X)) (up ℤ)))).CommShift ℤ
      infer_instance
    Functor.IsTriangulated F := by
  sorry

end

end AlgebraicGeometry.RingedSpace
