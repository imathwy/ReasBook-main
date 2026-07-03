import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits ComplexShape MonoidalCategory

noncomputable section

set_option checkBinderAnnotations false

universe u

section

variable {C : Type u} [Category C] [Preadditive C] [HasZeroObject C]
variable [MonoidalCategory C] [SymmetricCategory C]
variable [(curriedTensor C).Additive]
variable [∀ X : C, ((curriedTensor C).obj X).Additive]
variable [∀ G₁ G₂ : GradedObject ℤ C, GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C, GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C, GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ C, GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [∀ X : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X)]
variable [∀ X : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X)]

local notation "Cpx" => CochainComplex C ℤ
private abbrev forgetGraded : Cpx ⥤ GradedObject ℤ C :=
  HomologicalComplex.forget C (up ℤ)

/-- The graded-object isomorphism underlying the tensor symmetry on cochain complexes. -/
private noncomputable def tensorBraidingGradedIso
    (K L : Cpx) :
    forgetGraded.obj (K ⊗ L) ≅ forgetGraded.obj (L ⊗ K) :=
  (Functor.Monoidal.μIso forgetGraded K L).symm ≪≫
    β_ _ _ ≪≫
    Functor.Monoidal.μIso forgetGraded L K

/-- The degreewise component of the tensor symmetry on cochain complexes. -/
private noncomputable abbrev tensorBraidingComponent
    (K L : Cpx) (n : ℤ) :
    (K ⊗ L).X n ≅ (L ⊗ K).X n :=
  (GradedObject.eval n).mapIso (tensorBraidingGradedIso K L)

-- Proof sketch: after forgetting to graded objects, the braiding is the graded symmetry with the
-- usual Koszul sign rule. Checking the two summands of the total differential shows that the
-- degreewise braiding components satisfy the chain-map relation.
/-- The degreewise tensor symmetry commutes with the differentials of cochain complexes. -/
private lemma tensorBraidingComponentComm
    (K L : Cpx) (i j : ℤ) (h : (up ℤ).Rel i j) :
    (tensorBraidingComponent K L i).hom ≫ (L ⊗ K).d i j =
      (K ⊗ L).d i j ≫ (tensorBraidingComponent K L j).hom := sorry

/-- The braiding isomorphism on cochain complexes. -/
private noncomputable def tensorBraiding
    (K L : Cpx) :
    K ⊗ L ≅ L ⊗ K :=
  HomologicalComplex.Hom.isoOfComponents
    (tensorBraidingComponent K L)
    (tensorBraidingComponentComm K L)

-- Proof sketch: apply the faithful forgetful functor from cochain complexes to graded objects.
-- Under this functor, the complex-level braiding is exactly the graded braiding transported across
-- the monoidal comparison isomorphisms `μ`.
/-- The forgetful functor to graded objects sends the complex-level braiding to the graded
braiding. -/
private lemma forget_map_tensorBraiding
    (K L : Cpx) :
    Functor.LaxMonoidal.μ forgetGraded K L ≫
      forgetGraded.map (tensorBraiding K L).hom =
      (β_ _ _).hom ≫
        Functor.LaxMonoidal.μ forgetGraded L K := sorry

/-- The braided monoidal structure on cochain complexes induced from the graded symmetry. -/
noncomputable instance : BraidedCategory Cpx :=
  BraidedCategory.ofFaithful (C := Cpx) (D := GradedObject ℤ C)
    (HomologicalComplex.forget C (up ℤ))
    tensorBraiding
    forget_map_tensorBraiding

/-- The forgetful functor from cochain complexes to graded objects is braided for the tensor
symmetry on complexes. -/
noncomputable instance : (HomologicalComplex.forget C (up ℤ)).Braided where
  braided := forget_map_tensorBraiding

/-- The canonical symmetric monoidal structure on cochain complexes extending the totalized
tensor product. -/
noncomputable instance : SymmetricCategory Cpx :=
  SymmetricCategory.ofFaithful (C := Cpx) (D := GradedObject ℤ C)
    (HomologicalComplex.forget C (up ℤ))

end

section

variable {R : Type u} [CommRing R]

/- Lemma 15.58.1: the category of cochain complexes of `R`-modules is a symmetric monoidal
category for the tensor product given by the total complex of the pointwise tensor product. -/
example : SymmetricCategory (CochainComplex (ModuleCat R) ℤ) := inferInstance

end
