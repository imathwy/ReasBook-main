import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Homology.BifunctorFlip
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.GradedObject.Braiding
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex MonoidalCategory

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

/- Domain-style sampling for Lemma 15.58.1:
- primary domain: symmetric monoidal structures on cochain complexes, with tensor symmetry given
  by the canonical total-complex flip;
- sampled owner declarations:
  `mapBifunctorFlipIso`,
  `mapBifunctorFlipIso_hom_naturality`,
  `BraidedCategory.curriedBraidingNatIso`,
  `HomologicalComplex₂.total.mapIso`,
  `BraidedCategory`,
  `SymmetricCategory`;
- best owner abstraction: the public owner layer is the braided/symmetric typeclass structure on
  cochain complexes; the concrete bridge data are the total-complex flip
  `mapBifunctorFlipIso` and the pointwise tensor braiding induced from
  `BraidedCategory.curriedBraidingNatIso`;
- primitive vs derived:
  primitive data are the pointwise braiding on bicomplexes and the total-complex flip;
  the braided and symmetric instances on cochain complexes are derived packaging;
- source/core/bridge triage:
  `source-facing`: the symmetric monoidal structure on cochain complexes from the Stacks lemma;
  `core/canonical`: the typeclass owners `BraidedCategory` and `SymmetricCategory`;
  `bridge/view`: the bicomplex pointwise braiding and the canonical flip
  `mapBifunctorFlipIso _ _ (curriedTensor C) (up ℤ)`.
-/

private abbrev forgetGraded : Cpx ⥤ GradedObject ℤ C :=
  HomologicalComplex.forget C (up ℤ)

private noncomputable def tensorBraidingGradedIso
    (K L : Cpx) :
    forgetGraded.obj (K ⊗ L) ≅ forgetGraded.obj (L ⊗ K) :=
  (Functor.Monoidal.μIso forgetGraded K L).symm ≪≫
    β_ _ _ ≪≫
    Functor.Monoidal.μIso forgetGraded L K

private noncomputable abbrev tensorBraidingComponent
    (K L : Cpx) (n : ℤ) :
    (K ⊗ L).X n ≅ (L ⊗ K).X n :=
  (GradedObject.eval n).mapIso (tensorBraidingGradedIso K L)

private lemma tensorBraidingComponentComm
    (K L : Cpx) (i j : ℤ) (h : (up ℤ).Rel i j) :
    (tensorBraidingComponent K L i).hom ≫ (L ⊗ K).d i j =
      (K ⊗ L).d i j ≫ (tensorBraidingComponent K L j).hom := by
  sorry

/-- Implementation bridge for `BraidedCategory.ofFaithful`; the public braiding on cochain
complexes is the canonical `β_`. -/
private noncomputable def tensorBraiding
    (K L : Cpx) :
    K ⊗ L ≅ L ⊗ K :=
  HomologicalComplex.Hom.isoOfComponents
    (tensorBraidingComponent K L)
    (tensorBraidingComponentComm K L)

private lemma forget_map_tensorBraiding
    (K L : Cpx) :
    Functor.LaxMonoidal.μ forgetGraded K L ≫
      forgetGraded.map (tensorBraiding K L).hom =
      (β_ _ _).hom ≫
        Functor.LaxMonoidal.μ forgetGraded L K := by
  sorry

/-- The canonical symmetric monoidal structure on cochain complexes extending the totalized
tensor product. -/
noncomputable instance cochainComplexSymmetricCategory : SymmetricCategory Cpx :=
  letI : BraidedCategory Cpx :=
    BraidedCategory.ofFaithful forgetGraded
      tensorBraiding
      forget_map_tensorBraiding
  letI : (HomologicalComplex.forget C (up ℤ)).Braided :=
    { braided := forget_map_tensorBraiding }
  SymmetricCategory.ofFaithful forgetGraded

end

section

variable {R : Type u} [CommRing R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

/- Lemma 15.58.1 for `R`-modules is the canonical specialization of the chapter owner
`SymmetricCategory (CochainComplex C ℤ)`. The `ModuleCat` colimit and closed-monoidal owner
instances discharge the graded tensor side conditions automatically, so no local compatibility
instances or duplicate specialized wrapper are needed here. -/
#synth SymmetricCategory Cpx

end
