import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.Localization
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.Localization.Monoidal.Braided
import Mathlib.CategoryTheory.Monoidal.Preadditive

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_58_1 (from Chap15) -/
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

/-! ### Lemma_15_58_2 (from Chap15) -/
/- Domain-style sampling for Lemma 15.58.2:
- primary domain: homotopy transport along totalized tensor-product maps for cochain complexes;
- sampled owner declarations:
  `HomologicalComplex.mapBifunctorMapHomotopy₁`,
  `Functor.map₂CochainComplex`,
  `Functor.mapHomotopyCategory`;
- best owner abstraction: the core/canonical owner is
  `HomologicalComplex.mapBifunctorMapHomotopy₁`, while the induced homotopy-category functor is
  the canonical owner `((tensor.map₂CochainComplex).flip.obj Y).mapHomotopyCategory (up ℤ)`;
- source/core/bridge triage:
  `source-facing`: the fixed-right-factor tensor homotopy statement from the text;
  `core/canonical`: `HomologicalComplex.mapBifunctorMapHomotopy₁`,
    `Functor.mapHomotopyCategory`;
  `bridge/view`: none;
- layer: `bridge/view`; Lemma 15.58.2 is only the `ModuleCat R` tensor specialization of the
  canonical homotopy-transport statement, so the refined file should reuse the upstream owner
  directly rather than keep a second public definition with the same interface;
- primitive data: a bilinear bifunctor, a fixed right complex, and a homotopy in the varying left
  complex;
- derived API: the induced morphisms on totalized tensor products and their transported homotopy
  are already provided by the sampled owners above.
-/

/- Lemma 15.58.2: for the totalized tensor product with a fixed right factor, a homotopy
`α ∼ β` in the varying left complex induces a homotopy between the corresponding totalized tensor
maps. This is exactly the canonical owner `HomologicalComplex.mapBifunctorMapHomotopy₁`,
specialized in applications to `curriedTensor (ModuleCat R)`. -/
#check HomologicalComplex.mapBifunctorMapHomotopy₁

/-! ### Lemma_15_58_3 (from Chap15) -/
/- Domain-style sampling for Lemma 15.58.3:
- primary domain: monoidal and symmetric monoidal structures on the homotopy category of cochain
  complexes, induced from the totalized tensor product on complexes;
- sampled owner declarations:
  `tensor_right_homotopy_functor`,
  `tensor_left_homotopy_functor`,
  `MonoidalCategory`,
  `SymmetricCategory`;
- best owner abstraction: the source-facing goal is a `SymmetricCategory` instance on
  `HomotopyCategory (ModuleCat R) (up ℤ)`, while the primitive homotopy-descent data for the
  whiskering maps is already canonically owned by the Chapter 13 functors
  `tensor_right_homotopy_functor (curriedTensor (ModuleCat R))` and
  `tensor_left_homotopy_functor (curriedTensor (ModuleCat R))`;
- primitive vs derived:
  primitive data are the monoidal tensor product on cochain complexes from Lemma `15.58.1` and
  the two fixed-factor tensor functors on the homotopy category;
  whiskering maps, tensor-hom identities, braiding, and the symmetric-category instance are
  derived API;
- source/core/bridge triage:
  `source-facing`: the symmetric monoidal structure on `K(R)`;
  `core/canonical`: the typeclass owners `MonoidalCategory`, `BraidedCategory`, and
  `SymmetricCategory`;
  `bridge/view`: the Chapter 13 tensor homotopy functors giving the canonical descent of fixed
  left/right tensoring to the homotopy category;
- layer: this file is the `source-facing` owner for the monoidal structure on `K(R)`, but its
  whiskering primitives should be expressed through the existing Chapter 13 bridge rather than by
  duplicating a parallel raw-quotient congruence API.
-/

open CategoryTheory ComplexShape HomotopyCategory MonoidalCategory

noncomputable section

universe u

variable {R : Type u} [CommRing R]

local notation "Complexes" => CochainComplex (ModuleCat R) ℤ
local notation "HomotopyComplexes" => HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ)
local notation "homotopyQuotient" =>
  HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)
local notation "tensor" => curriedTensor (ModuleCat R)
local notation "tensorRight" => tensor_right_homotopy_functor tensor
local notation "tensorLeft" => tensor_left_homotopy_functor tensor

/-- The tensor-product object on the homotopy category of complexes of `R`-modules. -/
private noncomputable instance homotopyCategory_moduleCat_monoidalStruct :
    MonoidalCategoryStruct HomotopyComplexes where
  tensorObj X Y := (homotopyQuotient).obj (X.as ⊗ Y.as)
  whiskerLeft X {_ _} f := (tensorRight X.as).map f
  whiskerRight {_ _} f Y := (tensorLeft Y.as).map f
  tensorUnit := (homotopyQuotient).obj (𝟙_ Complexes)
  associator X Y Z := (homotopyQuotient).mapIso (α_ X.as Y.as Z.as)
  leftUnitor X := (homotopyQuotient).mapIso (λ_ X.as)
  rightUnitor X := (homotopyQuotient).mapIso (ρ_ X.as)

-- Proof sketch: expand `tensorHom` using the quotient representatives of the two whiskering maps
-- and compare with the class of the pointwise tensor product map on complexes.
/-- The tensor product of morphisms in the homotopy category is represented by the tensor product
of the underlying chain maps. -/
private theorem homotopyCategory_tensorHom_def
    {X₁ Y₁ X₂ Y₂ : HomotopyComplexes} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ⊗ₘ g = (f ▷ X₂) ≫ (Y₁ ◁ g) := sorry

-- Proof sketch: reduce to representatives in the quotient hom-sets and apply the identity law for
-- tensoring morphisms of cochain complexes.
/-- Tensoring identity morphisms is the identity in the homotopy category. -/
private theorem homotopyCategory_id_tensorHom_id
    (X Y : HomotopyComplexes) :
    (𝟙 X) ⊗ₘ (𝟙 Y) = 𝟙 (X ⊗ Y) := sorry

-- Proof sketch: pass to representatives and use the functoriality of tensoring morphisms of
-- complexes; then descend the resulting equality to the quotient.
/-- Tensoring morphisms in the homotopy category is compatible with composition. -/
private theorem homotopyCategory_tensorHom_comp_tensorHom
    {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : HomotopyComplexes}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂) := sorry

-- Proof sketch: left whiskering is the map of the Chapter 13 functor
-- `tensor_right_homotopy_functor (curriedTensor (ModuleCat R)) X.as`, which sends identities to
-- identities.
/-- Left whiskering by a fixed object sends identity morphisms to identities in the homotopy
category. -/
private theorem homotopyCategory_whiskerLeft_id
    (X Y : HomotopyComplexes) :
    X ◁ (𝟙 Y) = 𝟙 (X ⊗ Y) := sorry

-- Proof sketch: right whiskering is the map of the Chapter 13 functor
-- `tensor_left_homotopy_functor (curriedTensor (ModuleCat R)) Y.as`, which preserves identities.
/-- Right whiskering by a fixed object sends identity morphisms to identities in the homotopy
category. -/
private theorem homotopyCategory_id_whiskerRight
    (X Y : HomotopyComplexes) :
    (𝟙 X) ▷ Y = 𝟙 (X ⊗ Y) := sorry

-- Proof sketch: the associator on the homotopy category is the image of the complex associator,
-- so naturality descends directly from the monoidal structure on cochain complexes.
/-- The associator of the homotopy-category tensor product is natural. -/
private theorem homotopyCategory_associator_naturality
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : HomotopyComplexes}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom =
      (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) := sorry

-- Proof sketch: apply the quotient functor to the naturality of the left unitor on cochain
-- complexes.
/-- The left unitor of the homotopy-category tensor product is natural. -/
private theorem homotopyCategory_leftUnitor_naturality
    {X Y : HomotopyComplexes} (f : X ⟶ Y) :
    ((𝟙_ HomotopyComplexes) ◁ f) ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := sorry

-- Proof sketch: apply the quotient functor to the naturality of the right unitor on cochain
-- complexes.
/-- The right unitor of the homotopy-category tensor product is natural. -/
private theorem homotopyCategory_rightUnitor_naturality
    {X Y : HomotopyComplexes} (f : X ⟶ Y) :
    (f ▷ (𝟙_ HomotopyComplexes)) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := sorry

-- Proof sketch: the pentagon identity holds on cochain complexes, and the quotient functor
-- preserves the composites appearing in the pentagon diagram.
/-- The associator on the homotopy-category tensor product satisfies the pentagon identity. -/
private theorem homotopyCategory_pentagon
    (W X Y Z : HomotopyComplexes) :
    ((α_ W X Y).hom ▷ Z) ≫ (α_ W (X ⊗ Y) Z).hom ≫ (W ◁ (α_ X Y Z).hom) =
      (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom := sorry

-- Proof sketch: the triangle identity is inherited from the tensor product on cochain complexes
-- by applying the quotient functor to the standard triangle diagram.
/-- The unitors and associator on the homotopy-category tensor product satisfy the triangle
identity. -/
private theorem homotopyCategory_triangle
    (X Y : HomotopyComplexes) :
    (α_ X (𝟙_ HomotopyComplexes) Y).hom ≫ (X ◁ (λ_ Y).hom) =
      (ρ_ X).hom ▷ Y := sorry

/-- The monoidal structure on the homotopy category of complexes of `R`-modules induced by the
totalized tensor product of complexes. -/
noncomputable instance homotopyCategory_moduleCat_monoidal_category :
    MonoidalCategory HomotopyComplexes where
  tensorHom_def := homotopyCategory_tensorHom_def
  id_tensorHom_id := homotopyCategory_id_tensorHom_id
  tensorHom_comp_tensorHom := homotopyCategory_tensorHom_comp_tensorHom
  whiskerLeft_id := homotopyCategory_whiskerLeft_id
  id_whiskerRight := homotopyCategory_id_whiskerRight
  associator_naturality := homotopyCategory_associator_naturality
  leftUnitor_naturality := homotopyCategory_leftUnitor_naturality
  rightUnitor_naturality := homotopyCategory_rightUnitor_naturality
  pentagon := homotopyCategory_pentagon
  triangle := homotopyCategory_triangle

/-- The braiding isomorphism on the homotopy category of complexes of `R`-modules. -/
private noncomputable def homotopyCategory_tensor_braiding
    (X Y : HomotopyComplexes) :
    X ⊗ Y ≅ Y ⊗ X :=
  (homotopyQuotient).mapIso (β_ X.as Y.as)

-- Proof sketch: the braiding is the quotient of the complex-level symmetry, so right naturality
-- follows by applying the quotient functor to the corresponding naturality identity for complexes.
/-- The tensor braiding on the homotopy category is natural in the right variable. -/
private theorem homotopyCategory_tensor_braiding_naturality_right
    (X : HomotopyComplexes) {Y Z : HomotopyComplexes} (f : Y ⟶ Z) :
    (X ◁ f) ≫ (homotopyCategory_tensor_braiding X Z).hom =
      (homotopyCategory_tensor_braiding X Y).hom ≫ (f ▷ X) := sorry

-- Proof sketch: the braiding is the quotient of the complex-level symmetry, so left naturality
-- is inherited from the corresponding naturality identity on complexes.
/-- The tensor braiding on the homotopy category is natural in the left variable. -/
private theorem homotopyCategory_tensor_braiding_naturality_left
    {X Y : HomotopyComplexes} (f : X ⟶ Y) (Z : HomotopyComplexes) :
    (f ▷ Z) ≫ (homotopyCategory_tensor_braiding Y Z).hom =
      (homotopyCategory_tensor_braiding X Z).hom ≫ (Z ◁ f) := sorry

-- Proof sketch: apply the quotient functor to the forward hexagon identity for the complex-level
-- tensor symmetry and use the quotient descriptions of associators and whiskering.
/-- The tensor braiding on the homotopy category satisfies the forward hexagon identity. -/
private theorem homotopyCategory_tensor_hexagon_forward
    (X Y Z : HomotopyComplexes) :
    (α_ X Y Z).hom ≫ (homotopyCategory_tensor_braiding X (Y ⊗ Z)).hom ≫
        (α_ Y Z X).hom =
      ((homotopyCategory_tensor_braiding X Y).hom ▷ Z) ≫
        (α_ Y X Z).hom ≫
          (Y ◁ (homotopyCategory_tensor_braiding X Z).hom) := sorry

-- Proof sketch: apply the quotient functor to the reverse hexagon identity for the complex-level
-- tensor symmetry and then rewrite the quotient images of the structural morphisms.
/-- The tensor braiding on the homotopy category satisfies the reverse hexagon identity. -/
private theorem homotopyCategory_tensor_hexagon_reverse
    (X Y Z : HomotopyComplexes) :
    (α_ X Y Z).inv ≫ (homotopyCategory_tensor_braiding (X ⊗ Y) Z).hom ≫
        (α_ Z X Y).inv =
      (X ◁ (homotopyCategory_tensor_braiding Y Z).hom) ≫
        (α_ X Z Y).inv ≫
          ((homotopyCategory_tensor_braiding X Z).hom ▷ Y) := sorry

/-- The braided monoidal structure on the homotopy category of complexes of `R`-modules. -/
private noncomputable instance homotopyCategory_moduleCat_braided_category :
    BraidedCategory HomotopyComplexes where
  braiding := homotopyCategory_tensor_braiding
  braiding_naturality_right := homotopyCategory_tensor_braiding_naturality_right
  braiding_naturality_left := homotopyCategory_tensor_braiding_naturality_left
  hexagon_forward := homotopyCategory_tensor_hexagon_forward
  hexagon_reverse := homotopyCategory_tensor_hexagon_reverse

-- Proof sketch: the quotient braiding is induced from the involutive symmetry on complexes, so
-- the composite of the braiding with its reverse is the image of the identity.
/-- The tensor braiding on the homotopy category is involutive. -/
private theorem homotopyCategory_tensor_symmetry
    (X Y : HomotopyComplexes) :
    (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y) := sorry

/-- Lemma 15.58.3: the homotopy category `K(R)` of complexes of `R`-modules is a symmetric
monoidal category for the tensor product given by totalizing the pointwise tensor product of
complexes. -/
noncomputable instance homotopyCategory_moduleCat_symmetric_category :
    SymmetricCategory HomotopyComplexes where
  symmetry := homotopyCategory_tensor_symmetry

/-! ### Lemma_15_58_3_Internal (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open HomologicalComplex
open HomotopyCategory
open MonoidalCategory
open ModuleCat.MonoidalCategory

noncomputable section

set_option checkBinderAnnotations false

universe u

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Complexes" => CochainComplex (ModuleCat R) ℤ
local notation "KMod" => HomotopyCategory (ModuleCat R) (up ℤ)
local notation "Qh" =>
  (HomotopyCategory.quotient (ModuleCat R) (up ℤ) : Complexes ⥤ KMod)
local notation "Qis" =>
  (HomologicalComplex.homotopyEquivalences (ModuleCat R) (up ℤ) :
    MorphismProperty Complexes)

private noncomputable abbrev homotopyQuotientUnitIso :
    (Qh : Complexes ⥤ KMod).obj (MonoidalCategoryStruct.tensorUnit Complexes) ≅
      (Qh : Complexes ⥤ KMod).obj (MonoidalCategoryStruct.tensorUnit Complexes) :=
  Iso.refl _

local instance : HasBinaryBiproducts (ModuleCat R) := inferInstance
local instance : SymmetricCategory Complexes := cochainComplexSymmetricCategory

private theorem homotopyEquivalences_isMonoidal :
    MorphismProperty.IsMonoidal (C := Complexes) Qis := by
  sorry

local instance : MorphismProperty.IsMonoidal (C := Complexes) Qis :=
  homotopyEquivalences_isMonoidal

local instance : Functor.IsLocalization Qh Qis :=
  (ComplexShape.up ℤ).quotient_isLocalization
    (fun n ↦ ⟨n - 1, by simp⟩)
    (ModuleCat R)

@[implicit_reducible] noncomputable instance homotopyCategory_moduleCat_monoidalCategory :
    MonoidalCategory KMod := by
  letI : MorphismProperty.IsMonoidal (C := Complexes) Qis :=
    homotopyEquivalences_isMonoidal
  change MonoidalCategory (LocalizedMonoidal Qh Qis homotopyQuotientUnitIso)
  infer_instance

@[implicit_reducible] noncomputable instance homotopyCategory_quotient_monoidal :
    (Qh : Complexes ⥤ KMod).Monoidal := by
  letI : MorphismProperty.IsMonoidal (C := Complexes) Qis :=
    homotopyEquivalences_isMonoidal
  simpa using
    (inferInstance :
      (Localization.Monoidal.toMonoidalCategory
        Qh
        Qis
        homotopyQuotientUnitIso).Monoidal)

@[implicit_reducible] noncomputable instance homotopyCategory_moduleCat_symmetric_category :
    SymmetricCategory KMod := by
  letI : MorphismProperty.IsMonoidal (C := Complexes) Qis :=
    homotopyEquivalences_isMonoidal
  let _ : MonoidalCategory KMod := homotopyCategory_moduleCat_monoidalCategory
  change SymmetricCategory (LocalizedMonoidal Qh Qis homotopyQuotientUnitIso)
  infer_instance

end

end CategoryTheory

/-! ### Lemma_15_58_3_Owner (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open HomologicalComplex
open HomotopyCategory
open MonoidalCategory
open ModuleCat.MonoidalCategory

noncomputable section

set_option checkBinderAnnotations false

universe u

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Complexes" => CochainComplex (ModuleCat R) ℤ
local notation "KMod" => HomotopyCategory (ModuleCat R) (up ℤ)
local notation "Qh" =>
  (HomotopyCategory.quotient (ModuleCat R) (up ℤ) : Complexes ⥤ KMod)
local notation "Qis" =>
  (HomologicalComplex.homotopyEquivalences (ModuleCat R) (up ℤ) :
    MorphismProperty Complexes)

private noncomputable abbrev homotopyQuotientUnitIso :
    (Qh : Complexes ⥤ KMod).obj (MonoidalCategoryStruct.tensorUnit Complexes) ≅
      (Qh : Complexes ⥤ KMod).obj (MonoidalCategoryStruct.tensorUnit Complexes) :=
  Iso.refl _

local instance : HasBinaryBiproducts (ModuleCat R) := inferInstance
local instance : SymmetricCategory Complexes := cochainComplexSymmetricCategory

private theorem homotopyEquivalences_isMonoidal :
    MorphismProperty.IsMonoidal (C := Complexes) Qis := by
  sorry

local instance : MorphismProperty.IsMonoidal (C := Complexes) Qis :=
  homotopyEquivalences_isMonoidal

local instance : Functor.IsLocalization Qh Qis :=
  (ComplexShape.up ℤ).quotient_isLocalization
    (fun n ↦ ⟨n - 1, by simp⟩)
    (ModuleCat R)

@[implicit_reducible] noncomputable instance homotopyCategory_moduleCat_monoidalCategory :
    MonoidalCategory KMod := by
  letI : MorphismProperty.IsMonoidal (C := Complexes) Qis :=
    homotopyEquivalences_isMonoidal
  change MonoidalCategory (LocalizedMonoidal Qh Qis homotopyQuotientUnitIso)
  infer_instance

@[implicit_reducible] noncomputable instance homotopyCategory_quotient_monoidal :
    (Qh : Complexes ⥤ KMod).Monoidal := by
  letI : MorphismProperty.IsMonoidal (C := Complexes) Qis :=
    homotopyEquivalences_isMonoidal
  simpa using
    (inferInstance :
      (Localization.Monoidal.toMonoidalCategory
        Qh
        Qis
        homotopyQuotientUnitIso).Monoidal)

@[implicit_reducible] noncomputable instance homotopyCategory_moduleCat_symmetric_category :
    SymmetricCategory KMod := by
  letI : MorphismProperty.IsMonoidal (C := Complexes) Qis :=
    homotopyEquivalences_isMonoidal
  let _ : MonoidalCategory KMod := homotopyCategory_moduleCat_monoidalCategory
  change SymmetricCategory (LocalizedMonoidal Qh Qis homotopyQuotientUnitIso)
  infer_instance

end

end CategoryTheory

/-! ### Lemma_15_58_4 (from Chap15) -/
open CategoryTheory ComplexShape MonoidalCategory

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable [∀ (K₁ K₂ : CochainComplex (ModuleCat R) ℤ),
  CochainComplex.HasMapBifunctor K₁ K₂ (curriedTensor (ModuleCat R))]

local instance : CategoryTheory.Limits.HasBinaryBiproducts (CochainComplex (ModuleCat R) ℤ) :=
  cochainComplexHasBinaryBiproducts (ModuleCat R)

/- Domain-style sampling for Lemma 15.58.4:
- primary domain: homological algebra of totalized tensor-product functors on homotopy categories
  of cochain complexes;
- sampled owner API:
  `curriedTensor`,
  `Functor.map₂CochainComplex`,
  `Functor.mapHomotopyCategory`,
  `Functor.IsTriangulated`;
- best owner abstraction: the project-level owners for fixed-factor tensoring on homotopy
  categories are the canonical fixed-factor homotopy descents
  `((((curriedTensor (ModuleCat R)).map₂CochainComplex).obj P).mapHomotopyCategory (up ℤ))` and
  `(((((curriedTensor (ModuleCat R)).map₂CochainComplex).flip).obj P).mapHomotopyCategory
    (up ℤ))`,
  and exactness is encoded by `Functor.IsTriangulated`;
- primitive vs derived:
  primitive data are the bilinear tensor bifunctor `curriedTensor (ModuleCat R)` and the fixed
  complex `P`;
  the induced homotopy-category endofunctors and their triangulated structure are derived API
  already provided upstream in Chapter 13 through `Functor.mapHomotopyCategory`, so this file
  should specialize that owner rather than rebuild a parallel public quotient-lift theorem;
- source/core/bridge triage:
  the textbook lemma is source-facing exactness for the two tensor endofunctors on `K(R)`,
  the core/canonical owners are the two fixed-factor tensor homotopy descents above, and the
  declarations below are the thin Chapter 15 specialization recall;
- layer: `bridge/view`, since this file only records the Chapter 15 specialization of the
  Chapter 13 owner instances and introduces no new owner object. -/
variable (P : CochainComplex (ModuleCat R) ℤ)

/- Lemma 15.58.4: for a complex `P^\bullet` of `R`-modules, the endofunctor of `K(R)` given by
`L^\bullet ↦ \mathrm{Tot}(P^\bullet ⊗_R L^\bullet)` is exact. This is the specialized canonical
instance on the fixed-left-factor homotopy descent from Remark `13.10.9`. -/
#check
  (inferInstance :
    ((((curriedTensor (ModuleCat R)).map₂CochainComplex).obj P).mapHomotopyCategory
      (up ℤ)).IsTriangulated)

/- The symmetric fixed-right-factor form in Lemma `15.58.4` is likewise the specialized
canonical `Functor.IsTriangulated` instance on the corresponding homotopy descent. -/
#check
  (inferInstance :
    (((((curriedTensor (ModuleCat R)).map₂CochainComplex).flip).obj P).mapHomotopyCategory
      (up ℤ)).IsTriangulated)

end
