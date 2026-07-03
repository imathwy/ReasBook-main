import Mathlib
import stacks_project.Chap13.Remark_13_10_9
import stacks_project.Chap15.Lemma_15_58_1

-- Declarations for this item will be appended below by the statement pipeline.

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
