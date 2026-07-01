import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

namespace Functor

open ComplexShape

section

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]

/- Domain-style sampling for Lemma 13.14.16:
- primary domain: comparison morphisms for compositions of total left/right derived functors along
  localization functors;
- sampled owner declarations:
  `Functor.totalRightDerived`,
  `Functor.totalLeftDerived`,
  `Functor.rightDerivedDesc` / `Functor.rightDerived_fac`,
  `Functor.leftDerivedLift` / `Functor.leftDerived_fac`;
- best owner abstraction: the canonical owner is the comparison morphism itself in the
  `CategoryTheory.Functor` namespace, built from the universal property of the total derived
  functor. The localization classes are primitive owner parameters and should therefore be
  explicit in the public API instead of being hidden behind `@...` call sites.

Source/core/bridge triage:
- `source-facing`: the textbook comparison maps `R(G ∘ F) ⟶ RG ∘ RF'` and `LG ∘ LF' ⟶ L(G ∘ F)`;
- `core/canonical`: `Functor.totalRightDerived`, `Functor.totalLeftDerived`, and their universal
  morphisms `rightDerivedDesc` / `leftDerivedLift`;
- `bridge/view`: the two factorization lemmas, which expose the defining universal-property
  equations of the comparison morphisms.

Primitive data:
- the localization classes `S` on `A` and `S'` on `B`,
- the functors `F : A ⥤ B` and `G : B ⥤ C`,
- the three derived-functor existence instances needed to form the comparison.

Derived API:
- `rightDerivedCompComparison_fac`,
- `leftDerivedCompComparison_fac`.
-/

section Right

variable (S : MorphismProperty A) (S' : MorphismProperty B) (F : A ⥤ B) (G : B ⥤ C)
variable [(F ⋙ G).HasRightDerivedFunctor S]
variable [(F ⋙ S'.Q).HasRightDerivedFunctor S]
variable [G.HasRightDerivedFunctor S']

local notation "RF₁" => totalRightDerived (F ⋙ S'.Q) S.Q S
local notation "RG" => totalRightDerived G S'.Q S'
local notation "RGF" => totalRightDerived (F ⋙ G) S.Q S
local notation "α₁" => totalRightDerivedUnit (F ⋙ S'.Q) S.Q S
local notation "αG" => totalRightDerivedUnit G S'.Q S'
local notation "αGF" => totalRightDerivedUnit (F ⋙ G) S.Q S

/-- Lemma 13.14.16 (1): let `F' : A ⥤ S'⁻¹B` be the composite `F ⋙ S'.Q`. If the right derived
functors of `F'`, `G`, and `G ∘ F` are everywhere defined, then there is a canonical natural
transformation `R(G ∘ F) ⟶ RG ∘ RF'`. -/
noncomputable def rightDerivedCompComparison :
    RGF ⟶ RF₁ ⋙ RG :=
  rightDerivedDesc RGF αGF S (RF₁ ⋙ RG)
    (whiskerLeft F αG ≫
      (associator F S'.Q RG).hom ≫
      whiskerRight α₁ RG ≫
      (associator S.Q RF₁ RG).hom)

-- Proof sketch: this is the standard `rightDerived_fac` identity for the comparison morphism
-- defined via `rightDerivedDesc`.
/-- The right-derived comparison morphism factors the canonical unit of `R(G ∘ F)` through the
iterated right derived functor `RG ∘ RF'`. -/
@[reassoc]
theorem rightDerivedCompComparison_fac :
    αGF ≫ whiskerLeft S.Q (rightDerivedCompComparison S S' F G) =
      whiskerLeft F αG ≫
        (associator F S'.Q RG).hom ≫
        whiskerRight α₁ RG ≫
        (associator S.Q RF₁ RG).hom := by
  simpa [rightDerivedCompComparison] using
    (rightDerived_fac RGF αGF S (RF₁ ⋙ RG)
      (whiskerLeft F αG ≫
        (associator F S'.Q RG).hom ≫
        whiskerRight α₁ RG ≫
        (associator S.Q RF₁ RG).hom))

attribute [simp] rightDerivedCompComparison_fac rightDerivedCompComparison_fac_assoc

end Right

section Left

variable (S : MorphismProperty A) (S' : MorphismProperty B) (F : A ⥤ B) (G : B ⥤ C)
variable [(F ⋙ G).HasLeftDerivedFunctor S]
variable [(F ⋙ S'.Q).HasLeftDerivedFunctor S]
variable [G.HasLeftDerivedFunctor S']

local notation "LF₁" => totalLeftDerived (F ⋙ S'.Q) S.Q S
local notation "LG" => totalLeftDerived G S'.Q S'
local notation "LGF" => totalLeftDerived (F ⋙ G) S.Q S
local notation "β₁" => totalLeftDerivedCounit (F ⋙ S'.Q) S.Q S
local notation "βG" => totalLeftDerivedCounit G S'.Q S'
local notation "βGF" => totalLeftDerivedCounit (F ⋙ G) S.Q S

/-- Lemma 13.14.16 (2): let `F' : A ⥤ S'⁻¹B` be the composite `F ⋙ S'.Q`. If the left derived
functors of `F'`, `G`, and `G ∘ F` are everywhere defined, then there is a canonical natural
transformation `LG ∘ LF' ⟶ L(G ∘ F)`, written in Lean as
`LF' ⋙ LG ⟶ L(F ⋙ G)`. -/
noncomputable def leftDerivedCompComparison :
    LF₁ ⋙ LG ⟶ LGF :=
  leftDerivedLift LGF βGF S (LF₁ ⋙ LG)
    ((associator S.Q LF₁ LG).inv ≫
      whiskerRight β₁ LG ≫
      (associator F S'.Q LG).hom ≫
      whiskerLeft F βG)

-- Proof sketch: this is the standard `leftDerived_fac` identity for the comparison morphism
-- defined via `leftDerivedLift`.
/-- The left-derived comparison morphism factors the counit of the iterated left derived functor
through the canonical counit of `L(G ∘ F)`. -/
@[reassoc]
theorem leftDerivedCompComparison_fac :
    whiskerLeft S.Q (leftDerivedCompComparison S S' F G) ≫
      βGF =
        (associator S.Q LF₁ LG).inv ≫
          whiskerRight β₁ LG ≫
          (associator F S'.Q LG).hom ≫
          whiskerLeft F βG := by
  simpa [leftDerivedCompComparison] using
    (leftDerived_fac LGF βGF S (LF₁ ⋙ LG)
      ((associator S.Q LF₁ LG).inv ≫
        whiskerRight β₁ LG ≫
        (associator F S'.Q LG).hom ≫
        whiskerLeft F βG))

attribute [simp] leftDerivedCompComparison_fac leftDerivedCompComparison_fac_assoc

end Left

section Homotopy

variable [Preadditive A] [Preadditive B] [Preadditive C]

private theorem mapHomotopyCategoryComp_hom_naturality
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    ∀ ⦃K L : HomotopyCategory A (up ℤ)⦄ (φ : K ⟶ L),
      ((F ⋙ G).mapHomotopyCategory (up ℤ)).map φ ≫
          𝟙 (((F ⋙ G).mapHomotopyCategory (up ℤ)).obj L) =
        𝟙 (((F ⋙ G).mapHomotopyCategory (up ℤ)).obj K) ≫
          (F.mapHomotopyCategory (up ℤ) ⋙ G.mapHomotopyCategory (up ℤ)).map φ := by
  sorry

private theorem mapHomotopyCategoryComp_inv_naturality
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    ∀ ⦃K L : HomotopyCategory A (up ℤ)⦄ (φ : K ⟶ L),
      (F.mapHomotopyCategory (up ℤ) ⋙ G.mapHomotopyCategory (up ℤ)).map φ ≫
          𝟙 (((F ⋙ G).mapHomotopyCategory (up ℤ)).obj L) =
        𝟙 (((F ⋙ G).mapHomotopyCategory (up ℤ)).obj K) ≫
          ((F ⋙ G).mapHomotopyCategory (up ℤ)).map φ := by
  sorry

private abbrev mapHomotopyCategoryCompHom
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    (F ⋙ G).mapHomotopyCategory (up ℤ) ⟶
      F.mapHomotopyCategory (up ℤ) ⋙ G.mapHomotopyCategory (up ℤ) :=
  NatTrans.mk
    (fun K ↦ 𝟙 (((F ⋙ G).mapHomotopyCategory (up ℤ)).obj K))
    (mapHomotopyCategoryComp_hom_naturality F G)

private abbrev mapHomotopyCategoryCompInv
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    F.mapHomotopyCategory (up ℤ) ⋙ G.mapHomotopyCategory (up ℤ) ⟶
      (F ⋙ G).mapHomotopyCategory (up ℤ) :=
  NatTrans.mk
    (fun K ↦ 𝟙 (((F ⋙ G).mapHomotopyCategory (up ℤ)).obj K))
    (mapHomotopyCategoryComp_inv_naturality F G)

private theorem mapHomotopyCategoryComp_hom_inv_id
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    mapHomotopyCategoryCompHom F G ≫ mapHomotopyCategoryCompInv F G =
      𝟙 ((F ⋙ G).mapHomotopyCategory (up ℤ)) := by
  sorry

private theorem mapHomotopyCategoryComp_inv_hom_id
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    mapHomotopyCategoryCompInv F G ≫ mapHomotopyCategoryCompHom F G =
      𝟙 (F.mapHomotopyCategory (up ℤ) ⋙ G.mapHomotopyCategory (up ℤ)) := by
  sorry

/-- Applying `mapHomotopyCategory` to a composite additive functor is canonically isomorphic to
composing the induced functors on homotopy categories. -/
noncomputable def mapHomotopyCategoryCompIso
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    (F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        G.mapHomotopyCategory (ComplexShape.up ℤ) where
  hom := mapHomotopyCategoryCompHom F G
  inv := mapHomotopyCategoryCompInv F G
  hom_inv_id := mapHomotopyCategoryComp_hom_inv_id F G
  inv_hom_id := mapHomotopyCategoryComp_inv_hom_id F G

/-- Applying `mapHomotopyCategory` to a natural isomorphism of additive functors yields the
corresponding isomorphism on homotopy categories. -/
noncomputable def mapHomotopyCategoryIso
    {F G : A ⥤ B} [F.Additive] [G.Additive] (e : F ≅ G) :
    F.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      G.mapHomotopyCategory (ComplexShape.up ℤ) where
  hom := NatTrans.mapHomotopyCategory e.hom (up ℤ)
  inv := NatTrans.mapHomotopyCategory e.inv (up ℤ)
  hom_inv_id := by
    rw [← NatTrans.mapHomotopyCategory_comp]
    simpa using
      congrArg (fun α ↦ NatTrans.mapHomotopyCategory α (up ℤ)) (Iso.hom_inv_id e)
  inv_hom_id := by
    rw [← NatTrans.mapHomotopyCategory_comp]
    simpa using
      congrArg (fun α ↦ NatTrans.mapHomotopyCategory α (up ℤ)) (Iso.inv_hom_id e)

end Homotopy

end

end Functor

end CategoryTheory
