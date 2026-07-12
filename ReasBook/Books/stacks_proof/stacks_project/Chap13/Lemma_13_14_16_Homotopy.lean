import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

namespace Functor

open ComplexShape

section

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
  [Preadditive A] [Preadditive B] [Preadditive C]

/- Domain-style sampling for the homotopy companions of Lemma 13.14.16:
- primary domain: additive functors on homotopy categories of cochain complexes;
- sampled owner declarations:
  `Functor.mapHomotopyCategory`,
  `NatTrans.mapHomotopyCategory`,
  `Iso.hom_inv_id`,
  `Iso.inv_hom_id`;
- best owner abstraction: these are `bridge/view` utilities relating functor composition and
  natural isomorphisms to the induced functors on homotopy categories. They should live in a
  light owner file because later chapter files use them independently of the derived-comparison
  morphisms from Lemma `13.14.16`;
- primitive data: additive functors `F`, `G` and a natural isomorphism `e`;
- derived API: `mapHomotopyCategoryCompIso` and `mapHomotopyCategoryIso`.

Source/core/bridge triage:
- `source-facing`: none; this file only provides reusable homotopy-category transport bridges;
- `core/canonical`: `Functor.mapHomotopyCategory` and `NatTrans.mapHomotopyCategory`;
- `bridge/view`: the two canonical comparison isomorphisms below. -/

/-- Helper for Chap13 Lemma 13 14 16 Homotopy: the induced functors of a composite additive
functor and of the iterated induced functors agree on each object. -/
private theorem mapHomotopyCategoryComp_obj_eq
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    ∀ (K : HomotopyCategory A (up ℤ)),
      ((F ⋙ G).mapHomotopyCategory (up ℤ)).obj K =
        (F.mapHomotopyCategory (up ℤ) ⋙ G.mapHomotopyCategory (up ℤ)).obj K := by
  rintro ⟨K⟩
  -- Reduce to representatives in the quotient model of the homotopy category.
  rfl

/-- Helper for Chap13 Lemma 13 14 16 Homotopy: the induced functors of a composite additive
functor and of the iterated induced functors agree on each morphism. -/
private theorem mapHomotopyCategoryComp_map_eq
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    ∀ ⦃K L : HomotopyCategory A (up ℤ)⦄ (φ : K ⟶ L),
      ((F ⋙ G).mapHomotopyCategory (up ℤ)).map φ =
        (F.mapHomotopyCategory (up ℤ) ⋙ G.mapHomotopyCategory (up ℤ)).map φ := by
  rintro ⟨K⟩ ⟨L⟩ ⟨φ⟩
  -- Reduce to representatives in the quotient model of the homotopy category.
  rfl

private theorem mapHomotopyCategoryComp_hom_naturality
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    ∀ ⦃K L : HomotopyCategory A (up ℤ)⦄ (φ : K ⟶ L),
      ((F ⋙ G).mapHomotopyCategory (up ℤ)).map φ ≫
          𝟙 (((F ⋙ G).mapHomotopyCategory (up ℤ)).obj L) =
        𝟙 (((F ⋙ G).mapHomotopyCategory (up ℤ)).obj K) ≫
          (F.mapHomotopyCategory (up ℤ) ⋙ G.mapHomotopyCategory (up ℤ)).map φ := by
  intro K L φ
  -- Route correction: rewrite the quotient-lift map to the iterated induced map first.
  rw [mapHomotopyCategoryComp_map_eq F G φ]
  -- Once the maps agree, naturality is just cancellation of identity components.
  simp only [Category.id_comp, Category.comp_id]

private theorem mapHomotopyCategoryComp_inv_naturality
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    ∀ ⦃K L : HomotopyCategory A (up ℤ)⦄ (φ : K ⟶ L),
      (F.mapHomotopyCategory (up ℤ) ⋙ G.mapHomotopyCategory (up ℤ)).map φ ≫
          𝟙 (((F ⋙ G).mapHomotopyCategory (up ℤ)).obj L) =
        𝟙 (((F ⋙ G).mapHomotopyCategory (up ℤ)).obj K) ≫
          ((F ⋙ G).mapHomotopyCategory (up ℤ)).map φ := by
  intro K L φ
  -- Reuse the forward naturality statement after identifying the two induced maps.
  simpa only [mapHomotopyCategoryComp_map_eq F G φ] using
    (mapHomotopyCategoryComp_hom_naturality F G φ)

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
  ext K
  -- Evaluate both natural transformations at `K`; only identities remain.
  simpa only [mapHomotopyCategoryCompHom, mapHomotopyCategoryCompInv, NatTrans.comp_app,
    NatTrans.id_app] using
    (Category.id_comp (𝟙 (((F ⋙ G).mapHomotopyCategory (up ℤ)).obj K)))

private theorem mapHomotopyCategoryComp_inv_hom_id
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    mapHomotopyCategoryCompInv F G ≫ mapHomotopyCategoryCompHom F G =
      𝟙 (F.mapHomotopyCategory (up ℤ) ⋙ G.mapHomotopyCategory (up ℤ)) := by
  ext K
  -- Evaluate both natural transformations at `K` and rewrite the target object spelling.
  simpa only [mapHomotopyCategoryCompHom, mapHomotopyCategoryCompInv, NatTrans.comp_app,
    NatTrans.id_app, mapHomotopyCategoryComp_obj_eq F G K] using
    (Category.id_comp (𝟙 (((F ⋙ G).mapHomotopyCategory (up ℤ)).obj K)))

/-- Chap13 Lemma 13 14 16 Homotopy: applying `mapHomotopyCategory` to a composite additive
functor is canonically isomorphic to composing the induced functors on homotopy categories. -/
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

end

end Functor

end CategoryTheory
