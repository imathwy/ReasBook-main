import Mathlib
import StacksProject_2024.stacks_project.Chap07.Lemma_7_28_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe u v w w'

noncomputable section

section

variable {C : Type u} [Category.{v} C]
variable {A : Type w} [Category.{w'} A]
variable (J : GrothendieckTopology C)
variable {U' U V' V : C}
variable (i : U' ⟶ U) (p : U' ⟶ V') (f : U ⟶ V) (g : V' ⟶ V)

/-
Domain-style sampling for Lemma 7.27.5:
- primary domain: relocalization for slice sites and the induced inverse-image and direct-image functors on
  sheaves;
- sampled owner API:
  `Over.mapComp_eq`,
  `GrothendieckTopology.overMapPullbackComp`,
  `GrothendieckTopology.overMapPullbackCongr`,
  `site_square_direct_image_inverse_image_iso`;
- source-facing layer: the commutative square and base-change statements for relocalization along a
  commutative square in `C`;
- core/canonical layer: the slice functors `Over.map _`, the localized inverse-image owner
  `J.overMapPullback _ _`, and the site-square Beck-Chevalley owner
  `site_square_direct_image_inverse_image_iso`;
- bridge/view layer: clause `(1)` should be organized around the functor-square owner
  `CatCommSq`, with the strict slice-functor equality only as a companion; clauses `(2)` and `(3)`
  are the canonical comparison isomorphisms specialized from those owners rather than any
  strictified local copies.

Primitive data are just the commutative square `i ≫ f = p ≫ g` and, for the base-change part, the
cartesian hypothesis. The source-facing owner for clause `(1)` is the induced `CatCommSq` on slice
functors, while the strict equality of composites is a derived companion. The sheaf-level
comparisons are derived API and should remain at the canonical isomorphism level owned upstream.
-/

/-- The two composites of slice relocalization functors agree for a commutative square. -/
-- Proof sketch: use `Over.mapComp_eq` to identify each composite with the relocalization functor
-- attached to the composite morphism, then rewrite along `hcomm`.
private theorem over_map_square_eq
    (hcomm : i ≫ f = p ≫ g) :
    Over.map i ⋙ Over.map f = Over.map p ⋙ Over.map g := sorry

/-! The file keeps the three clauses of Lemma 7.27.5 as separate atomic declarations. -/

/-- Lemma 7.27.5 (1): the relocalization functors attached to a commutative square
`U' ⟶ U ⟶ V` and `U' ⟶ V' ⟶ V` form a commutative square of continuous and cocontinuous functors
between the localized sites. -/
abbrev relocalization_over_map_square
    (hcomm : i ≫ f = p ≫ g) :
    CatCommSq (Over.map i) (Over.map p) (Over.map f) (Over.map g) where
  iso := eqToIso (over_map_square_eq i p f g hcomm)

/-- Equality form of Lemma 7.27.5 (1), derived from the canonical `CatCommSq` owner. -/
theorem relocalization_over_map_square_eq
    (hcomm : i ≫ f = p ≫ g) :
    Over.map i ⋙ Over.map f = Over.map p ⋙ Over.map g :=
  over_map_square_eq i p f g hcomm

-- Proof sketch: compose the canonical owner isomorphisms
-- `J.overMapPullbackComp` for the two routes around the square and insert
-- `J.overMapPullbackCongr` for the equality `i ≫ f = p ≫ g`.
/-- Lemma 7.27.5 (2): the commutative square of relocalization functors induces a commutative
square of localized topoi, expressed by the canonical comparison isomorphism of inverse-image
functors on sheaves. -/
noncomputable def relocalization_inverse_image_square_iso
    (hcomm : i ≫ f = p ≫ g) :
    J.overMapPullback A f ⋙ J.overMapPullback A i ≅
      J.overMapPullback A g ⋙ J.overMapPullback A p :=
  J.overMapPullbackComp A i f ≪≫
    J.overMapPullbackCongr A hcomm ≪≫
      (J.overMapPullbackComp A p g).symm

/-- The costructured-arrow comparison functors for a cartesian relocalization square are final. -/
-- Proof sketch: identify each costructured-arrow category with the corresponding pullback fiber
-- category and use the cartesian hypothesis to construct the required terminal comparison object.
private theorem relocalization_costructuredArrowRightwards_final
    (hcart : IsPullback i p f g) :
    ∀ X : Over V',
      Functor.Final
        (TwoSquare.costructuredArrowRightwards
          (relocalization_over_map_square i p f g hcart.w).iso.hom X) := sorry

-- Proof sketch: specialize the Chapter 7 Beck-Chevalley owner theorem
-- `site_square_direct_image_inverse_image_iso` to the square of slice functors
-- `Over.map i`, `Over.map p`, `Over.map f`, and `Over.map g`; the cartesian hypothesis gives the
-- needed explicit finality hypothesis for the induced costructured-arrow functors.
/-- Lemma 7.27.5 (3): if the square
`U' ⟶ U ⟶ V` and `U' ⟶ V' ⟶ V` is cartesian, then inverse image along `V' ⟶ V` commutes with
direct image along `U ⟶ V` after relocalization via the canonical Beck-Chevalley comparison
isomorphism. -/
noncomputable def relocalization_pushforward_inverse_image_iso
    (hcart : IsPullback i p f g)
    [HasWeakSheafify (J.over U') (Type w)]
    [HasWeakSheafify (J.over U) (Type w)]
    [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.map f).op.HasPointwiseRightKanExtension F]
    [∀ F : (Over U')ᵒᵖ ⥤ Type w, (Over.map p).op.HasPointwiseRightKanExtension F] :
    (Over.map f).sheafPushforwardCocontinuous (Type w) (J.over U) (J.over V) ⋙
        J.overMapPullback (Type w) g ≅
      J.overMapPullback (Type w) i ⋙
        (Over.map p).sheafPushforwardCocontinuous (Type w) (J.over U') (J.over V') :=
  (site_square_direct_image_inverse_image_iso
    (J.over U')
    (J.over U)
    (J.over V')
    (J.over V)
    (relocalization_over_map_square i p f g hcart.w)
    (relocalization_costructuredArrowRightwards_final i p f g hcart)).symm

-- Proof sketch: expand `relocalization_inverse_image_square_iso` as a composite of canonical
-- isomorphisms and use the triangle identities for isomorphisms.
/-- The forward and inverse comparison morphisms of
`relocalization_inverse_image_square_iso` compose to the identity. -/
theorem relocalization_inverse_image_square_iso_hom_inv_id
    (hcomm : i ≫ f = p ≫ g) :
    ((relocalization_inverse_image_square_iso J i p f g hcomm :
        J.overMapPullback A f ⋙ J.overMapPullback A i ≅
          J.overMapPullback A g ⋙ J.overMapPullback A p).hom) ≫
        ((relocalization_inverse_image_square_iso J i p f g hcomm :
          J.overMapPullback A f ⋙ J.overMapPullback A i ≅
            J.overMapPullback A g ⋙ J.overMapPullback A p).inv) =
      𝟙 _ := sorry

-- Proof sketch: any isomorphism satisfies `hom ≫ inv = 𝟙`; apply this to
-- `relocalization_pushforward_inverse_image_iso`.
/-- The forward and inverse comparison morphisms of
`relocalization_pushforward_inverse_image_iso` compose to the identity. -/
theorem relocalization_pushforward_inverse_image_iso_hom_inv_id
    (hcart : IsPullback i p f g)
    [HasWeakSheafify (J.over U') (Type w)]
    [HasWeakSheafify (J.over U) (Type w)]
    [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.map f).op.HasPointwiseRightKanExtension F]
    [∀ F : (Over U')ᵒᵖ ⥤ Type w, (Over.map p).op.HasPointwiseRightKanExtension F] :
    (relocalization_pushforward_inverse_image_iso J i p f g hcart).hom ≫
        (relocalization_pushforward_inverse_image_iso J i p f g hcart).inv =
      𝟙 _ := sorry

end
