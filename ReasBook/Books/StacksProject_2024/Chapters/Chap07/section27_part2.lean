import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_7_27_5 (from Chap07) -/
open CategoryTheory Opposite
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open scoped SheafifiedRepresentable

universe u v w

noncomputable section

section

variable {C : Type u} [Category.{v} C]
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
    Over.map i ⋙ Over.map f = Over.map p ⋙ Over.map g := by
  -- Normalize both composites to the relocalization functor of the corresponding composite.
  rw [← Over.mapComp_eq, ← Over.mapComp_eq]
  -- The commutative square identifies the two composite arrows.
  simp [hcomm]

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
    J.overMapPullback (Type w) f ⋙ J.overMapPullback (Type w) i ≅
      J.overMapPullback (Type w) g ⋙ J.overMapPullback (Type w) p :=
  J.overMapPullbackComp (Type w) i f ≪≫
    J.overMapPullbackCongr (Type w) hcomm ≪≫
      (J.overMapPullbackComp (Type w) p g).symm

/-- Helper for Lemma 7.27.5: a cartesian square in `C` remains cartesian after applying the
sheafified-representable functor. -/
private theorem sheafified_representable_square_isPullback
    (hcart : IsPullback i p f g) :
    IsPullback (J.sheafifiedRepresentableMap i) (J.sheafifiedRepresentableMap p)
      (J.sheafifiedRepresentableMap f) (J.sheafifiedRepresentableMap g) := by
  -- The sheafified-representable functor preserves pullbacks, so the source cartesian square
  -- transports directly to the sheaf topos.
  simpa [GrothendieckTopology.sheafifiedRepresentableMap,
    GrothendieckTopology.sheafifiedRepresentableFunctor,
    GrothendieckTopology.uliftSheafifiedRepresentableFunctor] using
    hcart.map (CategoryTheory.uliftYoneda.{max u v} ⋙
      presheafToSheaf J (Type (max u v)))

/-- Helper for Lemma 7.27.5: the left-hand base-change object is the canonical pullback over
`h[U]^#[J]`. -/
private theorem sheafified_representable_base_change_source_isPullback
    (A : Over h[V']^#[J]) :
    IsPullback
      (pullback.snd (A.hom ≫ J.sheafifiedRepresentableMap g) (J.sheafifiedRepresentableMap f))
      (pullback.fst (A.hom ≫ J.sheafifiedRepresentableMap g) (J.sheafifiedRepresentableMap f))
      (J.sheafifiedRepresentableMap f)
      (A.hom ≫ J.sheafifiedRepresentableMap g) := by
  -- The source object is defined by the ordinary pullback in the ambient slice category.
  exact
    (IsPullback.of_hasPullback
      (A.hom ≫ J.sheafifiedRepresentableMap g) (J.sheafifiedRepresentableMap f)).flip

/-- Helper for Lemma 7.27.5: the right-hand base-change object is the pullback obtained by pasting
the cartesian square of sheafified representables with the canonical pullback over `h[V']^#[J]`. -/
private theorem sheafified_representable_base_change_target_isPullback
    (hcart : IsPullback i p f g) (A : Over h[V']^#[J]) :
    IsPullback
      ((pullback.snd A.hom (J.sheafifiedRepresentableMap p)) ≫
        J.sheafifiedRepresentableMap i)
      (pullback.fst A.hom (J.sheafifiedRepresentableMap p))
      (J.sheafifiedRepresentableMap f)
      (A.hom ≫ J.sheafifiedRepresentableMap g) := by
  let hsheaf := sheafified_representable_square_isPullback (J := J) i p f g hcart
  -- Pasting with the sheafified cartesian square identifies the target object with the same
  -- ambient pullback cospan as the source object.
  exact
    (IsPullback.of_hasPullback A.hom (J.sheafifiedRepresentableMap p)).flip.paste_horiz hsheaf

/-- Helper for Lemma 7.27.5: objectwise, the two slice-level base-change constructions are
canonically isomorphic because they are pullbacks of the same cospan. -/
private noncomputable def sheafified_representable_base_change_obj_iso
    (hcart : IsPullback i p f g) (A : Over h[V']^#[J]) :
    ((Over.map (J.sheafifiedRepresentableMap g) ⋙
          Over.pullback (J.sheafifiedRepresentableMap f)).obj A) ≅
      ((Over.pullback (J.sheafifiedRepresentableMap p) ⋙
          Over.map (J.sheafifiedRepresentableMap i)).obj A) := by
  let hleft :=
    sheafified_representable_base_change_source_isPullback (J := J) (f := f) (g := g) A
  let hright :=
    sheafified_representable_base_change_target_isPullback
      (J := J) (i := i) (p := p) (f := f) (g := g) hcart A
  let e :
      pullback (A.hom ≫ J.sheafifiedRepresentableMap g) (J.sheafifiedRepresentableMap f) ≅
        pullback A.hom (J.sheafifiedRepresentableMap p) :=
    hleft.flip.isoPullback ≪≫ (hright.flip.isoPullback).symm
  -- The slice-object isomorphism is just the ambient pullback isomorphism with the structure map
  -- compatibility recorded separately.
  exact Over.isoMk e <| by
    simp [e, Category.assoc]

/-- Helper for Lemma 7.27.5: the component isomorphism matches the second pullback projection. -/
private theorem sheafified_representable_base_change_obj_iso_hom_comp_snd
    (hcart : IsPullback i p f g) (A : Over h[V']^#[J]) :
    (sheafified_representable_base_change_obj_iso
          (J := J) (i := i) (p := p) (f := f) (g := g) hcart A).hom.left ≫
        pullback.snd A.hom (J.sheafifiedRepresentableMap p) ≫
          J.sheafifiedRepresentableMap i =
      pullback.snd (A.hom ≫ J.sheafifiedRepresentableMap g)
        (J.sheafifiedRepresentableMap f) := by
  -- Unfolding the objectwise pullback comparison reveals the defining second-projection formula.
  simp [sheafified_representable_base_change_obj_iso, Category.assoc]

/-- Helper for Lemma 7.27.5: the component isomorphism matches the first pullback projection. -/
private theorem sheafified_representable_base_change_obj_iso_hom_comp_fst
    (hcart : IsPullback i p f g) (A : Over h[V']^#[J]) :
    (sheafified_representable_base_change_obj_iso
          (J := J) (i := i) (p := p) (f := f) (g := g) hcart A).hom.left ≫
        pullback.fst A.hom (J.sheafifiedRepresentableMap p) =
      pullback.fst (A.hom ≫ J.sheafifiedRepresentableMap g)
        (J.sheafifiedRepresentableMap f) := by
  -- Unfolding the objectwise pullback comparison reveals the defining first-projection formula.
  simp [sheafified_representable_base_change_obj_iso, Category.assoc]

/-- Helper for Lemma 7.27.5: the objectwise pullback comparison is natural in the slice object over
`h[V']^#[J]`. -/
private theorem sheafified_representable_base_change_obj_iso_naturality
    (hcart : IsPullback i p f g) {A B : Over h[V']^#[J]} (η : A ⟶ B) :
    ((Over.map (J.sheafifiedRepresentableMap g) ⋙
          Over.pullback (J.sheafifiedRepresentableMap f)).map η) ≫
        (sheafified_representable_base_change_obj_iso
          (J := J) (i := i) (p := p) (f := f) (g := g) hcart B).hom =
      (sheafified_representable_base_change_obj_iso
          (J := J) (i := i) (p := p) (f := f) (g := g) hcart A).hom ≫
        ((Over.pullback (J.sheafifiedRepresentableMap p) ⋙
            Over.map (J.sheafifiedRepresentableMap i)).map η) := by
  -- TODO: Compare both sides after composing with the two pullback projections of the target
  -- object. The component lemmas
  -- `sheafified_representable_base_change_obj_iso_hom_comp_snd` and
  -- `sheafified_representable_base_change_obj_iso_hom_comp_fst` reduce the problem to the
  -- explicit `Over.pullback` map formulas for `η`, but the remaining reduction currently needs a
  -- stabilized proof term for those formulas.
  sorry

/-- Helper for Lemma 7.27.5: the pullback square of sheafified representables induces the usual
base-change isomorphism between slice postcomposition and pullback functors. -/
private noncomputable def sheafified_representable_base_change_iso
    (hcart : IsPullback i p f g) :
    Over.map (J.sheafifiedRepresentableMap g) ⋙
        Over.pullback (J.sheafifiedRepresentableMap f) ≅
      Over.pullback (J.sheafifiedRepresentableMap p) ⋙
        Over.map (J.sheafifiedRepresentableMap i) :=
  NatIso.ofComponents
    (fun A ↦ sheafified_representable_base_change_obj_iso
      (J := J) (i := i) (p := p) (f := f) (g := g) hcart A)
    (fun η ↦ sheafified_representable_base_change_obj_iso_naturality
      (J := J) (i := i) (p := p) (f := f) (g := g) hcart η)

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
  -- TODO: Route correction for Lemma 7.27.5: construct this comparison by transporting the
  -- lower-shriek square through `representableLocalizationComparison`, inserting the slice
  -- Beck-Chevalley isomorphism coming from the pullback square of sheafified representables, and
  -- then applying uniqueness of right adjoints. The previous later-item import route is removed
  -- so that this file stays dependency-closed.
  sorry

-- Proof sketch: expand `relocalization_inverse_image_square_iso` as a composite of canonical
-- isomorphisms and use the triangle identities for isomorphisms.
/-- The forward and inverse comparison morphisms of
`relocalization_inverse_image_square_iso` compose to the identity. -/
theorem relocalization_inverse_image_square_iso_hom_inv_id
    (hcomm : i ≫ f = p ≫ g) :
    (relocalization_inverse_image_square_iso J i p f g hcomm).hom ≫
        (relocalization_inverse_image_square_iso J i p f g hcomm).inv =
      𝟙 _ := by
  -- This is the defining `Iso.hom_inv_id` identity for the comparison isomorphism.
  exact (relocalization_inverse_image_square_iso J i p f g hcomm).hom_inv_id

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
      𝟙 _ := by
  -- This is the defining `Iso.hom_inv_id` identity for the Beck-Chevalley comparison.
  exact (relocalization_pushforward_inverse_image_iso J i p f g hcart).hom_inv_id

end
