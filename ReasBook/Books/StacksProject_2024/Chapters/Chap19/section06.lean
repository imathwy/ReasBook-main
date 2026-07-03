import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_19_6_1 (from Chap19) -/
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory

universe v u

namespace CategoryTheory

noncomputable section

/- Domain-style sampling for Proposition 19.6.1:
- primary domain: functorial injective embeddings in the abelian-presheaf category on `C`,
  obtained by adjoint transfer from the discrete object category;
- sampled owner declarations:
  `PAb(C)`,
  `Functor.ranAdjunction`,
  `HasFunctorialInjectiveEmbeddings`,
  `hasFunctorialInjectiveEmbeddings_of_rightAdjoint_of_preservesMonomorphisms`;
- best owner abstraction: the source-facing owner `PAb(C)` together with the Chapter 12 transfer
  owner `HasFunctorialInjectiveEmbeddings (PAb(C))`;
- primitive data: the restriction functor from `PAb(C)` to the discrete object category
  `Discrete Cᵒᵖ ⥤ AddCommGrpCat`, its right adjoint given by right Kan extension, and the
  pointwise functorial injective embedding owner on that discrete target;
- derived API: the induced owner instance on `PAb(C)`.

Source/core/bridge triage:
- `source-facing`: abelian presheaves on `C`, written `PAb(C)`;
- `core/canonical`: the Chapter 12 owner `HasFunctorialInjectiveEmbeddings`;
- `bridge/view`: the restriction/right-Kan-extension adjunction between `PAb(C)` and the abelian
  presheaf category on the discrete object category, together with the transferred embedding
  `B ⟶ u(J(v(B)))`.
-/

variable (C : Type u) [Category.{v} C]

/-- The inclusion of the discrete object category of `Cᵒᵖ` into `Cᵒᵖ`. -/
private abbrev abelianPresheafObjectInclusion : Discrete Cᵒᵖ ⥤ Cᵒᵖ :=
  Discrete.functor (fun X : Cᵒᵖ ↦ X)

/-- Restriction of an abelian presheaf on `C` to the discrete category of objects of `C`. -/
private abbrev abelianPresheafObjectRestriction :
    PAb(C) ⥤ Discrete Cᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  (Functor.whiskeringLeft (Discrete Cᵒᵖ) Cᵒᵖ AddCommGrpCat.{max u v}).obj
    (abelianPresheafObjectInclusion C)

/-- The right adjoint to restriction to the discrete object category, given by right Kan
extension. -/
private abbrev abelianPresheafObjectCorestriction :
    (Discrete Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ PAb(C) :=
  (abelianPresheafObjectInclusion C).ran

section

variable [HasFunctorialInjectiveEmbeddings AddCommGrpCat.{max u v}]

/-- The pointwise injective target functor on the discrete object category. -/
private abbrev discreteAbelianPresheafInjectiveUnder
    (F : Discrete Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    Discrete Cᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  Discrete.functor
    (fun X : Cᵒᵖ ↦ HasFunctorialInjectiveEmbeddings.under (F.obj (Discrete.mk X)))

/-- The pointwise injective embedding of a discrete abelian presheaf. -/
private def discreteAbelianPresheafInjectiveHom
    (F : Discrete Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    F ⟶ discreteAbelianPresheafInjectiveUnder C F :=
  show F ⟶ Discrete.functor
      (fun X : Cᵒᵖ ↦ HasFunctorialInjectiveEmbeddings.under (F.obj (Discrete.mk X))) from
    Discrete.natTrans (fun X ↦ HasFunctorialInjectiveEmbeddings.ι (F.obj X))

/-- The pointwise injective embedding of a discrete abelian presheaf. -/
private def discreteAbelianPresheafInjectiveArrow
    (F : Discrete Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    Arrow (Discrete Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :=
  Arrow.mk (discreteAbelianPresheafInjectiveHom C F)

/-- The map between the pointwise injective targets induced by a morphism of discrete abelian
presheaves. -/
private def discreteAbelianPresheafInjectiveUnderMap
    {F G : Discrete Cᵒᵖ ⥤ AddCommGrpCat.{max u v}} (φ : F ⟶ G) :
    discreteAbelianPresheafInjectiveUnder C F ⟶ discreteAbelianPresheafInjectiveUnder C G :=
  show Discrete.functor
        (fun X : Cᵒᵖ ↦ HasFunctorialInjectiveEmbeddings.under (F.obj (Discrete.mk X))) ⟶
      Discrete.functor
        (fun X : Cᵒᵖ ↦ HasFunctorialInjectiveEmbeddings.under (G.obj (Discrete.mk X))) from
    Discrete.natTrans (fun X ↦ HasFunctorialInjectiveEmbeddings.underMap (φ.app X))

omit [Category.{v} C] in
/-- The pointwise injective embeddings commute with the induced target maps. -/
private lemma discreteAbelianPresheafInjectiveArrowMap_w
    {F G : Discrete Cᵒᵖ ⥤ AddCommGrpCat.{max u v}} (φ : F ⟶ G) (X : Discrete Cᵒᵖ) :
    φ.app X ≫ HasFunctorialInjectiveEmbeddings.ι (G.obj X) =
      HasFunctorialInjectiveEmbeddings.ι (F.obj X) ≫
        HasFunctorialInjectiveEmbeddings.underMap (φ.app X) := by
  simpa using (HasFunctorialInjectiveEmbeddings.ι_naturality (φ.app X)).w

/-- The commutative square on pointwise injective embeddings induced by a morphism of discrete
abelian presheaves. -/
private def discreteAbelianPresheafInjectiveArrowMap
    {F G : Discrete Cᵒᵖ ⥤ AddCommGrpCat.{max u v}} (φ : F ⟶ G) :
    discreteAbelianPresheafInjectiveArrow C F ⟶ discreteAbelianPresheafInjectiveArrow C G :=
  Arrow.homMk φ
    (discreteAbelianPresheafInjectiveUnderMap C φ)
    (by
      sorry)

/-- The discrete abelian presheaf category admits functorial injective embeddings pointwise. -/
private instance discreteAbelianPresheaf_hasFunctorialInjectiveEmbeddings :
    HasFunctorialInjectiveEmbeddings (Discrete Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) where
  J :=
    { obj := discreteAbelianPresheafInjectiveArrow C
      map := discreteAbelianPresheafInjectiveArrowMap C
      map_id := by
        sorry
      map_comp := by
        sorry }
  leftFunc_comp_J := rfl
  mono_obj F := by
    change Mono (discreteAbelianPresheafInjectiveHom C F)
    rw [NatTrans.mono_iff_mono_app]
    intro X
    change Mono (HasFunctorialInjectiveEmbeddings.ι (F.obj X))
    infer_instance
  injective_obj F := by
    sorry

end

/-- If an abelian presheaf is zero after restriction to the discrete object category, then it is
already zero. -/
private lemma abelianPresheafObjectRestriction_isZero_reflects (F : PAb(C))
    (hF : IsZero ((abelianPresheafObjectRestriction C).obj F)) :
    IsZero F := by
  sorry

-- Proof sketch: restrict an abelian presheaf to the discrete object category of `C`, apply the
-- pointwise functorial injective embedding there, and transfer it back along the right
-- Kan-extension adjunction using the Chapter 12 adjoint-transfer owner.
/-- Proposition 19.6.1: the category `PAb(C)` of abelian presheaves on `C` admits functorial
injective embeddings. -/
instance abelianPresheaf_hasFunctorialInjectiveEmbeddings :
    HasFunctorialInjectiveEmbeddings (PAb(C)) := by
  letI : HasFunctorialInjectiveEmbeddings AddCommGrpCat.{max u v} :=
    hasFunctorialInjectiveEmbeddings_of_isGrothendieckAbelian
  let δ := abelianPresheafObjectInclusion C
  let v' := abelianPresheafObjectRestriction C
  let u' := abelianPresheafObjectCorestriction C
  let hzero : ∀ F : PAb(C), IsZero (v'.obj F) → IsZero F :=
    abelianPresheafObjectRestriction_isZero_reflects C
  exact hasFunctorialInjectiveEmbeddings_of_rightAdjoint_of_preservesMonomorphisms
    u' v' (δ.ranAdjunction AddCommGrpCat.{max u v}) hzero

end

end CategoryTheory
