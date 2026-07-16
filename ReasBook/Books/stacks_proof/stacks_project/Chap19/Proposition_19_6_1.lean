import Mathlib
import stacks_proof.stacks_project.Chap12.Lemma_12_29_5
import stacks_proof.stacks_project.Chap18.Lemma_18_2_1

open CategoryTheory.Limits
open scoped CategoryTheory

universe v u

namespace CategoryTheory

noncomputable section

/- Domain-style sampling for Proposition 19.6.1:
- primary domain: functorial injective embeddings for abelian presheaves, built by transferring the
  Chapter 12 owner along restriction to the discrete object category;
- sampled owner declarations:
  `PAb(C)`,
  `HasFunctorialInjectiveEmbeddings`,
  `NatTrans.arrowFunctor`,
  `hasFunctorialInjectiveEmbeddings_of_rightAdjoint_of_preservesMonomorphisms`;
- best owner abstraction: the source-facing owner is `HasFunctorialInjectiveEmbeddings (PAb(C))`,
  produced by the Chapter 12 right-adjoint transfer bridge from the discrete functor category;
- primitive data: restriction from `PAb(C)` to `Discrete Cᵒᵖ ⥤ AddCommGrpCat`, the right Kan
  extension adjunction, and the pointwise endofunctor/natural transformation on the discrete
  target induced by `HasFunctorialInjectiveEmbeddings AddCommGrpCat`;
- derived API: the induced owner instance on `PAb(C)`.

Source/core/bridge triage:
- `source-facing`: abelian presheaves on `C`, written `PAb(C)`;
- `core/canonical`: the Chapter 12 owner `HasFunctorialInjectiveEmbeddings`;
- `bridge/view`: restriction to the discrete object category, its right adjoint by right Kan
  extension, and the pointwise natural transformation whose `arrowFunctor` supplies the discrete
  functor-category embedding data.

Primitive-vs-derived split:
- primitive data on the discrete target is the endofunctor of pointwise injective targets together
  with the pointwise embedding natural transformation;
- the `Arrow`-valued functor is derived canonically from that natural transformation via
  `NatTrans.arrowFunctor`, so this file should not keep parallel hand-written arrow/map wrappers
  for the same data. -/

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

omit [Category.{v} C] [HasFunctorialInjectiveEmbeddings AddCommGrpCat.{max u v}] in
/-- Helper for Proposition 19.6.1: a discrete diagram of abelian groups is injective once each
value is injective. -/
private lemma discrete_functor_injective_of_pointwise
    (J : Discrete Cᵒᵖ ⥤ AddCommGrpCat.{max u v})
    (hJ : ∀ X : Discrete Cᵒᵖ, Injective (J.obj X)) :
    Injective J := by
  refine ⟨?_⟩
  intro A B g f _
  -- Convert the monomorphism of natural transformations into componentwise monomorphisms.
  have hf : ∀ X : Discrete Cᵒᵖ, Mono (f.app X) :=
    (NatTrans.mono_iff_mono_app f).1 inferInstance
  -- Lift each component through the injective value of `J` and reassemble the lifts on the
  -- discrete index category.
  refine ⟨Discrete.natTrans (fun X ↦
    @Injective.factorThru AddCommGrpCat.{max u v} _ (J.obj X) (A.obj X) (B.obj X)
      (hJ X) (g.app X) (f.app X) (hf X)), ?_⟩
  ext X
  simpa using
    @Injective.comp_factorThru AddCommGrpCat.{max u v} _ (J.obj X) (A.obj X) (B.obj X)
      (hJ X) (g.app X) (f.app X) (hf X)

/-- The pointwise injective target endofunctor on the discrete object category. -/
private def discreteAbelianPresheafInjectiveUnderFunctor :
    (Discrete Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤
      (Discrete Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) where
  obj F :=
    Discrete.functor
      (fun X : Cᵒᵖ ↦ HasFunctorialInjectiveEmbeddings.under (F.obj (Discrete.mk X)))
  map {F G} φ :=
    Discrete.natTrans (fun X ↦ HasFunctorialInjectiveEmbeddings.underMap (φ.app X))
  map_id F := by
    ext X
    simpa [HasFunctorialInjectiveEmbeddings.underMap] using
      congrArg Arrow.Hom.right (HasFunctorialInjectiveEmbeddings.J.map_id (F.obj X))
  map_comp φ ψ := by
    ext X
    simpa [HasFunctorialInjectiveEmbeddings.underMap, Functor.map_comp] using
      congrArg Arrow.Hom.right
        (HasFunctorialInjectiveEmbeddings.J.map_comp (φ.app X) (ψ.app X))

/-- The pointwise injective embedding natural transformation on the discrete object category. -/
private def discreteAbelianPresheafInjectiveι :
    𝟭 (Discrete Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⟶
      discreteAbelianPresheafInjectiveUnderFunctor C where
  app F := Discrete.natTrans (fun X ↦ HasFunctorialInjectiveEmbeddings.ι (F.obj X))
  naturality {F G} φ := by
    ext X x
    simpa [discreteAbelianPresheafInjectiveUnderFunctor] using
      congrFun
        (congrArg AddCommGrpCat.Hom.hom
          (HasFunctorialInjectiveEmbeddings.ι_naturality_w (φ.app X)))
        x

/-- The discrete abelian presheaf category admits functorial injective embeddings pointwise. -/
private instance discreteAbelianPresheaf_hasFunctorialInjectiveEmbeddings :
    HasFunctorialInjectiveEmbeddings (Discrete Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) where
  J := (discreteAbelianPresheafInjectiveι C).arrowFunctor
  leftFunc_comp_J := rfl
  mono_obj F := by
    change Mono ((discreteAbelianPresheafInjectiveι C).app F)
    rw [NatTrans.mono_iff_mono_app]
    intro X
    change Mono (HasFunctorialInjectiveEmbeddings.ι (F.obj X))
    infer_instance
  injective_obj F := by
    -- The discrete target is injective because its values are the chosen injective envelopes in
    -- `AddCommGrpCat`.
    change Injective ((discreteAbelianPresheafInjectiveUnderFunctor C).obj F)
    refine discrete_functor_injective_of_pointwise (C := C)
      ((discreteAbelianPresheafInjectiveUnderFunctor C).obj F) ?_
    intro X
    simpa [discreteAbelianPresheafInjectiveUnderFunctor] using
      (HasFunctorialInjectiveEmbeddings.under_injective (F.obj X))

end

/-- If an abelian presheaf is zero after restriction to the discrete object category, then it is
already zero. -/
private lemma abelianPresheafObjectRestriction_isZero_reflects (F : PAb(C))
    (hF : IsZero ((abelianPresheafObjectRestriction C).obj F)) :
    IsZero F := by
  -- It is enough to show that the identity of `F` is zero, and this can be checked on each
  -- object after restricting to the discrete object category.
  apply (IsZero.iff_id_eq_zero F).2
  apply NatTrans.ext
  funext U
  have hIdZero : 𝟙 ((abelianPresheafObjectRestriction C).obj F) = 0 :=
    (IsZero.iff_id_eq_zero ((abelianPresheafObjectRestriction C).obj F)).1 hF
  have hComponent :
      NatTrans.app (𝟙 ((abelianPresheafObjectRestriction C).obj F)) (Discrete.mk U) =
        NatTrans.app
          (0 : ((abelianPresheafObjectRestriction C).obj F) ⟶
            ((abelianPresheafObjectRestriction C).obj F))
          (Discrete.mk U) :=
    congrArg (fun η ↦ NatTrans.app η (Discrete.mk U)) hIdZero
  -- The restricted identity at `Discrete.mk U` is exactly the component identity on `F.obj U`.
  simpa using hComponent

-- Proof sketch: restrict an abelian presheaf to the discrete object category of `C`, apply the
-- pointwise functorial injective embedding there, and transfer it back along the right
-- Kan-extension adjunction using the Chapter 12 adjoint-transfer owner.
/-- Proposition 19.6.1: the category `PAb(C)` of abelian presheaves on `C` admits functorial
injective embeddings. -/
@[stacks 01DK]
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
