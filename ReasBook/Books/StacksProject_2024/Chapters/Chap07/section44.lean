import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_44_1 (from Chap07) -/
open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A : Type u₃} [Category.{v₃} A]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (u : C ⥤ D)
variable [Functor.IsContinuous u J K]

/- Domain-style sampling for Definition 7.44.1:
- primary domain: direct-image functors on sheaf categories induced by continuous functors of
  sites;
- sampled owner API:
  `Functor.sheafPushforwardContinuous`,
  `Functor.sheafPushforwardContinuousCompSheafToPresheafIso`,
  `Functor.sheafAdjunctionContinuous`,
  `IsMorphismOfSites`;
- source-facing layer: the Stacks definition of the direct-image functor `f_*` attached to a
  morphism of sites presented by a continuous functor `u : C ⥤ D`;
- core/canonical owner: `u.sheafPushforwardContinuous A J K`;
- bridge/view: the underlying-presheaf comparison
  `u.sheafPushforwardContinuousCompSheafToPresheafIso A J K`, expressing that the owner functor
  is induced by precomposition with `u.op`.

Primitive data are only the topologies `J`, `K`, the functor `u`, and its continuity. The sheaf
pushforward and its comparison with precomposition on presheaves are derived API of that owner, so
this file should recall the canonical owner directly rather than introduce a local alias or wrapper.
-/

/- Definition 7.44.1: if `f : (D, K) ⟶ (C, J)` is the morphism of sites presented by a continuous
functor `u : C ⥤ D`, then the pushforward on sheaves of `A`-valued algebraic structures is the
canonical functor `u.sheafPushforwardContinuous A J K : Sheaf K A ⥤ Sheaf J A`. -/
recall Functor.sheafPushforwardContinuous

/- Companion check: on presheaves of `A`-valued algebraic structures, pushforward is just
precomposition with `u.op`, i.e. `u^p ℱ (U) = ℱ (u.obj U)`. -/
#check (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op

/- Companion recall: the sheaf pushforward functor above is induced by the same precomposition rule
on the underlying presheaves, which is the precise formal content of the objectwise formula
`f_*ℱ(U) = ℱ(uU)`. -/
recall Functor.sheafPushforwardContinuousCompSheafToPresheafIso

end

/-! ### Lemma_7_44_2 (from Chap07) -/
open CategoryTheory Opposite
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Functor.sheafPullbackConstruction

universe u₁ u₂ v w

noncomputable section

namespace CategoryTheory

variable {C : Type u₁} [Category.{v} C]
variable {D : Type u₂} [Category.{v} D]
variable {A : Type w} [Category.{max u₁ u₂ v} A]
variable {FA : A → A → Type (max u₁ u₂ v)} {CA : A → Type (max u₁ u₂ v)}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]

/-
Domain-style sampling for Lemma 7.44.2:
- primary domain: direct- and inverse-image functors on presheaves and sheaves of algebraic
  structures, together with their compatibility with the forgetful functor to sets;
- sampled owner API:
  `Functor.lanAdjunction`,
  `Functor.lanCompIsoOfPreserves`,
  `Functor.sheafAdjunctionContinuous`,
  `Functor.sheafPullbackConstruction.sheafPullbackIso`;
- source/core/bridge triage:
  `source-facing`: the Stacks lemma asserting that presheaf/sheaf inverse and direct image for
  algebraic structures are the expected adjoint functors and commute with forgetting to sets;
  `core/canonical`: the presheaf left Kan extension owner `u.op.lan`, the sheaf pushforward owner
  `u.sheafPushforwardContinuous A J K` under continuity, and the sheaf pullback owner
  `u.sheafPullback A J K` under the standard continuity/Kan-extension/sheafification hypotheses;
  `bridge/view`: `Functor.lanCompIsoOfPreserves`, `sheafComposeNatIso`, and
  `Functor.sheafPullbackConstruction.sheafPullbackIso`, which transport the forgetful functor
  across the canonical owners.

Primitive data are only the functor `u`, the site topologies, the existence of the relevant left
Kan extensions, and the preservation hypotheses letting `forget A` commute with Kan extension and
sheafification. The adjunctions and forget-comparison maps are derived API owned upstream, so this
file should reuse those owners directly and keep only the source-facing comparison statements.
-/

section PresheafAdjunction

variable (u : C ⥤ D)
variable [∀ P : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension P]

/- Canonical presheaf adjunction recall: on presheaves of `A`-valued algebraic structures, the
pullback functor `uₚ`, realized as left Kan extension along `u.op`, is left adjoint to the
pushforward functor `u^p`, realized as precomposition by `u.op`. -/
recall Functor.lanAdjunction

end PresheafAdjunction

-- Proof sketch: both composites act on a presheaf `P : Dᵒᵖ ⥤ A` by precomposition with `u.op`
-- and then objectwise application of the forgetful functor `forget A`, so the two functors agree
-- definitionally.
/-- Lemma 7.44.2 (1): presheaf pushforward, i.e. precomposition with `u.op`, commutes with
taking the underlying set-valued presheaf. Applied to algebraic-structure categories, this is the
compatibility of direct image with the underlying presheaf of sets. -/
theorem presheaf_pushforward_forget
    (u : C ⥤ D) :
    (whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op ⋙
        (whiskeringRight Cᵒᵖ A (Type (max u₁ u₂ v))).obj (forget A) =
      (whiskeringRight Dᵒᵖ A (Type (max u₁ u₂ v))).obj (forget A) ⋙
        (whiskeringLeft Cᵒᵖ Dᵒᵖ (Type (max u₁ u₂ v))).obj u.op := rfl

section PresheafForgetPullback

variable (u : C ⥤ D)
variable [∀ P : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension P]
variable [∀ P : Cᵒᵖ ⥤ Type (max u₁ u₂ v), u.op.HasLeftKanExtension P]
variable [(forget A).PreservesLeftKanExtensions u.op]

/- Canonical presheaf pullback/forget recall: for presheaves of algebraic structures, forgetting to
sets commutes with the presheaf pullback `uₚ`, i.e. the left Kan extension along `u.op`, via the
canonical comparison isomorphism. -/
recall Functor.lanCompIsoOfPreserves

end PresheafForgetPullback

section Sheaves

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (u : C ⥤ D)

section SheafAdjunction

variable [u.IsContinuous J K]
variable [∀ P : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension P]
variable [HasWeakSheafify K A]

/- Canonical sheaf adjunction recall: on sheaves of `A`-valued algebraic structures, the
inverse-image functor `f⁻¹`, realized as `u.sheafPullback A J K`, is left adjoint to the
direct-image functor `f_* = u.sheafPushforwardContinuous A J K`. -/
recall Functor.sheafAdjunctionContinuous

end SheafAdjunction

-- Proof sketch: `u.sheafPushforwardContinuous` is defined by precomposition with `u.op`, and
-- `sheafCompose` is obtained by objectwise composition with `forget A`; thus the two composites
-- agree definitionally.
/-- Lemma 7.44.2 (2): sheaf pushforward commutes with taking the underlying sheaf of sets.
Applied to algebraic-structure categories, this is the compatibility of direct image with the
underlying sheaf of sets. -/
theorem sheaf_pushforward_forget
    [u.IsContinuous J K]
    [J.HasSheafCompose (forget A)]
    [K.HasSheafCompose (forget A)] :
    u.sheafPushforwardContinuous A J K ⋙ sheafCompose J (forget A) =
      sheafCompose K (forget A) ⋙ u.sheafPushforwardContinuous (Type (max u₁ u₂ v)) J K := rfl

-- Proof sketch: realize both pullback functors by left Kan extension followed by sheafification,
-- use clause (2) to move `forget A` across the left Kan extension, and then use compatibility of
-- sheafification with `forget A` to identify the resulting set-valued sheaf.
section SheafPullbackForget

variable [u.IsContinuous J K]
variable [∀ P : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension P]
variable [∀ P : Cᵒᵖ ⥤ Type (max u₁ u₂ v), u.op.HasLeftKanExtension P]
variable [(forget A).PreservesLeftKanExtensions u.op]
variable [HasWeakSheafify K A]
variable [HasWeakSheafify K (Type (max u₁ u₂ v))]
variable [J.HasSheafCompose (forget A)]
variable [K.HasSheafCompose (forget A)]
variable [K.PreservesSheafification (forget A)]

/-
Bridge/view step: the explicit Kan-extension-and-sheafification construction of pullback commutes
with forgetting to sets via the canonical sheafification comparison `sheafComposeNatIso` and the
canonical Kan-extension comparison `(forget A).lanCompIsoOfPreserves u.op`.
-/
private noncomputable def sheafPullbackConstruction_forget :
    sheafPullbackConstruction.sheafPullback u A J K ⋙ sheafCompose K (forget A) ≅
      sheafCompose J (forget A) ⋙
        sheafPullbackConstruction.sheafPullback u (Type (max u₁ u₂ v)) J K :=
  (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (sheafToPresheaf J A)
        (Functor.associator _ _ _ ≪≫
          isoWhiskerLeft u.op.lan
            (sheafComposeNatIso K (forget A) (sheafificationAdjunction K A)
              (sheafificationAdjunction K (Type (max u₁ u₂ v)))).symm)) ≪≫
    isoWhiskerLeft (sheafToPresheaf J A)
      ((Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight ((forget A).lanCompIsoOfPreserves u.op)
          (presheafToSheaf K (Type (max u₁ u₂ v))) ≪≫
        Functor.associator _ _ _) ≪≫
    Iso.refl _

/-- Lemma 7.44.2 (3): sheaf pullback commutes with taking the underlying sheaf of sets. Applied to
algebraic-structure categories, this is the compatibility of inverse image with the underlying
sheaf of sets. -/
noncomputable def sheaf_pullback_forget
    :
    u.sheafPullback A J K ⋙ sheafCompose K (forget A) ≅
      sheafCompose J (forget A) ⋙ u.sheafPullback (Type (max u₁ u₂ v)) J K :=
  isoWhiskerRight (sheafPullbackIso u A J K) (sheafCompose K (forget A)) ≪≫
    sheafPullbackConstruction_forget J K u ≪≫
    isoWhiskerLeft (sheafCompose J (forget A))
      (sheafPullbackIso u (Type (max u₁ u₂ v)) J K).symm

-- Proof sketch: this is the componentwise `hom ≫ inv = 𝟙` identity for the natural isomorphism
-- `sheaf_pullback_forget`.
/-- The comparison isomorphism `sheaf_pullback_forget` is componentwise invertible. -/
theorem sheaf_pullback_forget_hom_inv_app
    (ℱ : Sheaf J A) :
    ((sheaf_pullback_forget J K u).hom.app ℱ) ≫
        ((sheaf_pullback_forget J K u).inv.app ℱ) =
      𝟙 ((u.sheafPullback A J K ⋙ sheafCompose K (forget A)).obj ℱ) := by
  -- Specialize the natural-isomorphism identity to the comparison isomorphism at `ℱ`.
  simpa using Iso.hom_inv_id_app (sheaf_pullback_forget J K u) ℱ

end SheafPullbackForget

end Sheaves

end CategoryTheory

end

/-! ### Proposition_7_44_3 (from Chap07) -/
universe u₁ u₂ v w

namespace CategoryTheory

open scoped MorphismOfTopoiIn

/-
Domain-style sampling for Proposition 7.44.3:
- primary domain: morphisms of topoi and the induced inverse-image and direct-image functors on
  sheaves of
  algebraic structures;
- sampled owner API:
  `MorphismOfTopoiIn.presentationFunctor_pushforwardIso`,
  `Functor.sheafAdjunctionContinuous`,
  `sheaf_pushforward_forget`,
  `sheaf_pullback_forget`;
- source/core/bridge triage:
  `source-facing`: the Stacks comparison between a presented morphism of topoi and the induced
  inverse-image and direct-image functors on sheaves of algebraic structures;
  `core/canonical`: the topoi-presentation comparison isomorphisms from `Remark_7_15_4` and the
  forget-compatibility owners from `Lemma_7_44_2`;
  `bridge/view`: the two whiskered comparison expressions below.

Primitive data are only the morphism-of-sites presentation and the algebraic-structure owner
`IsAlgebraicStructure A (forget A)`. The comparison isomorphisms are derived bridge API, so this
file should recall the upstream owners directly and keep only the thin whiskered comparison
expressions below.
-/

section MorphismOfTopoi

variable {C : Type u₁} [Category.{v} C]
variable {D : Type u₂} [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Proposition 7.44.3: for a morphism of topoi `f : Sh(K) ⟶ Sh(J)`, the canonical presentation
`U ↦ f⁻¹(h_U^#)` from `Remark_7_15_4` recovers the original direct-image functor on underlying
sheaves of sets. -/
recall MorphismOfTopoiIn.presentationFunctor_pushforwardIso

end MorphismOfTopoi

section AlgebraicStructures

variable {C : Type u₁} [Category.{v} C]
variable {D : Type u₂} [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Proposition 7.44.3: the additional Stacks examples of sheaves of algebraic structures are
obtained by applying the general sheaf-theoretic constructions to the standard algebraic-structure
categories already recorded in Lemma 6.15.2. The listed categories are therefore reused directly,
rather than repackaged into a new conjunction theorem. -/
recall pointed_sets_algebraic_structure_type
recall abelian_groups_algebraic_structure_type
recall groups_algebraic_structure_type
recall monoids_algebraic_structure_type
recall rings_algebraic_structure_type
recall modules_algebraic_structure_type (R : Type w) [Ring R] :
  IsAlgebraicStructure (ModuleCat.{w} R) (forget (ModuleCat.{w} R))
recall lie_algebras_algebraic_structure_type (R : Type w) [CommRing R] :
  IsAlgebraicStructure (LieAlgebraCat R) (forget (LieAlgebraCat R))

variable (A : Type w) [Category.{max u₁ u₂ v} A]
variable {FA : A → A → Type (max u₁ u₂ v)} {CA : A → Type (max u₁ u₂ v)}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
variable [IsAlgebraicStructure A (forget A)]
variable (u : C ⥤ D)

variable [IsMorphismOfSites J K u]
variable [∀ P : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension P]
variable [HasWeakSheafify K A]

/- Proposition 7.44.3: on sheaves of algebraic structures, the induced inverse-image and
direct-image functors are the canonical adjoint pair `u.sheafPullback A J K ⊣
u.sheafPushforwardContinuous A J K`. -/
recall Functor.sheafAdjunctionContinuous

variable [J.HasSheafCompose (forget A)] [K.HasSheafCompose (forget A)]
variable {f : MorphismOfTopoiIn J K}
variable (ePush : u.sheafPushforwardContinuous (Type (max u₁ u₂ v)) J K ≅ f _*)

/- Proposition 7.44.3: if the direct-image functor of a morphism of topoi
`f : Sh(K) ⟶ Sh(J)` is presented on underlying sheaves of sets by the continuous functor `u`,
then the induced direct image on sheaves of `A`-valued algebraic structures forgets to the direct
image of `f`; this is exactly the canonical forget-comparison from `Lemma_7_44_2`, whiskered with
the presentation isomorphism `ePush`. -/
#check
  (eqToIso (sheaf_pushforward_forget J K u) ≪≫
      (sheafCompose K (forget A)).isoWhiskerLeft ePush :
    u.sheafPushforwardContinuous A J K ⋙ sheafCompose J (forget A) ≅
      sheafCompose K (forget A) ⋙ f _*)

/- Proposition 7.44.3: the induced direct-image functor on sheaves of algebraic structures
commutes with forgetting to sheaves of sets. -/
recall sheaf_pushforward_forget

variable [∀ P : Cᵒᵖ ⥤ Type (max u₁ u₂ v), u.op.HasLeftKanExtension P]
variable [(forget A).PreservesLeftKanExtensions u.op]
variable [HasWeakSheafify K (Type (max u₁ u₂ v))]
variable [K.PreservesSheafification (forget A)]
variable (eInv : u.sheafPullback (Type (max u₁ u₂ v)) J K ≅ f⁻¹)

/- Proposition 7.44.3: if the inverse-image functor of a morphism of topoi
`f : Sh(K) ⟶ Sh(J)` is presented on underlying sheaves of sets by the continuous functor `u`,
then the induced inverse image on sheaves of `A`-valued algebraic structures forgets to the
inverse image of `f`; this is exactly the canonical forget-comparison from `Lemma_7_44_2`,
whiskered with the presentation isomorphism `eInv`. -/
#check
  (sheaf_pullback_forget J K u ≪≫
      (sheafCompose J (forget A)).isoWhiskerLeft eInv :
    u.sheafPullback A J K ⋙ sheafCompose K (forget A) ≅
      sheafCompose J (forget A) ⋙ f⁻¹)

/- Proposition 7.44.3: the induced inverse-image functor on sheaves of algebraic structures
commutes with forgetting to sheaves of sets. -/
recall sheaf_pullback_forget

end AlgebraicStructures

end CategoryTheory

/-! ### Remark_7_44_4 (from Chap07) -/
open CategoryTheory Opposite
open CategoryTheory.Functor

universe uC vC uD vD w

section

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable (u : D ⥤ C)

/- Domain-style sampling for Remark 7.44.4:
- primary domain: presheaf left Kan extensions and forgetful comparison for abelian-group-valued
  presheaves;
- sampled owner API:
  `Functor.lan`,
  `Functor.lanAdjunction`,
  `Functor.lanCompIsoOfPreserves`,
  `Functor.whiskeringRight`;
- current-chapter reuse point:
  `Lemma_7_44_2`, which already reuses `Functor.lanAdjunction` and
  `Functor.lanCompIsoOfPreserves` for general algebraic-structure-valued presheaves, so this file
  should specialize the same owners to `AddCommGrpCat` rather than introduce a parallel abelian
  wrapper;
- source/core/bridge triage:
  `source-facing`: the Stacks remark identifying the abelian-presheaf pullback functor `uₚ^{ab}`
  and its adjunction/preservation properties;
  `core/canonical`: mathlib's left Kan extension owner `u.op.lan`, together with
  `u.op.lanAdjunction AddCommGrpCat` and the forgetful comparison isomorphism
  `(forget AddCommGrpCat).lanCompIsoOfPreserves u.op`;
  `bridge/view`: the specialization from the general presheaf Kan-extension API to the specific
  target category `AddCommGrpCat`.

Primitive data are the functor `u`, the existence of left Kan extensions along `u.op` for
`AddCommGrpCat`-valued and set-valued presheaves, and preservation of those left Kan extensions by
`forget AddCommGrpCat`. The functor `u.op.lan`, its adjunction, and the forgetful comparison
isomorphism are derived API owned upstream, so this file should reuse those owners directly rather
than introduce a parallel local wrapper for abelian presheaves.
-/

section PresheafAdjunction

variable [∀ F : Dᵒᵖ ⥤ AddCommGrpCat, u.op.HasLeftKanExtension F]

/- Remark 7.44.4: for a functor `u : D ⥤ C`, the abelian-presheaf pullback functor `uₚ^{ab}` is
the canonical left Kan extension along `u.op`, i.e. `u.op.lan`. Its adjunction with
precomposition by `u.op` is the specialized Kan-extension adjunction
`u.op.lanAdjunction AddCommGrpCat`, while agreement with the set-valued left Kan extension after
forgetting to sets is a separate comparison statement and need not hold without extra hypotheses.
-/
#check (u.op.lan : (Dᵒᵖ ⥤ AddCommGrpCat) ⥤ Cᵒᵖ ⥤ AddCommGrpCat)

/- Remark 7.44.4, owner form: the adjunction between abelian-presheaf pullback and pushforward is
the `AddCommGrpCat` specialization of the canonical presheaf left-Kan-extension adjunction. -/
recall Functor.lanAdjunction

/- Remark 7.44.4, specialized form: the abelian-presheaf pullback/pushforward adjunction is
`u.op.lanAdjunction AddCommGrpCat`. -/
#check (u.op.lanAdjunction AddCommGrpCat :
  (u.op.lan : (Dᵒᵖ ⥤ AddCommGrpCat) ⥤ Cᵒᵖ ⥤ AddCommGrpCat) ⊣
    (whiskeringLeft Dᵒᵖ Cᵒᵖ AddCommGrpCat).obj u.op)

end PresheafAdjunction

variable [∀ F : Dᵒᵖ ⥤ AddCommGrpCat, u.op.HasLeftKanExtension F]

section PresheafForgetComparison

variable [∀ F : Dᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension F]
variable [(forget AddCommGrpCat).PreservesLeftKanExtensions u.op]

/- Companion check: when `forget AddCommGrpCat` preserves the left Kan extensions along `u.op`,
forgetting the abelian-group-valued left Kan extension agrees canonically with the set-valued left
Kan extension of the underlying presheaf. This is exactly the conditional comparison alluded to in
the remark; the remark also notes that such agreement need not hold without extra hypotheses. -/
recall Functor.lanCompIsoOfPreserves

#check ((forget AddCommGrpCat).lanCompIsoOfPreserves u.op)

end PresheafForgetComparison

end
