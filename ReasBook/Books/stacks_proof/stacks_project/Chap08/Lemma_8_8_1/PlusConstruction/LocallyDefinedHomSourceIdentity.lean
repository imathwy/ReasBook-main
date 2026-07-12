import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomCast
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomIdentityRepresentative

universe u v uX vX

namespace CategoryTheory

open Bicategory
open FibredCategoryMor
open Functor
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace FibredCategoryMor

namespace LocallyDefinedHomRepresentativeOver

theorem overMorphism_heq_of_left_heq
    {U : C} {A B A' B' : Over U} (hA : A = A') (hB : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'} (hleft : HEq f.left g.left) :
    HEq f g := by
  cases hA
  cases hB
  exact heq_of_eq (Over.OverMorphism.ext (eq_of_heq hleft))

/-- Source stage 2.4 left-identity local-family law using the literal source representative
`(id_U, {id_U}, id_x)`.

This is separated from the older ordinary-arrow representative because the latter has displayed
base `X.p.map (𝟙 x)`, while this source representative has displayed base literally
`𝟙 (X.p.obj x)`. -/
noncomputable def sourceComposeOverLeftIdentityFamilyLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f) : Prop :=
  let comp := composeOver (J := J) (sourceIdentityHomToRepresentativeOver (J := J) X x) α
  let hbase : 𝟙 (X.p.obj x) ≫ f = f := by simp
  castBaseFamily (J := J) hbase comp =
    α.family.refine (sourceIdentityCompositionCoverLeftHom (J := J) α)

/-- Source stage 2.4 right-identity local-family law using the literal source representative
`(id_V, {id_V}, id_y)`. -/
noncomputable def sourceComposeOverRightIdentityFamilyLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f) : Prop :=
  let comp := composeOver (J := J) α (sourceIdentityHomToRepresentativeOver (J := J) X y)
  let hbase : f ≫ 𝟙 (X.p.obj y) = f := by simp
  castBaseFamily (J := J) hbase comp =
    α.family.refine (sourceIdentityCompositionCoverRightHom (J := J) α)

/-- On the source left-identity composition cover, the right local arrow is the original cover
arrow used by the identity-cover refinement. -/
theorem sourceIdentityCompositionCoverLeft_toRight
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (I : (compositionCover (J := J)
      (sourceIdentityHomToRepresentativeOver (J := J) X x) α).Arrow) :
    compositionCoverToRight (J := J)
        (sourceIdentityHomToRepresentativeOver (J := J) X x) α I =
      (⟨I.Y, I.f,
        (leOfHom (sourceIdentityCompositionCoverLeftHom (J := J) α)) _ I.hf⟩ :
        α.cover.Arrow) := by
  cases I with
  | mk Y k hk =>
      apply GrothendieckTopology.Cover.Arrow.ext
      · cases Y with
        | mk left right hom =>
            cases right with
            | mk as =>
                dsimp [compositionCoverToRight,
                  LocallyDefinedHomRepresentative.compositionCoverToRight]
                simp only [Category.comp_id]
                cases as
                rfl
      · cases Y with
        | mk left right hom =>
            cases right with
            | mk as =>
                cases as
                dsimp [compositionCoverToRight,
                  LocallyDefinedHomRepresentative.compositionCoverToRight]
                simp only [Category.comp_id]
                apply overMorphism_heq_of_left_heq
                · rw [Category.comp_id]
                  rfl
                · rfl
                · apply heq_of_eq
                  change 𝟙 left ≫ hom = k.left
                  rw [Category.id_comp]
                  simpa using k.w.symm

/-- On the source left-identity composition cover, the left local arrow is the restriction of
the literal identity representative to the cover member. -/
theorem sourceIdentityCompositionCoverLeft_leftLocal_down
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (I : (compositionCover (J := J)
      (sourceIdentityHomToRepresentativeOver (J := J) X x) α).Arrow) :
    let Fp := canonicalFiberPseudofunctor X.p
    let xF : X.p.Fiber (X.p.obj x) := Functor.Fiber.mk (p := X.p) (a := x) rfl
    ((compositionLeftLocal (J := J)
        (sourceIdentityHomToRepresentativeOver (J := J) X x) α I).down) =
      (Fp.map I.Y.hom.op.toLoc).toFunctor.map
        ((Fp.mapId (LocallyDiscrete.mk (op (X.p.obj x)))).inv.toNatTrans.app xF) := by
  intro Fp xF
  simpa [compositionLeftLocal, compositionCoverToLeft, Fp, xF] using
    sourceIdentityHomToRepresentativeOver_family_apply_down
      (J := J) X x
      (compositionCoverToLeft (J := J)
        (sourceIdentityHomToRepresentativeOver (J := J) X x) α I)

/-- On the source left-identity composition cover, the right local arrow is heterogeneously the
original representative's local arrow on the refinement to the original cover.  The heterogeneous
statement records the slice-object owner change rather than erasing it. -/
theorem sourceIdentityCompositionCoverLeft_rightLocal_down_heq
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (I : (compositionCover (J := J)
      (sourceIdentityHomToRepresentativeOver (J := J) X x) α).Arrow) :
    HEq
      ((compositionRightLocal (J := J)
        (sourceIdentityHomToRepresentativeOver (J := J) X x) α I).down)
      ((α.family (⟨I.Y, I.f,
        (leOfHom (sourceIdentityCompositionCoverLeftHom (J := J) α)) _ I.hf⟩ :
        α.cover.Arrow)).down) := by
  have htoRight := sourceIdentityCompositionCoverLeft_toRight (J := J) α I
  exact htoRight ▸ HEq.rfl

/-- On the source right-identity composition cover, the left local arrow is the original cover
arrow used by the identity-cover refinement. -/
theorem sourceIdentityCompositionCoverRight_toLeft
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (I : (compositionCover (J := J) α
      (sourceIdentityHomToRepresentativeOver (J := J) X y)).Arrow) :
    compositionCoverToLeft (J := J) α
        (sourceIdentityHomToRepresentativeOver (J := J) X y) I =
      (⟨I.Y, I.f,
        (leOfHom (sourceIdentityCompositionCoverRightHom (J := J) α)) _ I.hf⟩ :
        α.cover.Arrow) :=
  rfl

/-- On the source right-identity composition cover, the left local arrow is heterogeneously the
original representative's local arrow on the refinement to the original cover. -/
theorem sourceIdentityCompositionCoverRight_leftLocal_down_heq
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (I : (compositionCover (J := J) α
      (sourceIdentityHomToRepresentativeOver (J := J) X y)).Arrow) :
    HEq
      ((compositionLeftLocal (J := J) α
        (sourceIdentityHomToRepresentativeOver (J := J) X y) I).down)
      ((α.family (⟨I.Y, I.f,
        (leOfHom (sourceIdentityCompositionCoverRightHom (J := J) α)) _ I.hf⟩ :
        α.cover.Arrow)).down) := by
  have htoLeft := sourceIdentityCompositionCoverRight_toLeft (J := J) α I
  exact htoLeft ▸ HEq.rfl

/-- A source left-identity family calculation gives fixed-base equivalence to the original
representative. -/
theorem sourceComposeOver_left_identity_equivalent_of_familyLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (hα : sourceComposeOverLeftIdentityFamilyLaw (J := J) α) :
    Equivalent (J := J)
      (castBase (J := J) (by simp :
        𝟙 (X.p.obj x) ≫ f = f)
        (composeOver (J := J) (sourceIdentityHomToRepresentativeOver (J := J) X x) α))
      α := by
  let comp := composeOver (J := J) (sourceIdentityHomToRepresentativeOver (J := J) X x) α
  let hbase : 𝟙 (X.p.obj x) ≫ f = f := by simp
  change Equivalent (J := J) (castBase (J := J) hbase comp) α
  refine ⟨comp.cover, coverHomCastBase (J := J) hbase comp,
    sourceIdentityCompositionCoverLeftHom (J := J) α, ?_⟩
  rw [castBase_family_refine_coverHomCastBase]
  exact hα

/-- A source right-identity family calculation gives fixed-base equivalence to the original
representative. -/
theorem sourceComposeOver_right_identity_equivalent_of_familyLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (hα : sourceComposeOverRightIdentityFamilyLaw (J := J) α) :
    Equivalent (J := J)
      (castBase (J := J) (by simp :
        f ≫ 𝟙 (X.p.obj y) = f)
        (composeOver (J := J) α (sourceIdentityHomToRepresentativeOver (J := J) X y)))
      α := by
  let comp := composeOver (J := J) α (sourceIdentityHomToRepresentativeOver (J := J) X y)
  let hbase : f ≫ 𝟙 (X.p.obj y) = f := by simp
  change Equivalent (J := J) (castBase (J := J) hbase comp) α
  refine ⟨comp.cover, coverHomCastBase (J := J) hbase comp,
    sourceIdentityCompositionCoverRightHom (J := J) α, ?_⟩
  rw [castBase_family_refine_coverHomCastBase]
  exact hα

end LocallyDefinedHomRepresentativeOver

namespace LocallyDefinedHomRepresentative

/-- Raw locally-defined composition satisfies source left identity once the literal fixed-base
family law has been supplied. -/
theorem source_compose_left_identity_equivalent_of_familyLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    (α : LocallyDefinedHomRepresentative (J := J) X x y)
    (hα : LocallyDefinedHomRepresentativeOver.sourceComposeOverLeftIdentityFamilyLaw
      (J := J) α.representative) :
    Equivalent (J := J)
      (compose (J := J) (sourceIdentityHomToRepresentative (J := J) X x) α) α := by
  apply (equivalent_iff_exists_base_eq (J := J)
    (compose (J := J) (sourceIdentityHomToRepresentative (J := J) X x) α) α).2
  refine ⟨by simp [sourceIdentityHomToRepresentative], ?_⟩
  rcases α with ⟨f, a⟩
  dsimp [compose, sourceIdentityHomToRepresentative]
  exact
    LocallyDefinedHomRepresentativeOver.sourceComposeOver_left_identity_equivalent_of_familyLaw
      (J := J) a hα

/-- Raw locally-defined composition satisfies source right identity once the literal fixed-base
family law has been supplied. -/
theorem source_compose_right_identity_equivalent_of_familyLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    (α : LocallyDefinedHomRepresentative (J := J) X x y)
    (hα : LocallyDefinedHomRepresentativeOver.sourceComposeOverRightIdentityFamilyLaw
      (J := J) α.representative) :
    Equivalent (J := J)
      (compose (J := J) α (sourceIdentityHomToRepresentative (J := J) X y)) α := by
  apply (equivalent_iff_exists_base_eq (J := J)
    (compose (J := J) α (sourceIdentityHomToRepresentative (J := J) X y)) α).2
  refine ⟨by simp [sourceIdentityHomToRepresentative], ?_⟩
  rcases α with ⟨f, a⟩
  dsimp [compose, sourceIdentityHomToRepresentative]
  exact
    LocallyDefinedHomRepresentativeOver.sourceComposeOver_right_identity_equivalent_of_familyLaw
      (J := J) a hα

end LocallyDefinedHomRepresentative

namespace LocallyDefinedHom

/-- Plus-packaged composition satisfies source left identity once a representative satisfies the
literal fixed-base family law. -/
theorem source_id_comp_of_representative_familyLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    (a : locallyDefinedHom (J := J) X x y)
    (α : LocallyDefinedHomRepresentative (J := J) X x y)
    (hα : α.toLocallyDefinedHom = a)
    (hLaw : LocallyDefinedHomRepresentativeOver.sourceComposeOverLeftIdentityFamilyLaw
      (J := J) α.representative) :
    comp (J := J) (sourceIdentityHomToLocallyDefinedHom (J := J) X x) a = a := by
  calc
    comp (J := J) (sourceIdentityHomToLocallyDefinedHom (J := J) X x) a =
        (LocallyDefinedHomRepresentative.compose (J := J)
          (sourceIdentityHomToRepresentative (J := J) X x) α).toLocallyDefinedHom := by
      exact comp_eq_of_representatives (J := J)
        (sourceIdentityHomToRepresentative (J := J) X x).toLocallyDefinedHom a
        (sourceIdentityHomToRepresentative (J := J) X x) α rfl hα
    _ = α.toLocallyDefinedHom :=
      LocallyDefinedHomRepresentative.source_compose_left_identity_equivalent_of_familyLaw
        (J := J) α hLaw
    _ = a := hα

/-- Plus-packaged composition satisfies source right identity once a representative satisfies the
literal fixed-base family law. -/
theorem source_comp_id_of_representative_familyLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    (a : locallyDefinedHom (J := J) X x y)
    (α : LocallyDefinedHomRepresentative (J := J) X x y)
    (hα : α.toLocallyDefinedHom = a)
    (hLaw : LocallyDefinedHomRepresentativeOver.sourceComposeOverRightIdentityFamilyLaw
      (J := J) α.representative) :
    comp (J := J) a (sourceIdentityHomToLocallyDefinedHom (J := J) X y) = a := by
  calc
    comp (J := J) a (sourceIdentityHomToLocallyDefinedHom (J := J) X y) =
        (LocallyDefinedHomRepresentative.compose (J := J)
          α (sourceIdentityHomToRepresentative (J := J) X y)).toLocallyDefinedHom := by
      exact comp_eq_of_representatives (J := J)
        a (sourceIdentityHomToRepresentative (J := J) X y).toLocallyDefinedHom
        α (sourceIdentityHomToRepresentative (J := J) X y) hα rfl
    _ = α.toLocallyDefinedHom :=
      LocallyDefinedHomRepresentative.source_compose_right_identity_equivalent_of_familyLaw
        (J := J) α hLaw
    _ = a := hα

end LocallyDefinedHom

end FibredCategoryMor

end CategoryTheory
