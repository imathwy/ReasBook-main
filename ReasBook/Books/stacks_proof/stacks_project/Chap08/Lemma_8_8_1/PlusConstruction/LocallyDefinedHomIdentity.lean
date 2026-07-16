import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomCast
import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomIdentityCoherence

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

/-- Source stage 2.4 left-identity local-family law.  This is the exact remaining local
coherence calculation after the cover-theoretic identity refinement has been separated out:
the transported composite of the trivial identity representative with `α` must be the refinement
of `α` to the composition cover. -/
noncomputable def composeOverLeftIdentityFamilyLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f) : Prop :=
  let comp := composeOver (J := J) (ordinaryHomToRepresentativeOver (J := J) X (𝟙 x)) α
  let hbase : (ordinaryHomToRepresentative (J := J) X (𝟙 x)).base ≫ f = f := by
    simp [ordinaryHomToRepresentative]
  castBaseFamily (J := J) hbase comp =
    α.family.refine (compositionCoverLeftIdentityHom (J := J) α)

/-- Source stage 2.4 right-identity local-family law. -/
noncomputable def composeOverRightIdentityFamilyLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f) : Prop :=
  let comp := composeOver (J := J) α (ordinaryHomToRepresentativeOver (J := J) X (𝟙 y))
  let hbase : f ≫ (ordinaryHomToRepresentative (J := J) X (𝟙 y)).base = f := by
    simp [ordinaryHomToRepresentative]
  castBaseFamily (J := J) hbase comp =
    α.family.refine (compositionCoverRightIdentityHom (J := J) α)

/-- If the left-identity local-family law holds, the fixed-base composite representative is
equivalent to the original representative. -/
theorem composeOver_left_identity_equivalent_of_familyLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (hα : composeOverLeftIdentityFamilyLaw (J := J) α) :
    Equivalent (J := J)
      (castBase (J := J) (by simp [ordinaryHomToRepresentative] :
        (ordinaryHomToRepresentative (J := J) X (𝟙 x)).base ≫ f = f)
        (composeOver (J := J) (ordinaryHomToRepresentativeOver (J := J) X (𝟙 x)) α))
      α := by
  let comp := composeOver (J := J) (ordinaryHomToRepresentativeOver (J := J) X (𝟙 x)) α
  let hbase : (ordinaryHomToRepresentative (J := J) X (𝟙 x)).base ≫ f = f := by
    simp [ordinaryHomToRepresentative]
  change Equivalent (J := J) (castBase (J := J) hbase comp) α
  refine ⟨comp.cover, coverHomCastBase (J := J) hbase comp,
    compositionCoverLeftIdentityHom (J := J) α, ?_⟩
  rw [castBase_family_refine_coverHomCastBase]
  exact hα

/-- If the right-identity local-family law holds, the fixed-base composite representative is
equivalent to the original representative. -/
theorem composeOver_right_identity_equivalent_of_familyLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (hα : composeOverRightIdentityFamilyLaw (J := J) α) :
    Equivalent (J := J)
      (castBase (J := J) (by simp [ordinaryHomToRepresentative] :
        f ≫ (ordinaryHomToRepresentative (J := J) X (𝟙 y)).base = f)
        (composeOver (J := J) α (ordinaryHomToRepresentativeOver (J := J) X (𝟙 y))))
      α := by
  let comp := composeOver (J := J) α (ordinaryHomToRepresentativeOver (J := J) X (𝟙 y))
  let hbase : f ≫ (ordinaryHomToRepresentative (J := J) X (𝟙 y)).base = f := by
    simp [ordinaryHomToRepresentative]
  change Equivalent (J := J) (castBase (J := J) hbase comp) α
  refine ⟨comp.cover, coverHomCastBase (J := J) hbase comp,
    compositionCoverRightIdentityHom (J := J) α, ?_⟩
  rw [castBase_family_refine_coverHomCastBase]
  exact hα

end LocallyDefinedHomRepresentativeOver

namespace LocallyDefinedHomRepresentative

/-- Raw locally-defined composition satisfies the left identity law once the fixed-base
local-family identity calculation has been supplied. -/
theorem compose_left_identity_equivalent_of_familyLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    (α : LocallyDefinedHomRepresentative (J := J) X x y)
    (hα : LocallyDefinedHomRepresentativeOver.composeOverLeftIdentityFamilyLaw
      (J := J) α.representative) :
    Equivalent (J := J)
      (compose (J := J) (ordinaryHomToRepresentative (J := J) X (𝟙 x)) α) α := by
  apply (equivalent_iff_exists_base_eq (J := J)
    (compose (J := J) (ordinaryHomToRepresentative (J := J) X (𝟙 x)) α) α).2
  refine ⟨by simp [ordinaryHomToRepresentative], ?_⟩
  rcases α with ⟨f, a⟩
  dsimp [compose, ordinaryHomToRepresentative]
  exact LocallyDefinedHomRepresentativeOver.composeOver_left_identity_equivalent_of_familyLaw
    (J := J) a hα

/-- Raw locally-defined composition satisfies the right identity law once the fixed-base
local-family identity calculation has been supplied. -/
theorem compose_right_identity_equivalent_of_familyLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    (α : LocallyDefinedHomRepresentative (J := J) X x y)
    (hα : LocallyDefinedHomRepresentativeOver.composeOverRightIdentityFamilyLaw
      (J := J) α.representative) :
    Equivalent (J := J)
      (compose (J := J) α (ordinaryHomToRepresentative (J := J) X (𝟙 y))) α := by
  apply (equivalent_iff_exists_base_eq (J := J)
    (compose (J := J) α (ordinaryHomToRepresentative (J := J) X (𝟙 y))) α).2
  refine ⟨by simp [ordinaryHomToRepresentative], ?_⟩
  rcases α with ⟨f, a⟩
  dsimp [compose, ordinaryHomToRepresentative]
  exact LocallyDefinedHomRepresentativeOver.composeOver_right_identity_equivalent_of_familyLaw
    (J := J) a hα

end LocallyDefinedHomRepresentative

namespace LocallyDefinedHom

/-- Locally-defined composition satisfies the left identity law once a representative of the
given plus-section satisfies the fixed-base local-family identity calculation. -/
theorem id_comp_of_representative_familyLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    (a : locallyDefinedHom (J := J) X x y)
    (α : LocallyDefinedHomRepresentative (J := J) X x y)
    (hα : α.toLocallyDefinedHom = a)
    (hLaw : LocallyDefinedHomRepresentativeOver.composeOverLeftIdentityFamilyLaw
      (J := J) α.representative) :
    comp (J := J) (locallyDefinedHomId (J := J) X x) a = a := by
  calc
    comp (J := J) (locallyDefinedHomId (J := J) X x) a =
        (LocallyDefinedHomRepresentative.compose (J := J)
          (ordinaryHomToRepresentative (J := J) X (𝟙 x)) α).toLocallyDefinedHom := by
      rw [locallyDefinedHomId, ordinaryHomToLocallyDefinedHom]
      exact comp_eq_of_representatives (J := J)
        (ordinaryHomToRepresentative (J := J) X (𝟙 x)).toLocallyDefinedHom a
        (ordinaryHomToRepresentative (J := J) X (𝟙 x)) α rfl hα
    _ = α.toLocallyDefinedHom :=
      LocallyDefinedHomRepresentative.compose_left_identity_equivalent_of_familyLaw
        (J := J) α hLaw
    _ = a := hα

/-- Locally-defined composition satisfies the right identity law once a representative of the
given plus-section satisfies the fixed-base local-family identity calculation. -/
theorem comp_id_of_representative_familyLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    (a : locallyDefinedHom (J := J) X x y)
    (α : LocallyDefinedHomRepresentative (J := J) X x y)
    (hα : α.toLocallyDefinedHom = a)
    (hLaw : LocallyDefinedHomRepresentativeOver.composeOverRightIdentityFamilyLaw
      (J := J) α.representative) :
    comp (J := J) a (locallyDefinedHomId (J := J) X y) = a := by
  calc
    comp (J := J) a (locallyDefinedHomId (J := J) X y) =
        (LocallyDefinedHomRepresentative.compose (J := J)
          α (ordinaryHomToRepresentative (J := J) X (𝟙 y))).toLocallyDefinedHom := by
      rw [locallyDefinedHomId, ordinaryHomToLocallyDefinedHom]
      exact comp_eq_of_representatives (J := J)
        a (ordinaryHomToRepresentative (J := J) X (𝟙 y)).toLocallyDefinedHom
        α (ordinaryHomToRepresentative (J := J) X (𝟙 y)) hα rfl
    _ = α.toLocallyDefinedHom :=
      LocallyDefinedHomRepresentative.compose_right_identity_equivalent_of_familyLaw
        (J := J) α hLaw
    _ = a := hα

end LocallyDefinedHom
end FibredCategoryMor

end CategoryTheory
