import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomIdentityCoherence
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHom

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

/-- Source stage 2.4 identity representative with the base arrow literally `𝟙`.

The older ordinary-arrow representative of `𝟙 x` has base arrow `X.p.map (𝟙 x)`, which is only
propositionally equal to `𝟙 (X.p.obj x)`.  This source-facing representative records the Stacks
datum `(id_U, {id_U}, id_x)` on the owner where the base identity is literal. -/
noncomputable def sourceIdentityHomToRepresentativeOver
    (X : FibredCategoryOver.{u, v, uX, vX} C) (x : X.S) :
    LocallyDefinedHomRepresentativeOver (J := J) X (𝟙 (X.p.obj x)) where
  cover := ⊤
  family :=
    Meq.mk ⊤
      (ULift.up
        (((canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv)
          (((canonicalFiberPseudofunctor X.p).mapId
            (LocallyDiscrete.mk (op (X.p.obj x)))).inv.toNatTrans.app
              (Functor.Fiber.mk (p := X.p) (a := x) rfl))))

/-- Source stage 2.4 identity representative, including the displayed base arrow. -/
noncomputable def sourceIdentityHomToRepresentative
    (X : FibredCategoryOver.{u, v, uX, vX} C) (x : X.S) :
    LocallyDefinedHomRepresentative (J := J) X x x where
  base := 𝟙 (X.p.obj x)
  representative := sourceIdentityHomToRepresentativeOver (J := J) X x

/-- The plus-packaged morphism represented by the source-facing identity representative. -/
noncomputable def sourceIdentityHomToLocallyDefinedHom
    (X : FibredCategoryOver.{u, v, uX, vX} C) (x : X.S) :
    locallyDefinedHom (J := J) X x x :=
  (sourceIdentityHomToRepresentative (J := J) X x).toLocallyDefinedHom

@[simp]
theorem sourceIdentityHomToLocallyDefinedHom_base
    (X : FibredCategoryOver.{u, v, uX, vX} C) (x : X.S) :
    (sourceIdentityHomToLocallyDefinedHom (J := J) X x).1 = 𝟙 (X.p.obj x) :=
  rfl

/-- Applying the literal identity representative on a cover arrow is restriction of the global
identity-slice representative. -/
theorem sourceIdentityHomToRepresentativeOver_family_apply
    (X : FibredCategoryOver.{u, v, uX, vX} C) (x : X.S)
    (I : (sourceIdentityHomToRepresentativeOver (J := J) X x).cover.Arrow) :
    (sourceIdentityHomToRepresentativeOver (J := J) X x).family I =
      (locallyDefinedHomSaturatedPresheaf X (𝟙 (X.p.obj x))).map I.f.op
        (ULift.up
          (((canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv)
            (((canonicalFiberPseudofunctor X.p).mapId
              (LocallyDiscrete.mk (op (X.p.obj x)))).inv.toNatTrans.app
                (Functor.Fiber.mk (p := X.p) (a := x) rfl)))) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Applying the literal identity representative on a cover arrow, with the `ULift` and
identity-slice Hom equivalence removed.  This is the local form of the source datum
`id_x|_{U_i}`. -/
theorem sourceIdentityHomToRepresentativeOver_family_apply_down
    (X : FibredCategoryOver.{u, v, uX, vX} C) (x : X.S)
    (I : (sourceIdentityHomToRepresentativeOver (J := J) X x).cover.Arrow) :
    ((sourceIdentityHomToRepresentativeOver (J := J) X x).family I).down =
      ((canonicalFiberPseudofunctor X.p).map I.Y.hom.op.toLoc).toFunctor.map
        (((canonicalFiberPseudofunctor X.p).mapId
          (LocallyDiscrete.mk (op (X.p.obj x)))).inv.toNatTrans.app
            (Functor.Fiber.mk (p := X.p) (a := x) rfl)) := by
  let Fp := canonicalFiberPseudofunctor X.p
  let xF : X.p.Fiber (X.p.obj x) := Functor.Fiber.mk (p := X.p) (a := x) rfl
  let idInv : xF ⟶ (Fp.map (𝟙 (LocallyDiscrete.mk (op (X.p.obj x))))).toFunctor.obj xF :=
    (Fp.mapId (LocallyDiscrete.mk (op (X.p.obj x)))).inv.toNatTrans.app xF
  rw [sourceIdentityHomToRepresentativeOver_family_apply (J := J) X x I]
  have hf : I.f = (Over.homMk I.Y.hom : I.Y ⟶ Over.mk (𝟙 (X.p.obj x))) := by
    ext
    simpa using I.f.w
  rw [hf]
  change ((locallyDefinedHomSaturatedPresheaf X (𝟙 (X.p.obj x))).map
        (Over.homMk I.Y.hom : I.Y ⟶ Over.mk (𝟙 (X.p.obj x))).op
        (ULift.up (((canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv) idInv))).down = _
  simpa [locallyDefinedHomSaturatedPresheaf, locallyDefinedHomPresheaf, Fp, xF, idInv] using
    (presheafHom_map_identitySlice_hom_overMk (p := X.p) I.Y.hom
      xF ((Fp.map (𝟙 (LocallyDiscrete.mk (op (X.p.obj x))))).toFunctor.obj xF) idInv)

namespace LocallyDefinedHomRepresentativeOver

/-- The source cover for the literal identity representative followed by a fixed representative
refines the representative's original cover. -/
noncomputable def sourceIdentityCompositionCoverLeftHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f) :
    compositionCover (J := J) (sourceIdentityHomToRepresentativeOver (J := J) X x) α ⟶
      α.cover :=
  homOfLE (by
    intro Y k hk
    let q : Y.left ⟶ X.p.obj x := k.left
    let Y0 : Over (X.p.obj x) := Over.mk (q ≫ 𝟙 (X.p.obj x))
    let θ0 : Y0 ⟶ Over.mk (𝟙 (X.p.obj x)) := Over.homMk q
    have hpull : (((J.pullback (𝟙 (X.p.obj x))).obj α.baseCover) :
        Sieve (X.p.obj x)) q := by
      have hslice :
          ((identitySliceCoverOfBaseCover (J := J)
              (((J.pullback (𝟙 (X.p.obj x))).obj α.baseCover)) :
              (J.over (X.p.obj x)).Cover (Over.mk (𝟙 (X.p.obj x)))) :
              Sieve (Over.mk (𝟙 (X.p.obj x)))) k := hk.2
      exact
        (Sieve.overEquiv_symm_iff
          (Y := Over.mk (𝟙 (X.p.obj x)))
          ((((J.pullback (𝟙 (X.p.obj x))).obj α.baseCover) :
            Sieve (X.p.obj x))) k).1 hslice
    have hbase : (α.baseCover : Sieve (X.p.obj x)) q := by
      change (α.baseCover : Sieve (X.p.obj x)) (q ≫ 𝟙 (X.p.obj x)) at hpull
      simpa [q] using hpull
    have hθ0 : (α.cover : Sieve (Over.mk (𝟙 (X.p.obj x)))) θ0 := by
      simpa [q, Y0, θ0] using
        (Sieve.overEquiv_iff (Y := Over.mk (𝟙 (X.p.obj x)))
          (α.cover : Sieve (Over.mk (𝟙 (X.p.obj x)))) q).1 hbase
    let θ : Y ⟶ Y0 := Over.homMk (𝟙 Y.left) (by simpa [q, Y0] using k.w)
    have hθ : θ ≫ θ0 = k := by
      ext
      exact Category.id_comp k.left
    simpa [hθ] using α.cover.1.downward_closed hθ0 θ)

/-- The source cover for a fixed representative followed by the literal identity representative
refines the representative's original cover. -/
noncomputable def sourceIdentityCompositionCoverRightHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f) :
    compositionCover (J := J) α (sourceIdentityHomToRepresentativeOver (J := J) X y) ⟶
      α.cover :=
  homOfLE (by
    intro Y k hk
    exact hk.1)

/-- Conversely, the original cover refines the source cover for the literal identity
representative followed by a fixed representative. -/
noncomputable def sourceIdentityCompositionCoverLeftInvHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f) :
    α.cover ⟶
      compositionCover (J := J) (sourceIdentityHomToRepresentativeOver (J := J) X x) α :=
  homOfLE (by
    intro Y k hk
    refine ⟨?_, ?_⟩
    · trivial
    · let Y₀ : Over (X.p.obj x) := Over.mk (k.left ≫ 𝟙 (X.p.obj x))
      let θ : Y₀ ⟶ Y := Over.homMk (𝟙 Y.left) (by simpa [Y₀] using k.w.symm)
      have hθ : θ ≫ k =
          (Over.homMk k.left :
            Over.mk (k.left ≫ 𝟙 (X.p.obj x)) ⟶
              Over.mk (𝟙 (X.p.obj x))) := by
        ext
        exact Category.id_comp k.left
      have hkcanon :
          (α.cover : Sieve (Over.mk (𝟙 (X.p.obj x))))
            (Over.homMk k.left :
              Over.mk (k.left ≫ 𝟙 (X.p.obj x)) ⟶
                Over.mk (𝟙 (X.p.obj x))) := by
        simpa [hθ] using α.cover.1.downward_closed hk θ
      have hbase : (α.baseCover : Sieve (X.p.obj x)) k.left := by
        exact
          (Sieve.overEquiv_iff (Y := Over.mk (𝟙 (X.p.obj x)))
            (α.cover : Sieve (Over.mk (𝟙 (X.p.obj x)))) k.left).2 hkcanon
      have hpull : (((J.pullback (𝟙 (X.p.obj x))).obj α.baseCover) :
          Sieve (X.p.obj x)) k.left := by
        change (α.baseCover : Sieve (X.p.obj x)) (k.left ≫ 𝟙 (X.p.obj x))
        simpa using hbase
      exact
        (Sieve.overEquiv_symm_iff (Y := Over.mk (𝟙 (X.p.obj x)))
          ((((J.pullback (𝟙 (X.p.obj x))).obj α.baseCover) :
            Sieve (X.p.obj x))) k).2 hpull)

/-- Conversely, the original cover refines the source cover for a fixed representative followed
by the literal identity representative. -/
noncomputable def sourceIdentityCompositionCoverRightInvHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f) :
    α.cover ⟶
      compositionCover (J := J) α (sourceIdentityHomToRepresentativeOver (J := J) X y) :=
  homOfLE (by
    intro Y k hk
    refine ⟨hk, ?_⟩
    have hbase :
        ((sourceIdentityHomToRepresentativeOver (J := J) X y).baseCover :
          Sieve (X.p.obj y)) (k.left ≫ f) := by
      change
        ((Sieve.overEquiv (Over.mk (𝟙 (X.p.obj y))))
          (⊤ : Sieve (Over.mk (𝟙 (X.p.obj y))))) (k.left ≫ f)
      exact
        (Sieve.overEquiv_iff (Y := Over.mk (𝟙 (X.p.obj y)))
          (⊤ : Sieve (Over.mk (𝟙 (X.p.obj y)))) (k.left ≫ f)).2 trivial
    have hpull : (((J.pullback f).obj
        (sourceIdentityHomToRepresentativeOver (J := J) X y).baseCover) :
        Sieve (X.p.obj x)) k.left := by
      change
        ((sourceIdentityHomToRepresentativeOver (J := J) X y).baseCover :
          Sieve (X.p.obj y)) (k.left ≫ f)
      exact hbase
    exact
      (Sieve.overEquiv_symm_iff (Y := Over.mk (𝟙 (X.p.obj x)))
        ((((J.pullback f).obj
          (sourceIdentityHomToRepresentativeOver (J := J) X y).baseCover) :
          Sieve (X.p.obj x))) k).2 hpull)

end LocallyDefinedHomRepresentativeOver

end FibredCategoryMor

end CategoryTheory
