import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

namespace Scheme

/- Semantic recall: `lean_leansearch` surfaced the canonical morphism owner
`AlgebraicGeometry.LocallyOfFinitePresentation` and base-change stability for it, while local
Chapter 34 precedent represents full subcategories over a scheme by
`ObjectProperty.FullSubcategory`. Local Chapter 32 precedent represents directed limits of schemes
by `D : OrderDual I ⥤ Scheme`, a cone `c`, and `hc : IsLimit c`. -/

/-- The object property on `Over T` selecting quasi-compact, quasi-separated schemes locally of
finite presentation over `T`. -/
@[stacks 0EY1]
abbrev qcqsLocallyOfFinitePresentationOverProperty (T : Scheme.{u}) :
    ObjectProperty (Over T) :=
  fun W ↦ CompactSpace W.left.carrier ∧
    QuasiSeparatedSpace W.left.carrier ∧ LocallyOfFinitePresentation W.hom

/-- The full subcategory of schemes over `T` whose source is quasi-compact and quasi-separated
and whose structure morphism to `T` is locally of finite presentation. -/
@[stacks 0EY1]
abbrev QcqsLocallyOfFinitePresentationOver (T : Scheme.{u}) : Type (u + 1) :=
  (qcqsLocallyOfFinitePresentationOverProperty T).FullSubcategory

namespace QcqsLocallyOfFinitePresentationOver

/-- The inclusion of `QcqsLocallyOfFinitePresentationOver T` into all schemes over `T`. -/
abbrev inclusion (T : Scheme.{u}) :
    QcqsLocallyOfFinitePresentationOver T ⥤ Over T :=
  (qcqsLocallyOfFinitePresentationOverProperty T).ι

/-- Objects of `QcqsLocallyOfFinitePresentationOver T` have quasi-compact source. -/
instance instCompactSpaceLeft (T : Scheme.{u}) (W : QcqsLocallyOfFinitePresentationOver T) :
    CompactSpace (W.obj.left : Scheme.{u}).carrier :=
  W.property.1

/-- Objects of `QcqsLocallyOfFinitePresentationOver T` have quasi-separated source. -/
instance instQuasiSeparatedSpaceLeft (T : Scheme.{u})
    (W : QcqsLocallyOfFinitePresentationOver T) :
    QuasiSeparatedSpace (W.obj.left : Scheme.{u}).carrier :=
  W.property.2.1

/-- Objects of `QcqsLocallyOfFinitePresentationOver T` are locally of finite presentation over
the base. -/
instance instLocallyOfFinitePresentationHom (T : Scheme.{u})
    (W : QcqsLocallyOfFinitePresentationOver T) :
    LocallyOfFinitePresentation W.obj.hom :=
  W.property.2.2

/-- Membership in `QcqsLocallyOfFinitePresentationOver T` exposes exactly the three source
conditions: quasi-compact source, quasi-separated source, and locally finite presentation over
`T`. -/
theorem property_iff (T : Scheme.{u}) (W : Over T) :
    qcqsLocallyOfFinitePresentationOverProperty T W ↔
      CompactSpace W.left.carrier ∧
        QuasiSeparatedSpace W.left.carrier ∧ LocallyOfFinitePresentation W.hom := sorry

/-- Base change sends objects of `QcqsLocallyOfFinitePresentationOver T` to objects of
`QcqsLocallyOfFinitePresentationOver T'`. -/
@[stacks 0EY1]
theorem baseChange_mem {T T' : Scheme.{u}} (f : T' ⟶ T)
    (W : Over T) (hW : qcqsLocallyOfFinitePresentationOverProperty T W) :
    qcqsLocallyOfFinitePresentationOverProperty T' ((Over.pullback f).obj W) := sorry

/-- Lemma 32.10.5 (1): for `C_T` the full subcategory of schemes `W` over `T` such that `W` is
quasi-compact and quasi-separated and `W ⟶ T` is locally of finite presentation, if
`S = lim_i S_i` is a directed limit of schemes with affine transition morphisms, then every
object of `C_S` descends after increasing the index. This is the essential-surjectivity clause of
the base-change functor `colim_i C_{S_i} ⥤ C_S`. -/
@[stacks 0EY1]
theorem exists_stage_of_qcqsLocallyOfFinitePresentationOver_limit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j).carrier]
    [∀ j, QuasiSeparatedSpace (D.obj j).carrier]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (X : Over c.pt) (hX : qcqsLocallyOfFinitePresentationOverProperty c.pt X) :
    ∃ (i : I) (Xi : Over (D.obj i)),
      qcqsLocallyOfFinitePresentationOverProperty (D.obj i) Xi ∧
        Nonempty ((Over.pullback (c.π.app i)).obj Xi ≅ X) := sorry

/-- Lemma 32.10.5 (2): in the directed inverse-limit setup of Lemma 32.10.5, a morphism over the
limit between two base-changed objects descends, after passing to a later stage, to a morphism
between the corresponding stagewise base changes. This is the fullness clause of the base-change
functor `colim_i C_{S_i} ⥤ C_S`. -/
@[stacks 0EY1]
theorem exists_ge_hom_stageBaseChange_of_limitBaseChange
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j).carrier]
    [∀ j, QuasiSeparatedSpace (D.obj j).carrier]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (i : I) (X Y : Over (D.obj i))
    (hX : qcqsLocallyOfFinitePresentationOverProperty (D.obj i) X)
    (hY : qcqsLocallyOfFinitePresentationOverProperty (D.obj i) Y)
    (f : (Over.pullback (c.π.app i)).obj X ⟶ (Over.pullback (c.π.app i)).obj Y) :
    ∃ (i' : I) (hii' : i ≤ i')
      (hcomp : c.π.app i' ≫ D.map (homOfLE hii') = c.π.app i)
      (g : (Over.pullback (D.map (homOfLE hii'))).obj X ⟶
        (Over.pullback (D.map (homOfLE hii'))).obj Y),
      (Over.pullbackComp (c.π.app i') (D.map (homOfLE hii'))).hom.app X ≫
          (Over.pullback (c.π.app i')).map g ≫
        (Over.pullbackComp (c.π.app i') (D.map (homOfLE hii'))).inv.app Y =
        eqToHom (congrArg (fun F : Over (D.obj i) ⥤ Over c.pt ↦ F.obj X)
          (Over.pullback.congr_simp (c.π.app i' ≫ D.map (homOfLE hii'))
            (c.π.app i) hcomp)) ≫
          f ≫
        eqToHom (Eq.symm (congrArg (fun F : Over (D.obj i) ⥤ Over c.pt ↦ F.obj Y)
          (Over.pullback.congr_simp (c.π.app i' ≫ D.map (homOfLE hii'))
            (c.π.app i) hcomp))) := sorry

/-- Lemma 32.10.5 (3): in the directed inverse-limit setup of Lemma 32.10.5, if two morphisms
between objects of some `C_{S_i}` agree after base change to `S`, then after passing to a later
stage their base changes already agree. This is the faithfulness clause of the base-change functor
`colim_i C_{S_i} ⥤ C_S`. -/
@[stacks 0EY1]
theorem exists_ge_eq_stageBaseChange_of_eq_limitBaseChange
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j).carrier]
    [∀ j, QuasiSeparatedSpace (D.obj j).carrier]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (i : I) (X Y : Over (D.obj i))
    (hX : qcqsLocallyOfFinitePresentationOverProperty (D.obj i) X)
    (hY : qcqsLocallyOfFinitePresentationOverProperty (D.obj i) Y)
    (f g : X ⟶ Y)
    (hfg : (Over.pullback (c.π.app i)).map f = (Over.pullback (c.π.app i)).map g) :
    ∃ (i' : I) (hii' : i ≤ i'),
      (Over.pullback (D.map (homOfLE hii'))).map f =
        (Over.pullback (D.map (homOfLE hii'))).map g := sorry

end QcqsLocallyOfFinitePresentationOver

end Scheme

end AlgebraicGeometry
