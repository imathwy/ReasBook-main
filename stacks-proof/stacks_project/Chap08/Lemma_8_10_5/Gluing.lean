import stacks_project.Chap08.Definition_8_2_2
import stacks_project.Chap08.Definition_8_5_5
import stacks_project.Chap08.Lemma_8_10_5.ForgetToSourceDescent

universe uC uX vC vX

namespace CategoryTheory

open FibredCategoryMor
open Functor IsStronglyCartesian
open StackInGroupoidsOver.Hom
open Opposite

section

variable {C : Type uC} [Category.{vC} C]
variable {J : GrothendieckTopology C}
variable {Xₛ Yₛ : StackInGroupoidsOver J}

/-- Helper for Lemma 8.10.5: once the source descent datum has been glued to an object `x`, the
`i`-th counit component in `Xₛ` becomes an isomorphism in the target fiber after applying `F` and
composing with the local target identification of `D.obj i`. -/
theorem inherited_basis_target_comparison_component_isIso
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (forgetToX : ((canonicalFiberPseudofunctor (G F)).DescentData g) ⥤
      ((canonicalFiberPseudofunctor Xₛ.p).DescentData (fun i ↦ Yₛ.p.map (g i))))
    (eX : Xₛ.p.Fiber (Yₛ.p.obj y) ≌
      ((canonicalFiberPseudofunctor Xₛ.p).DescentData (fun i ↦ Yₛ.p.map (g i))))
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g))
    (targetIso : ∀ i,
      (fiberFunctor F (Yₛ.p.obj (Y i))).obj ((forgetToX.obj D).obj i) ≅
        Functor.Fiber.mk (a := Y i) rfl)
    (i : ι) :
    IsIso
      ((fiberFunctor F (Yₛ.p.obj (Y i))).map ((eX.counitIso.app (forgetToX.obj D)).hom.hom i) ≫
        (targetIso i).hom) := by
  -- Both factors are isomorphisms: the first from the counit isomorphism component, the second
  -- by the supplied local target comparison in `(G F).Fiber (Y i)`.
  infer_instance

/-- Helper for Lemma 8.10.5: this packages the `i`-th local comparison between the glued target
`F(x)` and the descent object `D.obj i` as a section of the sheaf `Isom_Y(F(x), y)` over the
basis leg `g i`. The two restriction isomorphisms identify the slice-leg pullbacks of the global
comparison endpoints with their literal local models; the canonical instantiations supply them
definitionally. -/
noncomputable def inherited_basis_target_comparison_section
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (forgetToX : ((canonicalFiberPseudofunctor (G F)).DescentData g) ⥤
      ((canonicalFiberPseudofunctor Xₛ.p).DescentData (fun i ↦ Yₛ.p.map (g i))))
    (eX : Xₛ.p.Fiber (Yₛ.p.obj y) ≌
      ((canonicalFiberPseudofunctor Xₛ.p).DescentData (fun i ↦ Yₛ.p.map (g i))))
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g))
    (targetIso : ∀ i,
      (fiberFunctor F (Yₛ.p.obj (Y i))).obj ((forgetToX.obj D).obj i) ≅
        Functor.Fiber.mk (a := Y i) rfl)
    (i : ι)
    (restrictSourceIso :
      (((canonicalFiberPseudofunctor Yₛ.p).map (Yₛ.p.map (g i)).op.toLoc).toFunctor.obj
          ((fiberFunctor F (Yₛ.p.obj y)).obj (eX.inverse.obj (forgetToX.obj D)))) ≅
        ((fiberFunctor F (Yₛ.p.obj (Y i))).obj
          ((eX.functor.obj (eX.inverse.obj (forgetToX.obj D))).obj i)))
    (restrictTargetIso :
      (((canonicalFiberPseudofunctor Yₛ.p).map (Yₛ.p.map (g i)).op.toLoc).toFunctor.obj
          (Functor.Fiber.mk (a := y) rfl)) ≅
        (Functor.Fiber.mk (a := Y i) rfl : Yₛ.p.Fiber (Yₛ.p.obj (Y i)))) :
    ((fiberIsomorphismSubfunctor Yₛ.p
      ((fiberFunctor F (Yₛ.p.obj y)).obj (eX.inverse.obj (forgetToX.obj D)))
      (Functor.Fiber.mk (a := y) rfl)).toFunctor).obj (op (Over.mk (Yₛ.p.map (g i)))) := by
  letI : IsIso
      ((fiberFunctor F (Yₛ.p.obj (Y i))).map
          ((eX.counitIso.app (forgetToX.obj D)).hom.hom i) ≫
        (targetIso i).hom) :=
    inherited_basis_target_comparison_component_isIso
      (F := F) (Y := Y) (g := g) forgetToX eX D targetIso i
  -- Record the slice-restricted comparison composite as a section of the isomorphism
  -- subpresheaf by its `IsIso` witness.
  exact ⟨restrictSourceIso.hom ≫
      ((fiberFunctor F (Yₛ.p.obj (Y i))).map
          ((eX.counitIso.app (forgetToX.obj D)).hom.hom i) ≫
        (targetIso i).hom) ≫ restrictTargetIso.inv,
    (mem_fiberIsomorphismSubfunctor_obj_iff Yₛ.p
      ((fiberFunctor F (Yₛ.p.obj y)).obj (eX.inverse.obj (forgetToX.obj D)))
      (Functor.Fiber.mk (a := y) rfl)
      (A := op (Over.mk (Yₛ.p.map (g i))))
      (restrictSourceIso.hom ≫
        ((fiberFunctor F (Yₛ.p.obj (Y i))).map
            ((eX.counitIso.app (forgetToX.obj D)).hom.hom i) ≫
          (targetIso i).hom) ≫ restrictTargetIso.inv)).2
      (IsIso.comp_isIso' inferInstance
        (IsIso.comp_isIso'
          (inherited_basis_target_comparison_component_isIso
            (F := F) (Y := Y) (g := g) forgetToX eX D targetIso i)
          inferInstance))⟩

end

end CategoryTheory
