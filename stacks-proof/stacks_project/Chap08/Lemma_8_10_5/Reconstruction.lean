import stacks_project.Chap04.Lemma_4_2_18
import stacks_project.Chap08.Lemma_8_10_5.Gluing

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

/-- Helper for Lemma 8.10.5: the reconstructed object over `y` is obtained by pulling the glued
source object back along the inverse of the glued target comparison `F(x) ≅ y`. -/
noncomputable def inherited_basis_reconstructed_object
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (gluedSourceObject : ((canonicalFiberPseudofunctor (G F)).DescentData g) →
      Xₛ.p.Fiber (Yₛ.p.obj y))
    (gluedTargetComparison : (D : ((canonicalFiberPseudofunctor (G F)).DescentData g)) →
      (fiberFunctor F (Yₛ.p.obj y)).obj (gluedSourceObject D) ≅
        Functor.Fiber.mk (a := y) rfl)
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g)) :
    (G F).Fiber y :=
  (((canonicalFiberPseudofunctor (G F)).map (gluedTargetComparison D).inv.1.op.toLoc).toFunctor.obj
    (Functor.Fiber.mk (a := (gluedSourceObject D).1) rfl))

/-- Helper for Lemma 8.10.5: restricting the glued terminal section of a slice-site sheaf along
one leg of the covering family recovers the corresponding local section. -/
theorem inherited_basis_glued_target_comparison_restrict
    {U : C} {ι : Type*} {Uᵢ : ι → C} (π : ∀ i, Uᵢ i ⟶ U)
    (P : (Over U)ᵒᵖ ⥤ Type _)
    (hP : Presheaf.IsSheaf (J.over U) P)
    (hf :
      Sieve.ofArrows (fun i ↦ Over.mk (π i))
        (fun i ↦
          (show Over.mk (π i) ⟶ Over.mk (𝟙 U) from Over.homMk (π i))) ∈
        (J.over U) (Over.mk (𝟙 U)))
    (x : ∀ i, P.obj (op (Over.mk (π i))))
    (hx :
      ∀ ⦃W : Over U⦄ ⦃i₁ i₂ : ι⦄
        (a : W ⟶ Over.mk (π i₁)) (b : W ⟶ Over.mk (π i₂)),
        P.map a.op (x i₁) = P.map b.op (x i₂))
    (i : ι) :
    P.map
        (show Over.mk (π i) ⟶ Over.mk (𝟙 U) from Over.homMk (π i)).op
        ((hP.amalgamateOfArrows
          (f := fun j ↦
            (show Over.mk (π j) ⟶ Over.mk (𝟙 U) from Over.homMk (π j)))
          (hf := hf)
          (x := fun j _ ↦ x j)
          (hx := by
            intro W i₁ i₂ a b hab
            funext _
            simpa using hx a b))
          PUnit.unit) =
      x i := by
  -- Use the owner restriction formula once, so later reconstruction lemmas do not reopen the
  -- amalgamated section itself.
  exact congrFun
    ((hP.amalgamateOfArrows_map
      (f := fun j ↦
        (show Over.mk (π j) ⟶ Over.mk (𝟙 U) from Over.homMk (π j)))
      (hf := hf)
      (x := fun j _ ↦ x j)
      (hx := by
        intro W i₁ i₂ a b hab
        funext _
        simpa using hx a b)
      i))
    PUnit.unit

/-- Helper for Lemma 8.10.5: once the reconstructed object comes with an objectwise counit
isomorphism, the canonical descent functor is an equivalence by the standard fully-faithful plus
objectwise-essential-surjectivity criterion. -/
theorem inherited_basis_toDescentData_isEquivalence_of_objwise_iso
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    [Functor.Full (((canonicalFiberPseudofunctor (G F)).toDescentData g))]
    [Functor.Faithful (((canonicalFiberPseudofunctor (G F)).toDescentData g))]
    (reconstructedObject : ((canonicalFiberPseudofunctor (G F)).DescentData g) →
      (G F).Fiber y)
    (hCounit :
      ∀ D : ((canonicalFiberPseudofunctor (G F)).DescentData g),
        (((canonicalFiberPseudofunctor (G F)).toDescentData g).obj
          (reconstructedObject D)) ≅ D) :
    (((canonicalFiberPseudofunctor (G F)).toDescentData g)).IsEquivalence := by
  -- The only remaining source-faithful input is the objectwise counit package for the
  -- reconstructed preimage assignment.
  exact
    Functor.fully_faithful_isEquivalence_of_objwise_iso
      (F := ((canonicalFiberPseudofunctor (G F)).toDescentData g))
      reconstructedObject
      (fun D ↦ (hCounit D).symm)

end

end CategoryTheory
