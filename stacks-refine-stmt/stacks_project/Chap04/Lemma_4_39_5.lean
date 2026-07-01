import Mathlib
import stacks_project.Chap04.Definition_4_32_1
import stacks_project.Chap04.Definition_4_38_3
import stacks_project.Chap04.Definition_4_39_3
import stacks_project.Chap04.Lemma_4_33_7
import stacks_project.Chap04.Lemma_4_35_9
import stacks_project.Chap04.Lemma_4_38_6

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Opposite
open BasedFunctor
open CategoryOfElements

namespace Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

/-- The restriction map on isomorphism classes induced by the canonical pullback functor. -/
private noncomputable def fiberIsoClassPresheafMap
    (p : S ⥤ C) [p.IsFibered] {U V : Cᵒᵖ} (f : U ⟶ V) :
    isomorphismClasses.obj (Cat.of (p.Fiber (unop U))) →
      isomorphismClasses.obj (Cat.of (p.Fiber (unop V))) :=
  isomorphismClasses.map ((canonicalPullbackChoice p).pullbackFunctor f.unop).toCatHom

/-- Pullback along an identity morphism acts trivially on isomorphism classes in the fibers. -/
private theorem fiberIsoClassPresheafMap_id
    (p : S ⥤ C) [p.IsFibered] (U : Cᵒᵖ) :
    fiberIsoClassPresheafMap p (𝟙 U) = id := sorry

/-- Pullback on isomorphism classes is contravariantly functorial in the base morphism. -/
private theorem fiberIsoClassPresheafMap_comp
    (p : S ⥤ C) [p.IsFibered] {U V W : Cᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) :
    fiberIsoClassPresheafMap p (f ≫ g) =
      fiberIsoClassPresheafMap p g ∘
        fiberIsoClassPresheafMap p f := sorry

/-- The presheaf sending `U` to the set of isomorphism classes of objects in the fiber `p⁻¹(U)`.
-/
noncomputable def fiberIsoClassPresheaf
    (p : S ⥤ C) [p.IsFibered] : Presheaf.{u₂} C where
  obj U := isomorphismClasses.obj (Cat.of (p.Fiber (unop U)))
  map f := fiberIsoClassPresheafMap p f
  map_id := fiberIsoClassPresheafMap_id p
  map_comp := fiberIsoClassPresheafMap_comp p

end Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {X : BasedCategory C}

/- Domain-style sampling for Lemma 4.39.5:
- primary domain: categories over a fixed base, compared by based equivalences and by the induced
  maps on isomorphism classes in each fiber;
- sampled owner-level declarations:
  `BasedFunctor.IsEquivalenceOverBase`,
  `BasedFunctor.fiberFunctor`,
  `IsFibredInSetoids`,
  `FibredInSetoidsOver.associatedFibredInSets`,
  `Functor.fiberIsoClassPresheaf`,
  `presheafToFibredInSetsOver`,
  `FibredInSetoidsOver.ofAmbientHom`;
- best owner abstraction: the based functor over `C` for the fiberwise clauses, and the canonical
  associated fibred-in-sets object `FibredInSetoidsOver.associatedFibredInSets` for the
  replacement-by-sets clause; the comparison morphism should expose only the owner hom, with its
  underlying based functor kept as internal bridge data;
- primitive data: bundled categories over `C` and, for the replacement-by-sets clause, the
  underlying based functor from `Z` to the category of elements of `Z.p.fiberIsoClassPresheaf`;
- derived API: the transported setoid condition, the induced bijection on isomorphism classes in
  each fiber, and the canonical comparison with the associated fibred-in-sets model.

Source/core/bridge triage:
- `source-facing`: the first two clauses of the lemma together with the canonical replacement by
  an associated fibred-in-sets object;
- `core/canonical`: `BasedFunctor.IsEquivalenceOverBase`, `BasedFunctor.fiberFunctor`,
  `IsFibredInSetoids`, `Functor.fiberIsoClassPresheaf`, and
  `FibredInSetoidsOver.associatedFibredInSets Z`;
- `bridge/view`: the internal based functor to the category of elements of
  `Z.p.fiberIsoClassPresheaf`, and the induced owner morphism `Z.toFibredInSets`. -/

namespace BasedFunctor

section

/-- In a discrete category, taking isomorphism classes is canonically equivalent to taking
objects. -/
private noncomputable def isoClassesEquivOfIsDiscrete
    (D : Type u₂) [Category.{v₂} D] [IsDiscrete D] :
    isomorphismClasses.obj (Cat.of D) ≃ D :=
  (Equiv.ofBijective
      (fun x : D ↦ Quotient.mk'' x)
      (by
        constructor
        · intro x y hxy
          exact Quotient.exact hxy |>.elim fun i ↦ obj_ext_of_isDiscrete i.hom
        · intro q
          refine Quotient.inductionOn q ?_
          intro x
          exact ⟨x, rfl⟩)).symm

/-- Equivalence over the base preserves the fibred-in-setoids condition. This is the transport
theorem used by later stack-in-setoids arguments. -/
theorem isFibredInSetoids_iff_of_isEquivalenceOverBase
    {Y : BasedCategory C} (F : X ⥤ᵇ Y) (hF : F.IsEquivalenceOverBase) :
    IsFibredInSetoids X.p ↔ IsFibredInSetoids Y.p := sorry

/-- An equivalence over the base induces a bijection on isomorphism classes in each fiber. -/
private theorem fiberIsoClassMap_bijective_of_isEquivalenceOverBase
    {Y : BasedCategory C} (F : X ⥤ᵇ Y) (hF : F.IsEquivalenceOverBase) (U : C) :
    Function.Bijective (isomorphismClasses.map (F.fiberFunctor U).toCatHom) := sorry

/-- If the target is fibred in sets, then its fiber over `U` is canonically identified with the
set of isomorphism classes in the source fiber over `U`. -/
noncomputable def fiberIsoClassesEquivFiber_of_isEquivalenceOverBase
    {Y : BasedCategory C} (F : X ⥤ᵇ Y) (hF : F.IsEquivalenceOverBase)
    [IsFibredInSets Y.p] (U : C) :
    isomorphismClasses.obj (Cat.of (X.p.Fiber U)) ≃ Y.p.Fiber U :=
  (Equiv.ofBijective
      (isomorphismClasses.map (F.fiberFunctor U).toCatHom)
      (fiberIsoClassMap_bijective_of_isEquivalenceOverBase F hF U)).trans
    (isoClassesEquivOfIsDiscrete (Y.p.Fiber U))

end

end BasedFunctor

namespace FibredInSetoidsOver

/-- Lemma 4.39.5: the category fibred in sets associated to `Z`, obtained from the category of
elements of the presheaf of fiberwise isomorphism classes. -/
noncomputable abbrev associatedFibredInSets
    (Z : FibredInSetoidsOver C) :
    FibredInSetsOver C :=
  presheafToFibredInSetsOver.obj Z.p.fiberIsoClassPresheaf

private noncomputable def fiberIsoClassElement
    (Z : FibredInSetoidsOver C) :
    Z.S → (Z.p.fiberIsoClassPresheaf).Elements :=
  fun a ↦
    (Z.p.fiberIsoClassPresheaf).elementsMk (op (Z.p.obj a)) (Quotient.mk'' ⟨a, rfl⟩)

private noncomputable def toFibredInSetsBasedFunctor
    (Z : FibredInSetoidsOver C) :
    Z.toBasedCategory ⥤ᵇ Z.associatedFibredInSets.toBasedCategory :=
  { toFunctor :=
      { obj := fun a ↦ op (fiberIsoClassElement Z a)
        map := fun {a b} φ ↦
          Quiver.Hom.op <|
            homMk
              (fiberIsoClassElement Z b)
              (fiberIsoClassElement Z a)
              (Z.p.map φ).op
              (by sorry)
        map_id := by
          intro a
          apply Quiver.Hom.unop_inj
          apply ext (Z.p.fiberIsoClassPresheaf)
          change (Z.p.map (𝟙 a)).op = 𝟙 (op (Z.p.obj a))
          simp
        map_comp := by
          intro a b c φ ψ
          apply Quiver.Hom.unop_inj
          apply ext (Z.p.fiberIsoClassPresheaf)
          change (Z.p.map (φ ≫ ψ)).op = (Z.p.map ψ).op ≫ (Z.p.map φ).op
          simp }
    w := rfl }

/-- The canonical comparison from a category fibred in setoids over `C` to the associated
category fibred in sets `Z.associatedFibredInSets`, given by the category of elements of the
owner presheaf `Z.p.fiberIsoClassPresheaf`. -/
noncomputable abbrev toFibredInSets
    (Z : FibredInSetoidsOver C) :
    Z ⟶ Z.associatedFibredInSets :=
  ofBasedFunctor (toFibredInSetsBasedFunctor Z)

/-- The canonical comparison from a category fibred in setoids over `C` to its associated
category fibred in sets is an equivalence over the base. -/
-- Proof sketch: identify the target with the category of elements of the presheaf of fiberwise
-- isomorphism classes and apply the fiberwise equivalence criterion from the first part of the
-- lemma to the canonical comparison functor `Z.toFibredInSets`.
theorem toFibredInSets_isEquivalenceOverBase
    (Z : FibredInSetoidsOver C) :
    IsEquivalenceOverBase
      ((Z.toFibredInSets) : Z ⟶ Z.associatedFibredInSets) :=
  sorry

end FibredInSetoidsOver

end CategoryTheory
