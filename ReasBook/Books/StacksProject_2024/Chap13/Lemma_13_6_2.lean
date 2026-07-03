import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/- Domain-style sampling for Lemma 13.6.2:
- primary domain: kernels of exact functors between pretriangulated categories, expressed as
  object properties and their induced full subcategories;
- sampled owner declarations:
  `Functor.kernel`,
  `ObjectProperty.inverseImage`,
  `ObjectProperty.IsTriangulated`,
  `IsTriangulated P.FullSubcategory`;
- best owner abstraction: `Functor.kernel F`, i.e. the inverse image of the owner property
  `IsZero` along `F`;
- primitive data: only the object property `IsZero` on the target category and the inverse-image
  construction along `F`;
- derived API: closure under isomorphisms, stability under retracts, triangulatedity of the
  kernel object property, and the induced triangulated structure on its full subcategory;
- source/core/bridge triage:
  `source-facing`: the Stacks lemma that the kernel of an exact functor is strictly full,
    saturated, and triangulated;
  `core/canonical`: `Functor.kernel F` together with the owner predicates on object properties;
  `bridge/view`: the full-subcategory realization `(Functor.kernel F).FullSubcategory`.

The only missing reusable owner facts are that `IsZero` is stable under retracts and
triangulated, plus that retract-stability is preserved by inverse image. Closure under
isomorphisms is then inherited from the generic retract-stability API.
Once those owner instances are present, all four statements of the lemma are direct recalls.
-/

namespace ObjectProperty

instance isZero_isStableUnderRetracts {C : Type u} [Category.{v₁} C] :
    IsStableUnderRetracts (IsZero : ObjectProperty C) where
  of_retract r hY := by
    refine ⟨?_, ?_⟩
    · intro Z
      refine ⟨⟨⟨r.i ≫ hY.to_ Z⟩, ?_⟩⟩
      intro f
      calc
        f = (r.i ≫ r.r) ≫ f := by simp [r.retract]
        _ = r.i ≫ (r.r ≫ f) := by simp
        _ = r.i ≫ hY.to_ Z := by rw [hY.eq_to (r.r ≫ f)]
    · intro Z
      refine ⟨⟨⟨hY.from_ Z ≫ r.r⟩, ?_⟩⟩
      intro f
      calc
        f = f ≫ (r.i ≫ r.r) := by simp [r.retract]
        _ = (f ≫ r.i) ≫ r.r := by simp
        _ = hY.from_ Z ≫ r.r := by rw [hY.eq_from (f ≫ r.i)]

instance inverseImage_isStableUnderRetracts
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (P : ObjectProperty D) [P.IsStableUnderRetracts] (F : C ⥤ D) :
    (P.inverseImage F).IsStableUnderRetracts where
  of_retract r hY := P.prop_of_retract (r.map F) hY

instance isZero_isStableUnderShift
    {C : Type u} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] :
    IsStableUnderShift (IsZero : ObjectProperty C) ℤ where
  isStableUnderShiftBy n := ⟨fun _ hX ↦ Functor.map_isZero (shiftFunctor C n) hX⟩

instance isZero_isTriangulated
    {C : Type u} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] :
    ObjectProperty.IsTriangulated (IsZero : ObjectProperty C) where
  exists_zero := ⟨0, isZero_zero C, isZero_zero C⟩
  toIsStableUnderShift := inferInstance
  toIsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ ↦ T.isZero₂_of_isZero₁₃ hT h₁ h₃)

end ObjectProperty

section StrictlyFull

variable {D : Type u₁} [Category.{v₁} D]
variable {D' : Type u₂} [Category.{v₂} D']
variable (F : D ⥤ D')

/- Lemma 13.6.2 (1): the objects of `D` sent to zero by `F` are closed under isomorphisms. This
is exactly the canonical instance on `Functor.kernel F`. -/
#check (inferInstance : ObjectProperty.IsClosedUnderIsomorphisms (Functor.kernel F))

end StrictlyFull

section KernelTriangulated

variable {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {D' : Type u₂} [Category.{v₂} D'] [HasZeroObject D'] [HasShift D' ℤ]
  [Preadditive D'] [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
variable (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]

/- Lemma 13.6.2 (2): the kernel object property is stable under retracts. This is the canonical
inverse-image instance, specialized to the owner property `IsZero`. -/
#check (inferInstance : ObjectProperty.IsStableUnderRetracts (Functor.kernel F))

/- Lemma 13.6.2 (3): the kernel object property is triangulated. This is the canonical inverse
image of the triangulated owner property `IsZero`. -/
#check (inferInstance : ObjectProperty.IsTriangulated (Functor.kernel F))

section

variable [CategoryTheory.IsTriangulated D]

/- Lemma 13.6.2 (4): if the ambient category is triangulated, then the full subcategory cut out by
`Functor.kernel F` is triangulated. This is the generic full-subcategory instance. -/
#check (inferInstance : CategoryTheory.IsTriangulated (Functor.kernel F).FullSubcategory)

end

end KernelTriangulated

end CategoryTheory
