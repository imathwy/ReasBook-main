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
- best owner abstraction: `F.kernel`, i.e. the inverse image of the owner property
  `IsZero` along `F`;
- primitive data: only the object property `IsZero` on the target category and the inverse-image
  construction along `F`;
- derived API: closure under isomorphisms, stability under retracts, triangulatedity of the
  kernel object property, and the induced triangulated structure on its full subcategory;
- source/core/bridge triage:
  `source-facing`: the Stacks lemma that the kernel of an exact functor is strictly full,
    saturated, and triangulated;
  `core/canonical`: `F.kernel` together with the owner predicates on object properties;
  `bridge/view`: the full-subcategory realization `F.kernel.FullSubcategory`.

The only missing reusable owner facts are that `IsZero` is closed under isomorphisms, stable under
retracts, and triangulated, plus that retract-stability is preserved by inverse image. The shift
and triangulated inverse-image owners are already upstream, so once these local owner facts are
present all four statements of the lemma are direct recalls.
-/

namespace ObjectProperty

instance {C : Type u} [Category.{v₁} C] :
    IsClosedUnderIsomorphisms (IsZero : ObjectProperty C) where
  of_iso e hY := IsZero.of_iso hY e.symm

instance {C : Type u} [Category.{v₁} C] [HasZeroMorphisms C] :
    IsStableUnderRetracts (IsZero : ObjectProperty C) where
  of_retract r hY := IsZero.of_mono r.i hY

instance
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (P : ObjectProperty D) [P.IsStableUnderRetracts] (F : C ⥤ D) :
    (P.inverseImage F).IsStableUnderRetracts where
  of_retract r hY := P.prop_of_retract (r.map F) hY

instance
    {C : Type u} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] :
    ObjectProperty.IsTriangulated (IsZero : ObjectProperty C) where
  exists_zero := ⟨0, isZero_zero C, isZero_zero C⟩
  toIsStableUnderShift := {
    isStableUnderShiftBy := fun n ↦
      ⟨fun _ hX ↦ Functor.map_isZero (shiftFunctor C n) hX⟩
  }
  toIsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ ↦ T.isZero₂_of_isZero₁₃ hT h₁ h₃)

end ObjectProperty

section StrictlyFull

variable {D : Type u₁} [Category.{v₁} D]
variable {D' : Type u₂} [Category.{v₂} D']
variable (F : D ⥤ D')

/- Lemma 13.6.2 (1): the objects of `D` sent to zero by `F` are closed under isomorphisms. This
is exactly the canonical instance on `F.kernel`. -/
#check (inferInstance : F.kernel.IsClosedUnderIsomorphisms)

end StrictlyFull

section StableUnderRetracts

variable {D : Type u₁} [Category.{v₁} D]
variable {D' : Type u₂} [Category.{v₂} D'] [HasZeroMorphisms D']
variable (F : D ⥤ D')

/- Lemma 13.6.2 (2): the kernel object property is stable under retracts. This is the canonical
inverse-image instance, specialized to the owner property `IsZero`, and only uses zero morphisms
on the target. -/
#check (inferInstance : F.kernel.IsStableUnderRetracts)

end StableUnderRetracts

section KernelTriangulated

variable {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {D' : Type u₂} [Category.{v₂} D'] [HasZeroObject D'] [HasShift D' ℤ]
  [Preadditive D'] [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
variable (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]

/- Lemma 13.6.2 (3): the kernel object property is triangulated. This is the canonical inverse
image of the triangulated owner property `IsZero`. -/
#check (inferInstance : F.kernel.IsTriangulated)

section

variable [IsTriangulated D]

/- Lemma 13.6.2 (4): if the ambient category is triangulated, then the full subcategory cut out by
`F.kernel` is triangulated. This is the generic full-subcategory instance. -/
#check (inferInstance : IsTriangulated F.kernel.FullSubcategory)

end

end KernelTriangulated

end CategoryTheory
