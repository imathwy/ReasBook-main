import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.Subobject.ArtinianObject
import Mathlib.CategoryTheory.Noetherian

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open Opposite

/-
Domain-style sampling for Lemma 12.9.4:
- primary domain: object properties in an abelian category, with Artinian and Noetherian
  conditions organized via the owner API `ObjectProperty`;
- inspected owner declarations:
  `isArtinianObject`,
  `isNoetherianObject`,
  `ObjectProperty.IsSerreClass`,
  `ObjectProperty.prop_iff_of_shortExact`;
- best owner abstraction: the object property `isArtinianObject : ObjectProperty C` together with
  the Serre-class owner interface;
- primitive data: only the Artinian object property itself and the short exact sequence;
- derived API: the Serre-class instance and the short-exact characterization obtained from
  `ObjectProperty.prop_iff_of_shortExact`.

Source/core/bridge triage:
- `source-facing`: the textbook statements that Artinian objects are closed under short exact
  sequences;
- `core/canonical`: `isArtinianObject : ObjectProperty C` and the owner theorem
  `ObjectProperty.prop_iff_of_shortExact`;
- `bridge/view`: the Artinian/Noetherian-op duality theorem below, which is the minimal bridge
  needed because mathlib does not yet provide this owner result.
-/

private theorem wellFoundedGT_subobject_iff_wellFoundedLT_subobject_op {C : Type u}
    [Category.{v} C] [Abelian C] (A : C) :
    WellFoundedGT (Subobject A) ↔ WellFoundedLT (Subobject (op A)) := by
  constructor
  · intro hA
    letI : WellFoundedGT (Subobject A) := hA
    letI : WellFoundedGT ((Subobject (op A))ᵒᵈ) :=
      (Abelian.subobjectIsoSubobjectOp A).symm.toOrderEmbedding.wellFoundedGT
    exact (wellFoundedGT_dual_iff (Subobject (op A))).1 inferInstance
  · intro hA
    letI : WellFoundedLT (Subobject (op A)) := hA
    letI : WellFoundedGT ((Subobject (op A))ᵒᵈ) := inferInstance
    exact (Abelian.subobjectIsoSubobjectOp A).toOrderEmbedding.wellFoundedGT

private theorem wellFoundedLT_subobject_iff_wellFoundedGT_subobject_op {C : Type u}
    [Category.{v} C] [Abelian C] (A : C) :
    WellFoundedLT (Subobject A) ↔ WellFoundedGT (Subobject (op A)) := by
  constructor
  · intro hA
    letI : WellFoundedLT (Subobject A) := hA
    letI : WellFoundedLT ((Subobject (op A))ᵒᵈ) :=
      (Abelian.subobjectIsoSubobjectOp A).symm.toOrderEmbedding.wellFoundedLT
    exact (wellFoundedGT_dual_iff ((Subobject (op A))ᵒᵈ)).1 inferInstance
  · intro hA
    letI : WellFoundedGT (Subobject (op A)) := hA
    have : WellFoundedLT ((Subobject (op A))ᵒᵈ) :=
      (wellFoundedGT_dual_iff ((Subobject (op A))ᵒᵈ)).1 inferInstance
    letI : WellFoundedLT (Subobject A) :=
      (Abelian.subobjectIsoSubobjectOp A).toOrderEmbedding.wellFoundedLT
    exact inferInstance

theorem isNoetherianObject_iff_isArtinianObject_op {C : Type u} [Category.{v} C]
    [Abelian C] (A : C) :
    IsNoetherianObject A ↔ IsArtinianObject (op A) := by
  simpa [IsNoetherianObject, ObjectProperty.is_iff, IsArtinianObject] using
    wellFoundedGT_subobject_iff_wellFoundedLT_subobject_op A

theorem isArtinianObject_iff_isNoetherianObject_op {C : Type u} [Category.{v} C]
    [Abelian C] (A : C) :
    IsArtinianObject A ↔ IsNoetherianObject (op A) := by
  simpa [IsArtinianObject, ObjectProperty.is_iff, IsNoetherianObject] using
    wellFoundedLT_subobject_iff_wellFoundedGT_subobject_op A

/-- Lemma 12.9.4 owner abstraction: in an abelian category, Artinian objects form a Serre
class. -/
instance isArtinianObject_isSerreClass {C : Type u} [Category.{v} C] [Abelian C] :
    (isArtinianObject : ObjectProperty C).IsSerreClass where
  exists_zero := ObjectProperty.ContainsZero.exists_zero
  prop_of_mono f _ hX := isArtinianObject.prop_of_mono f hX
  prop_of_epi {X} {Y} f _ hX := by
    rw [← isArtinianObject.is_iff] at hX ⊢
    letI : IsNoetherianObject (op X) :=
      (isArtinianObject_iff_isNoetherianObject_op X).mp hX
    exact (isArtinianObject_iff_isNoetherianObject_op Y).mpr
      (isNoetherianObject_of_mono f.op)
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    rw [← isArtinianObject.is_iff] at h₁ h₃ ⊢
    sorry

namespace ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex C}

/-- Lemma 12.9.4: in a short exact sequence in an abelian category, the middle object is
Artinian if and only if the left and right objects are Artinian. -/
-- Proof sketch: the owner abstraction is the object property `isArtinianObject`. Once this
-- property is known to form a Serre class, the statement is the canonical owner theorem
-- `ObjectProperty.prop_iff_of_shortExact`.
lemma isArtinianObject_iff_of_shortExact (hS : S.ShortExact) :
    IsArtinianObject S.X₂ ↔ IsArtinianObject S.X₁ ∧ IsArtinianObject S.X₃ := by
  simpa [IsArtinianObject, ObjectProperty.is_iff] using
    isArtinianObject.prop_iff_of_shortExact hS

end ShortComplex
end CategoryTheory
