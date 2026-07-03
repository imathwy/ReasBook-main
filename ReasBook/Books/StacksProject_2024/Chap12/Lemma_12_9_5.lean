import StacksProject_2024.Chap12.Lemma_12_9_4

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open Opposite

/-
Domain-style sampling for Lemma 12.9.5:
- primary domain: object properties in an abelian category, with Noetherian objects organized by
  the owner predicate `isNoetherianObject : ObjectProperty C`;
- inspected owner declarations:
  `isNoetherianObject`,
  `ObjectProperty.IsSerreClass`,
  `ObjectProperty.prop_iff_of_shortExact`,
  `ShortComplex.ShortExact.op`,
  `ShortComplex.isArtinianObject_iff_of_shortExact`;
- best owner abstraction: the object property `isNoetherianObject` together with the LinearRepresentations_Serre_1977-class
  owner interface;
- primitive data: a short exact sequence in `C`, together with the canonical opposite short
  complex in `Cᵒᵖ`;
- derived API: the LinearRepresentations_Serre_1977-class instance and the short-exact characterization obtained from
  `ObjectProperty.prop_iff_of_shortExact`.

Source/core/bridge triage:
- `source-facing`: the textbook statement that Noetherian objects are stable in short exact
  sequences;
- `core/canonical`: `isNoetherianObject : ObjectProperty C` and the owner theorem
  `ObjectProperty.prop_iff_of_shortExact`;
- `bridge/view`: the imported duality bridge `isNoetherianObject_iff_isArtinianObject_op` from
  Lemma 12.9.4 together with the canonical opposite short complex `S.op`.
-/

section

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem isNoetherianObject_iff_of_shortExact_aux {S : ShortComplex C} (hS : S.ShortExact) :
    IsNoetherianObject S.X₂ ↔ IsNoetherianObject S.X₁ ∧ IsNoetherianObject S.X₃ := by
  constructor
  · intro h₂
    have h₂' : IsArtinianObject (Opposite.op S.X₂) :=
      (isNoetherianObject_iff_isArtinianObject_op S.X₂).mp h₂
    have hOp := (ShortComplex.isArtinianObject_iff_of_shortExact hS.op).mp h₂'
    exact ⟨
      (isNoetherianObject_iff_isArtinianObject_op S.X₁).mpr (by simpa using hOp.2),
      (isNoetherianObject_iff_isArtinianObject_op S.X₃).mpr (by simpa using hOp.1)⟩
  · rintro ⟨h₁, h₃⟩
    have h₁' : IsArtinianObject (Opposite.op S.X₁) :=
      (isNoetherianObject_iff_isArtinianObject_op S.X₁).mp h₁
    have h₃' : IsArtinianObject (Opposite.op S.X₃) :=
      (isNoetherianObject_iff_isArtinianObject_op S.X₃).mp h₃
    exact (isNoetherianObject_iff_isArtinianObject_op S.X₂).mpr <|
      (ShortComplex.isArtinianObject_iff_of_shortExact hS.op).mpr ⟨h₃', h₁'⟩

/-- Lemma 12.9.5 owner abstraction: in an abelian category, Noetherian objects form a LinearRepresentations_Serre_1977
class. -/
instance isNoetherianObject_isSerreClass :
    (isNoetherianObject : ObjectProperty C).IsSerreClass where
  exists_zero := ObjectProperty.ContainsZero.exists_zero
  prop_of_mono f _ hX := isNoetherianObject.prop_of_mono f hX
  prop_of_epi {X} {Y} f _ hX := by
    rw [← isNoetherianObject.is_iff] at hX ⊢
    letI : IsArtinianObject (Opposite.op X) :=
      (isNoetherianObject_iff_isArtinianObject_op X).mp hX
    exact (isNoetherianObject_iff_isArtinianObject_op Y).mpr
      (isArtinianObject_of_mono f.op)
  prop_X₂_of_shortExact hS h₁ h₃ := by
    rw [← isNoetherianObject.is_iff] at h₁ h₃ ⊢
    exact (isNoetherianObject_iff_of_shortExact_aux hS).mpr ⟨h₁, h₃⟩

namespace ShortComplex

variable {S : ShortComplex C}

/-- Lemma 12.9.5: in a short exact sequence in an abelian category, the middle object is
Noetherian if and only if the left and right objects are Noetherian. -/
lemma isNoetherianObject_iff_of_shortExact (hS : S.ShortExact) :
    IsNoetherianObject S.X₂ ↔ IsNoetherianObject S.X₁ ∧ IsNoetherianObject S.X₃ := by
  simpa [IsNoetherianObject, ObjectProperty.is_iff] using
    isNoetherianObject.prop_iff_of_shortExact hS

end ShortComplex

end
end CategoryTheory
