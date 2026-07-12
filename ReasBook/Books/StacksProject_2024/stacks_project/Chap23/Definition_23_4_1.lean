import Mathlib.RingTheory.DividedPowers.DPMorphism

universe u v

namespace DividedPowers

/-
Source/core/bridge triage:
- `source-facing`: Definition 23.4.1 itself, namely the existence of divided powers on `I.map f`
  making `f` a divided power morphism.
- `core/canonical`: the predicate `DividedPowers.extendsAlong`.
- `bridge/view`: the bundled extension data `DividedPowers.Extension`.
-/

/-- An extension of the divided powers `γ` along `f` is a divided power structure on the image
ideal `Ideal.map f I` for which `f` is a divided power morphism. -/
abbrev Extension {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
    {B : Type v} [CommRing B] (f : A →+* B) :=
  { δ : DividedPowers (I.map f) // IsDPMorphism γ δ f }

/-- Definition 23.4.1: the divided powers `γ` extend along `f` if there exists divided powers on
`I.map f` making `f` a divided power morphism. -/
@[stacks 07H0]
def extendsAlong {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
    {B : Type v} [CommRing B] (f : A →+* B) : Prop :=
  ∃ δ : DividedPowers (I.map f), IsDPMorphism γ δ f

namespace Extension

variable {A : Type u} [CommRing A] {I : Ideal A} {γ : DividedPowers I}
variable {B : Type v} [CommRing B] {f : A →+* B}

/-- The divided power structure carried by an extension datum. -/
abbrev dividedPowers (h : γ.Extension f) : DividedPowers (I.map f) :=
  h.1

/-- The underlying ring map of an extension datum is a divided power morphism. -/
theorem isDPMorphism (h : γ.Extension f) :
    IsDPMorphism γ h.dividedPowers f :=
  h.2

theorem extendsAlong (h : γ.Extension f) : γ.extendsAlong f :=
  ⟨h.dividedPowers, h.isDPMorphism⟩

end Extension

/-- The defining expansion of `DividedPowers.extendsAlong`. -/
theorem extendsAlong_iff {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
    {B : Type v} [CommRing B] (f : A →+* B) :
    γ.extendsAlong f ↔ ∃ δ : DividedPowers (I.map f), IsDPMorphism γ δ f :=
  Iff.rfl

/-- The extension predicate is the nonemptiness of the type of extension data. -/
theorem extendsAlong_iff_nonempty_extension
    {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
    {B : Type v} [CommRing B] (f : A →+* B) :
    γ.extendsAlong f ↔ Nonempty (γ.Extension f) := by
  constructor
  · rintro ⟨δ, hδ⟩
    exact ⟨⟨δ, hδ⟩⟩
  · rintro ⟨h⟩
    exact h.extendsAlong

end DividedPowers
