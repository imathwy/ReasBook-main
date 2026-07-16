import StacksProject_2024.stacks_project.Chap23.Definition_23_4_1
import StacksProject_2024.stacks_project.Chapters.Chap23.section03

universe u v

namespace DividedPowerRing

/- Source/core/bridge triage:
- `source-facing`: none; Definition 23.4.1 is owned by `DividedPowers.extendsAlong`.
- `core/canonical`: the Chapter 23 owner `DividedPowers.extendsAlong`.
- `bridge/view`: the bundled `DividedPowerRing` spellings of the same extension data and
  extension predicate.
-/

/-- A bundled extension datum for the source-facing predicate `A.extendsTo f`. -/
abbrev Extension (A : DividedPowerRing.{u}) {B : Type v} [CommRing B] (f : A →+* B) :=
  A.dividedPowers.Extension f

/-- Bundled bridge for Definition 23.4.1: the divided powers on `A` extend to `B` along `f` when
the underlying divided powers `A.dividedPowers` extend along `f`. -/
abbrev extendsTo (A : DividedPowerRing.{u}) {B : Type v} [CommRing B] (f : A →+* B) : Prop :=
  A.dividedPowers.extendsAlong f

namespace Extension

variable {A : DividedPowerRing.{u}} {B : Type v} [CommRing B] {f : A →+* B}

/-- The divided power structure on `A.ideal.map f` carried by bundled extension data. -/
abbrev dividedPowers (h : A.Extension f) : DividedPowers (A.ideal.map f) :=
  h.1

/-- The underlying ring map of bundled extension data is a divided power morphism. -/
theorem isDPMorphism (h : A.Extension f) :
    IsDPMorphism A.dividedPowers h.dividedPowers f :=
  h.2

/-- Bundled extension data give the source-facing predicate `A.extendsTo f`. -/
theorem extendsTo (h : A.Extension f) : A.extendsTo f :=
  ⟨h.dividedPowers, h.isDPMorphism⟩

end Extension

/-- The defining expansion of `DividedPowerRing.extendsTo`. -/
theorem extendsTo_iff (A : DividedPowerRing.{u}) {B : Type v} [CommRing B] (f : A →+* B) :
    A.extendsTo f ↔
      ∃ δ : DividedPowers (A.ideal.map f), IsDPMorphism A.dividedPowers δ f :=
  DividedPowers.extendsAlong_iff A.dividedPowers f

/-- The extension predicate is the nonemptiness of the type of extension data. -/
theorem extendsTo_iff_nonempty_extension
    (A : DividedPowerRing.{u}) {B : Type v} [CommRing B] (f : A →+* B) :
    A.extendsTo f ↔ Nonempty (A.Extension f) :=
  DividedPowers.extendsAlong_iff_nonempty_extension A.dividedPowers f

end DividedPowerRing
