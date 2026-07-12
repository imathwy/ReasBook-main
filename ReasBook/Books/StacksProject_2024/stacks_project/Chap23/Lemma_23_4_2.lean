import StacksProject_2024.Chap23.DividedPowerRingExtendsTo
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Ideal.IsPrincipal

universe u v

namespace DividedPowers

/- 
Source/core/bridge triage:
- `source-facing`: the ring-level uniqueness and existence criteria for extending divided powers
  along a ring map.
- `core/canonical`: the owners `DividedPowers.Extension` and `DividedPowers.extendsAlong` from
  `Definition_23_4_1`.
- `bridge/view`: the bundled-owner companion
  `DividedPowerRing.extendsTo_of_map_eq_bot_or_isPrincipal_or_flat`.
-/

/-- Lemma 23.4.2 (1): for a divided power ideal `(A, I, γ)` and a ring map `f : A →+* B`, the type
of extension data for `γ` along `f` is subsingleton. -/
@[stacks 07H1]
theorem subsingletonExtensions {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
    {B : Type v} [CommRing B] (f : A →+* B) :
    Subsingleton (γ.Extension f) := by
  sorry

/-- Companion instance for Lemma 23.4.2 (1): extension data along a ring map are unique. -/
instance instSubsingletonExtension {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
    {B : Type v} [CommRing B] (f : A →+* B) :
    Subsingleton (γ.Extension f) :=
  subsingletonExtensions γ f

/-- Lemma 23.4.2 (2): if `I.map f = ⊥`, or `I` is principal, or `f` is flat, then the divided
powers `γ` extend along `f`. -/
@[stacks 07H1]
theorem extendsAlong_of_map_eq_bot_or_isPrincipal_or_flat
    {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
    {B : Type v} [CommRing B] (f : A →+* B)
    (h : I.map f = ⊥ ∨ I.IsPrincipal ∨ f.Flat) :
    γ.extendsAlong f := by
  sorry

end DividedPowers

namespace DividedPowerRing

/-- Lemma 23.4.2, bundled bridge: the same extension criterion is also available for the canonical
owner `DividedPowerRing`. -/
@[stacks 07H1]
theorem extendsTo_of_map_eq_bot_or_isPrincipal_or_flat
    (A : DividedPowerRing.{u}) {B : Type v} [CommRing B] (f : A →+* B)
    (h : A.ideal.map f = ⊥ ∨ A.ideal.IsPrincipal ∨ f.Flat) :
    A.extendsTo f :=
  A.dividedPowers.extendsAlong_of_map_eq_bot_or_isPrincipal_or_flat f h

end DividedPowerRing
