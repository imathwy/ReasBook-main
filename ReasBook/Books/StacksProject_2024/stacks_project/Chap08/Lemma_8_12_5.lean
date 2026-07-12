import Mathlib
import Mathlib.CategoryTheory.Localization.Predicate
import StacksProject_2024.Chap04.Lemma_4_18_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open Limits CategoricalPullback

universe uC uD uS vC vD vS w

namespace CategoryTheory
namespace Limits

/-- A functor preserves finite nonempty limits if it preserves limits of every finite nonempty
shape. -/
class PreservesFiniteNonemptyLimits
    {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D] (F : C ⥤ D) : Prop where
  /-- Preservation of a single finite nonempty limit shape. -/
  out (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J] :
    PreservesLimitsOfShape J F := by
      infer_instance

attribute [instance] PreservesFiniteNonemptyLimits.out

/-- Any functor preserving finite limits also preserves finite nonempty limits. -/
instance preservesFiniteNonemptyLimits_of_preservesFiniteLimits
    {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D] (F : C ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteNonemptyLimits F where
  out _ := inferInstance

/-- A functor preserving finite nonempty limits preserves limits of each finite nonempty shape. -/
instance preservesLimitsOfShape_of_preservesFiniteNonemptyLimits
    {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D] (F : C ⥤ D) [PreservesFiniteNonemptyLimits F]
    (J : Type w) [SmallCategory J] [FinCategory J] [Nonempty J] :
    PreservesLimitsOfShape J F := by
  apply preservesLimitsOfShape_of_equiv (FinCategory.equivAsType J)

attribute [instance 100] preservesLimitsOfShape_of_preservesFiniteNonemptyLimits

end Limits

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/- Domain-style sampling for Lemma 8.12.5:
- primary domain: pushforward of fibred categories along a functor, organized through a
  categorical pullback and localization at strongly cartesian vertical morphisms.
- inspected owner-level declarations:
  `CategoricalPullback`,
  `Functor.IsStronglyCartesian`,
  `MorphismProperty.HasRightCalculusOfFractions`,
  `Localization`.
- best owner abstraction: the functor-owned construction
  `Functor.pushforwardSource u p`, `Functor.pushforwardFractions u p`, `Functor.pushforward u p`,
  and `Functor.pushforwardProjection u p`.
- primitive data: the categorical pullback
  `CategoricalPullback (Comma.snd (𝟭 D) u) p` and the morphism property cutting out vertical
  strongly cartesian arrows.
- derived API: the scoped notation `u ₚₚ p`, the localized notation `u ₚ p`, and the canonical
  projection to `D`.

Source/core/bridge triage:
- `source-facing`: `Functor.pushforwardSource u p`, `Functor.pushforwardFractions u p`,
  `Functor.pushforward u p`.
- `core/canonical`: `CategoricalPullback`, `Functor.IsStronglyCartesian`,
  `MorphismProperty.HasRightCalculusOfFractions`, `Localization`.
- `bridge/view`: the notations `u ₚₚ p`, `u ₚ p`, and `Functor.pushforwardProjection u p`. -/

namespace Functor

/-- The category `u_{pp} S`, modeled as the explicit fibred `2`-fibre product of the comma
projection `Comma.snd (𝟭 D) u : Comma (𝟭 D) u ⥤ C` with the fibred category `p : S ⥤ C`. -/
abbrev pushforwardSource (u : C ⥤ D) (p : S ⥤ C) :=
  CategoricalPullback (Comma.snd (𝟭 D) u) p

/- Textbook notation for the prelocalized pushforward category `u_{pp} S`. -/
scoped infixr:100 " ₚₚ " => pushforwardSource

open scoped Functor

/-- A morphism in `u_{pp} S` is vertical over the `D`-object `V` if its left component is an
identity after identifying the source and target `D`-objects. -/
private def pushforwardSourceVertical
    (u : C ⥤ D) (p : S ⥤ C)
    {X Y : u ₚₚ p} (f : X ⟶ Y) : Prop :=
  ∃ hV : X.fst.left = Y.fst.left, f.fst.left = eqToHom hV

/-- The morphism property on `u_{pp} S` cut out by morphisms of the form `(a, id_V, α)` with
`α` strongly cartesian over its canonical base map `p.map α`. -/
def pushforwardFractions (u : C ⥤ D) (p : S ⥤ C) :
    MorphismProperty (u ₚₚ p) := fun {_ _} f ↦
  pushforwardSourceVertical u p f ∧
    p.IsStronglyCartesian (p.map f.snd) f.snd

/-- The category `u_p S`, obtained by localizing `u_{pp} S` at the right-fraction property from
Lemma `8.12.5`. -/
abbrev pushforward (u : C ⥤ D) (p : S ⥤ C) :=
  (pushforwardFractions u p).Localization

/- Textbook notation for the localized pushforward category `u_p S`. -/
scoped infixr:100 " ₚ " => pushforward

/-- The projection from `u_{pp} S` to `D`, given by the `D`-object in the comma-category
component. -/
private abbrev pushforwardSourceProjection (u : C ⥤ D) (p : S ⥤ C) :
    u ₚₚ p ⥤ D :=
  π₁ (Comma.snd (𝟭 D) u) p ⋙ Comma.fst (𝟭 D) u

-- Proof sketch: a morphism in `u.pushforwardFractions p` has identity `D`-component by
-- definition, so its image under the prelocalized projection is an isomorphism in `D`.
/-- The prelocalized projection inverts the right-fraction morphisms used to define `u_p S`. -/
private theorem pushforwardSourceProjection_invertsFractions
    (u : C ⥤ D) (p : S ⥤ C) :
    (u.pushforwardFractions p).IsInvertedBy (pushforwardSourceProjection u p) := sorry

/-- The canonical functor `u_p S ⥤ D` extending the projection `u_{pp} S ⥤ D` through the
localization. -/
noncomputable abbrev pushforwardProjection
    (u : C ⥤ D) (p : S ⥤ C) :
    u ₚ p ⥤ D :=
  Localization.lift
    (pushforwardSourceProjection u p)
    (pushforwardSourceProjection_invertsFractions u p)
    (u.pushforwardFractions p).Q

-- Proof sketch: verify the right-calculus-of-fractions axioms `RMS1`, `RMS2`, and `RMS3`. For
-- `RMS1`, compositions of strongly cartesian arrows remain strongly cartesian. For `RMS2`, use
-- pullbacks in `C` and the fibred pullback construction in `S` to complete a right Ore square
-- with identity left component over `D`. For `RMS3`, use equalizers in `C`, preserved by `u`, and
-- then take a strongly cartesian lift of the equalizer map in `S`.
/-- Lemma 8.12.5: let `p : S ⥤ C` be a fibred category, assume `C` has pullbacks and equalizers,
and assume `u : C ⥤ D` preserves pullbacks and equalizers. In the category `u ₚₚ p`, the
morphisms whose `D`-component is the identity and whose `S`-component is strongly cartesian form
a right multiplicative system, i.e. `u.pushforwardFractions p` has right calculus of fractions. -/
theorem pushforwardFractions_hasRightCalculusOfFractions
    (u : C ⥤ D) (p : S ⥤ C) [p.IsFibered]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    (u.pushforwardFractions p).HasRightCalculusOfFractions := sorry

instance
    (u : C ⥤ D) (p : S ⥤ C) [p.IsFibered]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    (u.pushforwardFractions p).HasRightCalculusOfFractions :=
  pushforwardFractions_hasRightCalculusOfFractions u p

end Functor

end

end CategoryTheory
