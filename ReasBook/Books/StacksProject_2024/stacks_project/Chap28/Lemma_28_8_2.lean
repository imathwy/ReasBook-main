import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap28.Definition_28_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-side owner
-- `AlgebraicGeometry.IsLocallyNoetherian`, and the local Chapter 31 analogue
-- `Scheme.Modules.isReflexive_tfae_stalk_and_closedPointStalk` shows that a source item giving
-- equivalent all-points and closed-points stalk criteria is best exposed as a single `List.TFAE`
-- statement. The ring-side owner for Cohen-Macaulay stalks is the existing `CohenMacaulayRing`.

/-- A stalkwise Cohen-Macaulay scheme is locally Noetherian and has Cohen-Macaulay local rings at
every point. -/
class StalkwiseCohenMacaulay (X : Scheme.{u}) : Prop where
  locallyNoetherian : IsLocallyNoetherian X
  stalk : ∀ x : X, CohenMacaulayRing (X.presheaf.stalk x)

/-- A stalkwise Cohen-Macaulay scheme is locally Noetherian. -/
instance instIsLocallyNoetherianOfStalkwiseCohenMacaulay (X : Scheme.{u})
    [h : StalkwiseCohenMacaulay X] : IsLocallyNoetherian X :=
  h.locallyNoetherian

/-- Unfold `StalkwiseCohenMacaulay` into its locally Noetherian and stalkwise
Cohen-Macaulay conditions. -/
theorem StalkwiseCohenMacaulay.spec {X : Scheme.{u}} (h : StalkwiseCohenMacaulay X) :
    IsLocallyNoetherian X ∧ ∀ x : X, CohenMacaulayRing (X.presheaf.stalk x) := sorry

/-- A closed-point stalkwise Cohen-Macaulay scheme is locally Noetherian and has
Cohen-Macaulay local rings at every closed point. -/
class ClosedPointStalkwiseCohenMacaulay (X : Scheme.{u}) : Prop where
  locallyNoetherian : IsLocallyNoetherian X
  stalk : ∀ x : X, x ∈ closedPoints X → CohenMacaulayRing (X.presheaf.stalk x)

/-- A closed-point stalkwise Cohen-Macaulay scheme is locally Noetherian. -/
instance instIsLocallyNoetherianOfClosedPointStalkwiseCohenMacaulay (X : Scheme.{u})
    [h : ClosedPointStalkwiseCohenMacaulay X] : IsLocallyNoetherian X :=
  h.locallyNoetherian

/-- Unfold `ClosedPointStalkwiseCohenMacaulay` into its locally Noetherian and closed-point
stalkwise Cohen-Macaulay conditions. -/
theorem ClosedPointStalkwiseCohenMacaulay.spec {X : Scheme.{u}}
    (h : ClosedPointStalkwiseCohenMacaulay X) :
    IsLocallyNoetherian X ∧
      ∀ x : X, x ∈ closedPoints X → CohenMacaulayRing (X.presheaf.stalk x) := sorry

/-- Lemma 28.8.2: for a scheme `X`, the following are equivalent: `X` is Cohen-Macaulay; `X` is
locally Noetherian and every stalk `\mathcal{O}_{X, x}` is Cohen-Macaulay; and `X` is locally
Noetherian and every closed-point stalk `\mathcal{O}_{X, x}` is Cohen-Macaulay. -/
@[stacks 02IP]
theorem cohenMacaulay_tfae_stalk_and_closedPointStalk (X : Scheme.{u}) :
    List.TFAE
      [ X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A)
      , StalkwiseCohenMacaulay X
      , ClosedPointStalkwiseCohenMacaulay X
      ] := sorry

end AlgebraicGeometry.Scheme
