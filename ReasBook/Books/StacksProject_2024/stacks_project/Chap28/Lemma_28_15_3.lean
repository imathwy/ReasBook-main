import StacksProject_2024.Chap10.Definition_10_155_3
import StacksProject_2024.Chap28.Definition_28_15_1
import Mathlib.Topology.Sober

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry PrimeSpectrum IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: Chapter 28 already owns the scheme-level source-facing predicate
-- `Scheme.isGeometricallyUnibranch`, while the canonical generic-point owner is `genericPoints X`.
-- Chapter 15 expresses punctured-spectrum disconnectedness for local rings via failure of
-- `PreconnectedSpace` on the canonical subtype of `PrimeSpectrum`. The source-facing scheme
-- statement below therefore keeps the quantification over strict henselizations of stalks, but
-- reuses the canonical generic-point and punctured-spectrum surfaces directly instead of importing
-- a later chapter alias or introducing a second owner.

variable (X : Scheme.{u})

private abbrev PuncturedSpectrum (R : Type u) [CommRing R] [IsLocalRing R] :=
  { p : PrimeSpectrum R // p.asIdeal ≠ maximalIdeal R }

/-- Lemma 28.15.3: for a Noetherian scheme `X`, being geometrically unibranch is equivalent to the
condition that for every point `x` which is not the generic point of an irreducible component of
`X`, the punctured spectrum of any chosen strict henselization of the stalk `X.presheaf.stalk x`
is connected. -/
@[stacks 0BQ4]
theorem isGeometricallyUnibranch_iff_connected_puncturedSpectrum_strictHenselization_awayFromGenericPoints
    [IsNoetherian X] :
    X.isGeometricallyUnibranch ↔
      ∀ x : X,
        x ∉ genericPoints X →
          ∀ (Ash : Type u) [CommRing Ash] [Algebra (X.presheaf.stalk x) Ash]
            [IsStrictHenselizationOf (X.presheaf.stalk x) Ash],
              ConnectedSpace (PuncturedSpectrum Ash) := by
  sorry

/-- Companion consequence of Lemma 28.15.3 using the weaker topological interface
`PreconnectedSpace`. -/
theorem preconnected_puncturedSpectrum_strictHenselization_awayFromGenericPoints_of_isGeometricallyUnibranch
    [IsNoetherian X] :
    X.isGeometricallyUnibranch →
      ∀ x : X,
        x ∉ genericPoints X →
          ∀ (Ash : Type u) [CommRing Ash] [Algebra (X.presheaf.stalk x) Ash]
            [IsStrictHenselizationOf (X.presheaf.stalk x) Ash],
              PreconnectedSpace (PuncturedSpectrum Ash) := by
  intro hX
  rw [isGeometricallyUnibranch_iff_connected_puncturedSpectrum_strictHenselization_awayFromGenericPoints
    (X := X)] at hX
  intro x hx Ash
  exact (hX x hx Ash).toPreconnectedSpace

end AlgebraicGeometry.Scheme
