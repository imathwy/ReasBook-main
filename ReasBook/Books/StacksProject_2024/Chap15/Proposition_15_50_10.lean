import Mathlib
import StacksProject_2024.Chap15.Lemma_15_50_2
import StacksProject_2024.Chap15.Proposition_15_51_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (R : Type u) {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.EssFiniteType R S]

/- Domain triage:
- primary domain: permanence of `G`-rings under essentially finite type algebra maps in
  commutative algebra;
- sampled owner declarations:
  `IsGRing`,
  `IsPRing`,
  `isGRing_iff_isPRing_isGeometricallyRegularProperty`,
  `isPRing_of_essFiniteType`;
- best owner abstraction: the source-facing `G`-ring proposition should be a thin specialization of
  the canonical owner theorem `isPRing_of_essFiniteType` through the bridge
  `IsGRing R ↔ IsPRing Algebra.IsGeometricallyRegularProperty R`, rather than a parallel
  typeclass-driven wrapper;
- primitive data: commutative rings `R` and `S`, an `R`-algebra structure on `S`, an essentially
  finite type hypothesis, and the owner hypothesis `[IsGRing R]`;
- derived API: the resulting owner assertion `IsGRing S`.

Source/core/bridge triage:
- `source-facing`: the permanence statement for `G`-rings;
- `core/canonical`: `IsGRing`, `IsPRing`, and `isPRing_of_essFiniteType`;
- `bridge/view`: `isGRing_iff_isPRing_isGeometricallyRegularProperty`.
-/
-- Proof sketch: specialize the generic essentially-finite-type permanence theorem for `P`-rings
-- to the field-algebra property `Algebra.IsGeometricallyRegularProperty`, then translate back
-- through the canonical owner bridge `IsGRing ↔ IsPRing Algebra.IsGeometricallyRegularProperty`.
/-- Proposition 15.50.10: an essentially finite type algebra over a `G`-ring is again a
`G`-ring. -/
theorem isGRing_of_essFiniteType [IsGRing R] :
    IsGRing S := sorry

end
