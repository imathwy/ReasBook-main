import Mathlib
import StacksProject_2024.Chap15.Lemma_15_50_2
import StacksProject_2024.Chap15.Lemma_15_51_4

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra

universe u

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/- Domain triage:
- primary domain: `G`-rings, formal fibers, and locality at maximal ideals in Noetherian
  commutative algebra;
- sampled owner declarations:
  `IsGRing`,
  `isGRing_iff_isPRing_isGeometricallyRegularProperty`,
  `Algebra.IsGeometricallyRegularProperty`,
  `LocalFormalFibersHaveProperty`,
  `isPRing_iff_localFormalFibersHaveProperty_atMaximal`;
- best owner abstraction: the source-facing theorem remains about `IsGRing`, but the canonical
  owner layer underneath is `IsPRing Algebra.IsGeometricallyRegularProperty`; the maximal-ideal
  formulation should therefore reuse the public owner API
  `isGRing_iff_localFormalFibersHaveProperty` and
  `isPRing_iff_localFormalFibersHaveProperty_atMaximal` instead of duplicating it locally;
- primitive data: only the Noetherian commutative ring `R`;
- derived API: the `P`-ring and local-formal-fiber reformulations of the `G`-ring condition.

Layering:
- `isGRing_iff_forall_localizationAtMaximal_isGRing` is `source-facing`;
- `IsGRing` and `IsPRing Algebra.IsGeometricallyRegularProperty` are the `core/canonical`
  owners;
- the maximal-localization formulation is the `bridge/view`, mediated by
  `LocalFormalFibersHaveProperty`.
-/
-- Proof sketch: specialize the canonical maximal-ideal criterion for `P`-rings from
-- `Lemma_15_51_4` to the field-algebra property `IsGeometricallyRegularProperty`. The auxiliary
-- owner `LocalFormalFibersHaveProperty` on each local ring `R_𝔪` is equivalent to `IsGRing R_𝔪`
-- by the public owner bridge `isGRing_iff_localFormalFibersHaveProperty`.
/-- Lemma 15.50.7: for a Noetherian ring `R`, `R` is a `G`-ring if and only if every localization
`R_𝔪` at a maximal ideal is a `G`-ring, equivalently every `R_𝔪` has geometrically regular formal
fibers. -/
theorem isGRing_iff_forall_localizationAtMaximal_isGRing :
    IsGRing R ↔ ∀ m : MaximalSpectrum R, IsGRing (Localization.AtPrime m.asIdeal) := by
  have hlocal :
      IsPRing Algebra.IsGeometricallyRegularProperty R ↔
        ∀ m : MaximalSpectrum R,
          LocalFormalFibersHaveProperty Algebra.IsGeometricallyRegularProperty
            (Localization.AtPrime m.asIdeal) :=
    isPRing_iff_localFormalFibersHaveProperty_atMaximal
      Algebra.IsGeometricallyRegularProperty
  have hmax :
      (∀ m : MaximalSpectrum R,
        LocalFormalFibersHaveProperty Algebra.IsGeometricallyRegularProperty
          (Localization.AtPrime m.asIdeal)) ↔
      ∀ m : MaximalSpectrum R, IsGRing (Localization.AtPrime m.asIdeal) := by
    constructor
    · intro h m
      exact
        (isGRing_iff_localFormalFibersHaveProperty
          (Localization.AtPrime m.asIdeal)).2 (h m)
    · intro h m
      exact
        (isGRing_iff_localFormalFibersHaveProperty
          (Localization.AtPrime m.asIdeal)).1 (h m)
  exact (isGRing_iff_isPRing_isGeometricallyRegularProperty R).trans hlocal |>.trans hmax

end
