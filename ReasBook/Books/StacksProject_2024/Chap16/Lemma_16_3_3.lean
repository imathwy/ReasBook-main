import Mathlib
import StacksProject_2024.Chap10.Definition_10_136_1
import StacksProject_2024.Chap10.Definition_10_136_5
import StacksProject_2024.Chap16.Lemma_16_3_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/- Domain-style sampling:
- primary domain: syntomic ring maps, smooth retractions, and relative global complete
  intersections;
- sampled owner declarations:
  `RingHom.Syntomic`,
  `Algebra.IsRelativeGlobalCompleteIntersection`,
  `exists_finiteType_retraction_with_smoothing_localizations`,
  `Algebra.Generators.exists_presentation_of_free_cotangent`;
- best owner abstraction:
  the ambient canonical owners are `RingHom.Syntomic` for `R → A` and
  `Algebra.IsRelativeGlobalCompleteIntersection R C` for the output algebra `C`; the localized
  free-cotangent presentations from Lemma `16.3.1` are bridge data used to construct the global
  complete-intersection owner and should not survive here as a parallel public wrapper;
- primitive vs. derived:
  this lemma exports only the smooth `A`-algebra retract and the canonical relative-global-complete
  intersection owner; finite presentation and local presentation data are derived API coming from
  those owners.

Source/core/bridge triage:
- `source-facing`: the existence of a smooth `A`-algebra retract `C` that is a relative global
  complete intersection over `R`;
- `core/canonical`: `RingHom.Syntomic` and `Algebra.IsRelativeGlobalCompleteIntersection`;
- `bridge/view`: `exists_finiteType_retraction_with_smoothing_localizations`, whose localized free
  cotangent presentations are converted into the source-facing owner below.
-/
-- Proof sketch: apply
-- `exists_finiteType_retraction_with_smoothing_localizations` to the syntomic map `R → A` to
-- obtain an `A`-algebra `C` with an `A`-algebra retraction such that `A → C` is smooth and the
-- localizations `C_a` admit free cotangent presentations over `R`. Then use
-- `Algebra.Generators.exists_presentation_of_free_cotangent` to replace those local presentations
-- by finite presentations whose defining equations map to bases of the corresponding conormal
-- modules, and apply Lemma `10.135.4` fiberwise to identify the fiber dimensions with the
-- presentation dimension.
/-- Lemma 16.3.3: if `R → A` is syntomic, then there exists an `A`-algebra `C` with an
`A`-algebra retraction `C → A` such that `A → C` is smooth and `C` is a relative global complete
intersection over `R`. The presentation-theoretic form of the last condition is packaged by the
owner `IsRelativeGlobalCompleteIntersection R C`, rather than by a separate local wrapper in this
file. -/
theorem exists_smooth_retraction_relativeGlobalCompleteIntersection_of_syntomic
    (hA : (algebraMap R A).Syntomic) :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra R C) (_ : Algebra A C)
      (_ : IsScalarTower R A C) (_ : Smooth A C) (r : C →ₐ[A] A),
      IsRelativeGlobalCompleteIntersection R C := by
  letI : FinitePresentation R A :=
    RingHom.finitePresentation_algebraMap.mp hA.finitePresentation
  sorry

end

end Algebra
