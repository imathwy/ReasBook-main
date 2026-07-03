import Mathlib
import StacksProject_2024.Chap10.Lemma_10_147_5
import StacksProject_2024.Chap15.Definition_15_41_1
import StacksProject_2024.Chap16.Situation_16_8_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace Algebra

universe u

section

variable {R : Type u} {Λ : Type u}
variable [CommRing R] [CommRing Λ] [Algebra R Λ]
variable [IsNoetherianRing R] [IsNoetherianRing Λ] [(algebraMap R Λ).IsRegularRingMap]

/- Domain-style sampling:
- primary domain: regular ring maps of Noetherian commutative rings and the PT property
  `RingHom.IsFilteredColimitOfSmooth`;
- sampled owner declarations:
  `RingHom.IsFilteredColimitOfSmooth`,
  `IsRegularRingMap`,
  `RingHom.IsFilteredColimitOfSmooth.isRegularRingMap_of_noetherianFibers`,
  `RingHom.smooth_ind_prodMap`;
- best owner abstraction: PT is already owned by
  `(algebraMap R Λ).IsFilteredColimitOfSmooth`, while Situation `16.8.1` itself is owned by the
  ambient instance `[IsRegularRingMap R Λ]`;
- primitive vs. derived: the only primitive input of the reduction theorem is the field-case PT
  hypothesis phrased directly at that owner. Any chosen presentation of a filtered diagram of
  smooth algebras is derived API already packaged by `RingHom.IsFilteredColimitOfSmooth`.

Source/core/bridge triage:
- `source-facing`: the reduction from arbitrary regular maps to the case where the source is a
  field;
- `core/canonical`: `[IsRegularRingMap R Λ]` for the ambient situation and
  `(algebraMap R Λ).IsFilteredColimitOfSmooth` for PT;
- `bridge/view`: the auxiliary reductions through quotients, total quotient rings, and product
  decompositions used in the proof sketch.
-/

-- Proof sketch: for an arbitrary regular map `R → Λ`, consider the set of ideals `I ⊆ R` for
-- which the quotient map `R / I → Λ / IΛ` does not satisfy PT, and choose a maximal such ideal if
-- any exist. After replacing the situation by this quotient, every nonzero quotient satisfies PT,
-- so Proposition `16.5.3` shows `R` is reduced. Localizing at the nonzerodivisors reduces to the
-- total ring of fractions, which is a finite product of fields; apply Lemmas `16.8.2`, `16.8.3`,
-- `16.6.1`, and `16.7.2` to descend the field-case smooth factorization back to `Λ`.
/-- Lemma 16.8.4: if PT, namely `RingHom.IsFilteredColimitOfSmooth`, holds for every
Situation 16.8.1 whose source ring is a field, then PT holds for every Situation 16.8.1. -/
theorem isFilteredColimitOfSmooth_of_forall_field_cases
    (hfield :
      ∀ {K A : Type u} [Field K] [CommRing A] [Algebra K A]
        [IsNoetherianRing A] [(algebraMap K A).IsRegularRingMap],
        (algebraMap K A).IsFilteredColimitOfSmooth) :
    (algebraMap R Λ).IsFilteredColimitOfSmooth := sorry

end

end Algebra
