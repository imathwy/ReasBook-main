import Mathlib
import StacksProject_2024.Chap16.Lemma_16_8_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MorphismProperty

namespace Algebra

universe u

section

variable {R : Type u} {Λ : Type u}
variable [CommRing R] [CommRing Λ] [Algebra R Λ]
variable [IsNoetherianRing R] [IsNoetherianRing Λ] [(algebraMap R Λ).IsRegularRingMap]

/- Domain-style sampling:
- primary domain: regular ring maps of Noetherian commutative rings and their presentation by
  filtered colimits of smooth algebras;
- sampled owner declarations:
  `RingHom.IsFilteredColimitOfSmooth`,
  `isFilteredColimitOfSmooth_of_forall_field_cases`,
  `IsRegularRingMap`,
  `ResolvableAtPrime`;
- best owner abstraction: the public owner is
  `(algebraMap R Λ).IsFilteredColimitOfSmooth`, while the ambient regularity assumptions already
  live in `[IsRegularRingMap R Λ]`;
- primitive data: only the Noetherian source and target, the algebra structure, and the regularity
  owner on `R → Λ`;
- derived API: any chosen filtered diagram of smooth algebras, and the field-case resolution data
  used to feed Lemma `16.8.4`.

Source/core/bridge triage:
- `source-facing`: Popescu's theorem for Noetherian regular ring maps;
- `core/canonical`: `(algebraMap R Λ).IsFilteredColimitOfSmooth` and `[IsRegularRingMap R Λ]`;
- `bridge/view`: the reduction theorem `isFilteredColimitOfSmooth_of_forall_field_cases`, whose
  field-case input is supplied by the chapter's resolution machinery.
-/

-- Proof sketch: apply Lemma `16.8.4` to reduce to the case where the source ring is a field. The
-- remaining field-case argument is the only genuine proof debt here; it is the place where the
-- chapter combines the resolution results from Lemmas `16.10.3` and `16.11.4` to produce the
-- required smooth factorization criterion for every finitely presented algebra over the field.
/-- Theorem 16.12.1 (Popescu): any regular homomorphism of Noetherian rings is a filtered colimit
of smooth ring maps. -/
theorem isFilteredColimitOfSmooth :
    (algebraMap R Λ).IsFilteredColimitOfSmooth := by
  have hfield :
      ∀ {K A : Type u} [Field K] [CommRing A] [Algebra K A]
        [IsNoetherianRing A] [(algebraMap K A).IsRegularRingMap],
        (algebraMap K A).IsFilteredColimitOfSmooth := by
    intro K A _ _ _ _ _
    sorry
  exact isFilteredColimitOfSmooth_of_forall_field_cases hfield

end

end Algebra
