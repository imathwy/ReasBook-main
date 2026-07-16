import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_162_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (R : Type u) [CommRing R]

/-
Domain-style sampling:
* primary domain: commutative algebra of finite normalization and the `N-1`/`N-2` criteria for
  universally Japanese rings;
* owner abstractions sampled for this refinement:
  - `IsN1Ring` and `IsN2Ring`, the chapter-owner source-facing classes from
    `Definition_10_161_1`;
  - `UniversallyJapaneseRing`, the source-facing owner introduced in `Definition_10_162_1`;
  - `isN2Ring_of_finite_extension`, the chapter bridge/view theorem for descending `N-2` along a
    finite extension of domains.
* layer triage:
  - `source-facing`: the theorem below, which gives a criterion for the existing owner
    `UniversallyJapaneseRing`;
  - `core/canonical`: the owner classes `IsN1Ring`, `IsN2Ring`, and `UniversallyJapaneseRing`;
  - `bridge/view`: finite domain models inside finite fraction-field extensions, together with the
    finite-extension descent theorem `isN2Ring_of_finite_extension`.

The primitive data are just the base ring `R` and the test family asserting `IsN1Ring` for every
finite type domain `R`-algebra. Finite-normalization statements in field extensions are derived
API from the sampled owners and should remain internal to the proof rather than being packaged
into a new public wrapper in this file.
-/

/-- Lemma 10.162.3: to prove that `R` is universally Japanese, it suffices to check that every
finite type `R`-algebra that is a domain is `N-1`. -/
-- Proof sketch: to show `R` is universally Japanese, fix a finite type domain `S` over `R` and a
-- finite extension `L / FractionRing S`. Choose a finite domain extension `S ⊆ S' ⊆ L` with
-- fraction field `L`; then `S'` is still finite type over `R`, hence `N-1` by hypothesis. The
-- integral closure of `S'` in `L` is therefore finite over `S'`, hence finite over `S`, and this
-- identifies with the integral closure of `S` in `L`, proving that `S` is `N-2`.
theorem universallyJapaneseRing_of_finiteType_domain_isN1
    (h :
      ∀ (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [IsDomain S],
        IsN1Ring S) :
    UniversallyJapaneseRing.{u, v} R := by
  refine
    { finiteType_algebra_isN2Ring := fun (S : Type v) [CommRing S] [Algebra R S]
        [Algebra.FiniteType R S] [IsDomain S] ↦ ?_ }
  have hS : IsN1Ring S := h S
  sorry

end
