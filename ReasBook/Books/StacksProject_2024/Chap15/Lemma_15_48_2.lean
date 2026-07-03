import Mathlib.RingTheory.Derivation.Basic
import StacksProject_2024.Chap10.Definition_10_110_7
import StacksProject_2024.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsRegularRing R]
variable {f : R}

/- Domain-style sampling:
* primary domain: regular rings, regular local rings on localizations, and absolute derivations on
  a commutative ring;
* sampled owner declarations:
  `IsRegularRing`,
  `IsRegularLocalRing`,
  `IsLocalRing.IsRegularSystemOfParameters.isRegularLocalRing_quotient_parameterIdeal`,
  `Derivation ℤ R R`;
* owner abstraction: the ambient owner is `IsRegularRing R`, localized in the proof sketch through
  the regular-local owner on prime localizations; the derivation datum is the canonical mathlib
  owner `Derivation ℤ R R`.

Primitive vs. derived:
* primitive data: a concrete derivation `D : Derivation ℤ R R` and the unit condition on the class
  of `D f` in `R ⧸ (f)`;
* derived API: the source-facing existential corollary, which packages the same primitive data in
  the textbook existence form.

Source/core/bridge triage:
* source-facing: `isRegularRing_quotient_principalIdeal_of_exists_derivation`, matching the
  textbook existence hypothesis;
* core/canonical: `IsRegularRing`, `IsRegularLocalRing`, and `Derivation ℤ R R`;
* bridge/view: `Derivation.isRegularRing_quotient_principalIdeal_of_isUnit`, which exposes the
  primitive derivation datum directly from the owner object.
-/

-- Proof sketch: regularity is local on `Spec R`, so localize at a maximal ideal of `R ⧸ (f)` and
-- reduce to the case of a regular local ring. There, Lemma `10.106.3` shows it is enough to prove
-- `f ∉ maximalIdeal R ^ 2`. If `f ∈ maximalIdeal R ^ 2`, write `f` as a sum of products of
-- elements of the maximal ideal and apply the Leibniz rule to see that `D f` still lies in the
-- maximal ideal, contradicting that its class in `R ⧸ (f)` is a unit.
namespace Derivation

/-- Primitive-input bridge for Lemma 15.48.2: if `R` is a regular ring and
`D : Derivation ℤ R R` sends `f` to an element whose class in `R ⧸ (f)` is a unit, then
`R ⧸ (f)` is a regular ring. -/
theorem isRegularRing_quotient_principalIdeal_of_isUnit (D : Derivation ℤ R R)
    (hDf : IsUnit (Ideal.Quotient.mk (principalIdeal f) (D f))) :
    IsRegularRing (R ⧸ principalIdeal f) := sorry

end Derivation

/-- Lemma 15.48.2: if `R` is a regular ring and `f` admits a derivation
`D : Derivation ℤ R R` whose value `D f` becomes a unit in `R ⧸ (f)`, then `R ⧸ (f)` is a
regular ring. -/
theorem isRegularRing_quotient_principalIdeal_of_exists_derivation
    (hD : ∃ D : Derivation ℤ R R,
      IsUnit (Ideal.Quotient.mk (principalIdeal f) (D f))) :
    IsRegularRing (R ⧸ principalIdeal f) := by
  obtain ⟨D, hDf⟩ := hD
  exact D.isRegularRing_quotient_principalIdeal_of_isUnit hDf

end
