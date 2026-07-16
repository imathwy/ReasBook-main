import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_119_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_119_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} {K : Type v} {L : Type w}
variable [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
variable [Algebra.EssFiniteType K L]

/-
Domain triage:
* primary domain: valuation subrings of finitely generated field extensions dominating the image of
  a fixed Noetherian local domain;
* sampled owner declarations:
  - `LocalSubring.exists_le_valuationSubring` and `ValuationSubring.toLocalSubring` for the
    domination relation on local subrings of a field;
  - `ValuationSubring.comap` for contraction along `K → L`;
  - `exists_one_dimensional_dominating_essFiniteType_overring_of_not_isField` and
    `discreteValuationRing_iff_regularLocalRing_dim_one` for the chapter's one-dimensional and
    discrete-valuation owners.
* best owner abstraction:
  - `source-facing`: existence of a discrete valuation subring of `L` dominating the image of `R`;
  - `core/canonical`: domination as the order on `LocalSubring L`, together with the owner
    predicate `IsDiscreteValuationRing`.
* primitive vs. derived:
  - primitive data: the witness `V : ValuationSubring L` and the domination inequality
    `LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring`;
  - derived API: the local structure on `V.toLocalSubring`, the intermediate one-dimensional
    overring supplied by Lemma `10.119.1`, and the regular-local reformulation of the DVR
    condition from Lemma `10.119.7`.
-/

-- Proof sketch: if `L / K` is not finite, choose a finite transcendence basis and replace `R` by
-- the localization of the polynomial extension obtained by adjoining those generators, reducing to
-- the finite extension case. Then use Lemma `10.119.1` to replace `R` by a one-dimensional
-- dominating overring, take the integral closure in `L`, apply Krull-Akizuki to get Noetherianity,
-- choose a prime over the maximal ideal by lying over, and finally apply Lemma `10.119.7` to the
-- resulting localization.
/-- Lemma 10.119.13: if `R` is a Noetherian local domain with fraction field `K`, `R` is not a
field, and `L / K` is a finitely generated field extension, then there exists a discrete valuation
subring of `L` whose associated local subring dominates the image of `R` in `L`. -/
theorem exists_discreteValuationSubring_dominating_of_not_isField_of_essFiniteType
    (hR : ¬ IsField R) :
    ∃ V : ValuationSubring L,
      IsDiscreteValuationRing V ∧
        LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring := sorry

end
