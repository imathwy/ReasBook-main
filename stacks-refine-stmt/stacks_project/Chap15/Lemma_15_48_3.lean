import Mathlib
import stacks_project.Chap10.Lemma_10_106_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing
open RingTheory Sequence

section

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]
variable {m : ℕ}

/- Domain-style sampling:
* primary domain: regular local rings, chosen families in the maximal ideal, cotangent-space
  criteria, and regular systems of parameters;
* sampled owner declarations upstream in the chapter/project:
  `parameterIdeal`,
  `IsPartOfRegularSystemOfParameters`,
  `IsPartOfRegularSystemOfParameters.isRegular`,
  `IsPartOfRegularSystemOfParameters.isRegularLocalRing_quotient_parameterIdeal`;
* source/core/bridge triage:
  `source-facing`: the Jacobian determinant criterion for the chosen family
  `x : Fin m → maximalIdeal R`;
  `core/canonical`: `IsPartOfRegularSystemOfParameters (maximalIdeal R).spanFinrank x`,
  together with the derived owners `parameterIdeal x` and `IsRegular R (List.ofFn fun i ↦ (x i : R))`;
  `bridge/view`: the two textbook consequences obtained from the Chapter 10 owner API;
* owner abstraction: the main declaration in this file should be exactly the bridge from the
  Jacobian determinant hypothesis to
  `IsPartOfRegularSystemOfParameters (maximalIdeal R).spanFinrank x`. The quotient regularity and
  list regularity statements are then canonical downstream views and should stay thin wrappers
  around the Chapter 10 owner theorems, not parallel local APIs;
* primitive data: the family `x`, the derivations `D`, and the unit Jacobian determinant
  hypothesis;
* derived API: `IsPartOfRegularSystemOfParameters (maximalIdeal R).spanFinrank x`, regularity of
  the quotient by `parameterIdeal x`, and regularity of `List.ofFn fun i ↦ (x i : R)`, with the
  latter two exposed only as direct owner consequences.

The source hypothesis `1 ≤ m` is mathematically redundant here: the empty family case is still a
valid regular sequence and quotient, so the public API keeps only the primitive data used by the
owner-level statements.
-/

-- Proof sketch: use the determinant hypothesis to show the classes of the `x i` are linearly
-- independent in `maximalIdeal R / (maximalIdeal R) ^ 2`, exactly as in the textbook proof. Extend
-- them to a basis of the cotangent space of the regular local ring `R`, lift that basis to a
-- regular system of parameters, and identify the original family `x` with the initial segment.
/-- Lemma 15.48.3 owner bridge: if the Jacobian determinant of the chosen derivations
`det (D i (x j))` is a unit, then `x` is part of a regular system of parameters. -/
theorem isPartOfRegularSystemOfParameters_of_jacobian_det_isUnit
    (x : Fin m → maximalIdeal R) (D : Fin m → Derivation ℤ R R)
    (hdet : IsUnit (Matrix.det fun i j ↦ D i (x j : R))) :
    IsPartOfRegularSystemOfParameters (maximalIdeal R).spanFinrank x := sorry

/-- Lemma 15.48.3 (1), derived owner view: if the Jacobian determinant of the chosen absolute
derivations `D i : Derivation ℤ R R` is a unit, then `R ⧸ parameterIdeal x` is a regular local
ring. -/
theorem isRegularLocalRing_quotient_parameterIdeal_of_jacobian_det_isUnit
    (x : Fin m → maximalIdeal R) (D : Fin m → Derivation ℤ R R)
    (hdet : IsUnit (Matrix.det fun i j ↦ D i (x j : R))) :
    IsRegularLocalRing (R ⧸ parameterIdeal x) :=
  IsPartOfRegularSystemOfParameters.isRegularLocalRing_quotient_parameterIdeal
    (isPartOfRegularSystemOfParameters_of_jacobian_det_isUnit x D hdet)

/-- Lemma 15.48.3 (2), derived owner view: under the same hypotheses, the underlying list of the
chosen family `x`, encoded as `List.ofFn fun i ↦ (x i : R)`, is a regular sequence in `R`. -/
theorem isRegular_of_jacobian_det_isUnit
    (x : Fin m → maximalIdeal R) (D : Fin m → Derivation ℤ R R)
    (hdet : IsUnit (Matrix.det fun i j ↦ D i (x j : R))) :
    IsRegular R (List.ofFn fun i ↦ (x i : R)) :=
  IsPartOfRegularSystemOfParameters.isRegular
    (isPartOfRegularSystemOfParameters_of_jacobian_det_isUnit x D hdet)

end
