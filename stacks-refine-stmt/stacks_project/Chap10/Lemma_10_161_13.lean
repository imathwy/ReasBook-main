import Mathlib
import stacks_project.Chap10.Lemma_10_37_14
import stacks_project.Chap10.Lemma_10_161_7
import stacks_project.Chap10.Lemma_10_161_11
import stacks_project.Chap10.Lemma_10_161_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

/-
Domain triage:
* primary domain: commutative algebra of the `N-1` and `N-2` conditions under polynomial
  extension;
* sampled owner/bridge declarations:
  - `IsN1Ring` and `IsN2Ring`, the source-facing owner classes from `Definition 10.161.1`;
  - `isNormalRing_polynomial`, the canonical polynomial normality theorem from `Lemma 10.37.14`;
  - `isN1Ring_iff_isN2Ring_of_noetherian_of_fractionRing_charZero`, the characteristic-zero
    bridge from `Lemma 10.161.11`;
  - `isN2Ring_iff_integralClosure_finite_for_finite_purelyInseparable_extensions`, the
    positive-characteristic bridge from `Lemma 10.161.12`.
* layer triage:
  - `source-facing`: the two polynomial stability theorems below;
  - `core/canonical`: the owner classes `IsN1Ring` and `IsN2Ring`;
  - `bridge/view`: polynomial normality and the characteristic-zero/positive-characteristic
    comparison theorems listed above, together with finite-extension descent from `Lemma 10.161.7`.

Primitive data are only the Noetherian domain `R` and the owner hypotheses `IsN1Ring R` or
`IsN2Ring R`. Normality of the normalization, polynomial normality, and the characteristic-case
reductions are derived API, so they should stay in the proof layer rather than being repackaged as
new public data in this file.
-/

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]

-- Proof sketch: let `R'` be the integral closure of `R` in `FractionRing R`. The `N-1`
-- hypothesis makes `R'` finite over `R`, hence `R'[X]` finite over `R[X]`. Since `R'` is normal,
-- the canonical theorem `isNormalRing_polynomial` makes `R'[X]` normal. Then
-- `isN1Ring_of_finite_extension` descends the `N-1` property from `R'[X]` to `R[X]`.
/-- Lemma 10.161.13 (1): if `R` is a Noetherian domain and `R` is `N-1`, then the polynomial ring
`R[X]` is `N-1`. -/
theorem isN1Ring_polynomial
    [IsN1Ring R] :
    IsN1Ring (Polynomial R) := sorry

-- Proof sketch: reduce first to the case where `R` is normal using the finite-extension descent
-- lemma `isN2Ring_of_finite_extension`. In characteristic zero, combine
-- `isN1Ring_polynomial` with Lemma `10.161.11`. In characteristic `p > 0`, use Lemma `10.161.12`
-- to reduce to finite purely inseparable extensions and identify the relevant integral closure
-- with a polynomial ring `R'[X^(1/q)]` over a finite integral extension `R' / R`, which is finite
-- over `R[X]`.
/-- Lemma 10.161.13 (2): if `R` is a Noetherian domain and `R` is `N-2`, then the polynomial ring
`R[X]` is `N-2`. -/
theorem isN2Ring_polynomial
    [IsN2Ring R] :
    IsN2Ring (Polynomial R) := sorry

end
