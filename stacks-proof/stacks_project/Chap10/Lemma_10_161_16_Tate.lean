import Mathlib
import stacks_project.Chap10.Definition_10_161_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Ideal

/-
Domain-style sampling:
* primary domain: commutative algebra of Japanese (`N-2`) domains under a principal `x`-adic
  reduction step;
* sampled owner abstractions:
  - `IsN2Ring`, the chapter-owner source-facing `N-2` condition from
    `Definition_10_161_1`;
  - `IsAdicComplete`, the canonical owner for `x`-adic completeness;
  - `moduleFinite_of_finite_quotient_of_isHausdorff`, the owner-facing finite-generation criterion
    from Lemma `10.96.12` used in the Tate argument;
  - `IsIntegralClosure.finite`, recalled in Lemma `10.161.8` for the separable normalization step.
* layer triage:
  - `source-facing`: the Tate criterion upgrading the quotient `R / xR` being `N-2` to `R`
    itself being `N-2`;
  - `core/canonical`: the owners `IsN2Ring` and `IsAdicComplete`;
  - `bridge/view`: the principal-quotient reduction and the finite-normalization argument inside
    the proof.

Primitive data are the ambient normal Noetherian domain `R`, the element `x`, the quotient-domain
assumption on `R ⧸ span ({x} : Set R)`, the owner hypothesis
`[IsN2Ring (R ⧸ span ({x} : Set R))]`, and the owner completeness hypothesis
`[IsAdicComplete (span ({x} : Set R)) R]`. The finite integral-closure statements and the
separated finite-generation step are derived API from the sampled owners and should remain
proof-level, not additional public wrapper data in this file.
-/

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

-- Proof sketch: reduce finite extensions of `FractionRing R` to the purely inseparable case using
-- Lemma `10.161.12`, adjoin a `q`th root `y` of `x`, and study the integral closure `S` of `R`
-- in the resulting extension. The quotient `S / yS` sits inside the integral closure of
-- `R / xR`, hence is finite by the `N-2` hypothesis on `R / xR`; then all quotients `S / y^n S`
-- are finite by a filtration argument, so also `S / xS` is finite. Finally apply the completeness
-- criterion of Lemma `10.96.12` to `S`, using Krull intersection to show `⋂ n, x^n S = 0`.
/-- Lemma 10.161.16 (Tate): if `R` is a normal Noetherian domain, `R ⧸ (x)` is a domain and
`N-2`, and `R` is complete for the `x`-adic topology, then `R` is `N-2`. -/
theorem isN2Ring_of_normal_of_adicComplete_of_principal_quotient_isN2Ring
    (x : R) [IsDomain (R ⧸ span ({x} : Set R))]
    [IsN2Ring (R ⧸ span ({x} : Set R))]
    [IsAdicComplete (span ({x} : Set R)) R] :
    IsN2Ring R := sorry

end
