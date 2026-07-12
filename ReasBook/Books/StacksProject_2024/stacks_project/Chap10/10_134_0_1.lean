import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Source-facing notation for the polynomial presentation with variables indexed by the target
ring, following the textbook notation `R[S]` and `[s]`. -/
scoped[MvPolynomial.Presentation] notation3:max R "[" S "]" => MvPolynomial S R
scoped[MvPolynomial.Presentation] notation:max "[" s "]" => (MvPolynomial.X s)

open scoped MvPolynomial.Presentation

section

variable (R : Type u) (S : Type v)
variable [CommSemiring R] [CommSemiring S] [Algebra R S]

/- Domain triage:
* primary domain: commutative-algebra presentations by multivariable polynomial rings;
* sampled owner API:
  `MvPolynomial.aeval`,
  `MvPolynomial.aeval_X`,
  `MvPolynomial.aeval_X_left`,
  `Algebra.Generators.self`;
* source-facing layer: the canonical self-presentation map `R[S] → S` and its generator notation
  `[s]`;
* core/canonical owner: `MvPolynomial.aeval`, specialized to the identity function `S → S`;
* bridge/view: `Algebra.Generators.self` packages the same map together with the tautological
  section `X`, but lives under stronger ring-level assumptions than the owner declarations used
  here.

Primitive data are only the rings and the identity assignment `S → S`. The induced `R`-algebra map
and its value on generators are derived API already owned upstream, so this file should reuse the
canonical owner directly instead of keeping a parallel local wrapper.
-/

/- 10.134.0.1: the canonical presentation map `R[S] → S` is the specialized multivariable
evaluation homomorphism sending the generator `[s]` to `s` itself. -/
#check (MvPolynomial.aeval (fun s : S ↦ s) : R[S] →ₐ[R] S)

/- Companion specialization: the owner theorem `MvPolynomial.aeval_X` gives the textbook formula
for the canonical presentation map on generators after specializing to `fun s : S ↦ s`. -/
#check
  ((fun s : S ↦ MvPolynomial.aeval_X (fun t : S ↦ t) s) :
    ∀ s : S, (MvPolynomial.aeval (fun t : S ↦ t)) ([s] : R[S]) = s)

end
