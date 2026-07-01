import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsReduced S]

/- Domain-style sampling for Lemma 10.123.9:
- primary domain: strong transcendence versus quasi-finiteness for a polynomially generated
  algebra;
- sampled owner declarations:
  `IsStronglyTranscendental`,
  `Algebra.QuasiFiniteAt`,
  `Algebra.not_isStronglyTranscendental_of_quasiFiniteAt`;
- best owner abstraction: the mathlib theorem
  `Algebra.not_isStronglyTranscendental_of_quasiFiniteAt`;
- primitive data: the element `x : S`, its strong transcendence over `R`, the finite polynomial map
  `Polynomial.aeval x`, and the prime `q : Ideal S`;
- derived API: the source-facing contrapositive below.

Source/core/bridge triage:
- `source-facing`: the textbook negation of quasi-finiteness under a strong-transcendence
  hypothesis;
- `core/canonical`: `Algebra.not_isStronglyTranscendental_of_quasiFiniteAt`;
- `bridge/view`: this theorem, which packages the canonical owner theorem in the source's
  contrapositive form. -/

-- Proof sketch: argue by contradiction. If `R → S` were quasi-finite at a prime `q`, then the
-- canonical mathlib theorem `Algebra.not_isStronglyTranscendental_of_quasiFiniteAt` applied to the
-- finite polynomial map `Polynomial.aeval x : R[X] →ₐ[R] S` would show that `x` is not strongly
-- transcendental over `R`.
/-- Lemma 10.123.9: the source states this for an inclusion of domains, but the canonical owner
theorem only needs `S` reduced. If `x : S` is strongly transcendental over `R` and `S` is finite
over the polynomial subring `R[x]`, then `R → S` is not quasi-finite at any prime of `S`. -/
theorem not_quasiFiniteAt_of_isStronglyTranscendental_of_aeval_finite
    {x : S} (hx : IsStronglyTranscendental R x)
    (hfinite : (Polynomial.aeval x : Polynomial R →ₐ[R] S).Finite)
    (q : Ideal S) [q.IsPrime] :
    ¬ Algebra.QuasiFiniteAt R q := by
  intro hq
  letI : Algebra.QuasiFiniteAt R q := hq
  exact (Algebra.not_isStronglyTranscendental_of_quasiFiniteAt hfinite q) hx

end
