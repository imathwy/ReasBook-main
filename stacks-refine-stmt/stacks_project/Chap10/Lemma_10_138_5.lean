import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable (R : Type u) (ι : Type v) (S : Type w) [CommRing R] [CommRing S] [Algebra R S]

/- Domain triage:
* primary domain: formal smoothness of commutative algebras via square-zero thickenings;
* sampled owner declarations:
  `Algebra.FormallySmooth`,
  `Algebra.mvPolynomial`,
  `Algebra.FormallySmooth.iff_split_surjection`,
  `AlgHom.kerSquareLift`;
* layer: `source-facing`, since the Stacks item is the polynomial-presentation specialization of the
  canonical split-surjection criterion;
* primitive data: a surjective polynomial presentation `f : MvPolynomial ι R →ₐ[R] S`;
* derived API: the section of `f.kerSquareLift`, already the canonical owner map
  `(MvPolynomial ι R) ⧸ (RingHom.ker f.toRingHom) ^ 2 →ₐ[R] S`.

There is no additional source-defined structure beyond this specialization, so the correct
refinement is to reuse the owner theorem directly rather than keep a parallel local criterion.
-/
-- Proof sketch: specialize `Algebra.FormallySmooth.iff_split_surjection` to the surjective
-- `R`-algebra map `f : MvPolynomial ι R →ₐ[R] S`. The source polynomial algebra is formally
-- smooth by the canonical instance from Lemma 10.138.4, and `f.kerSquareLift` is the quotient map
-- `P / J² → S` for `J = ker f`.
/-- Lemma 10.138.5: for a surjective `R`-algebra map from a polynomial ring
`f : MvPolynomial ι R →ₐ[R] S`, the `R`-algebra `S` is formally smooth over `R` if and only if
the induced surjection `(MvPolynomial ι R) ⧸ (RingHom.ker f.toRingHom) ^ 2 →ₐ[R] S` admits an
`R`-algebra section. -/
theorem formallySmooth_iff_exists_polynomial_presentation_section_mod_ker_sq
    (f : MvPolynomial ι R →ₐ[R] S) (hf : Function.Surjective f) :
    Algebra.FormallySmooth R S ↔
      ∃ σ : S →ₐ[R] MvPolynomial ι R ⧸ (RingHom.ker f.toRingHom) ^ 2,
        f.kerSquareLift.comp σ = AlgHom.id R S := by
  simpa using Algebra.FormallySmooth.iff_split_surjection f hf

end
