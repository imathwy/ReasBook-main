import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]

/- Domain-style sampling:
* primary domain: commutative algebra of prime ideals under scalar extension and the induced
  residue-field extension;
* layer triage:
  - `source-facing`: the existence statement for a finite free `R`-algebra realizing a prescribed
    finite extension of `κ(p)` at the extended prime `pS`;
  - `core/canonical`: `Ideal.LiesOver`, `Ideal.ResidueField`, and `Ideal.ResidueField.mapₐ`,
    which are the owner abstractions for the prime-over-prime relation and the `κ(p)`-algebra
    structure on residue fields;
  - `bridge/view`: `Polynomial.Monic.free_adjoinRoot` and `Polynomial.Monic.finite_adjoinRoot`
    for the monic-quotient model used in the proof, and
    `exists_etale_liesOver_with_residueField_equiv` as the separable special case.
* owner decision: the theorem remains source-facing, but the public output should stop at the
  canonical data carried by the owner abstractions.
* primitive data: the finite free `R`-algebra `S`; the extended ideal itself is the canonical
  owner `q := p.map (algebraMap R S)`, so it should not be repackaged as extra primitive data.
* derived API: after fixing the owner instances `q.IsPrime` and `q.LiesOver p`, the only further
  public output is the residue-field `AlgEquiv`; its compatibility with the `κ(p)`-algebra
  structures is already part of the owner API and should not be duplicated by an extra equality.
-/

-- Proof sketch: choose a primitive element of the finite extension `L / κ(p)`, clear
-- denominators in its minimal polynomial over `κ(p)`, and form the monic quotient
-- `S = R[X] / (f)`. The image of `p` in `S` is prime because the reduction of `f` is the
-- minimal polynomial over `κ(p)`, and the residue field of that prime identifies with `L`
-- through the canonical `κ(p)`-algebra equivalence.
/-- Lemma 10.159.3: for a prime ideal `p` of `R` and a finite field extension `L / κ(p)`, there
exists a finite free `R`-algebra `S` such that the extended ideal `pS` is prime and the induced
residue field extension at `pS` is isomorphic to `L` as a `κ(p)`-algebra. -/
theorem exists_finiteFree_with_prime_extendedIdeal_and_residueField_equiv
    (p : Ideal R) [p.IsPrime] (L : Type v) [Field L] [Algebra p.ResidueField L]
    [FiniteDimensional p.ResidueField L] :
    ∃ (S : Type (max u v)) (_ : CommRing S) (_ : Algebra R S) (_ : Module.Free R S)
      (_ : Module.Finite R S),
      let q : Ideal S := p.map (algebraMap R S)
      ∃ (_ : q.IsPrime) (_ : q.LiesOver p), Nonempty (q.ResidueField ≃ₐ[p.ResidueField] L) :=
      sorry

end
