import Mathlib.RingTheory.Etale.QuasiFinite

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

/- Domain-style sampling:
* primary domain: quasi-finite finite-type algebra maps and their étale-local splitting over a
  chosen fiber prime;
* sampled owner declarations:
  `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`,
  `Ideal.fiberIsoOfBijectiveResidueField`,
  `Ideal.primesOver`,
  `Algebra.QuasiFiniteAt`;
* best owner abstraction:
  the one-factor splitting owner theorem
  `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`, together with the fiber owner
  `Ideal.primesOver` and the local property owner `Algebra.QuasiFiniteAt`;
* layer:
  this numbered item is `source-facing`: it upgrades the one-factor owner theorem to a finite
  family decomposition, so it should stay a theorem rather than a new wrapper owner;
* primitive data:
  a finite-type `R`-algebra `S` and a prime `p ⊂ R`;
* derived API:
  the étale neighborhood, the residue-field bijection, the finite-indexed family of finite
  factors with their distinguished primes in the owner fibers `p'.primesOver (A i)`, and the
  non-quasi-finite remainder over `p'`.
-/

-- Proof sketch: induct on the number of isolated closed points of the fiber
-- `S ⊗[R] κ(p)`. If there are none, take no finite factors and keep the whole base change as the
-- remainder. Otherwise choose an isolated closed point, apply the one-factor splitting theorem of
-- Lemma `10.145.2`, identify the new fiber with the old one via the residue-field bijection, and
-- iterate on the complementary factor.
/-- Lemma 10.145.3: for a finite type ring map `R → S` and a prime `p ⊂ R`, there exists an
étale neighborhood `R → R'` with a prime `p'` over `p` and `κ(p') = κ(p)` such that the base
change `R' ⊗[R] S` decomposes as a finite product of finite `R'`-algebras, each equipped with its
unique prime `rᵢ` over `p'`, together with a remaining factor having no prime over `p'` at which
`R' → B` is quasi-finite. -/
theorem exists_etale_finite_product_decomposition_with_nonQuasiFinite_remainder
    (p : Ideal R) [p.IsPrime] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (p' : Ideal R') (_ : p'.IsPrime) (_ : p'.LiesOver p),
      ∃ hκ : Function.Bijective
        (Ideal.ResidueField.mapₐ p p' (Algebra.ofId _ _) (p'.over_def p)),
      ∃ (ι : Type (max u v)) (_ : Fintype ι) (A : ι → Type (max u v))
        (instAComm : ∀ i, CommRing (A i)) (instAAlg : ∀ i, Algebra R' (A i))
        (B : Type (max u v)) (instBComm : CommRing B) (instBAlg : Algebra R' B),
      letI : ∀ i, CommRing (A i) := instAComm
      letI : ∀ i, Algebra R' (A i) := instAAlg
      letI : CommRing B := instBComm
      letI : Algebra R' B := instBAlg
      ∃ e : R' ⊗[R] S ≃ₐ[R'] ((i : ι) → A i) × B,
      ∃ hfinite : ∀ i, Module.Finite R' (A i),
      ∃ r : ∀ i, p'.primesOver (A i),
      ∃ hsubsingleton : ∀ i, Subsingleton (p'.primesOver (A i)),
      ∀ q : p'.primesOver B, ¬ Algebra.QuasiFiniteAt R' q.1 := sorry

end
