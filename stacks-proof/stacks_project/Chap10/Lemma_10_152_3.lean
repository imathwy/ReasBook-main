import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling:
* primary domain: étale-local product decompositions for unramified finite-type algebra maps, with
  fiber primes tracked over a chosen base prime;
* sampled owner declarations:
  `exists_etale_finite_product_decomposition_with_purelyInseparable_residueFields_and_nonQuasiFinite_remainder`,
  `exists_etale_baseChange_prod_of_isUnramifiedAt`,
  `Ideal.primesOver`,
  `Algebra.isUnramifiedAt_iff_map_eq`;
* best owner abstraction:
  the chapter-local decomposition theorem
  `exists_etale_finite_product_decomposition_with_purelyInseparable_residueFields_and_nonQuasiFinite_remainder`,
  with factor primes recorded in the canonical owner fibers `p'.primesOver (A i)`;
* source/core/bridge triage:
  - `source-facing`: the present theorem, which keeps the finite product decomposition and upgrades
    the factor conclusions to surjectivity in the unramified case;
  - `core/canonical`: `Ideal.primesOver` for the distinguished factor primes;
  - `bridge/view`: the atomic identification of each distinguished prime with the extended ideal
    `Ideal.map (algebraMap R' (A i)) p'`;
* primitive data:
  an unramified `R`-algebra `S` and a prime `p ⊂ R`;
* derived API:
  the étale neighborhood, the finite family of factors, the distinguished primes over `p'`, the
  surjectivity of `R' → Aᵢ`, and the absence of primes of the remainder over `p'`.
-/

-- Proof sketch: start from the étale product decomposition of Lemma `10.145.4` applied to the
-- unramified finite type map `R → S`. For each finite factor `Aᵢ`, the unique prime over `p'`
-- has residue field both purely inseparable and separable over `κ(p')`, hence equal to `κ(p')`;
-- the local map `R'_{p'} → (Aᵢ)_{p'Aᵢ}` is therefore surjective by the unramified local
-- criterion. Finite generation lets one shrink the étale neighborhood so that each global map
-- `R' → Aᵢ` becomes surjective, and quasi-finiteness of unramified maps removes every prime of
-- the remainder `B` above `p'`.
/-- Lemma 10.152.3: if `R → S` is unramified and `p ⊂ R` is prime, then after an étale base
change `R → R'` with a prime `p'` over `p`, the algebra `R' ⊗[R] S` decomposes as a finite
product `A₁ × ... × Aₙ × B` such that each map `R' → Aᵢ` is surjective, the extended ideal
`p'Aᵢ` is a prime of `Aᵢ` lying over `p'`, and there is no prime of `B` lying over `p'`. -/
theorem exists_etale_product_decomposition_with_surjective_factors
    [Algebra.Unramified R S] (p : Ideal R) [p.IsPrime] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (p' : Ideal R') (_ : p'.IsPrime) (_ : p'.LiesOver p),
      ∃ (ι : Type (max u v)) (_ : Fintype ι) (A : ι → Type (max u v))
        (instAComm : ∀ i, CommRing (A i))
        (instAAlg : ∀ i, Algebra R' (A i)) (B : Type (max u v)) (instBComm : CommRing B)
        (instBAlg : Algebra R' B),
      letI : ∀ i, CommRing (A i) := instAComm
      letI : ∀ i, Algebra R' (A i) := instAAlg
      letI : CommRing B := instBComm
      letI : Algebra R' B := instBAlg
      ∃ e : R' ⊗[R] S ≃ₐ[R'] ((i : ι) → A i) × B,
      ∃ r : ∀ i, p'.primesOver (A i),
      (∀ i, Function.Surjective (algebraMap R' (A i))) ∧
        (∀ i, (r i).1 = Ideal.map (algebraMap R' (A i)) p') ∧
        (∀ q : p'.primesOver B, False) := sorry

end
