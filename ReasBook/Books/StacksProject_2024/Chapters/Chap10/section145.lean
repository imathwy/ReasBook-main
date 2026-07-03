import Mathlib
import Mathlib.RingTheory.Etale.QuasiFinite
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_145_1 (from Chap10) -/
open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S' : Type v} {S : Type w}
variable [CommRing R] [CommRing S'] [CommRing S]
variable [Algebra R S'] [Algebra R S]
variable [Algebra.IsIntegral R S'] [Algebra.FiniteType R S]

/- Domain-style sampling:
* primary domain: commutative algebra of localizations and fibers of finite-type / integral
  algebra maps;
* sampled owner declarations:
  `Localization.awayMapₐ`,
  `Ideal.Fiber`,
  `Localization.exists_finite_awayMapₐ_of_surjective_awayMapₐ`;
* best owner abstraction:
  the mathlib spreading-out lemma
  `Localization.exists_finite_awayMapₐ_of_surjective_awayMapₐ`;
* layer:
  this numbered item is direct `core/canonical` owner reuse, so no extra local bridge theorem is
  needed;
* primitive data:
  the algebra map `f`, the localization element `g`, the prime `p`, and the fiberwise unit
  hypothesis;
* derived API:
  finiteness of the localization `R[1/r] → S[1/r]` away from some `r ∉ p`.
-/

/- Lemma 10.145.1: this is exactly the canonical localization-away spreading-out lemma
`Localization.exists_finite_awayMapₐ_of_surjective_awayMapₐ`. The source-facing statement adds no
extra mathematical content beyond that owner theorem, so the file records direct reuse instead of a
stronger local bijectivity wrapper. -/
recall Localization.exists_finite_awayMapₐ_of_surjective_awayMapₐ

end

/-! ### Lemma_10_145_2 (from Chap10) -/
/- Domain-style sampling:
* primary domain: quasi-finite finite-type algebra maps and their étale-local splitting at a
  chosen prime;
* sampled owner declarations:
  `Algebra.QuasiFiniteAt`,
  `Ideal.fiberIsoOfBijectiveResidueField`,
  `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`;
* best owner abstraction:
  the canonical mathlib theorem
  `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`;
* layer:
  this numbered item is direct `core/canonical` owner reuse, not a new source-facing wrapper;
* primitive data:
  a finite-type `R`-algebra `S`, primes `p ⊂ R` and `q ⊂ S` with `q` lying over `p`, and the
  hypothesis `[Algebra.QuasiFiniteAt R q]`;
* derived API:
  the étale neighborhood, the prime above `p`, the bijective residue-field map, and the
  idempotent cutting out the distinguished finite factor of `R' ⊗[R] S`.
-/

/- Lemma 10.145.2: let `R → S` be a finite type ring map, let `q ⊂ S` be a prime lying over
`p ⊂ R`, and assume `R → S` is quasi-finite at `q`. Then after passing to an étale
neighborhood `R → R'` with a prime `p'` over `p` and `κ(p') = κ(p)`, the base change
`R' ⊗[R] S` splits as a product `A × B` such that `A` is finite over `R'`, `A` has a unique
prime over `p'` lying over `q`, and `B` has no prime simultaneously lying over `p'` and `q`.
Mathlib packages this canonical decomposition by the equivalent idempotent-element form
`Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`, where the product decomposition is
encoded by the idempotent corresponding to `(1, 0)`. -/
recall Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq

/-! ### Lemma_10_145_3 (from Chap10) -/
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

/-! ### Lemma_10_145_4 (from Chap10) -/
open scoped TensorProduct

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

/- Domain-style sampling:
* primary domain: quasi-finite finite-type algebra maps, étale neighborhoods, and residue-field
  control on the resulting fiber factors;
* sampled owner declarations:
  `exists_etale_liesOver_with_residueField_equiv`,
  `exists_etale_finite_product_decomposition_with_nonQuasiFinite_remainder`,
  `Ideal.primesOver`,
  `Ideal.ResidueField.mapₐ`;
* best owner abstraction:
  the chapter-local decomposition theorem
  `exists_etale_finite_product_decomposition_with_nonQuasiFinite_remainder`, with the fiber owner
  `Ideal.primesOver` and the canonical residue-field bridge supplied by the lies-over relation;
* layer triage:
  - `source-facing`: the present theorem, which keeps the decomposition from Lemma `10.145.3` and
    adds the purely inseparable residue-field conclusion;
  - `core/canonical`: `Ideal.primesOver` for the distinguished primes and the induced
    `κ(p')`-algebra structure on `κ(rᵢ)`;
  - `bridge/view`: `Ideal.ResidueField.mapₐ`, expressing the residue-field extension attached to a
    prime lying over `p'`;
* primitive data:
  a finite-type `R`-algebra `S` and a prime `p ⊂ R`;
* derived API:
  the étale neighborhood `R → R'`, the finite family of finite factors indexed by a canonical
  finite type `ι`, their distinguished primes in `p'.primesOver (A i)`, the finite purely
  inseparable residue-field extensions over `κ(p')`, and the non-quasi-finite remainder over `p'`.
-/

-- Proof sketch: first enlarge the residue field at `p` by a finite separable extension using
-- Lemma `10.144.3` so that every quasi-finite prime in the fiber acquires purely inseparable
-- residue field over the new base point. Then apply the product decomposition of Lemma `10.145.3`
-- to the resulting étale neighborhood; the distinguished primes in the finite factors keep the
-- same residue fields, while the remaining factor is not quasi-finite over the chosen prime.
/-- Lemma 10.145.4: for a finite type ring map `R → S` and a prime `p ⊂ R`, there exists an étale
neighborhood `R → R'` with a prime `p'` over `p` such that `R' ⊗[R] S` decomposes as a finite
product of finite `R'`-algebras `Aᵢ` and a remainder `B`, where each `Aᵢ` comes with its unique
prime `rᵢ` over `p'`, the corresponding residue field extension over `κ(p')` is finite and purely
inseparable, and `R' → B` is not quasi-finite at any prime over `p'`. -/
theorem exists_etale_finite_product_decomposition_with_purelyInseparable_residueFields_and_nonQuasiFinite_remainder
    (p : Ideal R) [p.IsPrime] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (p' : Ideal R') (_ : p'.IsPrime) (_ : p'.LiesOver p),
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
      ∃ hres :
        ∀ i,
          FiniteDimensional p'.ResidueField (r i).1.ResidueField ∧
            IsPurelyInseparable p'.ResidueField (r i).1.ResidueField,
      ∀ q : p'.primesOver B, ¬ Algebra.QuasiFiniteAt R' q.1 := sorry

end
