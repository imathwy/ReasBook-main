import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_10_152_1 (from Chap10) -/
namespace Algebra

/- Domain triage:
* primary domain: local structure of finite-type unramified algebra maps via standard étale
  neighborhoods and surjections onto basic-open localizations;
* sampled declarations: `IsUnramifiedAt`, `HasStandardEtaleSurjectionOn`,
  `IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn`, and `IsEtaleAt.exists_isStandardEtale`;
* source-facing layer: the existence of a standard étale `R`-algebra surjecting onto
  `S[1 / f]` near an unramified prime;
* core/canonical layer: `IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn`;
* bridge/view layer: `HasStandardEtaleSurjectionOn`, which packages the surjective map from a
  standard étale algebra to the localization.

Primitive-vs-derived split:
* primitive data: a prime `Q : Ideal S` with `[Q.IsPrime]`, finite type of `S` over `R`, and the
  local owner `[IsUnramifiedAt R Q]`;
* derived API: a witness `f ∉ Q` and the resulting `HasStandardEtaleSurjectionOn R f`.
-/

/- Proposition 10.152.1: if `Q ⊂ S` is a prime ideal and `R → S` is unramified at `Q`, then
there exists `f ∈ S \ Q` and a standard étale `R`-algebra surjecting onto the localization
`S[1 / f]`. This is exactly the canonical local-structure theorem
`IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn`. -/
recall IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn

end Algebra

/-! ### Lemma_10_152_2 (from Chap10) -/
open scoped TensorProduct
open Algebra.TensorProduct

universe u v

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]

/- Domain-style sampling:
* primary domain: unramified finite-type algebra maps and the étale-local quasi-finite splitting
  theorem at a chosen prime;
* sampled owner declarations:
  `Algebra.IsUnramifiedAt`,
  `Algebra.QuasiFiniteAt`,
  `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`,
  `Ideal.primesOver`;
* best owner abstraction:
  the core/canonical owner is the mathlib theorem
  `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`, reached here through the canonical
  implication `Algebra.IsUnramifiedAt R q → Algebra.QuasiFiniteAt R q`;
* layer triage:
  this numbered item is `source-facing`: it reformulates the idempotent-based owner theorem as a
  two-factor product decomposition with the distinguished prime singled out on the left factor;
* primitive data:
  the finite-type algebra `R → S`, the ideal `p ⊂ R`, the prime `q ⊂ S` with `q` lying over `p`,
  and the canonical local owner `[Algebra.IsUnramifiedAt R q]`;
* derived API:
  the étale neighborhood `R → R'`, the product decomposition `R' ⊗[R] S ≃ A × B`, the surjective
  map `R' → A`, the prime `p` recovered from `q.under R`, and the prime `p'A` identified with the
  chosen prime over `q`.
-/

-- Proof sketch: unramifiedness at `q` makes the localized map quasi-finite at `q`. Apply the
-- étale local splitting theorem that produces an étale neighborhood together with an idempotent in
-- `R' ⊗[R] S`, then convert that idempotent into a product decomposition `A × B`. The factor
-- singled out by the idempotent is finite over `R'`, which yields surjectivity of `R' → A`, and
-- the distinguished prime above `p'` corresponds to the prime lying over `q`.
/-- Lemma 10.152.2: if `q` lies over `p`, `R → S` is of finite type, and `R → S` is unramified at
`q`, then after an étale base change `R → R'` with a prime `p'` over `p`, the tensor product
`R' ⊗[R] S` splits as `A × B` so that `R' → A` is surjective and the extended ideal `p' A` is a
prime of `A` lying over both `p'` and `q`. -/
theorem exists_etale_baseChange_prod_of_isUnramifiedAt
    (p : Ideal R) (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra.IsUnramifiedAt R q] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (p' : Ideal R') (_ : p'.IsPrime) (_ : p'.LiesOver p)
      (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R' A)
      (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R' B)
      (e : R' ⊗[R] S ≃ₐ[R'] A × B),
      let pA : Ideal A := Ideal.map (algebraMap R' A) p'
      let πA : S →+* A :=
        (((RingHom.fst A B).comp e.toRingHom).comp
          (includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom)
      Function.Surjective (algebraMap R' A) ∧
        pA.IsPrime ∧
        pA.LiesOver p' ∧
        Ideal.comap πA pA = q := sorry

end

/-! ### Lemma_10_152_3 (from Chap10) -/
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
