import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
