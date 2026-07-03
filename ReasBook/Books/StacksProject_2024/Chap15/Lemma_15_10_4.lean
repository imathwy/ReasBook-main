import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Polynomial
open Polynomial

universe u v w w'

section

variable {A : Type u} {B : Type v} {B₁ : Type w} {B₂ : Type w'}
variable [CommRing A] [CommRing B] [CommRing B₁] [CommRing B₂]
variable [Algebra A B] [Module.Finite A B]
variable (I : Ideal A)
variable [Algebra (A ⧸ I) B₁] [Algebra (A ⧸ I) B₂]

/- Domain-style sampling:
- primary domain: finite commutative `A`-algebras, quotient product decompositions over `A ⧸ I`,
  and polynomial relations detected modulo `I`;
- sampled owner declarations:
  `Algebra.exists_monic_polynomial_of_isIdempotentElem_mod_map`,
  `aeval`,
  `Ideal.Quotient.mk`;
- best owner abstraction: the source-facing polynomial witness should use the direct existential
  owner style already established by `Algebra.exists_monic_polynomial_of_isIdempotentElem_mod_map`,
  with `f.Monic`, `aeval b f = 0`, and the quotient polynomial identity as derived witness data;
- primitive data: the product decomposition of `B ⧸ I B`, the surjectivity of `A ⧸ I → B₁`, and
  the element `b` mapping to `(1, 0)`;
- derived API: the existence of a monic annihilating polynomial with the specified image in
  `(A ⧸ I)[X]`.

Source/core/bridge triage:
- `source-facing`: the theorem below, which produces the polynomial relation attached to the chosen
  component `(1, 0)`;
- `core/canonical`: the chapter owner theorem
  `Algebra.exists_monic_polynomial_of_isIdempotentElem_mod_map` for the idempotent-lifting
  polynomial witness;
- `bridge/view`: the product decomposition hypothesis, which identifies the image of `b` with the
  distinguished idempotent `(1, 0)` and upgrades the generic idempotent witness to the sharper
  factor `(X - 1) * X ^ d`.

The previous local class only repackaged this witness data for a single theorem, so the public
surface should expose the direct existential statement instead of a parallel wrapper owner.
-/

-- Proof sketch: use Lemma `15.9.10` to lift the idempotent `(1, 0)` after an étale base change,
-- split the base change of `b` into the two factors, kill the second factor by a monic polynomial
-- with coefficients in `I`, and then descend the resulting relation from the faithfully flat étale
-- cover back to `B`.
/-- Lemma 15.10.4: for a finite `A`-algebra `B` over a Zariski pair `(A, I)`, if `B ⧸ I B`
identifies with a product `B₁ × B₂` of `A ⧸ I`-algebras, the map `A ⧸ I → B₁` is surjective, and
`b : B` maps to `(1, 0)`, then `b` satisfies a monic polynomial whose reduction modulo `I` is of
the form `(X - 1) * X^d` with `d ≥ 1`. -/
theorem exists_monic_polynomial_of_product_decomposition_mod_ideal
    (hI : I ≤ Ring.jacobson A)
    (hprod : (B ⧸ Ideal.map (algebraMap A B) I) ≃ₐ[A ⧸ I] (B₁ × B₂))
    (hsurj : Function.Surjective (algebraMap (A ⧸ I) B₁))
    (b : B)
    (hb : hprod (Ideal.Quotient.mk (Ideal.map (algebraMap A B) I) b) = ((1 : B₁), (0 : B₂))) :
    ∃ d : ℕ, 0 < d ∧ ∃ f : A[X],
      f.Monic ∧
        aeval b f = 0 ∧
          f.map (Ideal.Quotient.mk I) = ((X - 1) * X ^ d : (A ⧸ I)[X]) := by
  sorry

end
