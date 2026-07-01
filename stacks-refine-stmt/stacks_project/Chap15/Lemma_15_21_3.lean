import Mathlib
import stacks_project.Chap15.Lemma_15_21_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open MvPolynomial

universe u v

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]

/- Domain sampling for this item:
* primary domain: finite polynomial quotient models for finite algebras after finite free base
  change;
* sampled declarations: `exists_finiteFree_extension_with_monic_linear_factor`,
  `Algebra.FiniteType.iff_quotient_mvPolynomial''`, `MvPolynomial.aeval`, and
  `Algebra.TensorProduct.commRight`;
* layer triage:
  - `source-facing`: the existence of a finite free injective base change after which `S` is a
    quotient of a split polynomial algebra;
  - `core/canonical`: `Algebra.FiniteType.iff_quotient_mvPolynomial''` for quotient presentations
    by polynomial algebras, together with the canonical base-change owner `R' ⊗[R] S`;
  - `source-facing owner`: the quotient ring
    `MvPolynomial (Fin n) R' ⧸ Ideal.span (Set.range fun i ↦ ∏ j, (X i - C (α i j)))`
    together with its canonical `R'`-algebra map to `R' ⊗[R] S`;
  - `bridge/view`: the textbook right-tensor presentation `S ⊗[R] R'`, identified with the chosen
    owner by `Algebra.TensorProduct.commRight`.
* owner decision: keep the source-facing split quotient presentation, but phrase it directly as an
  `R'`-algebra quotient of the canonical base-change owner `R' ⊗[R] S`; the unsplit polynomial
  quotient owner already lives upstream in `Algebra.FiniteType.iff_quotient_mvPolynomial''`, so
  this file should add only the extra split-relations content.
* primitive data: the finite free injective extension `R → R'`, the arities `d`, and the chosen
  roots `α`;
* derived API: the quotient type and its surjective map to `R' ⊗[R] S`, obtained from
  `MvPolynomial.aeval` followed by the canonical ideal quotient lift; the right-tensor textbook
  form is only a bridge via tensor commutativity.
  -/

-- Proof sketch: choose finitely many generators `x₁, …, xₙ` of the finite `R`-algebra `S`. For
-- each generator, pick a monic annihilating polynomial over `R`, then apply Lemma `15.21.2`
-- repeatedly to obtain a finite free `R`-algebra `R'` over which all these polynomials split
-- completely. After base change, send `X i` to `1 ⊗ₜ[R] xᵢ` in the canonical base-change owner
-- `R' ⊗[R] S`; the split relations vanish, so `MvPolynomial.aeval` factors through the quotient
-- and remains surjective.
/-- Lemma 15.21.3: after a finite free injective base change `R → R'`, the canonical base-changed
algebra `R' ⊗[R] S` (equivalently the textbook `S ⊗[R] R'`) is a quotient of a split polynomial
algebra `R'[T₁, …, Tₙ] / (P₁(T₁), …, Pₙ(Tₙ))`, where each `Pᵢ` is a product of linear factors over
`R'`; the equivalence with `S ⊗[R] R'` is the tensor-symmetry bridge
`Algebra.TensorProduct.commRight`. -/
theorem exists_finiteFree_baseChange_surjective_splitPolynomialQuotient
    :
    ∃ (n : ℕ) (R' : Type (max u v)) (_ : CommRing R') (_ : Algebra R R')
      (_ : Function.Injective (algebraMap R R')) (_ : Module.Finite R R')
      (_ : Module.Free R R') (d : Fin n → ℕ) (α : ∀ i, Fin (d i) → R'),
      ∃ φ :
        (MvPolynomial (Fin n) R' ⧸
          Ideal.span (Set.range fun i ↦ ∏ j : Fin (d i), (X i - C (α i j)))) →ₐ[R']
          (R' ⊗[R] S),
        Function.Surjective φ := sorry

end
