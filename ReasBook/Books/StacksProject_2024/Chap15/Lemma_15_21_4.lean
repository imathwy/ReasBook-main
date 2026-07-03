import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MvPolynomial PrimeSpectrum
open scoped BigOperators

universe u

section

variable {R : Type u} [CommRing R]
variable {n : ℕ} (d : Fin n → ℕ)

/- Domain sampling for this item:
* primary domain: affine prime-spectrum images for quotients and finite products of commutative
  rings;
* sampled core owners: `PrimeSpectrum.range_comap_of_surjective`, `MvPolynomial.eval`,
  `Pi.ker_ringHom`, `PrimeSpectrum.iUnion_range_comap_comp_evalRingHom`, and `zeroLocus_inf`;
* layer: this lemma is a `source-facing` split-polynomial specialization of those owner
  constructions, not a new owner abstraction. -/
-- Proof sketch: form the product of the evaluation maps indexed by
-- `k : ∀ i : Fin n, Fin (d i)`. The split-polynomial hypothesis ensures that the quotient map to
-- this finite product is surjective, so `range_comap_of_surjective` identifies the spectrum image
-- with the zero locus of the kernel. Then compute that kernel with `Pi.ker_ringHom`, and rewrite
-- the finite-product spectrum image through `iUnion_range_comap_comp_evalRingHom` and
-- `zeroLocus_inf`.
/-- Lemma 15.21.4: if `J ⊆ R[T₁, …, Tₙ]` contains, for each variable `Tᵢ`, the split polynomial
`∏ⱼ (Tᵢ - αᵢⱼ)`, then for `S = R[T₁, …, Tₙ] / J` the image of `Spec(S) → Spec(R)` is the zero
locus `V(⋂ₖ Jₖ)`, where `Jₖ` is the image of `J` under evaluation at the tuple
`Tᵢ ↦ αᵢ,ₖᵢ`. -/
theorem range_comap_polynomial_quotient_eq_zeroLocus_iInf_evaluationImage
    (J : Ideal (MvPolynomial (Fin n) R)) (α : ∀ i : Fin n, Fin (d i) → R)
    (hJ : ∀ i : Fin n, ∏ j : Fin (d i), (X i - C (α i j)) ∈ J) :
    Set.range (comap (algebraMap R (MvPolynomial (Fin n) R ⧸ J))) =
      zeroLocus
        (⨅ k : ∀ i : Fin n, Fin (d i),
          Ideal.map (eval fun i ↦ α i (k i)) J) := sorry

end
