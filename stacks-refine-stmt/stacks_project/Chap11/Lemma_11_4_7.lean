import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {k : Type u} [Field k]
variable {A : Type v} {A' : Type w} [Ring A] [Ring A'] [Algebra k A] [Algebra k A']
variable [IsSimpleRing A] [IsSimpleRing A']

/-- If `A` is a finite-dimensional central simple `k`-algebra and `A'` is simple over `k`, then
`A ⊗[k] A'` is simple. -/
theorem isSimpleRing_tensorProduct_of_finite_central_left_factor
    [FiniteDimensional k A] [Algebra.IsCentral k A] :
    IsSimpleRing (A ⊗[k] A') := sorry

/-- Lemma 11.4.7: if `A` and `A'` are simple `k`-algebras and one of them is finite-dimensional
and central over `k`, then the tensor product `A ⊗[k] A'` is simple. -/
-- Proof sketch: argue by cases on which factor is finite and central. In the finite central case,
-- apply the Wedderburn decomposition of that factor into a matrix algebra over a central division
-- algebra, use Lemma 11.4.4 to obtain simplicity after tensoring with the division algebra, and
-- then transport simplicity across the resulting matrix-algebra identification using Lemma 11.4.5.
theorem isSimpleRing_tensorProduct_of_finite_central_factor
    (h : (FiniteDimensional k A ∧ Algebra.IsCentral k A) ∨
      (FiniteDimensional k A' ∧ Algebra.IsCentral k A')) :
    IsSimpleRing (A ⊗[k] A') := by
  rcases h with h | h
  · letI := h.1
    letI := h.2
    exact isSimpleRing_tensorProduct_of_finite_central_left_factor
  · letI := h.1
    letI := h.2
    let h' : IsSimpleRing (A' ⊗[k] A) :=
      isSimpleRing_tensorProduct_of_finite_central_left_factor
    exact IsSimpleRing.of_ringEquiv (Algebra.TensorProduct.comm k A' A).toRingEquiv h'

end
