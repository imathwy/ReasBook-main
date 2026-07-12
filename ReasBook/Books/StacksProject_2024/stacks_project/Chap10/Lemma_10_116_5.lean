import StacksProject_2024.Chap10.Lemma_10_115_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
variable {K : Type w} [Field K] [Algebra k K]

/-
Source/core/bridge triage:
* primary domain: Krull dimension of finite-type algebras over a field under scalar extension;
* sampled owner API:
  `exists_finite_inj_algHom_of_fg` from mathlib's Noether-normalization file,
  `ringKrullDim_quotient_mvPolynomial_eq_of_finite_injective_polynomial_algebra` from
    Lemma `10.115.4`,
  `ringKrullDim_eq_of_injective_algebraMap_of_isIntegral` from Lemma `10.112.4`,
  `primeSpectrumTopologicalKrullDimAt_eq_of_tensorProduct_fieldExtension` from Lemma `10.116.6`;
* layer: `bridge/view`, since the source-facing statement is a global equality for `ringKrullDim`,
  while the owner-level content lives in Noether normalization, integral invariance of Krull
  dimension, and the local topological-dimension comparison under field extension;
* primitive data vs derived API: no additional public data are primitive here beyond the field
  extension `k → K` and the finite-type `k`-algebra `S`. The equality itself is derived API and
  should remain a thin theorem rather than a new wrapper or packaged construction.
-/

-- Proof sketch: apply Noether normalization to the finite type `k`-algebra `S` to get a finite
-- injective map from a polynomial ring `k[y₁, …, y_d]` with `d = ringKrullDim S`. Base change this
-- map along `k → K` to obtain a finite injective map `K[y₁, …, y_d] → K ⊗[k] S`, then use the
-- polynomial-ring dimension computation over a field together with invariance of Krull dimension
-- under finite injective integral extensions.
/-- Lemma 10.116.5: if `S` is a finite type `k`-algebra and `K / k` is a field extension, then the
Krull dimension of `S` equals the Krull dimension of the base change `K ⊗[k] S`. -/
theorem ringKrullDim_tensorProduct_eq_of_fieldExtension :
    ringKrullDim S = ringKrullDim (K ⊗[k] S) := sorry

end
