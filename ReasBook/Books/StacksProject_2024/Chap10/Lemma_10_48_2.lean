import Mathlib
import stacks_project.Chap10.Definition_10_48_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open AlgebraicGeometry CommRingCat

namespace Algebra

universe u

section

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]

-- Proof sketch: the forward implication is immediate. For the converse, pass to
-- `SeparableClosure k`, use the idempotent criterion for connectedness together with the
-- finite-subalgebra detection of idempotents after tensor product, and then compare an arbitrary
-- base change with a common overfield containing both it and `SeparableClosure k`.
/-- Source-facing companion to Lemma 10.48.2: it suffices to test connectedness of
`Spec (R ⊗[k] K)` on finite separable field extensions `K / k`. -/
theorem connectedSpace_primeSpectrum_baseChange_iff_finiteSeparable_baseChange :
    (∀ (K : Type u) [Field K] [Algebra k K], ConnectedSpace (PrimeSpectrum (R ⊗[k] K))) ↔
      ∀ (K : Type u) [Field K] [Algebra k K]
        [FiniteDimensional k K] [Algebra.IsSeparable k K],
        ConnectedSpace (PrimeSpectrum (R ⊗[k] K)) := sorry

/-- Lemma 10.48.2 (Tag 037S): a `k`-algebra is geometrically connected iff it remains connected
after every finite separable base change. -/
@[stacks 037S]
theorem Lemma_10_48_2 :
    geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k R))) ↔
      ∀ (K : Type u) [Field K] [Algebra k K]
        [FiniteDimensional k K] [Algebra.IsSeparable k K],
        ConnectedSpace (PrimeSpectrum (R ⊗[k] K)) := by
  rw [geometricallyConnected_iff_connectedSpace_primeSpectrum_baseChange]
  exact connectedSpace_primeSpectrum_baseChange_iff_finiteSeparable_baseChange

end

end Algebra
