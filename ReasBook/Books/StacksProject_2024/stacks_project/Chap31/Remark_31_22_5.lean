import Mathlib
import StacksProject_2024.Chap15.Lemma_15_31_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open RingTheory.Sequence
open scoped TensorProduct
open Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.leftAlgebra

section

variable {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
variable [Algebra A B] [Algebra A A']
variable {r : ℕ} (f : Fin r → B)

-- Semantic recall: `lean_leansearch` surfaced the regular-sequence base-change owners
-- `RingTheory.Sequence.IsRegular.of_faithfullyFlat_of_isBaseChange` and
-- `RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange`; local Stacks precedent provides
-- `isQuasiRegularSequence_baseChange_of_flat_quotient` for the quasi-regular clause and
-- `RelativeQuasiRegularImmersion.isRegularImmersion_pullback_snd_of_flat_locallyOfFinitePresentation`
-- for the scheme-level regular-immersion interpretation.

/-- Remark 31.22.5 (1): if `f_1, ..., f_r` is a quasi-regular sequence in `B` and
`B / (f_1, ..., f_r)` is flat over `A`, then after any base change `A → A'` the sequence
`f_1 ⊗ 1, ..., f_r ⊗ 1` is quasi-regular in `B ⊗[A] A'`. The unchanged `Fin r` index records the
constant codimension. -/
@[stacks 0FUD]
theorem isQuasiRegularSequence_tensorProduct_baseChange_of_flat_quotient
    [Module.Flat A (B ⧸ Ideal.span (Set.range f))]
    (hqr : IsQuasiRegularSequence (List.ofFn f)) :
    IsQuasiRegularSequence
      (List.ofFn fun i : Fin r ↦ ((includeLeft : B →ₐ[A] B ⊗[A] A') (f i))) := sorry

/-- Remark 31.22.5 (2): if in addition `A → B` is flat and finitely presented, then for every
prime `q'` of the base-changed ring `B ⊗[A] A'`, the images of
`f_1 ⊗ 1, ..., f_r ⊗ 1` form a regular sequence in the local ring `(B ⊗[A] A')_{q'}`. -/
@[stacks 0FUD]
theorem isRegularSequence_localizationAtPrime_tensorProduct_baseChange_of_quasiRegularSequence
    [Module.Flat A B] [Algebra.FinitePresentation A B]
    [Module.Flat A (B ⧸ Ideal.span (Set.range f))]
    (hqr : IsQuasiRegularSequence (List.ofFn f))
    (q' : PrimeSpectrum (B ⊗[A] A')) :
    IsRegular (Localization.AtPrime q'.asIdeal)
      (List.ofFn fun i : Fin r ↦
        algebraMap (B ⊗[A] A') (Localization.AtPrime q'.asIdeal)
          ((includeLeft : B →ₐ[A] B ⊗[A] A') (f i))) := sorry

end

end
