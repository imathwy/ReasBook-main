import Mathlib
import StacksProject_2024.Chap31.Lemma_31_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory.Limits
open IsLocalRing
open PrimeSpectrum

universe u v

section

variable {A : Type u} [CommRing A] [IsLocalRing A]

-- Semantic recall: `lean_leansearch` surfaced the mathlib owner `localCohomology` together with
-- the standard local-homomorphism predicate `IsLocalHom`; `Chap31/Lemma_31_16_1` provides the
-- chapter's canonical punctured-spectrum open `puncturedSpectrumOpen`.

/-- Remark 31.16.3 (1): if the punctured spectrum of a local ring `(A, 𝔪)` is affine, then there
is a finitely generated ideal whose radical is the maximal ideal. -/
@[stacks 0BCT]
theorem exists_finite_radical_maximalIdeal_of_isAffineOpen_localPuncturedSpectrum
    (hU : IsAffineOpen (puncturedSpectrumOpen :
      (Spec (CommRingCat.of A)).Opens)) :
    ∃ I : Ideal A, I.FG ∧ maximalIdeal A = I.radical := sorry

/-- Remark 31.16.3 (2): if the maximal ideal of a local ring `(A, 𝔪)` is the radical of a
principal ideal, then the punctured spectrum of `A` is affine. -/
@[stacks 0BCT]
theorem isAffineOpen_localPuncturedSpectrum_of_radical_span_singleton
    {f : A} (hf : maximalIdeal A = (Ideal.span ({f} : Set A)).radical) :
    IsAffineOpen (puncturedSpectrumOpen :
      (Spec (CommRingCat.of A)).Opens) := sorry

/-- Remark 31.16.3 (3): if the punctured spectrum of `(A, 𝔪)` is affine, then for any finitely
generated ideal `I` with radical `𝔪`, the quotient by a nonzerodivisor `f ∈ 𝔪` cannot have
vanishing degree-zero local cohomology with support in `I`; in particular this rules out the
regular-sequence-of-length-two situation mentioned in the source. -/
@[stacks 0BCT]
theorem not_isZero_localCohomology_zero_quotient_of_isAffineOpen_localPuncturedSpectrum
    (hU : IsAffineOpen (puncturedSpectrumOpen :
      (Spec (CommRingCat.of A)).Opens))
    {I : Ideal A} (hIfg : I.FG) (hI : maximalIdeal A = I.radical)
    {f : A} (hf_mem : f ∈ maximalIdeal A) (hf_nzd : f ∈ nonZeroDivisors A) :
    ¬ IsZero (((localCohomology I 0).obj
      (ModuleCat.of A (A ⧸ Ideal.span ({f} : Set A))))) := sorry

/-- Remark 31.16.3 (4): the same nonvanishing conclusion holds after passing to a target local
ring `A'` of a local homomorphism `A → A'` for which the maximal ideal of `A'` is the radical of
the extended maximal ideal `𝔪_A A'`. -/
@[stacks 0BCT]
theorem not_isZero_localCohomology_zero_quotient_of_localHom_target
    (hU : IsAffineOpen (puncturedSpectrumOpen :
      (Spec (CommRingCat.of A)).Opens))
    {A' : Type v} [CommRing A'] [IsLocalRing A']
    (φ : A →+* A') [IsLocalHom φ]
    (hφ : maximalIdeal A' = (Ideal.map φ (maximalIdeal A)).radical)
    {f : A'} (hf_mem : f ∈ maximalIdeal A') (hf_nzd : f ∈ nonZeroDivisors A') :
    ¬ IsZero (((localCohomology (Ideal.map φ (maximalIdeal A)) 0).obj
      (ModuleCat.of A' (A' ⧸ Ideal.span ({f} : Set A'))))) := sorry

end
