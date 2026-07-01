import stacks_project.Chap10.Lemma_10_70_2

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum
open scoped nonZeroDivisors

universe u

section

variable {R : Type u} [CommRing R]

private theorem affineBlowupChart_span_singleton_radical_eq_of_zeroLocus_eq
    (I : Ideal R) (f : R)
    (hV : zeroLocus ({f} : Set R) = zeroLocus (I : Set R)) :
    (Ideal.span ({f} : Set R)).radical = I.radical := by
  rw [← zeroLocus_eq_iff, zeroLocus_span]
  exact hV

/-- Lemma 10.70.7 in canonical algebraic form: if the principal ideal `(f)` and `I` have the same
radical, then the image of `f` in `R[I/a]` is a nonzerodivisor. -/
theorem affineBlowupChart_isRegular_of_radical_eq
    (I : Ideal R) (a : I) (f : R)
    (hI : (Ideal.span ({f} : Set R)).radical = I.radical) :
    IsRegular (algebraMap R (affineBlowupChart I a) f) := by
  sorry

/-- Lemma 10.70.7 in canonical algebraic form: if the principal ideal `(f)` and `I` have the same
radical, then `R_a` is the localization of `R[I/a]` away from the image of `f`. -/
theorem affineBlowupChart_isLocalizationAway_of_radical_eq
    (I : Ideal R) (a : I) (f : R)
    (hI : (Ideal.span ({f} : Set R)).radical = I.radical) :
    IsLocalization.Away (algebraMap R (affineBlowupChart I a) f) (Localization.Away a.1) := by
  sorry

/-- Lemma 10.70.7 in the source-text form `V(f) = V(I)`: the image of `f` in `R[I/a]` is a
nonzerodivisor. -/
theorem affineBlowupChart_isRegular_of_zeroLocus_eq
    (I : Ideal R) (a : I) (f : R)
    (hV : zeroLocus ({f} : Set R) = zeroLocus (I : Set R)) :
    IsRegular (algebraMap R (affineBlowupChart I a) f) :=
  affineBlowupChart_isRegular_of_radical_eq I a f
    (affineBlowupChart_span_singleton_radical_eq_of_zeroLocus_eq I f hV)

/-- Lemma 10.70.7 in the source-text form `V(f) = V(I)`: `R_a` is the localization of `R[I/a]`
away from the image of `f`. -/
theorem affineBlowupChart_isLocalizationAway_of_zeroLocus_eq
    (I : Ideal R) (a : I) (f : R)
    (hV : zeroLocus ({f} : Set R) = zeroLocus (I : Set R)) :
    IsLocalization.Away (algebraMap R (affineBlowupChart I a) f) (Localization.Away a.1) :=
  affineBlowupChart_isLocalizationAway_of_radical_eq I a f
    (affineBlowupChart_span_singleton_radical_eq_of_zeroLocus_eq I f hV)

end
