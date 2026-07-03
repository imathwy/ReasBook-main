import Mathlib.Tactic.Recall
import StacksProject_2024.Chap15.Lemma_15_8_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Companion recall: the owner object for the textbook support of an `R`-module is
`Module.support R M`. -/
recall Module.support

/- Companion recall: for a finitely presented `R`-module, the canonical owner ideal cutting out
the support is the zeroth Fitting ideal `moduleFittingIdeal R M 0`. -/
recall moduleFittingIdeal

/- Companion recall: the support of a finite module is canonically the zero locus of its zeroth
Fitting ideal. This is the source-faithful bridge used in Lemma 10.40.8. -/
recall zeroLocus_moduleFittingIdeal_zero_eq_support

/- Companion recall: finite presentation makes the zeroth Fitting ideal finitely generated. -/
recall moduleFittingIdeal_fg_of_finitePresentation

/- Companion recall: finite modules have closed support. Since finitely presented modules are
finite, this supplies the closedness half of Lemma 10.40.8 directly from the owner abstraction
`Module.support`. -/
recall Module.isClosed_support

/- Companion recall: on `Spec R`, compact open subsets are exactly complements of zero loci of
finitely generated ideals. This is the ambient compact-open owner theorem used to package the
quasi-compactness conclusion. -/
recall PrimeSpectrum.isCompact_isOpen_iff_ideal

namespace Module

variable [FinitePresentation R M]

-- Proof sketch: rewrite `support R M` as the zero locus of the canonical zeroth Fitting ideal,
-- use finite presentation to make that ideal finitely generated, then apply
-- `PrimeSpectrum.isCompact_isOpen_iff_ideal`.
/-- Lemma 10.40.8: if `M` is a finitely presented `R`-module, then `Supp(M)` is closed and its
complement in `Spec R` is quasi-compact. In Lean, quasi-compactness of a subset of `Spec R` is
expressed by `IsCompact`. -/
theorem isClosed_support_and_isCompact_compl_support :
    IsClosed (support R M) ∧ IsCompact (support R M)ᶜ := by
  refine ⟨isClosed_support, ?_⟩
  simpa [zeroLocus_moduleFittingIdeal_zero_eq_support] using
    (isCompact_isOpen_iff_ideal.mpr
      ⟨moduleFittingIdeal R M 0, moduleFittingIdeal_fg_of_finitePresentation 0, rfl⟩).1

/-- Companion consequence of Lemma 10.40.8: for a finitely presented module, the complement of
`Supp(M)` is quasi-compact. -/
theorem isCompact_compl_support :
    IsCompact (support R M)ᶜ :=
  isClosed_support_and_isCompact_compl_support.2

end Module
