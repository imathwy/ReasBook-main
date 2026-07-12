import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Support
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Owner-form of Lemma 10.40.7: a prime lies in the support of the cyclic module `R ∙ m`
precisely when the image of `m` in the localization `M_𝔭` is nonzero. -/
theorem mem_support_span_singleton_iff_localized_ne_zero
    (p : PrimeSpectrum R) (m : M) :
    p ∈ Module.support R (R ∙ m) ↔
      LocalizedModule.mkLinearMap p.asIdeal.primeCompl M m ≠ 0 := by
  let S := p.asIdeal.primeCompl
  let e : (R ∙ m).localized S ≃ₗ[Localization S] LocalizedModule S (R ∙ m) :=
    Submodule.localizedEquiv S (R ∙ m)
  have hlocalized :
      (R ∙ m).localized S =
        (Localization S) ∙ LocalizedModule.mkLinearMap S M m := by
    simpa only [S, Submodule.localized, Set.image_singleton] using
      Submodule.localized'_span (Localization S) S (LocalizedModule.mkLinearMap S M)
        ({m} : Set M)
  rw [Module.mem_support_iff, ← e.toEquiv.nontrivial_congr, Submodule.nontrivial_iff_ne_bot,
    hlocalized]
  exact Submodule.span_singleton_eq_bot.not

/-- Lemma 10.40.7: a prime ideal lies in the zero locus of the annihilator of `m` precisely when
the image of `m` in the localization `M_𝔭` is nonzero.

This is a source-facing bridge from the owner abstraction `Module.support` for the cyclic module
`R ∙ m`, together with the canonical element-annihilator
`Ideal.torsionOf R M m = {r : R | r • m = 0}`. -/
@[stacks 07Z5]
theorem mem_zeroLocus_annihilator_span_singleton_iff_localized_ne_zero
    (p : PrimeSpectrum R) (m : M) :
    p ∈ PrimeSpectrum.zeroLocus (Ideal.torsionOf R M m) ↔
      LocalizedModule.mkLinearMap p.asIdeal.primeCompl M m ≠ 0 := by
  simpa [Module.support_eq_zeroLocus, Ideal.torsionOf, Submodule.annihilator_span_singleton] using
    (mem_support_span_singleton_iff_localized_ne_zero p m)

end
