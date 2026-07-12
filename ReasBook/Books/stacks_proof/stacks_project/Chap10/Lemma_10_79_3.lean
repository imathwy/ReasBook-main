import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (p : Ideal R) [p.IsPrime]
variable [Module.FinitePresentation R M]

/- Domain-style sampling:
* primary domain: localization descent for free finitely presented modules.
* sampled owner declarations:
  `Module.FinitePresentation.exists_free_localizedModule_powers`,
  `Module.freeLocus`,
  `Module.isOpen_freeLocus`.
* best owner abstraction: the canonical localized module map
  `LocalizedModule.mkLinearMap p.primeCompl M`; freeness after localization at a submonoid is the
  primitive owner statement, while primewise and open-locus formulations are derived views.
* layer: `bridge/view`; this item specializes the submonoid owner theorem to the complement of the
  prime ideal `p` and rewrites membership in `p.primeCompl` as the source-facing condition `f ∉ p`.
* primitive data: `M` and its canonical localization map at `p.primeCompl`.
* derived API: the witness `f ∉ p` and the away-localized freeness statement.
-/

-- Proof sketch: apply `Module.FinitePresentation.exists_free_localizedModule_powers` to the
-- canonical localization map `M → M_p` for the submonoid `p.primeCompl`. Since `M_p` is free, this
-- yields some `f ∈ p.primeCompl` such that `M` localized at the powers of `f` is free. Rewriting
-- `f ∈ p.primeCompl` as `f ∉ p` and the powers-localization as localization away from `f` gives
-- the stated result.
/-- Lemma 10.79.3: if a finitely presented `R`-module becomes free after localizing at the prime
ideal `p`, then there exists `f ∈ R` with `f ∉ p` such that localization away from `f` is a free
`R_f`-module. -/
@[stacks 0GWM]
theorem exists_not_mem_prime_localizedAway_free_of_localizedAtPrime_free
    [Module.Free (Localization.AtPrime p) (LocalizedModule.AtPrime p M)] :
    ∃ f : R, f ∉ p ∧ Module.Free (Localization.Away f) (LocalizedModule.Away f M) := by
  obtain ⟨f, hf, hfree, _⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M) (Localization.AtPrime p)
  exact ⟨f, hf, hfree⟩

end
