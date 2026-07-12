import StacksProject_2024.Chap10.Lemma_10_118_3
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M]

open GenericFlatness

/- Domain-style sampling:
* primary domain: generic freeness for finite type algebras and finite modules over a domain;
* sampled owner declarations:
  `Module.FinitePresentation.exists_free_localizedModule_powers`,
  `Module.freeLocus`,
  `LocalizationCondition`,
  `exists_nonzero_localization_away_free_and_finitePresentation_of_finiteType`;
* core/canonical owner in this chapter: `LocalizationCondition R S M f`;
* primitive vs derived API: the localization parameter `f` is primitive, while freeness of
  `LocalizedModule.Away (algebraMap R S f) M` is derived owner API via
  `LocalizationCondition.free_module`;
* layer triage: this file is `bridge/view`, keeping the source-facing freeness consequence while
  reusing the stronger localization owner from `Lemma_10_118_3`.
-/
-- Proof sketch: apply the stronger finite-type generic-flatness theorem `Lemma_10_118_3`, which
-- already produces a nonzero `f` with `LocalizationCondition R S M f`; the present statement is
-- just the `free_module` projection from that owner.
/-- Lemma 10.118.1: if `R` is a domain, `S` is a finite type `R`-algebra, and `M` is a finite
`S`-module, then some nonzero localization `M_f` is a free `R_f`-module. -/
@[stacks 051R]
theorem exists_nonzero_localization_away_module_free
    [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] :
    ∃ f : R, f ≠ 0 ∧
      Module.Free (Localization.Away f) (LocalizedModule.Away (algebraMap R S f) M) := by
  obtain ⟨f, hf, hcond⟩ : ∃ f : R, f ≠ 0 ∧ LocalizationCondition R S M f :=
    exists_nonzero_localization_away_free_and_finitePresentation_of_finiteType
  exact ⟨f, hf, hcond.free_module⟩

end
