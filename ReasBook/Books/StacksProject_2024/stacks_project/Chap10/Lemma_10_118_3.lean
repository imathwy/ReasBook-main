import StacksProject_2024.Chap10.«10_118_3_1»

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} [CommRing R] [IsDomain R]
variable {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
variable {M : Type w} [AddCommGroup M] [Module S M] [Module.Finite S M]

open GenericFlatness

/- Domain-style sampling:
* primary domain: generic freeness / generic flatness for finite type algebras and finite modules
  over a domain;
* sampled owner declarations:
  `GenericFlatness.LocalizationCondition`,
  `GenericFlatness.goodLocus`,
  `Module.FinitePresentation.exists_free_localizedModule_powers`,
  `Module.freeLocus`;
* best owner abstraction in this chapter: `LocalizationCondition R S M f`;
* primitive data: the rings/algebra/module and the localization parameter `f`;
* derived API: finite presentation and freeness of `S_f` and `M_f`;
* layer triage: this file is `source-facing`, asserting existence of a localization satisfying the
  chapter owner condition.
-/
-- Proof sketch: choose a finite presentation of `S` as a quotient of a polynomial ring over `R`
-- and first treat that polynomial case by replacing `M` with a finitely presented approximation
-- having the same generic fiber. Apply Lemma `10.118.2` to obtain a nonzero `f` making that
-- approximation free over `R_f`; then identify it with `M_f`. Finite presentation of `S_f` and
-- `M_f` follows from finite type after localizing away the same `f`.
/-- Lemma 10.118.3: if `R` is a domain, `R → S` is of finite type, and `M` is a finite `S`-module,
then there exists a nonzero `f ∈ R` such that `S_f` and `M_f` are free as `R_f`-modules, `S_f` is
a finitely presented `R_f`-algebra, and `M_f` is a finitely presented `S_f`-module. -/
lemma exists_nonzero_localization_away_free_and_finitePresentation_of_finiteType :
    ∃ f : R, f ≠ 0 ∧ LocalizationCondition R S M f := sorry

end
