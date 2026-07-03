import Mathlib
import StacksProject_2024.Chap15.Lemma_15_90_13

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

section

variable {R : Type u} [CommRing R]
variable {S : Type u} [CommRing S] [Algebra R S]
variable {t : ℕ} (f : Fin t → R)

/- Domain-style sampling for 15.90.14:
- primary domain: formal glueing for module categories and categorical equivalences;
- sampled owner declarations:
  `Glue`,
  `formalGlueingCan`,
  `formalGlueingCanAdjunction`,
  `Functor.IsEquivalence`;
- best owner abstraction: the source-facing statement should be the equivalence witness for the
  canonical functor `formalGlueingCan S f`;
- primitive data: only the canonical functor `formalGlueingCan S f` and the hypotheses
  `[Module.Flat R S]` and `Ideal.span (Set.range f) = ⊤`;
- derived API: the typeclass instance below. Any inverse functor and unit/counit isomorphisms are
  already provided canonically by `Functor.inv` and `Functor.asEquivalence`, so they should not be
  re-exposed here as parallel local owners.

Source/core/bridge triage:
- `source-facing`: `formalGlueingCan_isEquivalence_of_flat_of_span_eq_top`;
- `core/canonical`: `Functor.IsEquivalence`;
- `bridge/view`: the instance `formalGlueingCan_isEquivalence`.
-/

-- Proof sketch: combine the right quasi-inverse from Lemma `15.90.12` with the module glueing
-- existence-and-uniqueness statement from Algebra, Lemma `10.24.5`. When `Ideal.span (Set.range f)
-- = ⊤`, every formal glueing datum comes from a unique `R`-module, giving essential surjectivity of
-- `Can`; together with the quasi-inverse statement of Lemma `15.90.12`, this yields an equivalence.
/-- Lemma 15.90.14: if `φ : R → S` is a flat ring map and the generators `f₁, \ldots, fₜ`
generate the unit ideal of `R`, then the canonical formal glueing functor
`Can : Mod_R ⥤ Glue(R → S, f₁, …, fₜ)` is an equivalence of categories, where
`Glue(R → S, f₁, …, fₜ)` is the genuine formal glueing category from Remark `15.90.10`. -/
theorem formalGlueingCan_isEquivalence_of_flat_of_span_eq_top [Module.Flat R S]
    (hspan : Ideal.span (Set.range f) = ⊤) :
    Functor.IsEquivalence (formalGlueingCan S f) := sorry

/-- The equivalence instance attached to formal glueing when the `fᵢ` generate the unit ideal. -/
noncomputable instance formalGlueingCan_isEquivalence [Module.Flat R S]
    (hspan : Ideal.span (Set.range f) = ⊤) :
    Functor.IsEquivalence (formalGlueingCan S f) :=
  formalGlueingCan_isEquivalence_of_flat_of_span_eq_top f hspan

end
