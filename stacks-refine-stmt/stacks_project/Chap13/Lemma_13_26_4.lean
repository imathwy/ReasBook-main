import Mathlib
import stacks_project.Chap13.Lemma_13_26_3

noncomputable section

universe u v

namespace CategoryTheory

open FilteredObject.Hom
open scoped CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Lemma `13.26.4`.
- primary domain: strict monomorphisms of finite filtered objects and extension into filtered
  injectives;
- sampled owner declarations:
  `FilteredObject.Hom.Strict`,
  `IsFilteredInjective`,
  `Injective.factors`,
  `Injective.factorThru`,
  `Injective.comp_factorThru`;
- best owner abstraction: the chapter owner `IsFilteredInjective`, with the source-facing
  extension theorem modeled on the theorem-level owner `Injective.factors`; unlike ordinary
  injective objects, no canonical filtered factorization morphism is available here, so the public
  API should stay existential rather than introducing a chosen witness;
- primitive data: a strict monomorphism `u : A ⟶ B` in `Fil^f(𝒜)`, a map `f : A ⟶ I`, and a
  filtered-injective target `I`;
- derived API: only the theorem-level factorization statement below;
- source/core/bridge triage:
  `source-facing`: extension of a morphism across a strict monomorphism in `Fil^f(𝒜)`;
  `core/canonical`: `Strict` and `IsFilteredInjective`;
  `bridge/view`: the theorem below, which is the filtered analogue of `Injective.factors`.
-/

namespace IsFilteredInjective

/-- Lemma 13.26.4: a morphism from the source of a strict monomorphism in `Fil^f(𝒜)` to a
filtered injective object factors through that strict monomorphism. -/
theorem factors
    {A B I : Fil^f(𝒜)} [IsFilteredInjective I] (f : A ⟶ I) (u : A ⟶ B) [Mono u]
    (hu : Strict u.hom) :
    ∃ g : B ⟶ I, u ≫ g = f := by
  sorry

end IsFilteredInjective

end CategoryTheory
