import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap13.Lemma_13_26_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Definition 13.26.1:
- primary domain: filtered objects in an abelian category, specialized to the full subcategory of
  finite filtered objects;
- sampled owner declarations:
  `Injective`,
  `CochainComplex.IsKInjective`,
  `IsFilteredInjective`,
  `gr^{p}`,
  `finiteFilteredObjectCat`;
- owner abstraction: the source-facing owner is the class `IsFilteredInjective` on `Fil^f(𝒜)`,
  not a new wrapper on ambient filtered objects;
- source/core/bridge triage:
  `source-facing`: filtered injective objects of `Fil^f(𝒜)`;
  `core/canonical`: the existing chapter class owner `IsFilteredInjective`;
  `bridge/view`: the graded-piece characterization built into that owner.

This item is therefore a pure canonical-recall entry: the textbook definition already matches the
existing chapter owner exactly, so the file should recall that owner directly rather than
reintroducing a duplicate alias or `_iff` wrapper. -/

/- Definition 13.26.1: for an abelian category `𝒜`, an object `I` of `Fil^f(𝒜)` is filtered
injective when each graded piece `gr^p(I)` is an injective object of `𝒜`. The chapter owner is
the class `IsFilteredInjective`. -/
recall IsFilteredInjective

end CategoryTheory
