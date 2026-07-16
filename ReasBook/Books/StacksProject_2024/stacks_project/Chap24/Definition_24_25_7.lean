import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap13.Definition_13_31_1

open CategoryTheory

-- Semantic search note: `lean_leansearch` was unavailable in this runner, so the owner/API choice
-- was checked against the chapter-local graded-injective owner `Definition_24_25_2` and the
-- canonical K-injective owner/vanishing criterion already publicized in
-- `Chap13/Definition_13_31_1.lean`.

namespace DifferentialGradedModule

/- Domain-style sampling for Definition 24.25.7:
- primary domain: K-injective differential graded `\mathcal A`-modules;
- sampled canonical declarations:
  `CochainComplex.IsKInjective`,
  `CochainComplex.isKInjective_iff_homotopyCategory_from_acyclic_eq_zero`;
- best owner abstraction: Chapter 24 presents differential graded `\mathcal A`-modules through
  the ambient cochain-complex owner, so K-injectivity should reuse the canonical owner
  `I.IsKInjective` directly;
- primitive data: only the differential graded module `I`, viewed as a cochain complex;
- source/core/bridge triage:
  `source-facing`: the textbook characterization of a K-injective differential graded module by
  vanishing of morphisms from acyclic modules in the homotopy category;
  `core/canonical`: `CochainComplex.IsKInjective`;
  `bridge/view`: the explicit homotopy-category vanishing criterion.
-/

/- Definition 24.25.7: a differential graded `\mathcal A`-module `\mathcal I` is K-injective
exactly when it is K-injective as a cochain complex, i.e. when every morphism from an acyclic
dg-module to `\mathcal I` is zero in `K(\mathrm{Mod}(\mathcal A, d))`. -/
recall CochainComplex.IsKInjective

section

universe u v

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable (I : CochainComplex 𝒜 ℤ)

/- Companion recall: the canonical Chapter 13 vanishing criterion says that `I.IsKInjective` is
equivalent to the statement that every morphism from an acyclic differential graded module to `I`
vanishes in the homotopy category. Since Chapter 24 reads differential graded `\mathcal A`-modules
through their ambient cochain-complex category, this remains a direct recall rather than a second
wrapper theorem. -/
#check (CochainComplex.isKInjective_iff_homotopyCategory_from_acyclic_eq_zero I)

end

end DifferentialGradedModule
