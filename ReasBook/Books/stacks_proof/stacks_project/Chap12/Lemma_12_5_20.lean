import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

/- Domain-style sampling for Lemma 12.5.20:
- primary domain: abelian-category diagram lemmas for morphisms between exact rows;
- inspected owner declarations:
  `Abelian.mono_of_epi_of_mono_of_mono`,
  `Abelian.epi_of_epi_of_epi_of_mono`,
  `Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`;
- best owner abstraction: the canonical mathlib five-lemma owner
  `Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`;
- primitive data: a morphism `φ : R₁ ⟶ R₂` of length-`5` composable-arrow diagrams together with
  exactness of the two rows and the endpoint epi/mono hypotheses;
- derived API: the conclusion that the middle vertical morphism is an isomorphism.

Source/core/bridge triage:
- `source-facing`: the Stacks five-lemma statement for a commutative diagram with exact rows in an
  abelian category;
- `core/canonical`: `Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`;
- `bridge/view`: none needed here, because the textbook statement already matches the owner theorem.

This item is recall-only: there is no local source-facing wrapper to preserve, and adding one would
only duplicate the upstream owner theorem. -/
/- Lemma 12.5.20: in a commutative diagram with exact rows in an abelian category, if the
second and fourth vertical morphisms are isomorphisms, the fifth vertical morphism is a
monomorphism, and the first vertical morphism is an epimorphism, then the middle vertical
morphism is an isomorphism. -/
recall Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono

end CategoryTheory
