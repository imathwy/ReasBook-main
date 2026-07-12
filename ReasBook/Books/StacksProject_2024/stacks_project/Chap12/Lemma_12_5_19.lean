import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

/- Domain-style sampling for Lemma 12.5.19:
- primary domain: the four lemma in an abelian category, expressed for a morphism of exact
  four-term diagrams, i.e. a morphism `φ : R₁ ⟶ R₂` in `ComposableArrows C 3`;
- sampled owner declarations:
  `Abelian.mono_of_epi_of_mono_of_mono`,
  `Abelian.epi_of_epi_of_epi_of_mono`,
  `Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`,
  `ComposableArrows.Exact`;
- best owner abstraction:
  `source-facing`: the mono and epi forms of the four lemma stated in the source;
  `core/canonical`: the owner theorems
    `Abelian.mono_of_epi_of_mono_of_mono` and `Abelian.epi_of_epi_of_epi_of_mono` for exact
    morphisms of `ComposableArrows C 3`;
  `bridge/view`: none is needed here, because the source statements already coincide with the
    upstream owner-level theorems;
- primitive data vs derived API: the primitive data are the morphism of four-term diagrams and the
  exactness of the two rows, encoded by `φ : R₁ ⟶ R₂` with `R₁.Exact` and `R₂.Exact`; the mono and
  epi conclusions are derived API owned upstream, so any local restatement would only duplicate
  the canonical chapter/mathlib interface.

This file should stay recall-only: the source mathematics is already represented by the correct
owner abstraction, so the refined public surface is direct canonical recall rather than a local
wrapper or compatibility theorem.
-/

/- Lemma 12.5.19 (1): for a commutative diagram of four-term complexes with exact rows in an
abelian category, if the first and third vertical maps are epimorphisms and the fourth vertical
map is a monomorphism, then the second vertical map is an epimorphism. -/
recall Abelian.epi_of_epi_of_epi_of_mono

/- Lemma 12.5.19 (2): for a commutative diagram of four-term complexes with exact rows in an
abelian category, if the first vertical map is an epimorphism and the second and fourth vertical
maps are monomorphisms, then the third vertical map is a monomorphism. -/
recall Abelian.mono_of_epi_of_mono_of_mono

end CategoryTheory
