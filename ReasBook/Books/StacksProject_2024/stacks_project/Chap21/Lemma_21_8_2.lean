import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

/- Domain-style sampling for Lemma 21.8.2:
- primary domain: Grothendieck-topology sheaf conditions for abelian presheaves expressed through
  canonical multiequalizer comparison maps.
- inspected canonical declarations:
  `Presheaf.IsSheaf`,
  `GrothendieckTopology.Cover.toMultiequalizer`,
  `Presheaf.isSheaf_iff_multifork`,
  `Presheaf.isSheaf_iff_multiequalizer`;
- owner abstraction: `Presheaf.isSheaf_iff_multiequalizer`.
- primitive data: a cover `S : J.Cover X` and a presheaf `F : Cᵒᵖ ⥤ AddCommGrpCat`; the canonical
  map to the multiequalizer is derived from `S` as `S.toMultiequalizer F`.
- derived API: the equivalence between the sheaf predicate and the statement that each
  `S.toMultiequalizer F` is an isomorphism.

Source/core/bridge triage:
- `source-facing`: the Stacks criterion that for every covering sieve the canonical map
  `F(X) → Čech H⁰(𝒰, F)` is an isomorphism.
- `core/canonical`: the general theorem `Presheaf.isSheaf_iff_multiequalizer`.
- `bridge/view`: `GrothendieckTopology.Cover.toMultiequalizer`, which packages the source-facing
  comparison map into the canonical multiequalizer morphism.

This item is already a direct recall of the canonical owner theorem, so the refinement stays
recall-shaped rather than rebuilding a parallel local multiequalizer API. -/

/- Lemma 21.8.2: the canonical multiequalizer criterion for the sheaf condition. Specializing the
target category to `AddCommGrpCat` gives the Stacks statement for abelian presheaves: for every
covering sieve `S` of an object `X`, the canonical map from `F(X)` to the corresponding
multiequalizer, the library-facing form of `Čech H⁰(S, F)`, is an isomorphism. -/
recall Presheaf.isSheaf_iff_multiequalizer
