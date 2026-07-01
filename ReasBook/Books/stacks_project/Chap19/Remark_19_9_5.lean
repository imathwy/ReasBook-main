import Mathlib.CategoryTheory.Abelian.FreydMitchell
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Abelian

/- Domain-style sampling for Remark 19.9.5:
- primary domain: Freyd-Mitchell embeddings of abelian categories into module categories;
- sampled owner declarations:
  `CategoryTheory.Abelian.freyd_mitchell`,
  `CategoryTheory.Abelian.FreydMitchell.EmbeddingRing`,
  `CategoryTheory.Abelian.FreydMitchell.functor`;
- best owner abstraction: the theorem-level owner is
  `CategoryTheory.Abelian.freyd_mitchell`, while the construction named in this remark is the
  canonical packaged embedding functor `CategoryTheory.Abelian.FreydMitchell.functor`;
- primitive data: an abelian category;
- derived API: the embedding ring and the fully faithful exact functor to its module category.

Source/core/bridge triage:
- `source-facing`: the construction sketched in the remark;
- `core/canonical`: `CategoryTheory.Abelian.freyd_mitchell`;
- `bridge/view`: `CategoryTheory.Abelian.FreydMitchell.functor`.

This item is therefore a pure canonical recall of the packaged functor, not a place for a
parallel local embedding definition. -/
/- Remark 19.9.5: the construction sketched here is the canonical mathlib Freyd-Mitchell
embedding functor `CategoryTheory.Abelian.FreydMitchell.functor`, which packages the resulting
fully faithful exact embedding of an abelian category into a module category over the endomorphism
ring of a chosen projective generator in the auxiliary opposite Grothendieck category. -/
recall FreydMitchell.functor
