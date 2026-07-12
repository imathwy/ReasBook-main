import Mathlib.CategoryTheory.Abelian.FreydMitchell
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Abelian

/- Domain-style sampling for Remark 19.9.3:
- primary domain: Freyd-Mitchell embeddings of abelian categories into module categories;
- sampled owner declarations:
  `CategoryTheory.Abelian.freyd_mitchell`,
  `CategoryTheory.Abelian.FreydMitchell.functor`,
  `ExactStructure.sheafYoneda (abelianExactStructure A)` from Lemma 19.9.2 as the chapter-local
  sheaf-theoretic embedding;
- best owner abstraction: the canonical mathlib theorem
  `CategoryTheory.Abelian.freyd_mitchell`;
- primitive data: an abelian category;
- derived API: the existence of a ring and a fully faithful functor to a module category preserving
  finite limits and finite colimits, together with the packaged witness
  `CategoryTheory.Abelian.FreydMitchell.functor`.

Source/core/bridge triage:
- `source-facing`: the textbook Freyd-Mitchell embedding theorem;
- `core/canonical`: `CategoryTheory.Abelian.freyd_mitchell`;
- `bridge/view`: `CategoryTheory.Abelian.FreydMitchell.functor` and the sheaf-theoretic embedding
  of Lemma 19.9.2.

This item is therefore a pure canonical recall, not a place for a parallel local embedding
statement. -/
/- Remark 19.9.3: the Freyd-Mitchell embedding theorem is the canonical mathlib theorem
`CategoryTheory.Abelian.freyd_mitchell`, asserting that every abelian category admits a fully
faithful exact functor to a category of modules over a ring. This is stronger than
Lemma `19.9.2`, but the sheaf-theoretic embedding from that lemma is the one used in the Stacks
Project for diagram chasing in abelian sheaf categories. -/
recall freyd_mitchell
