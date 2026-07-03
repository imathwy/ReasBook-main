import Mathlib.Tactic.Recall
import stacks_project.Chap12.Lemma_12_6_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext

universe w v u

namespace CategoryTheory.Abelian.Ext

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable (A B : C)

/- Domain-style sampling for Lemma 13.27.6:
- primary domain: degree-one `Ext` in an abelian category and its classification by extension
  classes;
- sampled owner declarations:
  `ExtensionClass`,
  `ExtensionClass.toExt`,
  `ExtensionClass.toExtAddEquiv`,
  `Ext B A 1`;
- best owner abstraction: the canonical owner is `Ext B A 1`, while the source-facing extension
  group is `ExtensionClass A B`; the correct bridge for this lemma is the additive equivalence
  `ExtensionClass.toExtAddEquiv`;
- primitive-vs-derived split:
  primitive data: the ambient abelian category with `HasExt` and the objects `A`, `B`;
  derived API: the additive identification of the Chapter 12 extension group with `Ext B A 1`.

Source/core/bridge triage:
- `source-facing`: `ExtensionClass A B`;
- `core/canonical`: `Ext B A 1`;
- `bridge/view`: `ExtensionClass.toExtAddEquiv`.

This file should therefore stay at the bridge layer: it recalls the canonical additive
identification between the source-facing extension group and the owner `Ext¹`, without introducing
any parallel local alias.
-/

/- Lemma 13.27.6: in an abelian category, the extension group constructed from short exact
sequences is canonically identified with `Ext^1_{\mathcal A}(B, A)` by
`ExtensionClass.toExtAddEquiv`. -/
recall ExtensionClass.toExtAddEquiv

end

end CategoryTheory.Abelian.Ext
