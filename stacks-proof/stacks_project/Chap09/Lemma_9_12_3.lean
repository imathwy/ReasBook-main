import Mathlib.FieldTheory.Separable
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 9.12.3:
- primary domain: separability of elements and field extensions in a tower of field extensions;
- sampled owner declarations:
  `IsSeparable`,
  `Algebra.IsSeparable`;
- sampled derived API:
  `IsSeparable.tower_top`,
  `Algebra.isSeparable_tower_top_of_isSeparable`;
- best owner abstraction: the pointwise owner is `IsSeparable`, and the extension-level owner is
  `Algebra.IsSeparable`; the source lemma's two parts are exactly the tower-stability theorems
  derived from these owners;
- primitive data: none locally, since both the elementwise and extensionwise notions already have
  canonical mathlib owners;
- derived API: the pointwise descent theorem `IsSeparable.tower_top` and its quantified
  extension-level companion `Algebra.isSeparable_tower_top_of_isSeparable`.

Source/core/bridge triage:
- `source-facing`: in a tower `F ⟶ E ⟶ K`, separability over `F` implies separability over `E`,
  first for elements and then for the whole extension;
- `core/canonical`: `IsSeparable` and `Algebra.IsSeparable`;
- `bridge/view`: `IsSeparable.tower_top` and `Algebra.isSeparable_tower_top_of_isSeparable`,
  which restate the source lemma directly on the canonical owners.

This file should therefore stay recall-only: any local theorem shell would duplicate upstream
owner-derived API without adding new mathematics or a better statement surface. -/

/- Lemma 9.12.3 (1): the source states this for a tower of algebraic field extensions `K/E/F`,
but the canonical theorem `IsSeparable.tower_top` proves the same conclusion in any tower of
fields: if `α : K` is separable over `F`, then it is separable over `E`. -/
recall IsSeparable.tower_top

/- Lemma 9.12.3 (2): the source likewise assumes a tower of algebraic field extensions, while the
canonical theorem `Algebra.isSeparable_tower_top_of_isSeparable` is stronger and shows directly
that if `K/F` is separable, then `K/E` is separable. -/
recall Algebra.isSeparable_tower_top_of_isSeparable
