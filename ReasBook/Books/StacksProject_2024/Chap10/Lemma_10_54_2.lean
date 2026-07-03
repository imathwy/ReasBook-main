import StacksProject_2024.Chap10.Definition_10_54_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 10.54.2:
- primary domain: commutative-algebraic ring-hom properties recording essential finite type and
  essential finite presentation, together with their closure under composition.
- inspected canonical declarations:
  `RingHom.EssFiniteType.comp`,
  `RingHom.EssFiniteType.stableUnderComposition`,
  `RingHom.EssFinitePresentation.comp`,
  `RingHom.StableUnderComposition`;
- owner abstractions: `RingHom.EssFiniteType` in mathlib and the chapter owner
  `RingHom.EssFinitePresentation`.
- primitive data: ring homomorphisms `f : R →+* S` and `g : S →+* T` equipped with the owner
  predicates `f.EssFiniteType`, `g.EssFiniteType`, `f.EssFinitePresentation`, and
  `g.EssFinitePresentation`.
- derived API: the composite witnesses and the bundled meta-property
  `RingHom.StableUnderComposition`.

Source/core/bridge triage:
- `source-facing`: the Stacks clauses asserting that composition preserves the two finiteness
  properties.
- `core/canonical`: `RingHom.EssFiniteType.comp`, `RingHom.EssFinitePresentation.comp`, and the
  generic owner-level predicate `RingHom.StableUnderComposition`.
- `bridge/view`: the chapter-local essential finite presentation owner from
  `Definition_10_54_1`, whose composition theorem is already stated in the canonical
  `RingHom`-property namespace.

This item is already entirely owner-driven. The refinement therefore stays recall-shaped: there is
no additional source-facing mathematical content beyond the canonical composition theorems, so the
file should not introduce parallel local wrappers or restated `_iff` APIs. -/

/- Lemma 10.54.2 (1): the essentially finite type clause is exactly the canonical mathlib theorem
`RingHom.EssFiniteType.comp`. -/
recall RingHom.EssFiniteType.comp

/- Lemma 10.54.2 (2): essential finite presentation is preserved under composition. The chapter's
owner-namespace bridge theorem is `RingHom.EssFinitePresentation.comp`. -/
recall RingHom.EssFinitePresentation.comp

/- Companion recall: the corresponding meta-property witness is
`RingHom.EssFinitePresentation.stableUnderComposition`. -/
recall RingHom.EssFinitePresentation.stableUnderComposition
