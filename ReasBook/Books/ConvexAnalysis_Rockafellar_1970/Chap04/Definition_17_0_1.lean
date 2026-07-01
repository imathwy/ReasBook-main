import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_2_10

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: Definition 17.0.1 recalls the finite convex-combination notion used in Chapter
  4.
- `core/canonical`: the coefficient owner is `StdSimplex`; the represented point owner is the
  canonical object-prefix declaration `StdSimplex.convexCombination`, and its finite-support
  weighted-sum owner view is the dot-notation surface `w.sum`.
- `bridge/view`: for finite families `w : StdSimplex R ι` and `x : ι → E`, the represented point is
  `(w.map x).convexCombination`. The textbook weighted-sum display is the upstream
  owner-level bridge `StdSimplex.map_convexCombination_eq_sum`, stated on `w.sum` instead of the
  concrete coefficient field `w.weights`.
- Primitive data vs derived API: this file introduces no new primitive data. Nonnegativity and the
  total-mass condition belong to `StdSimplex`; the point and its weighted-sum display are derived
  API.
- Domain-style sampling: the relevant declarations are the earlier project recall
  `Items/Chap01/Definition_2_2_10.lean` together with mathlib's `StdSimplex`,
  `StdSimplex.convexCombination`, and the owner-side weighted-sum bridges
  `StdSimplex.convexCombination_eq_sum` and `StdSimplex.map_convexCombination_eq_sum`.
- Layer target: `core/canonical` recall, with no parallel Chapter 4 wrapper.

Abstraction checks for this item:
- Codomain/ambient concreteness: not applicable. This item is point-valued and introduces no
  ordered-extended codomain owner.
- Scalar/ambient structure: no concrete scalar model is fixed here; all recalled owners remain
  parametric in `R`, index type, and ambient point type.
- Owner choice: keep `StdSimplex` as the primitive coefficient owner; treat weighted-sum formulas
  as bridge views via owner-side theorems.
- Topology language: not applicable; no ambient/intrinsic closure or interior owner appears.
- Owner naming/notation: keep short canonical owners and object-prefix surface
  (`w.sum`, `(w.map x).convexCombination`) rather than concrete coordinate wrappers.
-/

/- Definition 17.0.1 reuses the earlier project recall of the canonical coefficient owner
`StdSimplex`. -/
recall StdSimplex

/- Finite families enter the owner layer via `StdSimplex.map`. -/
recall StdSimplex.map

/- Primitive canonical point owner for simplex coefficients. -/
recall ConvexSpace.convexCombination

/- The represented point owner is the canonical object-prefix declaration
`StdSimplex.convexCombination`. -/
recall StdSimplex.convexCombination

/- Primitive weighted-sum bridge for simplex convex combinations. -/
recall convexCombination_eq_sum

/- The canonical weighted-sum view of simplex convex combinations is the owner-side bridge theorem
`StdSimplex.convexCombination_eq_sum`. -/
recall StdSimplex.convexCombination_eq_sum

/- The textbook weighted-sum presentation is the canonical owner-side bridge theorem, with no
Chapter-4-specific wrapper. -/
recall StdSimplex.map_convexCombination_eq_sum
