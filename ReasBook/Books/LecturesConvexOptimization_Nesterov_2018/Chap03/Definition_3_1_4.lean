import Mathlib.Tactic.Recall
import Nesterov.Chap03.Definition_3_1_4_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 3.1.4 is a source-facing recall in the chapter's affine-hyperplane domain.

Primary domain:
- affine hyperplanes, supporting hyperplanes, and separation of a point from a set in a real
  inner-product space. Specializing `E = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ`
  setting.

Sampled owner-style declarations:
- `AffineHyperplane` in `Definition_3_1_4_1`, the owner of a nonzero normal vector and an offset;
- `AffineHyperplane.IsSupporting`, the owner-level support predicate;
- `hyperplane`, the coordinate carrier view of an affine hyperplane;
- `StrictlySeparatesPointFromWith`, the coordinate strict point-versus-set bridge;
- mathlib `Set.IsExposed`, a nearby exposed-face owner that is stronger than this source-facing
  point-versus-set hyperplane recall.

Best owner abstraction:
- `AffineHyperplane`

Source/core/bridge triage:
- source-facing: the textbook hyperplane, supporting-hyperplane, and point-versus-set separation
  notions;
- core/canonical: `AffineHyperplane`, whose primitive data are a nonzero normal vector and an
  offset;
- bridge/view: the coordinate carrier `hyperplane g γ`, together with
  `IsSupportingHyperplane`, `SeparatesPointFromWith`, and
  `StrictlySeparatesPointFromWith`.

Primitive data:
- the nonzero normal vector and offset packaged by `AffineHyperplane`.

Derived API:
- the owner-level support and point-separation predicates on `AffineHyperplane`;
- the coordinate bridge declarations `hyperplane`, `IsSupportingHyperplane`,
  `SeparatesPointFromWith`, and `StrictlySeparatesPointFromWith`.

The later two-set separation layer already has its own numbered recall in `Definition_3_12.lean`.
This file therefore recalls only the source-facing owner and bridge declarations for
Definition 3.1.4 instead of keeping a broader inventory that duplicated later chapter material.
-/

recall AffineHyperplane
recall AffineHyperplane.IsSupporting
recall AffineHyperplane.SeparatesPointFrom
recall AffineHyperplane.StrictlySeparatesPointFrom
recall hyperplane
recall IsSupportingHyperplane
recall SeparatesPointFromWith
recall StrictlySeparatesPointFromWith
