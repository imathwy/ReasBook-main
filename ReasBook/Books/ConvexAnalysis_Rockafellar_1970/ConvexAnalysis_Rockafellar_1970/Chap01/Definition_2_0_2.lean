import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Convex

/- 
Source/core/bridge triage:
- `source-facing`: Definition 2.0.2 names the closed line segment between two points by the usual
  one-parameter convex-combination formula.
- `core/canonical`: mathlib's owner object for this notion is `segment`, written `[x -[𝕜] y]`.
- `bridge/view`: `segment_eq_image₂` is the primitive image bridge for `segment` at the
  ordered-semiring/`SMul` layer, while `segment_eq_image` is the standard source-facing
  one-parameter description at the ordered-ring affine-combination layer.
- Domain-style sampling used here: `segment`, `segment_eq_image₂`, `segment_eq_image`.
- Primitive data vs derived API: the closed segment itself is the owner-level notion; the explicit
  `λ`-parameter formula is derived API and should remain a bridge to `segment`, not a parallel local
  definition.
- Layer target: `core/canonical`, with the textbook formula retained only through the canonical
  bridge theorem.

Abstraction audit (canonicalize):
- Codomain/ambient layer over-concrete? `No`: the owner is the intrinsic set-level `segment`.
- Scalar/ambient structure stronger than needed? `No`: the primitive bridge is kept at the weaker
  ordered-semiring/`SMul` layer via `segment_eq_image₂`, while the textbook one-parameter formula
  is retained as derived API via `segment_eq_image`.
- Owner tied to a concrete model? `No`: no `ℝ^n`, `EuclideanSpace`, or coordinate model is fixed.
- Ambient-vs-intrinsic topology mismatch? `No`: this item is algebraic/affine, not an ambient
  topology reformulation.
- Owner name/notation too heavy or concrete? `No`: the canonical short owner notation
  `[x -[𝕜] y]` is used directly.
- Need extra local notation? `No`: existing canonical `segment` notation already matches the
  textbook surface.
-/

/- Definition 2.0.2: the closed line segment between two points is the canonical mathlib set
`segment 𝕜 x y` (notation `[x -[𝕜] y]`). -/
recall segment

/- Primitive bridge at the weakest canonical layer: `segment` is the image of two nonnegative
coefficients summing to `1`. -/
recall segment_eq_image₂

/- The textbook one-parameter formula for the closed line segment is the standard image
characterization of `segment` (without specializing the scalar in the public owner layer). -/
recall segment_eq_image
