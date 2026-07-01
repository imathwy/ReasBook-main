import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 23.0.5 introduces the terminology that a dual-side element
  `xStar` is a subgradient of an extended-valued function `f` at `x` when it satisfies the
  global supporting-affine inequality.
- `core/canonical`: the chapter owner for this notion is `_root_.subdifferentialAt`, written on
  the theorem surface as `∂[Y]f(x)`.
- `bridge/view`: the source inequality is already the exact membership criterion
  `_root_.mem_subdifferentialAt_pairing`.

Domain-style sampling:
- `_root_.subdifferentialAt` from `Definition_23_0_6`, the intrinsic pairing-valued owner;
- `_root_.mem_subdifferentialAt_pairing` from the same file, the intrinsic
  supporting-inequality characterization;
- `_root_.mem_subdifferentialAt` from the same file, the default-`StrongDual` specialization;
- `Function.mem_subdifferentialAt` from the same file, the Euclidean inner-product bridge view.

Primitive data vs derived API:
- primitive owner data already exist upstream as `_root_.subdifferentialAt f x Y`;
- derived source-facing API here is only the terminology that a subgradient at `x` is exactly
  membership in that owner set, equivalently the supporting-affine inequality.

Layer target: `source-facing` recall of the existing pairing-level membership theorem. Introducing
an `IsSubgradientAt` alias here would duplicate the canonical chapter owner without adding new
mathematics.
-/

/- Definition 23.0.5: for a pairing-based Chapter 23 subdifferential owner, an element `xStar`
is a subgradient of `f` at `x` exactly when it belongs to `∂[Y]f(x)`, equivalently when it
satisfies the global supporting-affine inequality. -/
recall _root_.mem_subdifferentialAt_pairing
