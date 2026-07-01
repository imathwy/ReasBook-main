import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_5

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.30.6 introduces the terminology that a vector `x*` is a
  subgradient of a concave function `g` at `x` when it satisfies the global affine-support
  inequality.
- `core/canonical`: the chapter owner for this notion is the pairing-level set
  `_root_.concaveSubdifferentialAt`, with primitive pairing membership criterion
  `_root_.mem_concaveSubdifferentialAt_pairing`.
- `bridge/view`: the Euclidean vector statement is the Fréchet-Riesz specialization
  `Function.mem_concaveSubdifferentialAt`.

Domain-style sampling:
- `_root_.concaveSubdifferentialAt`,
  `_root_.mem_concaveSubdifferentialAt_pairing`,
  `_root_.mem_concaveSubdifferentialAt` from `Chap06.Definition_6_30_5`;
- `Function.concaveSubdifferentialAt` and `Function.mem_concaveSubdifferentialAt`, the Euclidean
  bridge specializations from the same file.

Primitive data vs derived API:
- primitive owner data already exist upstream as `_root_.concaveSubdifferentialAt g x`;
- derived source-facing `StrongDual` and Euclidean APIs are obtained by specialization.

Abstraction audit for this file:
- codomain/scalar/model-owner specialization (`EReal`, `ℝ`, default `StrongDual`) is inherited from
  the upstream owner in `Definition_6_30_5` and its Chapter 23 root owner
  `_root_.subdifferentialAt`; this file is not the first owner source for those parameters.
- therefore this item keeps a pure recall surface and exposes the pairing theorem first.
- any migration toward a more general codomain/scalar/pairing layer must start upstream from those
  owner declarations, then propagate to this recall-only file.

Layer target: `source-facing` recall of the intrinsic pairing membership theorem, followed by the
`StrongDual` and Euclidean bridge recalls. Introducing a new `IsSubgradientAt` alias here would
duplicate canonical owners without adding new mathematics.
-/

/- Definition 6.30.6, intrinsic owner form: for any pairing codomain, a functional is a subgradient
at `x` exactly when it belongs to the concave subdifferential at `x`, equivalently when it
satisfies the global affine-support inequality. -/
recall mem_concaveSubdifferentialAt_pairing

/- Definition 6.30.6, default dual-model bridge: the same criterion specialized to the chapter's
canonical default model `StrongDual ℝ E`. -/
recall mem_concaveSubdifferentialAt

namespace Function

/- Definition 6.30.6, Euclidean bridge form: in `ℝ^n`-style inner-product form, vectors satisfy
the same subgradient criterion via Fréchet-Riesz identification with the dual. -/
recall mem_concaveSubdifferentialAt

end Function
