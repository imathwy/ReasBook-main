import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: Theorem 3.4 states two closure properties for convex subsets under a linear
  map `A : E →ₗ[𝕜] F`: the image `A '' C` of a convex set `C` is convex, and the inverse image
  `A ⁻¹' D` of a convex set `D` is convex.
- `core/canonical`: the owner abstraction is the predicate `Convex 𝕜 s` on sets; after the
  standard image/preimage bridge, the exact owner theorems are `Convex.linear_image` and
  `Convex.linear_preimage`.
- `bridge/view`: by Text 3.4.0, the textbook notations `AC` and `A⁻¹D` are exactly the standard
  set image `A '' C` and preimage `A ⁻¹' D`.
- Primitive data vs derived API: the linear map `A` and the sets `C` and `D` are primitive; the
  theorem records only the derived convexity of their image and inverse image.
- Scalar/ambient minimization check: keep the linear-map owner layer. Moving to affine maps would
  strengthen assumptions (`Ring`, `AddCommGroup`) and is not needed for this item's primitive
  data.
- Domain-style sampling: the four declarations checked first are the project bridge
  `Text_3_4_0` for `Set.image`/`Set.preimage`, the nearby project exact-recall pattern
  `Theorem_3_1` for `Convex.add`, and the mathlib owner theorems `Convex.linear_image` and
  `Convex.linear_preimage`. They show that this item has no extra source-facing data beyond the
  standard set image/preimage constructions and their derived convexity closures.
- Layer target: `core/canonical`; after the notation bridge of Text 3.4.0, each clause is exact
  owner-side reuse, so the main entries should remain direct `recall`s rather than local wrapper
  theorems.
-/

/- Canonicalization decision record (this pass):
- Codomain/ambient layer over-concrete? `No`: this item is codomain-generic and already stated at
  the canonical `Convex 𝕜` owner layer.
- Scalar/ambient structure stronger than needed? `No`: `Convex.linear_image` and
  `Convex.linear_preimage` already sit at the minimal ordered-semiring/module layer used by the
  chapter's convex APIs.
- Concrete-model owner instead of intrinsic owner? `No`: the owner is the intrinsic set predicate
  `Convex 𝕜`, not a model-specific wrapper.
- Ambient-vs-intrinsic topology mismatch? `Not applicable`: Theorem 3.4 is not a topology-facing
  closure/interior statement.
- Owner-name or notation mismatch? `No`: the canonical owners are short (`Convex.linear_image`,
  `Convex.linear_preimage`) and the theorem surface uses the textbook-primary set notation
  `A '' C`, `A ⁻¹' D`.
- Upstream over-specialization forcing downstream noise? `No`: there is no over-concrete upstream
  bridge to repair; direct owner recalls are already the correct public API surface for this item.
-/

/- Theorem 3.4 (1): for a linear map `A`, the image `A '' C` of a convex set `C` is convex; this
is the canonical theorem `Convex.linear_image`. -/
recall Convex.linear_image

/- Theorem 3.4 (2): for a linear map `A`, the inverse image `A ⁻¹' D` of a convex set `D` is
convex; this is the canonical theorem `Convex.linear_preimage`. -/
recall Convex.linear_preimage
