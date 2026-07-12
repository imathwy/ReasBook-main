import Mathlib.Data.Set.Prod
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: Text 3.5.1 introduces the direct sum of two convex sets as the set of ordered
  pairs with first coordinate in `C` and second coordinate in `D`.
- `core/canonical`: this is exactly the Cartesian product of sets, namely `Set.prod` with notation
  `×ˢ`.
- `bridge/view`: convexity of the product belongs to the later owner theorem `Convex.prod`, not to
  the present definition itself.
- Primitive data vs derived API: the sets `C` and `D` are primitive; the direct sum itself is the
  canonical set product, so this item contributes no extra wrapper data and no derived API beyond
  recalling that owner.
- Domain-style sampling: the relevant owner-side declarations are `Set.prod`,
  `Set.mem_prod`, `Convex.prod`, and the downstream chapter use in `Text_3_5_2`. These confirm
  that the correct public surface is the ambient set-product owner, not a parallel chapter-local
  `directSum` alias.
- Layer target: `core/canonical`; this numbered text is exact owner recall, so the main entry
  should remain a direct `recall` rather than a local compatibility definition.

Abstraction audit (canonicalize):
- Codomain/ambient layer more concrete than needed? `No`: this owner is codomain-free set
  structure (`Set.prod`) and already sits at the intrinsic set layer.
- Scalar/ambient structure stronger than needed? `No`: this item uses no scalar assumptions.
- Owner tied to a concrete model? `No`: the owner is intrinsic set product, not a coordinate model.
- Ambient-vs-intrinsic topology mismatch? `Not applicable`: this item is set construction, not a
  topological closure/interior statement.
- Owner name too concrete/long? `No`: `Set.prod` with notation `×ˢ` is short and canonical.
- Missing notation surface? `No`: the canonical notation `×ˢ` is already primary and is used
  directly in the source-facing comment.
-/

/- Text 3.5.1: the direct sum of sets `C` and `D` is canonically their Cartesian product
`C ×ˢ D` (`Set.prod`), with canonical pair constructor/eliminator
`Set.mk_mem_prod` and `Set.mem_prod`. -/
recall Set.prod
recall Set.mk_mem_prod
recall Set.mem_prod
