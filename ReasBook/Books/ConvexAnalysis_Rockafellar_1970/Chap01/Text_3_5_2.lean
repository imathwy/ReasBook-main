import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: Text 3.5.2 says that the direct sum of two convex sets is convex.
- `core/canonical`: by Text 3.5.1, the direct sum is exactly the Cartesian product `C ×ˢ D`,
  and the canonical closure theorem is `Convex.prod`.
- `bridge/view`: the set-product bridge (`Set.prod`, `Set.mem_prod`) is upstream in Text 3.5.1;
  this item should expose only the convexity owner theorem.
- Primitive data vs derived API: convexity of the factors is primitive; convexity of the direct
  sum/product is the derived owner-level conclusion.
- Domain-style sampling: this follows the chapter owner-first pattern (for example Text 3.6.4 and
  Theorem 3.5 as direct recalls of `Convex.inter` and `Convex.prod`).
- Layer target: `core/canonical`; keep this file as direct owner reuse with no duplicated bridge
  recalls.

Abstraction audit (canonicalize):
- Codomain/ambient layer more concrete than needed? `No`: `Convex.prod` is already at the generic
  semiring/module convexity layer.
- Scalar/ambient structure stronger than needed? `No`: this uses the owner assumptions of
  `Convex.prod`, not an `ℝ`-specific specialization.
- Owner tied to a concrete model? `No`: owner is intrinsic `Convex 𝕜` on `Set`.
- Ambient-vs-intrinsic topology mismatch? `Not applicable`: this item is convexity closure, not a
  topology statement.
- Owner name too concrete/long? `No`: `Convex.prod` is the short canonical owner theorem.
- Missing notation surface? `No`: the primary notation `C ×ˢ D` is already provided upstream in
  Text 3.5.1.
-/

/- Text 3.5.2: once Text 3.5.1 identifies direct sum with the set product `C ×ˢ D`, convexity is
exactly the canonical owner theorem `Convex.prod`. -/
recall Convex.prod
