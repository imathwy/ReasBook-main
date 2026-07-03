import stacks_project.Chap14.Definition_14_18_1
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped Simplicial SimplexCategory.Truncated

universe u v

namespace CategoryTheory
namespace SimplicialObject.Truncated

open Splitting

section

variable {C : Type u} [Category.{v} C]
variable {n : ℕ} (X : SimplicialObject.Truncated C n) (s : Splitting X) (m : Fin (n + 1))

/- Domain-style sampling for 14.18.1.1:
- primary domain: truncated split simplicial objects and their canonical degreewise coproduct
  decompositions
- sampled owner API:
  `Splitting`,
  `cofan`,
  `isColimit`,
  `SimplicialObject.Splitting.cofan`
- best owner abstraction: the chapter owner `s : Splitting X`, with the degreewise coproduct
  decomposition exposed as the derived cofan `s.cofan`
- primitive data: the splitting fields `s.N`, `s.ι`, and `s.isColimit'`
- derived API: the evaluated cofan `s.cofan (op ⦋m⦌ₙ)` and its colimit witness
  `s.isColimit (op ⦋m⦌ₙ)`
- source/core/bridge triage: `SimplicialObject.Truncated.Splitting` is the source-facing owner in
  this chapter, and the displayed decomposition in a fixed degree is a `bridge/view`
  specialization, so the correct refinement is direct use of `s.cofan` and `s.isColimit` rather
  than a parallel local decomposition wrapper.
-/

/- 14.18.1.1: the degreewise coproduct decomposition attached to a truncated splitting is already
the canonical owner cofan `cofan`. -/
recall cofan

/- 14.18.1.1: this canonical cofan is colimiting by the owner witness
`isColimit`. -/
recall isColimit

/- Source-facing specialization: in degree `m`, the displayed coproduct decomposition is exactly
the cofan `s.cofan (op ⦋m⦌ₙ)`, and it is colimiting via `s.isColimit (op ⦋m⦌ₙ)`. -/
#check (s.cofan (op ⦋m⦌ₙ))
#check (s.isColimit (op ⦋m⦌ₙ))

end

end SimplicialObject.Truncated
end CategoryTheory
