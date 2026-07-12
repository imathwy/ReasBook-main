import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap14.Lemma_14_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialObject.Truncated
open scoped SimplexCategory.Truncated
open scoped Simplicial

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-
Domain-style sampling for Lemma 14.19.3:
- primary domain: limits of structured-arrow diagrams computing objectwise values over the
  truncated simplex inclusion;
- sampled owner API:
  `SimplexCategory.Truncated.matchingIndex`,
  `StructuredArrow.mkIdInitial`,
  `IsInitial.hasInitial`,
  `limitOfInitial`;
- best owner abstraction: `Limits.limitOfInitial`, after the local bridge
  `StructuredArrow.mkIdInitial.hasInitial` supplying the initial object of the indexing category;
- primitive data: the structured-arrow category
  `StructuredArrow (op ⦋n⦌) (SimplexCategory.Truncated.inclusion m).op`
  together with the distinguished object `op ⦋n,hn⦌ₘ` whose image under the inclusion is
  `op ⦋n⦌`;
- derived API: the canonical isomorphism identifying the limit of the diagram with its value at
  that initial object.

Source/core/bridge triage:
- `source-facing`: the degree-`n` limit computation for the opposite truncated over-category of
  `[n]`;
- `core/canonical`: `Limits.limitOfInitial`;
- `bridge/view`: the local `HasInitial` instance supplied by
  `StructuredArrow.mkIdInitial.hasInitial`, with no separate public specialization.
-/

section

variable {m n : ℕ} (hn : n ≤ m)

variable (U : SimplicialObject.Truncated C m)

/- The canonical initial object of the truncated over-category is the identity structured arrow on
`op ⦋n,hn⦌ₘ`. -/
recall StructuredArrow.mkIdInitial

/- The limit computation itself is the canonical owner theorem `Limits.limitOfInitial`. -/
recall limitOfInitial

/- Lemma 14.19.3: for an `m`-truncated simplicial object `U` and `n ≤ m`, the limit over the
opposite truncated over-category of `[n]` is canonically isomorphic to the degree-`n` object
`U _⦋n,hn⦌ₘ`. This is exactly the canonical owner `Limits.limitOfInitial`, with the only local
bridge being the chosen `HasInitial` structure on the indexing category coming from
`StructuredArrow.mkIdInitial.hasInitial`. -/
#check
  (by
    let Y := (SimplexCategory.Truncated.inclusion m).op.obj (op ⦋n,hn⦌ₘ)
    let F := StructuredArrow.proj (op ⦋n⦌) (SimplexCategory.Truncated.inclusion m).op ⋙ U
    letI : HasInitial (SimplexCategory.Truncated.matchingIndex m n) :=
      (StructuredArrow.mkIdInitial :
        IsInitial (StructuredArrow.mk (𝟙 Y) : SimplexCategory.Truncated.matchingIndex m n)).hasInitial
    simpa [F] using
      (limitOfInitial F :
        limit F ≅ F.obj (⊥_ (SimplexCategory.Truncated.matchingIndex m n))))

end

end CategoryTheory
