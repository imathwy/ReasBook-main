import Mathlib
import Mathlib.Tactic.Recall
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import stacks_project.Chap04.Lemma_4_18_2
import stacks_project.Chap14.Lemma_14_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Opposite
open SimplexCategory.Truncated
open scoped Simplicial
open scoped SimplexCategory.Truncated

universe v u

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Remark 14.19.11:
- primary domain: simplicial-object truncation/coskeleton adjunctions under weakened limit
  hypotheses;
- sampled owner declarations:
  `SimplexCategory.Truncated.initial_inclusion`,
  `Functor.final_op_of_initial`,
  `truncation`,
  `Truncated.cosk`,
  `coskAdj`;
- best owner abstraction: the source-facing remark about `cosk_k` for `k > 0` should be bridged to
  the owner-level Kan-extension instance making `Truncated.cosk k` and `coskAdj k` available under
  `[HasFiniteConnectedLimits C]`, with the connectedness of the matching-index categories supplied
  by the canonical owner `SimplexCategory.Truncated.initial_inclusion`;
- primitive data: the truncation level `k`, the positivity hypothesis `0 < k`, and the ambient
  category together with its relevant limit owner (`HasBinaryProducts` for `k = 0`,
  `HasFiniteConnectedLimits` for `k > 0`);
- derived API: the source-facing existence statement for `cosk₀`, and for `k > 0` the canonical
  owner declarations `Truncated.cosk k` and `coskAdj k`.

Source/core/bridge triage:
- `source-facing`: the source's two existence statements for `cosk₀` and `cosk_k`;
- `core/canonical`: `truncation`, `Truncated.cosk`, and `coskAdj`;
- `bridge/view`: Example 14.19.1 for `k = 0`, and the finite-connected-limit bridge below giving
  the right Kan extensions needed for `Truncated.cosk k` when `0 < k`, reusing the canonical
  matching-index owner `matchingIndex k n` from `Lemma_14_19_2` and the upstream initiality owner
  `SimplexCategory.Truncated.initial_inclusion`. -/

/-- If `k > 0` and `C` has finite connected limits, then the structured-arrow indexing categories
for the degreewise construction of `cosk_k` have limits. Hence the right Kan extensions defining
`Truncated.cosk k` exist under the weaker hypothesis `[HasFiniteConnectedLimits C]`. -/
instance simplexTruncatedInclusion_hasPointwiseRightKanExtension_of_finite_connected_limits
    (k : ℕ) (hk : 0 < k) [HasFiniteConnectedLimits C]
    (F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ C) :
    (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F := by
  intro Y
  cases Y with
  | op Y =>
      change HasLimit
        (StructuredArrow.proj (op Y) (SimplexCategory.Truncated.inclusion k).op ⋙ F)
      letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
      letI : FinCategory (matchingIndex k Y.len) := inferInstance
      letI : IsConnected (matchingIndex k Y.len) := inferInstance
      infer_instance

-- Proof sketch: Example 14.19.1 constructs `cosk₀` from the explicit self-product model
-- `X ↦ (n ↦ X^(n + 1))`. That source-facing construction is kept here as the `k = 0` companion.
/-- If `C` has binary products, then the `0`-truncation functor has a right adjoint, i.e. `cosk₀`
exists. -/
theorem truncation_zero_isLeftAdjoint_of_hasBinaryProducts [HasBinaryProducts C] :
    ((SimplicialObject.truncation 0 : SimplicialObject C ⥤ SimplicialObject.Truncated C 0)).IsLeftAdjoint := sorry

section Positive

variable (k : ℕ) (hk : 0 < k) [HasFiniteConnectedLimits C]

local instance :
    ∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ C,
      (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F :=
  fun F ↦ simplexTruncatedInclusion_hasPointwiseRightKanExtension_of_finite_connected_limits k hk F

/- For `k > 0`, the weaker finite-connected-limit hypothesis now makes the canonical owner
`Truncated.cosk k` available directly. -/
#check Truncated.cosk k

/- Remark 14.19.11 for `k > 0`: under `[HasFiniteConnectedLimits C]`, the canonical adjunction
`truncation k ⊣ Truncated.cosk k` is available directly. -/
#check (coskAdj k).isLeftAdjoint

end Positive

end CategoryTheory
