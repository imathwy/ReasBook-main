import Mathlib
import StacksProject_2024.Chap25.Remark_25_11_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace

universe u v

namespace SSet

-- Source/core/bridge triage:
-- `source-facing`: a Chapter 25 `SSet.OpenHypercovering` whose indexed opens all lie in a chosen
--   basis;
-- `core/canonical`: the basis/open-cover owners `TopologicalSpace.Opens.IsBasis` and
--   `TopologicalSpace.IsOpenCover`;
-- `bridge/view`: `OpenHypercovering.degreewiseOpensIn` and the degree-`0` companion API below.

namespace OpenHypercovering

section

variable {X : TopCat.{u}}

/-- An open hypercovering lies degreewise in `B` if every indexed open belongs to `B`. -/
def degreewiseOpensIn (H : OpenHypercovering X) (B : Set (Opens X)) : Prop :=
  ∀ ⦃Δ : SimplexCategoryᵒᵖ⦄ (i : H.I.obj Δ), H.family.openAt i ∈ B

/-- A hypercovering lies degreewise in `B` exactly when each simplicial degree family has all of
its indexed opens in `B`. -/
theorem degreewiseOpensIn_iff (H : OpenHypercovering X) (B : Set (Opens X)) :
    H.degreewiseOpensIn B ↔
      ∀ n : ℕ, ∀ i : H.I.obj (op <| SimplexCategory.mk n), H.family.openAt i ∈ B := sorry

/-- Unfolding `degreewiseOpensIn` says exactly that each indexed open of `H` belongs to `B`. -/
theorem degreewiseOpensIn_iff_forall_simplex (H : OpenHypercovering X) (B : Set (Opens X)) :
    H.degreewiseOpensIn B ↔
      ∀ ⦃Δ : SimplexCategoryᵒᵖ⦄ (i : H.I.obj Δ), H.family.openAt i ∈ B :=
  Iff.rfl

/-- Every indexed open of a hypercovering lying degreewise in `B` belongs to `B`. -/
theorem degreewiseOpensIn.openAt_mem
    {H : OpenHypercovering X} {B : Set (Opens X)}
    (hH : H.degreewiseOpensIn B) {Δ : SimplexCategoryᵒᵖ} (i : H.I.obj Δ) :
    H.family.openAt i ∈ B :=
  hH i

/-- Restricting to the nonempty simplices preserves the condition that all indexed opens lie in
`B`. -/
theorem degreewiseOpensIn.restrictToNonempty
    {H : OpenHypercovering X} {B : Set (Opens X)}
    (hH : H.degreewiseOpensIn B) :
    H.restrictToNonempty.degreewiseOpensIn B := by
  intro Δ i
  simpa using hH i.1

end

end OpenHypercovering

section

variable {X : TopCat.{u}}

/-- Lemma 25.11.3: every basis `B` of the topology of `X` admits a hypercovering of `X` whose
indexed opens all belong to `B`. -/
@[stacks 01H6]
theorem exists_openHypercovering_mem_basis
    (B : Set (Opens X)) (hB : Opens.IsBasis B) :
    ∃ H : OpenHypercovering.{u, v} X, H.degreewiseOpensIn B := sorry

end

end SSet
