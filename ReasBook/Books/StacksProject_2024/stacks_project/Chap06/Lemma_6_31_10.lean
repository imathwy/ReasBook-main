import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap06.Lemma_6_31_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open TopologicalSpace.Opens

noncomputable section

universe u

/-
Domain-style sampling for Lemma 6.31.10:
- primary domain: extension by zero / by the initial object for sheaves on an open subset, and the
  resulting essential-image criterion in terms of stalks;
- sampled owner API:
  `openSubsetSheafExtensionByInitialObject`,
  `openSubsetSheafExtensionByInitialObject_fullyFaithful`,
  `openSubsetSheafExtensionByInitialObject_essImage_iff_isIso_initial_to_stalk_of_not_mem`;
- `source-facing`: the abelian reformulation saying the stalks vanish outside `U`;
- `core/canonical`: the extension-by-initial-object functor and its initial-map / initial-stalk
  essential-image criterion;
- `bridge/view`: the `AddCommGrpCat` specialization converting the owner’s initial-stalk criterion
  into zero stalks via `isIsoZero_iff_source_target_isZero`.

Primitive data are only the open subset `U`, the sheaf `𝒢`, and the canonical extension-by-zero
owner from the previous file. The zero-stalk formulation is derived API from that owner and should
reuse the chapter-local essential-image criterion instead of introducing a parallel local bridge.
-/

section

variable {X : TopCat.{u}}
variable (U : Opens X)

private theorem addCommGrpCat_isIso_zero_iff_isZero (A : AddCommGrpCat.{u}) :
    IsIso (0 : ⊥_ AddCommGrpCat.{u} ⟶ A) ↔ IsZero A := by
  rw [isIsoZero_iff_source_target_isZero]
  constructor
  · rintro ⟨_, hA⟩
    exact hA
  · intro hA
    exact ⟨initialIsInitial.isZero, hA⟩

/- Fully faithful abelian specialization of the extension-by-zero functor on an open subset.
This is exactly the canonical instance
`openSubsetSheafExtensionByInitialObject_fullyFaithful`. -/
recall openSubsetSheafExtensionByInitialObject_fullyFaithful

/-- Lemma 6.31.10: a sheaf of abelian groups on `X` lies in the essential image of
extension by zero from `U` if and only if its stalks vanish at every point of `X \ U`. -/
theorem openSubsetSheafExtensionByInitialObject_essImage_iff_stalk_isZero_of_not_mem
    (𝒢 : X.Sheaf AddCommGrpCat.{u}) :
    (j! U).essImage 𝒢 ↔
      ∀ x : X, x ∉ (U : Set X) →
        IsZero (𝒢.presheaf.stalk x) := by
  simpa [addCommGrpCat_isIso_zero_iff_isZero] using
    (openSubsetSheafExtensionByInitialObject_essImage_iff_isIso_initial_to_stalk_of_not_mem
      U 𝒢)

end
