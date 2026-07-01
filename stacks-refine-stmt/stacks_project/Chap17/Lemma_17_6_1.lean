import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap06.Lemma_6_32_1
import stacks_project.Chap06.Lemma_6_32_3
import stacks_project.Chap17.Definition_17_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace

noncomputable section

universe u

section

variable {X : TopCat.{u}} {Z : Set X}

local notation "iZ" => X.closedSubsetInclusion Z

/- Definition 17.5.1 provides the canonical support owner for abelian sheaves. -/
recall abelianSheafSupport

/- A point lies in `abelianSheafSupport` exactly when the stalk at that point is nonzero. -/
recall mem_abelianSheafSupport_iff

-- Proof sketch: pushforward along the closed inclusion is both a right adjoint, via the canonical
-- pullback/pushforward adjunction, and a left adjoint, via the sections-with-support adjunction of
-- Lemma `17.6.3`. Hence it preserves finite limits and finite colimits, so it is exact.
/-- Lemma 17.6.1 (1): for the inclusion `i : Z → X` of a closed subset, the direct-image functor
`i_* : Ab(Z) ⥤ Ab(X)` on abelian sheaves is exact. -/
theorem closedSubsetAbelianSheafPushforward_exact
    (hZ : IsClosed Z)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}] :
    exactFunctor ((TopCat.of Z).Sheaf AddCommGrpCat.{u}) (X.Sheaf AddCommGrpCat.{u})
      (Sheaf.pushforward AddCommGrpCat.{u} iZ) := sorry

/- Lemma 17.6.1 (2): for the inclusion `i : Z → X` of a closed subset, the direct-image functor
`i_* : Ab(Z) ⥤ Ab(X)` is fully faithful. This is the `AddCommGrpCat` specialization of
`subsetSheafPushforward_fullyFaithful`. -/
recall subsetSheafPushforward_fullyFaithful

-- Proof sketch: by Lemma `closedSubsetAbelianSheafPushforward_essImage_iff_stalk_isZero_of_not_mem`,
-- an abelian sheaf lies in the essential image of `i_*` exactly when every stalk outside `Z` is
-- zero. Unfolding `abelianSheafSupport`, this is exactly the condition that the support be
-- contained in `Z`.
/-- Lemma 17.6.1 (3): the essential image of `i_* : Ab(Z) ⥤ Ab(X)` is exactly the abelian sheaves
whose support is contained in `Z`. -/
theorem closedSubsetAbelianSheafPushforward_essImage_iff_support_subset
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    (Sheaf.pushforward AddCommGrpCat.{u} iZ).essImage ℱ ↔
      abelianSheafSupport ℱ ⊆ Z := by
  rw [closedSubsetAbelianSheafPushforward_essImage_iff_stalk_isZero_of_not_mem hZ ℱ]
  constructor
  · intro h x hx
    by_contra hx'
    exact hx <| by simpa [mem_abelianSheafSupport_iff] using h x hx'
  · intro h x hx
    by_contra hx'
    exact hx <| h <| by simpa [mem_abelianSheafSupport_iff] using hx'

/- Lemma 17.6.1 (4): for the inclusion `i : Z → X`, the inverse-image functor `i⁻¹` is a left
inverse to `i_*`, equivalently the counit `i⁻¹ i_* ℱ ⟶ ℱ` is an isomorphism for every abelian
sheaf `ℱ` on `Z`. This is the `AddCommGrpCat` specialization of the subset-inclusion owner
theorem `subsetSheaf_pullback_pushforward_counit_isIso`. -/
recall subsetSheaf_pullback_pushforward_counit_isIso

end
