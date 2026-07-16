import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap06.Lemma_6_31_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open TopologicalSpace.Opens

noncomputable section

universe u

/-
Domain-style sampling for Lemma 6.31.9:
- primary domain: extension by the initial object along an open immersion, specialized to
  set-valued sheaves;
- sampled owner API:
  `OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction`,
  `OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalk_isInitial_of_not_mem`,
  `openSubsetSheafExtensionByInitialObject`,
  `openSubsetSheafExtensionByInitialObject_fullyFaithful`,
  `openSubsetSheafExtensionByInitialObject_essImage_iff_isIso_initial_to_stalk_of_not_mem`,
  `Types.initial_iff_empty`;
- `source-facing`: the set-valued reformulation saying that stalks outside `U` are empty;
- `core/canonical`: the chapter-local `OpenSubsetExtensionByInitial` owner together with the
  source-facing essential-image criterion in terms of the canonical map from the initial object to
  the stalk;
- `bridge/view`: the `Type` specialization converting that initial-map criterion into the
  emptiness of the stalk via `Types.initial_iff_empty`.

Primitive data are only the open subset `U`, the sheaf `𝒢`, and the canonical extension-by-zero
owner from the previous file. The empty-stalk formulation is derived API and should reuse the
existing chapter owner and the source-facing essential-image criterion together with the canonical
`Type`-level fact `Types.initial_iff_empty`, rather than introducing a parallel public wrapper.
-/

section

variable {X : TopCat.{u}}

private theorem type_isIso_initial_to_iff_isEmpty (A : Type u) :
    IsIso (initial.to A) ↔ IsEmpty A := by
  constructor
  · intro hA
    exact (Types.initial_iff_empty A).mp
      ⟨IsInitial.ofIso initialIsInitial (asIso (initial.to A))⟩
  · intro hA
    exact
      isIso_of_isInitial initialIsInitial ((Types.initial_iff_empty A).mpr hA).some
        (initial.to A)

/- The full-faithfulness clause is already available as the `Type`-valued specialization of the
canonical instance `openSubsetSheafExtensionByInitialObject_fullyFaithful`. -/
recall openSubsetSheafExtensionByInitialObject_fullyFaithful

-- Proof sketch: apply the canonical essential-image criterion for extension by the initial object
-- from Lemma 6.31.11, then identify `IsIso (initial.to A)` with `IsEmpty A` in `Type`.
/-- Lemma 6.31.9: a sheaf of sets on `X` lies in the essential image of extension by the empty set
from `U` if and only if all of its stalks outside `U` are empty. -/
theorem openSubsetSheafExtensionByInitialObject_essImage_iff_stalk_isEmpty_of_not_mem
    (U : Opens X) (𝒢 : X.Sheaf (Type u)) :
    (j! U).essImage 𝒢 ↔
      ∀ x : X, x ∉ (U : Set X) → IsEmpty (𝒢.presheaf.stalk x) := by
  simpa [type_isIso_initial_to_iff_isEmpty] using
    (openSubsetSheafExtensionByInitialObject_essImage_iff_isIso_initial_to_stalk_of_not_mem U 𝒢)

end
