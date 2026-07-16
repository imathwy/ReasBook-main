import StacksProject_2024.stacks_project.Chap28.Lemma_28_9_2
import StacksProject_2024.stacks_project.Chap28.Lemma_28_10_2
import StacksProject_2024.stacks_project.Chap28.Lemma_28_12_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Source/core/bridge triage:
-- * source-facing: `regular_of_isNormal_of_topologicalKrullDim_le_one`, the Stacks lemma that a
--   normal locally Noetherian scheme of dimension `≤ 1` is regular;
-- * core/canonical: the Chapter 28 scheme owner `Regular X`;
-- * bridge/view: the companion theorem below, which packages the source assumptions as the
--   stalkwise regular-local criterion used by `regular_iff_isLocallyNoetherian_and_forall_isRegularLocalRing_stalk`.

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- If `X` is locally Noetherian, normal, and has topological Krull dimension `≤ 1`, then every
stalk of `X` is a regular local ring. This is the canonical stalkwise bridge from the source
assumptions to the scheme-level regularity owner `Regular X`. -/
theorem forall_isRegularLocalRing_stalk_of_isNormal_of_topologicalKrullDim_le_one
    (hnormal : X.isNormal) (hdim : topologicalKrullDim X ≤ 1) :
    ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) := by
  have hR1 : satisfiesSerreConditionR X 1 :=
    (isNormal_iff_satisfiesSerreConditionR_one_and_stalkwise_serreConditionS_two X).1 hnormal |>.1
  rw [topologicalKrullDim_eq_iSup_ringKrullDim_stalk X] at hdim
  intro x
  exact hR1.isRegularLocalRing_stalk x
    ((le_iSup (fun y ↦ ringKrullDim (X.presheaf.stalk y)) x).trans hdim)

/-- Lemma 28.12.6: a locally Noetherian normal scheme `X` of dimension `≤ 1` is regular. The
dimension hypothesis is formalized as `topologicalKrullDim X ≤ 1`. -/
theorem regular_of_isNormal_of_topologicalKrullDim_le_one
    (hnormal : X.isNormal) (hdim : topologicalKrullDim X ≤ 1) :
    Regular X := by
  refine (regular_iff_isLocallyNoetherian_and_forall_isRegularLocalRing_stalk X).2 ?_
  exact ⟨inferInstance,
    forall_isRegularLocalRing_stalk_of_isNormal_of_topologicalKrullDim_le_one X hnormal hdim⟩

end AlgebraicGeometry.Scheme
