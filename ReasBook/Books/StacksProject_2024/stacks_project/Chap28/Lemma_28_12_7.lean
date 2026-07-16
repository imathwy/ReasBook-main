import StacksProject_2024.stacks_project.Chap28.Lemma_28_10_2
import StacksProject_2024.stacks_project.Chap28.Lemma_28_12_3
import StacksProject_2024.stacks_project.Chap28.Lemma_28_12_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped ENat

universe u

namespace AlgebraicGeometry.Scheme

-- Source/core/bridge triage:
-- * source-facing: `cohenMacaulay_of_isNormal_and_topologicalKrullDim_le_two`, the Stacks
--   theorem that a normal locally Noetherian scheme of dimension `≤ 2` is Cohen-Macaulay;
-- * core/canonical: the Chapter 30 scheme owner `satisfiesSerreConditionS X k`;
-- * bridge/view: the companion theorem below, which packages the normality-plus-dimension
--   hypotheses as the full family of scheme-level Serre conditions needed by
--   `cohenMacaulay_iff_forall_satisfiesSerreConditionS`.

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- If `X` is locally Noetherian, normal, and has topological Krull dimension `≤ 2`, then `X`
satisfies Serre's condition `(S_k)` for every `k`. This is the canonical scheme-level bridge from
the source assumptions to the Chapter 28 Cohen-Macaulay owner. -/
theorem satisfiesSerreConditionS_of_isNormal_of_topologicalKrullDim_le_two
    (hnormal : X.isNormal) (hdim : topologicalKrullDim X ≤ 2) (k : ℕ) :
    satisfiesSerreConditionS X k := by
  rw [satisfiesSerreConditionS_iff]
  rw [topologicalKrullDim_eq_iSup_ringKrullDim_stalk X] at hdim
  have hS2 : satisfiesSerreConditionS X 2 :=
    satisfiesSerreConditionS_two_of_isNormal X hnormal
  intro x
  have hsupp :
      Module.supportDim (X.presheaf.stalk x) (X.presheaf.stalk x) ≤ (2 : WithBot ℕ∞) := by
    rw [Module.supportDim_self_eq_ringKrullDim]
    exact (le_iSup (fun y ↦ ringKrullDim (X.presheaf.stalk y)) x).trans hdim
  have hdepth :
      Module.supportDim (X.presheaf.stalk x) (X.presheaf.stalk x) ≤
        WithBot.some (moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x) : ℕ∞) := by
    simpa [min_eq_right hsupp] using ((satisfiesSerreConditionS_iff X 2).1 hS2 x)
  exact le_trans (min_le_right (k : WithBot ℕ∞) _) hdepth

/-- Lemma 28.12.7: let `X` be a locally Noetherian scheme which is normal and has dimension
`≤ 2`. Then `X` is Cohen-Macaulay. The dimension hypothesis is expressed by
`topologicalKrullDim X ≤ 2`. -/
@[stacks 0B3D]
theorem cohenMacaulay_of_isNormal_and_topologicalKrullDim_le_two
    (hnormal : X.isNormal) (hdim : topologicalKrullDim X ≤ 2) :
    X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A) := by
  refine (cohenMacaulay_iff_forall_satisfiesSerreConditionS X).2 ?_
  exact satisfiesSerreConditionS_of_isNormal_of_topologicalKrullDim_le_two X hnormal hdim

end AlgebraicGeometry.Scheme
