import Mathlib.Tactic.Recall
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Lemma_6_3_2

open scoped ContinuousMap

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

-- Semantic recall via `lean_leansearch` surfaced only abstract model-category cofibration
-- factorizations, so this corollary uses the verified local Chapter 6 owners
-- `ContinuousMap.mappingCylinder`, `mappingCylinderIn`, `mappingCylinderProjection`,
-- `mappingCylinderTargetInclusion`, and `IsCofibration`.

/- Corollary 6.3.3 (2): the factorization identity is already the canonical theorem
`mappingCylinderFactorization f`. -/
recall mappingCylinderFactorization (f : C(X, Y)) :
    (mappingCylinderProjection f).comp (mappingCylinderIn f) = f

/-- Corollary 6.3.3 (3): up to homotopy, `f : C(X, Y)` is replaced by the cofibration
`mappingCylinderIn f` because the canonical projection `mappingCylinderProjection f` admits the
canonical homotopy inverse `ContinuousMap.mappingCylinderTargetInclusion f`. -/
theorem mappingCylinderFactorization_replacesByCofibration (f : C(X, Y)) :
    ContinuousMap.Homotopic
      ((mappingCylinderProjection f).comp (ContinuousMap.mappingCylinderTargetInclusion f))
      (ContinuousMap.id Y) ∧
    ContinuousMap.Homotopic
      ((ContinuousMap.mappingCylinderTargetInclusion f).comp (mappingCylinderProjection f))
      (ContinuousMap.id f.mappingCylinder) :=
  ⟨mappingCylinderProjection_comp_targetInclusion_homotopic_id f,
    mappingCylinderTargetInclusion_comp_projection_homotopic_id f⟩

/- Corollary 6.3.3 (3): the cofibration half of the replacement statement is exactly the
source-faithful top-slice factorization map from Lemma 6.3.2. -/
recall mappingCylinderFactorizationIn_isCofibration (f : C(X, Y)) :
    IsCofibration (mappingCylinderFactorizationIn f)
