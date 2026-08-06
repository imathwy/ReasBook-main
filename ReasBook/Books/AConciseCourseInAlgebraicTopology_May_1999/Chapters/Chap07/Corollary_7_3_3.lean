import Mathlib.Tactic.Recall
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Lemma_7_3_2

open scoped ContinuousMap

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
variable [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y]

-- Semantic recall via `lean_leansearch` surfaced only abstract model-category path-object
-- factorization APIs; the verified local Chapter 7 owners for this corollary are
-- `MappingPathSpace`, `mappingPathSpaceInclusion`, `mappingPathSpaceProjection`, and
-- `IsFibration`.

/- Corollary 7.3.3 (1): the homotopy-equivalence part of the mapping-path factorization is
already the canonical owner `mappingPathSpaceInclusion_homotopyEquiv f`. -/
example (f : C(X, Y)) : X ≃ₕ MappingPathSpace f :=
  mappingPathSpaceInclusion_homotopyEquiv f

/-- Composing the endpoint map with the forward map of
`mappingPathSpaceInclusion_homotopyEquiv f` recovers `f`. -/
@[simp] theorem mappingPathSpaceProjection_comp_mappingPathSpaceInclusion_homotopyEquiv_toFun
    (f : C(X, Y)) :
    (mappingPathSpaceProjection f).comp (mappingPathSpaceInclusion_homotopyEquiv f).toFun = f := by
  simpa using mappingPathSpaceProjection_comp_mappingPathSpaceInclusion f

/- Corollary 7.3.3 (2): the fibration part of the mapping-path factorization is the covering
homotopy property. The repository's stronger `IsFibration` wrapper additionally records
surjectivity, which is not part of May's assertion and need not hold for arbitrary `f`. -/
example (f : C(X, Y)) :
    HasCoveringHomotopyProperty.{max u v, v, max u v} (mappingPathSpaceProjection f) :=
  mappingPathSpaceProjection_hasCoveringHomotopyProperty f
