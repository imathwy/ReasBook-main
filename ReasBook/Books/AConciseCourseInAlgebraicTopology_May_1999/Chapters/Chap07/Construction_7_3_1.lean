import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_2_1

open scoped ContinuousMap unitInterval

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

-- Construction 7.3.1 specializes the source-facing owner `MappingPathSpace` from
-- Definition 7.2.1 to a continuous map `f : C(X, Y)`.

/-- Helper for Construction 7.3.1: the canonical map `x ↦ (x, const (f x))` lands continuously in
`MappingPathSpace f`. -/
lemma mappingPathSpaceInclusionContinuous (f : C(X, Y))
    [CompactlyGeneratedWeakHausdorffSpace.{u, u} X] :
    Continuous fun x : X ↦ MappingPathSpace.mk x (ContinuousMap.const I (f x)) rfl := by
  have hconst : Continuous fun y : Y ↦ ContinuousMap.const I y := by
    simpa using
      (ContinuousMap.continuous_const' : Continuous fun y : Y ↦ ContinuousMap.const I y)
  have hmem : ∀ x : X, ((x, ContinuousMap.const I (f x)) : X × C(I, Y)).2 0 = f x := by
    intro x
    rfl
  -- First build the ambient product map into `X × C(I, Y)`.
  -- The path coordinate is the continuous family of constant paths through `f x`.
  let _ : UCompactlyGeneratedSpace.{max u v} X :=
    uCompactlyGeneratedSpaceLift (X := X)
  exact MappingPathSpace.continuous_mk continuous_id (hconst.comp f.continuous) hmem

/-- Helper for Construction 7.3.1: forgetting the path coordinate is continuous on
`MappingPathSpace f`. -/
lemma mappingPathSpacePointProjectionContinuous (f : C(X, Y)) :
    Continuous fun xγ : MappingPathSpace f ↦ xγ.point := by
  -- This is the first projection of the ambient product, restricted to the subtype.
  simpa [MappingPathSpace.point] using
    (continuous_fst.comp (MappingPathSpace.continuous_subtypeVal (p := f)) :
      Continuous fun xγ : MappingPathSpace f ↦ (xγ : X × C(I, Y)).1)

/-- Helper for Construction 7.3.1: evaluating the path coordinate at `1` is continuous on
`MappingPathSpace f`. -/
lemma mappingPathSpaceEndpointContinuous (f : C(X, Y)) :
    Continuous fun xγ : MappingPathSpace f ↦ xγ.path 1 := by
  -- First project to the path coordinate, then evaluate the resulting path at the endpoint.
  simpa [MappingPathSpace.path] using
    ((continuous_eval_const (1 : I)).comp
      (continuous_snd.comp (MappingPathSpace.continuous_subtypeVal (p := f))) :
      Continuous fun xγ : MappingPathSpace f ↦ (xγ : X × C(I, Y)).2 1)

/-- The canonical map `X → MappingPathSpace f` sending `x` to the constant path at `f x`. -/
def mappingPathSpaceInclusion (f : C(X, Y))
    [CompactlyGeneratedWeakHausdorffSpace.{u, u} X] : C(X, MappingPathSpace f) where
  toFun x := MappingPathSpace.mk x (ContinuousMap.const I (f x)) rfl
  continuous_toFun := mappingPathSpaceInclusionContinuous f

/-- The point projection `MappingPathSpace f → X` forgetting the path coordinate. -/
def mappingPathSpacePointProjection (f : C(X, Y)) : C(MappingPathSpace f, X) where
  toFun xγ := xγ.point
  continuous_toFun := mappingPathSpacePointProjectionContinuous f

/-- Evaluating `mappingPathSpacePointProjection f` returns the `X`-coordinate. -/
@[simp] theorem mappingPathSpacePointProjection_apply (f : C(X, Y)) (xγ : MappingPathSpace f) :
    mappingPathSpacePointProjection f xγ = xγ.point :=
  rfl

/-- The endpoint map `MappingPathSpace f → Y` sending `(x, γ)` to `γ 1`. -/
def mappingPathSpaceProjection (f : C(X, Y)) : C(MappingPathSpace f, Y) where
  toFun xγ := xγ.path 1
  continuous_toFun := mappingPathSpaceEndpointContinuous f

/-- Evaluating `mappingPathSpaceProjection f` returns the endpoint `γ 1`. -/
@[simp] theorem mappingPathSpaceProjection_apply (f : C(X, Y)) (xγ : MappingPathSpace f) :
    mappingPathSpaceProjection f xγ = xγ.path 1 :=
  rfl

/-- Forgetting the path coordinate after the canonical inclusion recovers the original point. -/
@[simp] theorem mappingPathSpacePointProjection_comp_mappingPathSpaceInclusion (f : C(X, Y))
    [CompactlyGeneratedWeakHausdorffSpace.{u, u} X] :
    (mappingPathSpacePointProjection f).comp (mappingPathSpaceInclusion f) = ContinuousMap.id X := by
  apply ContinuousMap.ext
  intro x
  rfl

/-- Construction 7.3.1: for any map `f : C(X, Y)`, the mapping path space `MappingPathSpace f`
gives a factorization `X ⟶ MappingPathSpace f ⟶ Y`, realized by the canonical inclusion followed
by the endpoint projection. -/
theorem mappingPathSpaceProjection_comp_mappingPathSpaceInclusion (f : C(X, Y))
    [CompactlyGeneratedWeakHausdorffSpace.{u, u} X] :
    (mappingPathSpaceProjection f).comp (mappingPathSpaceInclusion f) = f := by
  apply ContinuousMap.ext
  intro x
  rfl
