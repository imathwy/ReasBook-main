import Mathlib.Topology.Homotopy.Lifting
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Theorem_3_8_10.ConnectedCovering
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_1_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Lemma_4_1_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Theorem_4_4_5.CoverGraph

open Topology
open scoped unitInterval

universe u v

variable {B₀ : Type u} {J : Type v}

-- Semantic recall: `IsCoveringMap.liftPath` indicates that the covering structure should be
-- recorded pointwise along lifted edges, not only on endpoint labels.
-- Semantic recall: `ConnectedCoveringSpace (graphRealization boundary)` is the chapter-local
-- owner for a connected covering, with covering-map and path-connected-total-space data obtained
-- from `X.obj.hom` and `ConnectedCoveringSpace.pathConnectedSpace X`.

namespace ConnectedCoveringSpace

/-- Helper for Theorem 4.4.5: once a quotient map identifies exactly the classes of a setoid, the
quotient is homeomorphic to the codomain. -/
private noncomputable def quotientHomeomorphOfRelIff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (q : C(X, Y)) (hq : Topology.IsQuotientMap q) (r : Setoid X)
    (hrel : ∀ x y : X, r x y ↔ q x = q y) :
    Quotient r ≃ₜ Y := by
  have hker : Setoid.ker q = r := by
    ext x y
    exact (hrel x y).symm
  exact hker ▸ Topology.IsQuotientMap.homeomorph hq

/-- Helper for Theorem 4.4.5: evaluating `quotientHomeomorphOfRelIff` on a representative returns
the original quotient map value. -/
private theorem quotientHomeomorphOfRelIff_apply_mk
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (q : C(X, Y)) (hq : Topology.IsQuotientMap q) (r : Setoid X)
    (hrel : ∀ x y : X, r x y ↔ q x = q y) (x : X) :
    quotientHomeomorphOfRelIff q hq r hrel (Quotient.mk'' x) = q x := by
  have hker : Setoid.ker q = r := by
    ext a b
    exact (hrel a b).symm
  subst hker
  rfl

/-- Helper for Theorem 4.4.5: the parametrization `t ↦ graphEdgePoint boundary j t` is a
continuous base-edge path. -/
theorem continuous_graphEdgePoint (boundary : J ↪ Fin 2 → B₀) (j : J) :
    Continuous (graphEdgePoint boundary j) := by
  -- The base edge is the quotient map applied to the continuous source inclusion
  -- `t ↦ Sum.inr (j, t)`.
  let _ : TopologicalSpace B₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  have hsource : Continuous (fun t : I ↦ (Sum.inr (j, t) : B₀ ⊕ (J × I))) := by
    continuity
  simpa [graphEdgePoint, graphRealizationPoint] using
    continuous_quotient_mk'.comp hsource

/-- Helper for Theorem 4.4.5: the canonical continuous map parametrizing the base edge indexed by
`j`. -/
def baseEdgePath (boundary : J ↪ Fin 2 → B₀) (j : J) : C(I, graphRealization boundary) :=
  ⟨graphEdgePoint boundary j, continuous_graphEdgePoint boundary j⟩

/-- Helper for Theorem 4.4.5: the initial segment of the base edge `j` ending at the parameter
`t`. -/
def baseEdgePrefixPath (boundary : J ↪ Fin 2 → B₀) (j : J) (t : I) :
    C(I, graphRealization boundary) :=
  ⟨fun s ↦ graphEdgePoint boundary j (s * t),
    (continuous_graphEdgePoint boundary j).comp <|
      Continuous.subtype_mk
        ((continuous_subtype_val.comp continuous_id).mul
          (continuous_subtype_val.comp continuous_const))
        (fun s ↦ unitInterval.mul_mem s.2 t.2)⟩

/-- Helper for Theorem 4.4.5: the reverse of the initial segment of the base edge `j` ending at
the parameter `t`. -/
def baseEdgeReversePrefixPath (boundary : J ↪ Fin 2 → B₀) (j : J) (t : I) :
    C(I, graphRealization boundary) :=
  ⟨fun s ↦ graphEdgePoint boundary j (unitInterval.symm s * t),
    (continuous_graphEdgePoint boundary j).comp <|
      Continuous.subtype_mk
        ((continuous_subtype_val.comp unitInterval.continuous_symm).mul
          (continuous_subtype_val.comp continuous_const))
        (fun s ↦ unitInterval.mul_mem
          (by
            change (1 - (s : ℝ)) ∈ Set.Icc (0 : ℝ) 1
            constructor
            · linarith [s.2.2]
            · linarith [s.2.1])
          t.2)⟩

/-- Helper for Theorem 4.4.5: the prefix path starts at the initial vertex of the base edge. -/
@[simp] theorem baseEdgePrefixPath_zero (boundary : J ↪ Fin 2 → B₀) (j : J) (t : I) :
    baseEdgePrefixPath boundary j t 0 =
      graphVertex boundary (boundary j 0) := by
  calc
    baseEdgePrefixPath boundary j t 0 = graphEdgePoint boundary j (0 * t) := rfl
    _ = graphEdgePoint boundary j 0 := by simp
    _ = graphVertex boundary (boundary j 0) :=
      (graphVertex_boundary_zero_eq_graphEdgePoint_zero boundary j).symm

/-- Helper for Theorem 4.4.5: the prefix path ends at the chosen base edge point. -/
@[simp] theorem baseEdgePrefixPath_one (boundary : J ↪ Fin 2 → B₀) (j : J) (t : I) :
    baseEdgePrefixPath boundary j t 1 =
      graphEdgePoint boundary j t := by
  simp [baseEdgePrefixPath]

/-- Helper for Theorem 4.4.5: the reverse prefix path starts at the chosen base edge point. -/
@[simp] theorem baseEdgeReversePrefixPath_zero (boundary : J ↪ Fin 2 → B₀) (j : J) (t : I) :
    baseEdgeReversePrefixPath boundary j t 0 =
      graphEdgePoint boundary j t := by
  simp [baseEdgeReversePrefixPath]

/-- Helper for Theorem 4.4.5: the reverse prefix path ends at the initial vertex of the base
edge. -/
@[simp] theorem baseEdgeReversePrefixPath_one (boundary : J ↪ Fin 2 → B₀) (j : J) (t : I) :
    baseEdgeReversePrefixPath boundary j t 1 =
      graphVertex boundary (boundary j 0) := by
  calc
    baseEdgeReversePrefixPath boundary j t 1 =
        graphEdgePoint boundary j (unitInterval.symm 1 * t) := rfl
    _ = graphEdgePoint boundary j 0 := by simp [unitInterval.symm]
    _ = graphVertex boundary (boundary j 0) :=
      (graphVertex_boundary_zero_eq_graphEdgePoint_zero boundary j).symm

/-- Helper for Theorem 4.4.5: the chosen initial lift point of a lifted edge index lies over the
source of the corresponding base-edge path. -/
theorem baseEdgePath_source_eq_coverGraphEdgeInitialVertex
    (boundary : J ↪ Fin 2 → B₀) (p : X → graphRealization boundary)
    (e : coverGraphEdgeIndex boundary p) :
    baseEdgePath boundary e.1 0 = p e.2.1 := by
  -- Identify the edge endpoint `0` with the initial graph vertex, then use the fiber condition
  -- built into the lifted edge index.
  calc
    baseEdgePath boundary e.1 0 = graphEdgePoint boundary e.1 0 := rfl
    _ = graphVertex boundary (boundary e.1 0) :=
      (graphVertex_boundary_zero_eq_graphEdgePoint_zero boundary e.1).symm
    _ = p e.2.1 := (coverGraphEdgeIndex_proj_eq_graphVertex boundary p e).symm

/-- Helper for Theorem 4.4.5: graph vertices remember their vertex labels. -/
theorem graphVertex_injective (boundary : J ↪ Fin 2 → B₀) :
    Function.Injective (graphVertex boundary) := by
  intro x y hxy
  -- Equality of quotient vertices transports the source-side vertex-fiber predicate.
  have hsetoid : graphRealizationSetoid boundary (Sum.inl x) (Sum.inl y) := by
    have hEq' :
        graphRealizationPoint boundary (Sum.inl x) =
          graphRealizationPoint boundary (Sum.inl y) := by
      simpa [graphVertex, graphRealizationPoint] using hxy
    exact Quotient.eq'.1 hEq'
  have hyx : y = x := by
    simpa [inVertexFiber] using
      (graphRealizationSetoid_inVertexFiber_iff boundary x hsetoid).1 (by simp [inVertexFiber])
  exact hyx.symm

/-- Helper for Theorem 4.4.5: the underlying map of a connected covering space is a covering map
in the usual mathlib sense. -/
theorem coveringMap_objHom (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary)) :
    IsCoveringMap X.obj.hom :=
  IsPathConnectedCoveringMap.isCoveringMap (ConnectedCoveringSpace.isPathConnectedCoveringMap X)

/-- Helper for Theorem 4.4.5: in the source-faithful topology on `graphRealization boundary`,
the parametrization `t ↦ graphEdgePoint boundary j t` is continuous. -/
theorem continuous_graphEdgePoint_sourceFaithful (boundary : J ↪ Fin 2 → B₀) (j : J) :
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    Continuous (graphEdgePoint boundary j) := by
  let _ : TopologicalSpace B₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  -- The source-faithful realization is still the quotient map applied to the continuous source
  -- inclusion `t ↦ Sum.inr (j, t)`.
  have hsource : Continuous (fun t : I ↦ (Sum.inr (j, t) : B₀ ⊕ (J × I))) := by
    continuity
  simpa [graphEdgePoint, graphRealizationPoint] using
    continuous_quotient_mk'.comp hsource

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the canonical continuous map
parametrizing the base edge indexed by `j`. -/
def baseEdgePathSourceFaithful (boundary : J ↪ Fin 2 → B₀) (j : J) :
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    C(I, graphRealization boundary) :=
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  ⟨graphEdgePoint boundary j, continuous_graphEdgePoint_sourceFaithful boundary j⟩

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the initial segment of the base edge
`j` ending at parameter `t`. -/
def baseEdgePrefixPathSourceFaithful (boundary : J ↪ Fin 2 → B₀) (j : J) (t : I) :
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    C(I, graphRealization boundary) :=
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  ⟨fun s ↦ graphEdgePoint boundary j (s * t),
    (continuous_graphEdgePoint_sourceFaithful boundary j).comp <|
      Continuous.subtype_mk
        ((continuous_subtype_val.comp continuous_id).mul
          (continuous_subtype_val.comp continuous_const))
        (fun s ↦ unitInterval.mul_mem s.2 t.2)⟩

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the reverse of the initial segment of
the base edge `j` ending at parameter `t`. -/
def baseEdgeReversePrefixPathSourceFaithful (boundary : J ↪ Fin 2 → B₀) (j : J) (t : I) :
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    C(I, graphRealization boundary) :=
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  ⟨fun s ↦ graphEdgePoint boundary j (unitInterval.symm s * t),
    (continuous_graphEdgePoint_sourceFaithful boundary j).comp <|
      Continuous.subtype_mk
        ((continuous_subtype_val.comp unitInterval.continuous_symm).mul
          (continuous_subtype_val.comp continuous_const))
        (fun s ↦ unitInterval.mul_mem
          (by
            change (1 - (s : ℝ)) ∈ Set.Icc (0 : ℝ) 1
            constructor
            · linarith [s.2.2]
            · linarith [s.2.1])
          t.2)⟩

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the prefix path starts at the initial
vertex of the base edge. -/
@[simp] theorem baseEdgePrefixPathSourceFaithful_zero
    (boundary : J ↪ Fin 2 → B₀) (j : J) (t : I) :
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    baseEdgePrefixPathSourceFaithful boundary j t 0 =
      graphVertex boundary (boundary j 0) := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  calc
    baseEdgePrefixPathSourceFaithful boundary j t 0 = graphEdgePoint boundary j (0 * t) := rfl
    _ = graphEdgePoint boundary j 0 := by simp
    _ = graphVertex boundary (boundary j 0) :=
      (graphVertex_boundary_zero_eq_graphEdgePoint_zero boundary j).symm

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the prefix path ends at the chosen
base edge point. -/
@[simp] theorem baseEdgePrefixPathSourceFaithful_one
    (boundary : J ↪ Fin 2 → B₀) (j : J) (t : I) :
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    baseEdgePrefixPathSourceFaithful boundary j t 1 =
      graphEdgePoint boundary j t := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  simp [baseEdgePrefixPathSourceFaithful]

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the reverse prefix path starts at the
chosen base edge point. -/
@[simp] theorem baseEdgeReversePrefixPathSourceFaithful_zero
    (boundary : J ↪ Fin 2 → B₀) (j : J) (t : I) :
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    baseEdgeReversePrefixPathSourceFaithful boundary j t 0 =
      graphEdgePoint boundary j t := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  simp [baseEdgeReversePrefixPathSourceFaithful]

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the reverse prefix path ends at the
initial vertex of the base edge. -/
@[simp] theorem baseEdgeReversePrefixPathSourceFaithful_one
    (boundary : J ↪ Fin 2 → B₀) (j : J) (t : I) :
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    baseEdgeReversePrefixPathSourceFaithful boundary j t 1 =
      graphVertex boundary (boundary j 0) := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  calc
    baseEdgeReversePrefixPathSourceFaithful boundary j t 1 =
        graphEdgePoint boundary j (unitInterval.symm 1 * t) := rfl
    _ = graphEdgePoint boundary j 0 := by simp [unitInterval.symm]
    _ = graphVertex boundary (boundary j 0) :=
      (graphVertex_boundary_zero_eq_graphEdgePoint_zero boundary j).symm

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the chosen initial lift point of a
lifted edge index lies over the source of the corresponding base-edge path. -/
theorem baseEdgePathSourceFaithful_source_eq_coverGraphEdgeInitialVertex
    (boundary : J ↪ Fin 2 → B₀) (p : X → graphRealization boundary)
    (e : coverGraphEdgeIndex boundary p) :
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    baseEdgePathSourceFaithful boundary e.1 0 = p e.2.1 := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  -- The endpoint computation is purely combinatorial, so the same vertex-identification argument
  -- works verbatim in the source-faithful owner.
  calc
    baseEdgePathSourceFaithful boundary e.1 0 = graphEdgePoint boundary e.1 0 := rfl
    _ = graphVertex boundary (boundary e.1 0) :=
      (graphVertex_boundary_zero_eq_graphEdgePoint_zero boundary e.1).symm
    _ = p e.2.1 := (coverGraphEdgeIndex_proj_eq_graphVertex boundary p e).symm

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the underlying map of a connected
covering space is again a covering map. -/
theorem coveringMap_objHom_sourceFaithful (boundary : J ↪ Fin 2 → B₀)
    [_hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary)) :
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    IsCoveringMap X.obj.hom := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  -- Once the source-faithful owner is fixed locally, the covering-map extraction is the same
  -- path-connected-covering-space API as before.
  exact IsPathConnectedCoveringMap.isCoveringMap
    (ConnectedCoveringSpace.isPathConnectedCoveringMap X)

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the canonical lifted path over a base
edge starts at the chosen fiber point of the lifted edge index. -/
noncomputable def liftedEdgePathSourceFaithful (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) :
    C(I, X.obj.left) :=
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  let cov : IsCoveringMap X.obj.hom := coveringMap_objHom_sourceFaithful boundary X
  cov.liftPath (baseEdgePathSourceFaithful boundary e.1) e.2.1
    (baseEdgePathSourceFaithful_source_eq_coverGraphEdgeInitialVertex boundary X.obj.hom e)

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the canonical lifted edge starts at
the chosen initial point. -/
@[simp] theorem liftedEdgePathSourceFaithful_zero (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) :
    liftedEdgePathSourceFaithful boundary X e 0 = e.2.1 := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  -- This is the defining initial-value property of `IsCoveringMap.liftPath`.
  simpa [liftedEdgePathSourceFaithful] using
    (coveringMap_objHom_sourceFaithful boundary X).liftPath_zero
      (baseEdgePathSourceFaithful boundary e.1) e.2.1
      (baseEdgePathSourceFaithful_source_eq_coverGraphEdgeInitialVertex
        boundary X.obj.hom e)

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the canonical lifted edge projects
pointwise to the original base edge. -/
theorem liftedEdgePathSourceFaithful_lifts (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) :
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    X.obj.hom ∘ liftedEdgePathSourceFaithful boundary X e =
      baseEdgePathSourceFaithful boundary e.1 := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  -- Path lifting is again characterized by the pointwise projection identity in the
  -- source-faithful owner.
  simpa [liftedEdgePathSourceFaithful] using
    (coveringMap_objHom_sourceFaithful boundary X).liftPath_lifts
      (baseEdgePathSourceFaithful boundary e.1) e.2.1
      (baseEdgePathSourceFaithful_source_eq_coverGraphEdgeInitialVertex
        boundary X.obj.hom e)

/-- Helper for Theorem 4.4.5: in the source-faithful owner, reparametrizing a lifted edge by the
prefix map still gives the canonical lift of the corresponding base-edge prefix path. -/
theorem liftedEdgePrefixPathSourceFaithful_eq_liftPath (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) (t : I) :
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    (coveringMap_objHom_sourceFaithful boundary X).liftPath
        (baseEdgePrefixPathSourceFaithful boundary e.1 t) e.2.1
        (by
          calc
            baseEdgePrefixPathSourceFaithful boundary e.1 t 0 =
                graphVertex boundary (boundary e.1 0) :=
              baseEdgePrefixPathSourceFaithful_zero boundary e.1 t
            _ = X.obj.hom e.2.1 :=
              (coverGraphEdgeIndex_proj_eq_graphVertex boundary X.obj.hom e).symm) =
      ⟨fun s ↦ liftedEdgePathSourceFaithful boundary X e (s * t),
        (liftedEdgePathSourceFaithful boundary X e).continuous.comp <|
          Continuous.subtype_mk
            ((continuous_subtype_val.comp continuous_id).mul
              (continuous_subtype_val.comp continuous_const))
            (fun s ↦ unitInterval.mul_mem s.2 t.2)⟩ := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  exact (((coveringMap_objHom_sourceFaithful boundary X).eq_liftPath_iff'
      (by
        calc
          baseEdgePrefixPathSourceFaithful boundary e.1 t 0 =
              graphVertex boundary (boundary e.1 0) :=
            baseEdgePrefixPathSourceFaithful_zero boundary e.1 t
          _ = X.obj.hom e.2.1 :=
            (coverGraphEdgeIndex_proj_eq_graphVertex boundary X.obj.hom e).symm)).2 <| by
      constructor
      · ext s
        calc
          X.obj.hom (liftedEdgePathSourceFaithful boundary X e (s * t)) =
              baseEdgePathSourceFaithful boundary e.1 (s * t) := by
                exact congrFun (liftedEdgePathSourceFaithful_lifts boundary X e) (s * t)
          _ = baseEdgePrefixPathSourceFaithful boundary e.1 t s := rfl
      · calc
          liftedEdgePathSourceFaithful boundary X e (0 * t) =
              liftedEdgePathSourceFaithful boundary X e 0 := by simp
          _ = e.2.1 := liftedEdgePathSourceFaithful_zero boundary X e).symm

/-- Helper for Theorem 4.4.5: the canonical lifted path over a base edge starts at the chosen
fiber point of the lifted edge index. -/
noncomputable def liftedEdgePath (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) : C(I, X.obj.left) :=
  let cov : IsCoveringMap X.obj.hom := coveringMap_objHom boundary X
  cov.liftPath (baseEdgePath boundary e.1) e.2.1
    (baseEdgePath_source_eq_coverGraphEdgeInitialVertex boundary X.obj.hom e)

/-- Helper for Theorem 4.4.5: the canonical lifted edge starts at the chosen initial point. -/
@[simp] theorem liftedEdgePath_zero (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) :
    liftedEdgePath boundary X e 0 = e.2.1 := by
  -- This is the defining initial-value property of `IsCoveringMap.liftPath`.
  simpa [liftedEdgePath] using
    (coveringMap_objHom boundary X).liftPath_zero
      (baseEdgePath boundary e.1) e.2.1
      (baseEdgePath_source_eq_coverGraphEdgeInitialVertex boundary X.obj.hom e)

/-- Helper for Theorem 4.4.5: the canonical lifted edge projects pointwise to the original base
edge. -/
theorem liftedEdgePath_lifts (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) :
    X.obj.hom ∘ liftedEdgePath boundary X e = baseEdgePath boundary e.1 := by
  -- Path lifting is characterized by the pointwise projection identity.
  simpa [liftedEdgePath] using
    (coveringMap_objHom boundary X).liftPath_lifts
      (baseEdgePath boundary e.1) e.2.1
      (baseEdgePath_source_eq_coverGraphEdgeInitialVertex boundary X.obj.hom e)

/-- Helper for Theorem 4.4.5: reparametrizing a lifted edge by the prefix map still gives the
canonical lift of the corresponding base-edge prefix path. -/
theorem liftedEdgePrefixPath_eq_liftPath (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) (t : I) :
    (coveringMap_objHom boundary X).liftPath (baseEdgePrefixPath boundary e.1 t) e.2.1
        (by
          calc
            baseEdgePrefixPath boundary e.1 t 0 =
                graphVertex boundary (boundary e.1 0) :=
              baseEdgePrefixPath_zero boundary e.1 t
            _ = X.obj.hom e.2.1 :=
              (coverGraphEdgeIndex_proj_eq_graphVertex boundary X.obj.hom e).symm) =
      ⟨fun s ↦ liftedEdgePath boundary X e (s * t),
        (liftedEdgePath boundary X e).continuous.comp <|
          Continuous.subtype_mk
            ((continuous_subtype_val.comp continuous_id).mul
              (continuous_subtype_val.comp continuous_const))
            (fun s ↦ unitInterval.mul_mem s.2 t.2)⟩ := by
  symm
  exact ((coveringMap_objHom boundary X).eq_liftPath_iff'
      (by
        calc
          baseEdgePrefixPath boundary e.1 t 0 =
              graphVertex boundary (boundary e.1 0) :=
            baseEdgePrefixPath_zero boundary e.1 t
          _ = X.obj.hom e.2.1 :=
            (coverGraphEdgeIndex_proj_eq_graphVertex boundary X.obj.hom e).symm)).2 <| by
    constructor
    · ext s
      calc
        X.obj.hom (liftedEdgePath boundary X e (s * t)) =
            baseEdgePath boundary e.1 (s * t) := by
              exact congrFun (liftedEdgePath_lifts boundary X e) (s * t)
        _ = baseEdgePrefixPath boundary e.1 t s := rfl
    · calc
        liftedEdgePath boundary X e (0 * t) = liftedEdgePath boundary X e 0 := by simp
        _ = e.2.1 := liftedEdgePath_zero boundary X e

/-- Helper for Theorem 4.4.5: a point lying over `graphEdgePoint boundary j t` determines the
unique lifted edge indexed by `j` that passes through that point at parameter `t`. -/
noncomputable def liftedEdgeIndexOfPoint (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary))
    (j : J) (t : I) (x : X.obj.left)
    (hx : X.obj.hom x = graphEdgePoint boundary j t) :
    coverGraphEdgeIndex boundary X.obj.hom := by
  let cov : IsCoveringMap X.obj.hom := coveringMap_objHom boundary X
  let reverseLift :=
    cov.liftPath (baseEdgeReversePrefixPath boundary j t) x
      (by
        calc
          baseEdgeReversePrefixPath boundary j t 0 = graphEdgePoint boundary j t :=
            baseEdgeReversePrefixPath_zero boundary j t
          _ = X.obj.hom x := hx.symm)
  refine ⟨j, ⟨reverseLift 1, ?_⟩⟩
  have hproj :
      X.obj.hom (reverseLift 1) = graphVertex boundary (boundary j 0) := by
    calc
      X.obj.hom (reverseLift 1) = baseEdgeReversePrefixPath boundary j t 1 := by
        exact congrFun
          (cov.liftPath_lifts (baseEdgeReversePrefixPath boundary j t) x
            (by
              calc
                baseEdgeReversePrefixPath boundary j t 0 = graphEdgePoint boundary j t :=
                  baseEdgeReversePrefixPath_zero boundary j t
                _ = X.obj.hom x := hx.symm))
          1
      _ = graphVertex boundary (boundary j 0) := baseEdgeReversePrefixPath_one boundary j t
  simpa [Set.mem_singleton_iff] using hproj

/-- Helper for Theorem 4.4.5: the lifted edge determined by a point over `graphEdgePoint boundary
j t` passes through that point at parameter `t`. -/
theorem liftedEdgeIndexOfPoint_spec (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary))
    (j : J) (t : I) (x : X.obj.left)
    (hx : X.obj.hom x = graphEdgePoint boundary j t) :
    liftedEdgePath boundary X (liftedEdgeIndexOfPoint boundary X j t x hx) t = x := by
  let cov : IsCoveringMap X.obj.hom := coveringMap_objHom boundary X
  let reverseLift :=
    cov.liftPath (baseEdgeReversePrefixPath boundary j t) x
      (by
        calc
          baseEdgeReversePrefixPath boundary j t 0 = graphEdgePoint boundary j t :=
            baseEdgeReversePrefixPath_zero boundary j t
          _ = X.obj.hom x := hx.symm)
  let e : coverGraphEdgeIndex boundary X.obj.hom := liftedEdgeIndexOfPoint boundary X j t x hx
  have he :
      e = ⟨j, ⟨reverseLift 1, by
        have hproj :
            X.obj.hom (reverseLift 1) = graphVertex boundary (boundary j 0) := by
          calc
            X.obj.hom (reverseLift 1) = baseEdgeReversePrefixPath boundary j t 1 := by
              exact congrFun
                (cov.liftPath_lifts (baseEdgeReversePrefixPath boundary j t) x
                  (by
                    calc
                      baseEdgeReversePrefixPath boundary j t 0 = graphEdgePoint boundary j t :=
                        baseEdgeReversePrefixPath_zero boundary j t
                      _ = X.obj.hom x := hx.symm))
                1
            _ = graphVertex boundary (boundary j 0) := baseEdgeReversePrefixPath_one boundary j t
        simpa [Set.mem_singleton_iff] using hproj⟩⟩ := rfl
  have hstart :
      baseEdgePrefixPath boundary j t 0 = X.obj.hom (reverseLift 1) := by
    calc
      baseEdgePrefixPath boundary j t 0 = graphVertex boundary (boundary j 0) :=
        baseEdgePrefixPath_zero boundary j t
      _ = X.obj.hom (reverseLift 1) := by
        symm
        calc
          X.obj.hom (reverseLift 1) = baseEdgeReversePrefixPath boundary j t 1 := by
            exact congrFun
              (cov.liftPath_lifts (baseEdgeReversePrefixPath boundary j t) x
                (by
                  calc
                    baseEdgeReversePrefixPath boundary j t 0 = graphEdgePoint boundary j t :=
                      baseEdgeReversePrefixPath_zero boundary j t
                    _ = X.obj.hom x := hx.symm))
              1
          _ = graphVertex boundary (boundary j 0) := baseEdgeReversePrefixPath_one boundary j t
  have hreverse :
      cov.liftPath (baseEdgePrefixPath boundary j t) (reverseLift 1) hstart =
        ⟨fun s ↦ reverseLift (unitInterval.symm s),
          reverseLift.continuous.comp unitInterval.continuous_symm⟩ := by
    symm
    exact (cov.eq_liftPath_iff' hstart).2 <| by
      constructor
      · ext s
        calc
          X.obj.hom (reverseLift (unitInterval.symm s)) =
              baseEdgeReversePrefixPath boundary j t (unitInterval.symm s) := by
                exact congrFun
                  (cov.liftPath_lifts (baseEdgeReversePrefixPath boundary j t) x
                    (by
                      calc
                        baseEdgeReversePrefixPath boundary j t 0 = graphEdgePoint boundary j t :=
                          baseEdgeReversePrefixPath_zero boundary j t
                        _ = X.obj.hom x := hx.symm))
                  (unitInterval.symm s)
          _ = baseEdgePrefixPath boundary j t s := by
                simp [baseEdgeReversePrefixPath, baseEdgePrefixPath]
      · change reverseLift (unitInterval.symm 0) = reverseLift 1
        simp [unitInterval.symm]
  have hprefix :=
    liftedEdgePrefixPath_eq_liftPath boundary X e t
  have hvalue :
      (⟨fun s ↦ reverseLift (unitInterval.symm s),
          reverseLift.continuous.comp unitInterval.continuous_symm⟩ : C(I, X.obj.left)) 1 = x := by
    simpa [reverseLift, unitInterval.symm] using
      (cov.liftPath_zero (baseEdgeReversePrefixPath boundary j t) x
        (by
          calc
            baseEdgeReversePrefixPath boundary j t 0 = graphEdgePoint boundary j t :=
              baseEdgeReversePrefixPath_zero boundary j t
            _ = X.obj.hom x := hx.symm))
  have hprefixEval :
      (⟨fun s ↦ liftedEdgePath boundary X e (s * t),
          (liftedEdgePath boundary X e).continuous.comp <|
            Continuous.subtype_mk
              ((continuous_subtype_val.comp continuous_id).mul
                (continuous_subtype_val.comp continuous_const))
              (fun s ↦ unitInterval.mul_mem s.2 t.2)⟩ : C(I, X.obj.left)) 1 =
        cov.liftPath (baseEdgePrefixPath boundary j t) (reverseLift 1) hstart 1 := by
    simpa [he] using congrArg (fun Γ : C(I, X.obj.left) ↦ Γ 1) hprefix.symm
  have hreverseEval :
      cov.liftPath (baseEdgePrefixPath boundary j t) (reverseLift 1) hstart 1 = x := by
    simpa using (congrArg (fun Γ : C(I, X.obj.left) ↦ Γ 1) hreverse).trans hvalue
  rw [he] at hprefix
  have hfirst :
      liftedEdgePath boundary X e t =
        (⟨fun s ↦ liftedEdgePath boundary X e (s * t),
          (liftedEdgePath boundary X e).continuous.comp <|
            Continuous.subtype_mk
              ((continuous_subtype_val.comp continuous_id).mul
                (continuous_subtype_val.comp continuous_const))
              (fun s ↦ unitInterval.mul_mem s.2 t.2)⟩ : C(I, X.obj.left)) 1 := by
    simp
  exact hfirst.trans (hprefixEval.trans hreverseEval)

/-- Helper for Theorem 4.4.5: reconstructing the lifted edge index from a point on a canonical
lifted edge recovers the original lifted edge index. -/
theorem liftedEdgeIndexOfPoint_eq (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) (t : I) :
    liftedEdgeIndexOfPoint boundary X e.1 t (liftedEdgePath boundary X e t)
      (congrFun (liftedEdgePath_lifts boundary X e) t) = e := by
  let cov : IsCoveringMap X.obj.hom := coveringMap_objHom boundary X
  let reverseLift :=
    cov.liftPath (baseEdgeReversePrefixPath boundary e.1 t) (liftedEdgePath boundary X e t)
      (by
        calc
          baseEdgeReversePrefixPath boundary e.1 t 0 = graphEdgePoint boundary e.1 t :=
            baseEdgeReversePrefixPath_zero boundary e.1 t
          _ = X.obj.hom (liftedEdgePath boundary X e t) := by
            symm
            exact congrFun (liftedEdgePath_lifts boundary X e) t)
  have hreverse :
      reverseLift =
        ⟨fun s ↦ liftedEdgePath boundary X e (unitInterval.symm s * t),
          (liftedEdgePath boundary X e).continuous.comp <|
            Continuous.subtype_mk
              ((continuous_subtype_val.comp unitInterval.continuous_symm).mul
                (continuous_subtype_val.comp continuous_const))
              (fun s ↦ unitInterval.mul_mem
                (by
                  change (1 - (s : ℝ)) ∈ Set.Icc (0 : ℝ) 1
                  constructor
                  · linarith [s.2.2]
                  · linarith [s.2.1])
                t.2)⟩ := by
    -- Compare the reverse-prefix lift with the canonical lifted edge after reversing the
    -- parameter, then invoke path-lift uniqueness.
    symm
    exact (cov.eq_liftPath_iff'
      (by
        calc
          baseEdgeReversePrefixPath boundary e.1 t 0 = graphEdgePoint boundary e.1 t :=
            baseEdgeReversePrefixPath_zero boundary e.1 t
          _ = X.obj.hom (liftedEdgePath boundary X e t) := by
            symm
            exact congrFun (liftedEdgePath_lifts boundary X e) t)).2 <| by
      constructor
      · ext s
        calc
          X.obj.hom (liftedEdgePath boundary X e (unitInterval.symm s * t)) =
              baseEdgePath boundary e.1 (unitInterval.symm s * t) := by
                exact congrFun (liftedEdgePath_lifts boundary X e) (unitInterval.symm s * t)
          _ = baseEdgeReversePrefixPath boundary e.1 t s := rfl
      · change liftedEdgePath boundary X e (unitInterval.symm 0 * t) =
          liftedEdgePath boundary X e t
        simp [unitInterval.symm]
  have hstart :
      reverseLift 1 = e.2.1 := by
    -- Evaluate the uniqueness comparison at `1`; the reversed parameter becomes `0`.
    have hEval :
        reverseLift 1 = liftedEdgePath boundary X e 0 := by
      simpa [unitInterval.symm] using
        congrArg (fun Γ : C(I, X.obj.left) ↦ Γ 1) hreverse
    exact hEval.trans (liftedEdgePath_zero boundary X e)
  cases e with
  | mk j ej =>
      -- Once the chosen starting point is recovered, the sigma data is forced.
      apply Sigma.ext
      · rfl
      exact heq_of_eq <| Subtype.ext hstart

/-- Helper for Theorem 4.4.5: in the source-faithful owner, a point lying over
`graphEdgePoint boundary j t` determines the unique lifted edge indexed by `j` that passes
through that point at parameter `t`. -/
noncomputable def liftedEdgeIndexOfPointSourceFaithful (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary))
    (j : J) (t : I) (x : X.obj.left)
    (hx :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      X.obj.hom x = graphEdgePoint boundary j t) :
    coverGraphEdgeIndex boundary X.obj.hom := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  let cov : IsCoveringMap X.obj.hom := coveringMap_objHom_sourceFaithful boundary X
  let reverseLift :=
    cov.liftPath (baseEdgeReversePrefixPathSourceFaithful boundary j t) x
      (by
        calc
          baseEdgeReversePrefixPathSourceFaithful boundary j t 0 =
              graphEdgePoint boundary j t :=
            baseEdgeReversePrefixPathSourceFaithful_zero boundary j t
          _ = X.obj.hom x := hx.symm)
  refine ⟨j, ⟨reverseLift 1, ?_⟩⟩
  have hproj :
      X.obj.hom (reverseLift 1) = graphVertex boundary (boundary j 0) := by
    calc
      X.obj.hom (reverseLift 1) = baseEdgeReversePrefixPathSourceFaithful boundary j t 1 := by
        exact congrFun
          (cov.liftPath_lifts (baseEdgeReversePrefixPathSourceFaithful boundary j t) x
            (by
              calc
                baseEdgeReversePrefixPathSourceFaithful boundary j t 0 =
                    graphEdgePoint boundary j t :=
                  baseEdgeReversePrefixPathSourceFaithful_zero boundary j t
                _ = X.obj.hom x := hx.symm))
          1
      _ = graphVertex boundary (boundary j 0) :=
        baseEdgeReversePrefixPathSourceFaithful_one boundary j t
  simpa [Set.mem_singleton_iff] using hproj

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the lifted edge determined by a point
over `graphEdgePoint boundary j t` passes through that point at parameter `t`. -/
theorem liftedEdgeIndexOfPointSourceFaithful_spec (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary))
    (j : J) (t : I) (x : X.obj.left)
    (hx :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      X.obj.hom x = graphEdgePoint boundary j t) :
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    liftedEdgePathSourceFaithful boundary X
        (liftedEdgeIndexOfPointSourceFaithful boundary X j t x hx) t = x := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  let cov : IsCoveringMap X.obj.hom := coveringMap_objHom_sourceFaithful boundary X
  let reverseLift :=
    cov.liftPath (baseEdgeReversePrefixPathSourceFaithful boundary j t) x
      (by
        calc
          baseEdgeReversePrefixPathSourceFaithful boundary j t 0 =
              graphEdgePoint boundary j t :=
            baseEdgeReversePrefixPathSourceFaithful_zero boundary j t
          _ = X.obj.hom x := hx.symm)
  let e : coverGraphEdgeIndex boundary X.obj.hom :=
    liftedEdgeIndexOfPointSourceFaithful boundary X j t x hx
  have he :
      e = ⟨j, ⟨reverseLift 1, by
        have hproj :
            X.obj.hom (reverseLift 1) = graphVertex boundary (boundary j 0) := by
          calc
            X.obj.hom (reverseLift 1) =
                baseEdgeReversePrefixPathSourceFaithful boundary j t 1 := by
                  exact congrFun
                    (cov.liftPath_lifts
                      (baseEdgeReversePrefixPathSourceFaithful boundary j t) x
                      (by
                        calc
                          baseEdgeReversePrefixPathSourceFaithful boundary j t 0 =
                              graphEdgePoint boundary j t :=
                            baseEdgeReversePrefixPathSourceFaithful_zero boundary j t
                          _ = X.obj.hom x := hx.symm))
                    1
            _ = graphVertex boundary (boundary j 0) :=
              baseEdgeReversePrefixPathSourceFaithful_one boundary j t
        simpa [Set.mem_singleton_iff] using hproj⟩⟩ := rfl
  have hstart :
      baseEdgePrefixPathSourceFaithful boundary j t 0 = X.obj.hom (reverseLift 1) := by
    calc
      baseEdgePrefixPathSourceFaithful boundary j t 0 =
          graphVertex boundary (boundary j 0) :=
        baseEdgePrefixPathSourceFaithful_zero boundary j t
      _ = X.obj.hom (reverseLift 1) := by
        symm
        calc
          X.obj.hom (reverseLift 1) =
              baseEdgeReversePrefixPathSourceFaithful boundary j t 1 := by
                exact congrFun
                  (cov.liftPath_lifts
                    (baseEdgeReversePrefixPathSourceFaithful boundary j t) x
                    (by
                      calc
                        baseEdgeReversePrefixPathSourceFaithful boundary j t 0 =
                            graphEdgePoint boundary j t :=
                          baseEdgeReversePrefixPathSourceFaithful_zero boundary j t
                        _ = X.obj.hom x := hx.symm))
                  1
          _ = graphVertex boundary (boundary j 0) :=
            baseEdgeReversePrefixPathSourceFaithful_one boundary j t
  have hreverse :
      cov.liftPath (baseEdgePrefixPathSourceFaithful boundary j t) (reverseLift 1) hstart =
        ⟨fun s ↦ reverseLift (unitInterval.symm s),
          reverseLift.continuous.comp unitInterval.continuous_symm⟩ := by
    symm
    exact (cov.eq_liftPath_iff' hstart).2 <| by
      constructor
      · ext s
        calc
          X.obj.hom (reverseLift (unitInterval.symm s)) =
              baseEdgeReversePrefixPathSourceFaithful boundary j t (unitInterval.symm s) := by
                exact congrFun
                  (cov.liftPath_lifts
                    (baseEdgeReversePrefixPathSourceFaithful boundary j t) x
                    (by
                      calc
                        baseEdgeReversePrefixPathSourceFaithful boundary j t 0 =
                            graphEdgePoint boundary j t :=
                          baseEdgeReversePrefixPathSourceFaithful_zero boundary j t
                        _ = X.obj.hom x := hx.symm))
                  (unitInterval.symm s)
          _ = baseEdgePrefixPathSourceFaithful boundary j t s := by
                simp [baseEdgeReversePrefixPathSourceFaithful,
                  baseEdgePrefixPathSourceFaithful]
      · change reverseLift (unitInterval.symm 0) = reverseLift 1
        simp [unitInterval.symm]
  have hprefix := liftedEdgePrefixPathSourceFaithful_eq_liftPath boundary X e t
  have hvalue :
      (⟨fun s ↦ reverseLift (unitInterval.symm s),
          reverseLift.continuous.comp unitInterval.continuous_symm⟩ : C(I, X.obj.left)) 1 = x := by
    simpa [reverseLift, unitInterval.symm] using
      (cov.liftPath_zero (baseEdgeReversePrefixPathSourceFaithful boundary j t) x
        (by
          calc
            baseEdgeReversePrefixPathSourceFaithful boundary j t 0 =
                graphEdgePoint boundary j t :=
              baseEdgeReversePrefixPathSourceFaithful_zero boundary j t
            _ = X.obj.hom x := hx.symm))
  have hprefixEval :
      (⟨fun s ↦ liftedEdgePathSourceFaithful boundary X e (s * t),
          (liftedEdgePathSourceFaithful boundary X e).continuous.comp <|
            Continuous.subtype_mk
              ((continuous_subtype_val.comp continuous_id).mul
                (continuous_subtype_val.comp continuous_const))
              (fun s ↦ unitInterval.mul_mem s.2 t.2)⟩ : C(I, X.obj.left)) 1 =
        cov.liftPath (baseEdgePrefixPathSourceFaithful boundary j t) (reverseLift 1) hstart 1 := by
    simpa [he] using congrArg (fun Γ : C(I, X.obj.left) ↦ Γ 1) hprefix.symm
  have hreverseEval :
      cov.liftPath (baseEdgePrefixPathSourceFaithful boundary j t) (reverseLift 1) hstart 1 = x := by
    simpa using (congrArg (fun Γ : C(I, X.obj.left) ↦ Γ 1) hreverse).trans hvalue
  rw [he] at hprefix
  have hfirst :
      liftedEdgePathSourceFaithful boundary X e t =
        (⟨fun s ↦ liftedEdgePathSourceFaithful boundary X e (s * t),
          (liftedEdgePathSourceFaithful boundary X e).continuous.comp <|
            Continuous.subtype_mk
              ((continuous_subtype_val.comp continuous_id).mul
                (continuous_subtype_val.comp continuous_const))
              (fun s ↦ unitInterval.mul_mem s.2 t.2)⟩ : C(I, X.obj.left)) 1 := by
    simp
  exact hfirst.trans (hprefixEval.trans hreverseEval)

/-- Helper for Theorem 4.4.5: in the source-faithful owner, reconstructing the lifted edge index
from a point on a canonical lifted edge recovers the original lifted edge index. -/
theorem liftedEdgeIndexOfPointSourceFaithful_eq (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) (t : I) :
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    liftedEdgeIndexOfPointSourceFaithful boundary X e.1 t
      (liftedEdgePathSourceFaithful boundary X e t)
      (congrFun (liftedEdgePathSourceFaithful_lifts boundary X e) t) = e := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  let cov : IsCoveringMap X.obj.hom := coveringMap_objHom_sourceFaithful boundary X
  let reverseLift :=
    cov.liftPath
      (baseEdgeReversePrefixPathSourceFaithful boundary e.1 t)
      (liftedEdgePathSourceFaithful boundary X e t)
      (by
        calc
          baseEdgeReversePrefixPathSourceFaithful boundary e.1 t 0 =
              graphEdgePoint boundary e.1 t :=
            baseEdgeReversePrefixPathSourceFaithful_zero boundary e.1 t
          _ = X.obj.hom (liftedEdgePathSourceFaithful boundary X e t) := by
            symm
            exact congrFun (liftedEdgePathSourceFaithful_lifts boundary X e) t)
  have hreverse :
      reverseLift =
        ⟨fun s ↦ liftedEdgePathSourceFaithful boundary X e (unitInterval.symm s * t),
          (liftedEdgePathSourceFaithful boundary X e).continuous.comp <|
            Continuous.subtype_mk
              ((continuous_subtype_val.comp unitInterval.continuous_symm).mul
                (continuous_subtype_val.comp continuous_const))
              (fun s ↦ unitInterval.mul_mem
                (by
                  change (1 - (s : ℝ)) ∈ Set.Icc (0 : ℝ) 1
                  constructor
                  · linarith [s.2.2]
                  · linarith [s.2.1])
                t.2)⟩ := by
    -- Compare the reverse-prefix lift with the canonical lifted edge after reversing the
    -- parameter, then invoke path-lift uniqueness in the source-faithful owner.
    symm
    exact (cov.eq_liftPath_iff'
      (by
        calc
          baseEdgeReversePrefixPathSourceFaithful boundary e.1 t 0 =
              graphEdgePoint boundary e.1 t :=
            baseEdgeReversePrefixPathSourceFaithful_zero boundary e.1 t
          _ = X.obj.hom (liftedEdgePathSourceFaithful boundary X e t) := by
            symm
            exact congrFun (liftedEdgePathSourceFaithful_lifts boundary X e) t)).2 <| by
      constructor
      · ext s
        calc
          X.obj.hom (liftedEdgePathSourceFaithful boundary X e (unitInterval.symm s * t)) =
              baseEdgePathSourceFaithful boundary e.1 (unitInterval.symm s * t) := by
                exact congrFun
                  (liftedEdgePathSourceFaithful_lifts boundary X e) (unitInterval.symm s * t)
          _ = baseEdgeReversePrefixPathSourceFaithful boundary e.1 t s := rfl
      · change liftedEdgePathSourceFaithful boundary X e (unitInterval.symm 0 * t) =
          liftedEdgePathSourceFaithful boundary X e t
        simp [unitInterval.symm]
  have hstart :
      reverseLift 1 = e.2.1 := by
    -- Evaluate the uniqueness comparison at `1`; the reversed parameter becomes `0`.
    have hEval :
        reverseLift 1 = liftedEdgePathSourceFaithful boundary X e 0 := by
      simpa [unitInterval.symm] using
        congrArg (fun Γ : C(I, X.obj.left) ↦ Γ 1) hreverse
    exact hEval.trans (liftedEdgePathSourceFaithful_zero boundary X e)
  cases e with
  | mk j ej =>
      -- Once the chosen starting point is recovered, the sigma data is forced.
      apply Sigma.ext
      · rfl
      exact heq_of_eq <| Subtype.ext hstart

/-- Helper for Theorem 4.4.5: the endpoint of the canonical lifted edge lies over the terminal
vertex of the underlying base edge. -/
theorem liftedEdgeEndpoint_proj_eq_terminalVertex (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) :
    X.obj.hom (liftedEdgePath boundary X e 1) =
      graphVertex boundary (boundary e.1 1) := by
  -- Evaluate the projection identity at `1` and rewrite the base endpoint as a graph vertex.
  calc
    X.obj.hom (liftedEdgePath boundary X e 1) = baseEdgePath boundary e.1 1 := by
      exact congrFun (liftedEdgePath_lifts boundary X e) 1
    _ = graphEdgePoint boundary e.1 1 := rfl
    _ = graphVertex boundary (boundary e.1 1) :=
      (graphVertex_boundary_one_eq_graphEdgePoint_one boundary e.1).symm

/-- Helper for Theorem 4.4.5: the terminal endpoint of a lifted edge gives the terminal lifted
vertex in the covering graph. -/
noncomputable def liftedEdgeTerminalVertex (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) :
    coverGraphVertexSet boundary X.obj.hom :=
  ⟨liftedEdgePath boundary X e 1, ⟨boundary e.1 1,
    (liftedEdgeEndpoint_proj_eq_terminalVertex boundary X e).symm⟩⟩

/-- Helper for Theorem 4.4.5: the terminal lifted vertex projects to the terminal vertex of the
underlying base edge. -/
@[simp] theorem liftedEdgeTerminalVertex_proj_eq_graphVertex (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) :
    X.obj.hom (liftedEdgeTerminalVertex boundary X e).1 =
      graphVertex boundary (boundary e.1 1) :=
  liftedEdgeEndpoint_proj_eq_terminalVertex boundary X e

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the endpoint of the canonical lifted
edge lies over the terminal vertex of the underlying base edge. -/
theorem liftedEdgeEndpoint_proj_eq_terminalVertexSourceFaithful (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) :
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    X.obj.hom (liftedEdgePathSourceFaithful boundary X e 1) =
      graphVertex boundary (boundary e.1 1) := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  -- Evaluate the projection identity at `1` and rewrite the base endpoint as a graph vertex.
  calc
    X.obj.hom (liftedEdgePathSourceFaithful boundary X e 1) =
        baseEdgePathSourceFaithful boundary e.1 1 := by
          exact congrFun (liftedEdgePathSourceFaithful_lifts boundary X e) 1
    _ = graphEdgePoint boundary e.1 1 := rfl
    _ = graphVertex boundary (boundary e.1 1) :=
      (graphVertex_boundary_one_eq_graphEdgePoint_one boundary e.1).symm

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the terminal endpoint of a lifted
edge gives the terminal lifted vertex in the covering graph. -/
noncomputable def sourceFaithfulLiftedEdgeTerminalVertex (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) :
    coverGraphVertexSet boundary X.obj.hom :=
  ⟨liftedEdgePathSourceFaithful boundary X e 1, ⟨boundary e.1 1,
    (liftedEdgeEndpoint_proj_eq_terminalVertexSourceFaithful boundary X e).symm⟩⟩

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the terminal lifted vertex projects to
the terminal vertex of the underlying base edge. -/
@[simp] theorem sourceFaithfulLiftedEdgeTerminalVertex_proj_eq_graphVertex
    (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) :
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    X.obj.hom (sourceFaithfulLiftedEdgeTerminalVertex boundary X e).1 =
      graphVertex boundary (boundary e.1 1) :=
  liftedEdgeEndpoint_proj_eq_terminalVertexSourceFaithful boundary X e

/-- Helper for Theorem 4.4.5: the lifted boundary function records the chosen initial lifted
vertex at `0` and the canonical lifted terminal vertex at `1`. -/
noncomputable def liftedBoundaryMap (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) :
    Fin 2 → coverGraphVertexSet boundary X.obj.hom :=
  Fin.cases
    (coverGraphEdgeInitialVertex boundary X.obj.hom e)
    (fun _ ↦ liftedEdgeTerminalVertex boundary X e)

/-- Helper for Theorem 4.4.5: the lifted boundary function starts at the prescribed initial
lifted vertex. -/
@[simp] theorem liftedBoundaryMap_zero (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) :
    liftedBoundaryMap boundary X e 0 =
      coverGraphEdgeInitialVertex boundary X.obj.hom e :=
  rfl

/-- Helper for Theorem 4.4.5: the lifted boundary function ends at the canonical lifted terminal
vertex. -/
@[simp] theorem liftedBoundaryMap_one (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) :
    liftedBoundaryMap boundary X e 1 =
      liftedEdgeTerminalVertex boundary X e :=
  rfl

/-- Helper for Theorem 4.4.5: the lifted boundary assignment is injective, so it packages to the
required embedding of lifted edges into endpoint pairs of lifted vertices. -/
theorem liftedBoundary_injective (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary)) :
    Function.Injective (liftedBoundaryMap boundary X) := by
  intro e e' hEq
  -- Compare the two lifted boundaries at the initial endpoint to recover the chosen fiber point.
  have hstart : e.2.1 = e'.2.1 := by
    have h0 := congrArg (fun f ↦ (f 0).1) hEq
    simpa [liftedBoundaryMap] using h0
  have hstartProjEq : X.obj.hom e.2.1 = X.obj.hom e'.2.1 := by
    -- Project the equality of the initial lifted points back to the base.
    exact congrArg X.obj.hom hstart
  have hstartProj : graphVertex boundary (boundary e.1 0) =
      graphVertex boundary (boundary e'.1 0) := by
    exact (coverGraphEdgeIndex_proj_eq_graphVertex boundary X.obj.hom e).symm.trans
      (hstartProjEq.trans (coverGraphEdgeIndex_proj_eq_graphVertex boundary X.obj.hom e'))
  have hstartBase : boundary e.1 0 = boundary e'.1 0 :=
    graphVertex_injective boundary hstartProj
  -- Compare the terminal lifted vertices to recover the terminal base endpoint as well.
  have hend : (liftedEdgeTerminalVertex boundary X e).1 =
      (liftedEdgeTerminalVertex boundary X e').1 := by
    have h1 := congrArg (fun f ↦ (f 1).1) hEq
    simpa [liftedBoundaryMap] using h1
  have hendProjEq :
      X.obj.hom (liftedEdgeTerminalVertex boundary X e).1 =
        X.obj.hom (liftedEdgeTerminalVertex boundary X e').1 := by
    -- Project the equality of terminal lifted points to the base.
    exact congrArg X.obj.hom hend
  have hendProj : graphVertex boundary (boundary e.1 1) =
      graphVertex boundary (boundary e'.1 1) := by
    exact (liftedEdgeTerminalVertex_proj_eq_graphVertex boundary X e).symm.trans
      (hendProjEq.trans (liftedEdgeTerminalVertex_proj_eq_graphVertex boundary X e'))
  have hendBase : boundary e.1 1 = boundary e'.1 1 :=
    graphVertex_injective boundary hendProj
  have hEdge : e.1 = e'.1 := by
    -- The original boundary embedding is recovered from its two endpoint values.
    apply boundary.injective
    ext i
    fin_cases i
    · simpa using hstartBase
    · simpa using hendBase
  -- Once the base edge matches, the equality of initial lift points identifies the sigma data.
  cases e with
  | mk j ej =>
      cases e' with
      | mk j' ej' =>
          dsimp at hstart hEdge
          cases hEdge
          have hej : ej = ej' := by
            apply Subtype.ext
            exact hstart
          cases hej
          rfl

/-- Helper for Theorem 4.4.5: the lifted boundary embedding attached to the covering `X`. -/
noncomputable def liftedBoundary (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary)) :
    coverGraphEdgeIndex boundary X.obj.hom ↪ Fin 2 → coverGraphVertexSet boundary X.obj.hom :=
  ⟨liftedBoundaryMap boundary X, liftedBoundary_injective boundary X⟩

/-- Helper for Theorem 4.4.5: the source-level map sending each lifted vertex to its underlying
point of `X.obj.left` and each lifted edge point to the corresponding lifted path point. -/
noncomputable def coverGraphRealizationRaw (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary)) :
    coverGraphVertexSet boundary X.obj.hom ⊕
        (coverGraphEdgeIndex boundary X.obj.hom × I) →
      X.obj.left
  | Sum.inl x => x.1
  | Sum.inr (e, t) => liftedEdgePath boundary X e t

/-- Helper for Theorem 4.4.5: the source-level realization map is constant on the quotient
relation defining `graphRealization (liftedBoundary boundary X)`. -/
theorem coverGraphRealizationRaw_respectsBoundary (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary))
    (a b :
      coverGraphVertexSet boundary X.obj.hom ⊕
        (coverGraphEdgeIndex boundary X.obj.hom × I))
    (hab : graphRealizationSetoid (liftedBoundary boundary X) a b) :
    coverGraphRealizationRaw boundary X a = coverGraphRealizationRaw boundary X b := by
  -- Reduce the quotient compatibility to the endpoint formulas already proved for lifted edges.
  induction hab with
  | rel a b hrel =>
      cases a with
      | inl x =>
          cases b with
          | inl y =>
              cases hrel
          | inr et =>
              rcases et with ⟨e, t⟩
              rcases hrel with hzero | hone
              · rcases hzero with ⟨hx, ht⟩
                subst hx
                subst ht
                calc
                  ((liftedBoundary boundary X) e 0).1 = e.2.1 := by
                    rfl
                  _ = liftedEdgePath boundary X e 0 := by
                    exact (liftedEdgePath_zero boundary X e).symm
              · rcases hone with ⟨hx, ht⟩
                subst hx
                subst ht
                rfl
      | inr edgeData =>
          rcases edgeData with ⟨e, t⟩
          cases b with
          | inl x =>
              rcases hrel with hzero | hone
              · rcases hzero with ⟨ht, hx⟩
                subst ht
                subst hx
                calc
                  liftedEdgePath boundary X e 0 = e.2.1 := liftedEdgePath_zero boundary X e
                  _ = ((liftedBoundary boundary X) e 0).1 := by
                    rfl
              · rcases hone with ⟨ht, hx⟩
                subst ht
                subst hx
                rfl
          | inr bt =>
              cases hrel
  | refl a =>
      rfl
  | symm a b hab ih =>
      exact ih.symm
  | trans a b c hab hbc ihab ihbc =>
      exact ihab.trans ihbc

/-- Helper for Theorem 4.4.5: if a lifted vertex representative and a lifted edge representative
have the same raw image in `X.obj.left`, then they are related by the lifted-boundary setoid. -/
theorem coverGraphRealizationRaw_eq_vertex_edge (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary))
    (x : coverGraphVertexSet boundary X.obj.hom)
    (e : coverGraphEdgeIndex boundary X.obj.hom) (t : I)
    (h :
      coverGraphRealizationRaw boundary X (Sum.inl x) =
        coverGraphRealizationRaw boundary X (Sum.inr (e, t))) :
    graphRealizationSetoid (liftedBoundary boundary X) (Sum.inl x) (Sum.inr (e, t)) := by
  rcases coverGraphVertexSet_exists_vertex boundary X.obj.hom x with ⟨b, hb⟩
  have hbase :
      graphVertex boundary b = graphEdgePoint boundary e.1 t := by
    -- Project the raw equality to the base graph and classify the edge parameter there.
    have hproj :
        X.obj.hom (liftedEdgePath boundary X e t) = graphEdgePoint boundary e.1 t := by
      exact congrFun (liftedEdgePath_lifts boundary X e) t
    exact hb.symm.trans ((congrArg X.obj.hom h).trans hproj)
  have hsetoidBase :
      graphRealizationSetoid boundary (Sum.inl b) (Sum.inr (e.1, t)) := by
    exact Quotient.eq'.1 hbase
  rcases graphRealizationSetoid_vertex_cases boundary b hsetoidBase with
      hvertex | hzero | hone
  · cases hvertex
  · rcases hzero with ⟨j, hjt, hjb⟩
    cases hjt
    -- An equality with a lifted vertex can only occur at the initial endpoint `t = 0`.
    have hx :
        x = coverGraphEdgeInitialVertex boundary X.obj.hom e := by
      apply Subtype.ext
      simpa [coverGraphEdgeInitialVertex] using h.trans (liftedEdgePath_zero boundary X e)
    subst hx
    simpa [liftedBoundary] using
      graphRealizationSetoid_vertex_boundary_zero (liftedBoundary boundary X) e
  · rcases hone with ⟨j, hjt, hjb⟩
    cases hjt
    -- Similarly, the terminal endpoint is the only other way to hit a lifted vertex.
    have hx :
        x = liftedEdgeTerminalVertex boundary X e := by
      apply Subtype.ext
      simpa [liftedEdgeTerminalVertex] using h
    subst hx
    simpa [liftedBoundary] using
      graphRealizationSetoid_vertex_boundary_one (liftedBoundary boundary X) e

/-- Helper for Theorem 4.4.5: the previous vertex-edge comparison is symmetric. -/
theorem coverGraphRealizationRaw_eq_edge_vertex (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) (t : I)
    (x : coverGraphVertexSet boundary X.obj.hom)
    (h :
      coverGraphRealizationRaw boundary X (Sum.inr (e, t)) =
        coverGraphRealizationRaw boundary X (Sum.inl x)) :
    graphRealizationSetoid (liftedBoundary boundary X) (Sum.inr (e, t)) (Sum.inl x) := by
  exact (coverGraphRealizationRaw_eq_vertex_edge boundary X x e t h.symm).symm

/-- Helper for Theorem 4.4.5: equality of raw lifted-graph representatives is exactly the
graph-realization setoid relation for the lifted boundary. -/
theorem coverGraphRealizationRaw_eq_iff_setoid (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary))
    (a b :
      coverGraphVertexSet boundary X.obj.hom ⊕
        (coverGraphEdgeIndex boundary X.obj.hom × I)) :
    graphRealizationSetoid (liftedBoundary boundary X) a b ↔
      coverGraphRealizationRaw boundary X a = coverGraphRealizationRaw boundary X b := by
  constructor
  · exact coverGraphRealizationRaw_respectsBoundary boundary X a b
  · intro hab
    cases a with
    | inl x =>
        cases b with
        | inl y =>
            -- Equal lifted vertices are identical as subtype points, so the quotient relation is reflexive.
            have hxy : x = y := by
              apply Subtype.ext
              simpa using hab
            subst hxy
            rfl
        | inr bt =>
            rcases bt with ⟨e, t⟩
            exact coverGraphRealizationRaw_eq_vertex_edge boundary X x e t hab
    | inr edgeData =>
        rcases edgeData with ⟨e, s⟩
        cases b with
        | inl x =>
            exact coverGraphRealizationRaw_eq_edge_vertex boundary X e s x hab
        | inr bt =>
            rcases bt with ⟨e', t⟩
            by_cases hs0 : s = 0
            · subst hs0
              -- Endpoint equalities are routed through the corresponding lifted vertex.
              have hleft :
                  graphRealizationSetoid (liftedBoundary boundary X)
                    (Sum.inr (e, 0))
                    (Sum.inl (coverGraphEdgeInitialVertex boundary X.obj.hom e)) := by
                simpa [liftedBoundary] using
                  (graphRealizationSetoid_vertex_boundary_zero (liftedBoundary boundary X) e).symm
              have hvertexEq :
                  coverGraphRealizationRaw boundary X
                      (Sum.inl (coverGraphEdgeInitialVertex boundary X.obj.hom e)) =
                    coverGraphRealizationRaw boundary X (Sum.inr (e', t)) := by
                simpa [coverGraphRealizationRaw, coverGraphEdgeInitialVertex, liftedEdgePath_zero]
                  using hab
              have hright :
                  graphRealizationSetoid (liftedBoundary boundary X)
                    (Sum.inl (coverGraphEdgeInitialVertex boundary X.obj.hom e))
                    (Sum.inr (e', t)) := by
                exact coverGraphRealizationRaw_eq_vertex_edge boundary X
                  (coverGraphEdgeInitialVertex boundary X.obj.hom e) e' t hvertexEq
              exact Relation.EqvGen.trans _ _ _ hleft hright
            · by_cases hs1 : s = 1
              · subst hs1
                have hleft :
                    graphRealizationSetoid (liftedBoundary boundary X)
                      (Sum.inr (e, 1))
                      (Sum.inl (liftedEdgeTerminalVertex boundary X e)) := by
                  simpa [liftedBoundary] using
                    (graphRealizationSetoid_vertex_boundary_one (liftedBoundary boundary X) e).symm
                have hvertexEq :
                    coverGraphRealizationRaw boundary X
                        (Sum.inl (liftedEdgeTerminalVertex boundary X e)) =
                      coverGraphRealizationRaw boundary X (Sum.inr (e', t)) := by
                  simpa [coverGraphRealizationRaw, liftedEdgeTerminalVertex] using hab
                have hright :
                    graphRealizationSetoid (liftedBoundary boundary X)
                      (Sum.inl (liftedEdgeTerminalVertex boundary X e))
                      (Sum.inr (e', t)) := by
                  exact coverGraphRealizationRaw_eq_vertex_edge boundary X
                    (liftedEdgeTerminalVertex boundary X e) e' t hvertexEq
                exact Relation.EqvGen.trans _ _ _ hleft hright
              · by_cases ht0 : t = 0
                · subst ht0
                  have hvertexEq :
                      coverGraphRealizationRaw boundary X (Sum.inr (e, s)) =
                        coverGraphRealizationRaw boundary X
                          (Sum.inl (coverGraphEdgeInitialVertex boundary X.obj.hom e')) := by
                    simpa [coverGraphRealizationRaw, coverGraphEdgeInitialVertex, liftedEdgePath_zero]
                      using hab
                  have hleft :
                      graphRealizationSetoid (liftedBoundary boundary X)
                        (Sum.inr (e, s))
                        (Sum.inl (coverGraphEdgeInitialVertex boundary X.obj.hom e')) := by
                    exact coverGraphRealizationRaw_eq_edge_vertex boundary X e s
                      (coverGraphEdgeInitialVertex boundary X.obj.hom e') hvertexEq
                  have hright :
                      graphRealizationSetoid (liftedBoundary boundary X)
                        (Sum.inl (coverGraphEdgeInitialVertex boundary X.obj.hom e'))
                        (Sum.inr (e', 0)) := by
                    simpa [liftedBoundary] using
                      graphRealizationSetoid_vertex_boundary_zero (liftedBoundary boundary X) e'
                  exact Relation.EqvGen.trans _ _ _ hleft hright
                · by_cases ht1 : t = 1
                  · subst ht1
                    have hvertexEq :
                        coverGraphRealizationRaw boundary X (Sum.inr (e, s)) =
                          coverGraphRealizationRaw boundary X
                            (Sum.inl (liftedEdgeTerminalVertex boundary X e')) := by
                      simpa [coverGraphRealizationRaw, liftedEdgeTerminalVertex] using hab
                    have hleft :
                        graphRealizationSetoid (liftedBoundary boundary X)
                          (Sum.inr (e, s))
                          (Sum.inl (liftedEdgeTerminalVertex boundary X e')) := by
                      exact coverGraphRealizationRaw_eq_edge_vertex boundary X e s
                        (liftedEdgeTerminalVertex boundary X e') hvertexEq
                    have hright :
                        graphRealizationSetoid (liftedBoundary boundary X)
                          (Sum.inl (liftedEdgeTerminalVertex boundary X e'))
                          (Sum.inr (e', 1)) := by
                      simpa [liftedBoundary] using
                        graphRealizationSetoid_vertex_boundary_one (liftedBoundary boundary X) e'
                    exact Relation.EqvGen.trans _ _ _ hleft hright
                  · -- With both parameters in the open interval, the base quotient fixes the edge
                    -- representative, and the recovered lifted edge index must match as well.
                    have hbase :
                        graphEdgePoint boundary e.1 s = graphEdgePoint boundary e'.1 t := by
                      have hleftProj :
                          graphEdgePoint boundary e.1 s =
                            X.obj.hom (liftedEdgePath boundary X e s) := by
                        symm
                        exact congrFun (liftedEdgePath_lifts boundary X e) s
                      have hrightProj :
                          X.obj.hom (liftedEdgePath boundary X e' t) =
                            graphEdgePoint boundary e'.1 t := by
                        exact congrFun (liftedEdgePath_lifts boundary X e') t
                      exact hleftProj.trans ((congrArg X.obj.hom hab).trans hrightProj)
                    have hsetoidBase :
                        graphRealizationSetoid boundary
                          (Sum.inr (e.1, s)) (Sum.inr (e'.1, t)) := by
                      exact Quotient.eq'.1 hbase
                    have hpair :
                        (e'.1, t) = (e.1, s) := by
                      injection
                        (graphRealizationSetoid_interior_eq boundary e.1 s hs0 hs1 hsetoidBase)
                    have hBaseEdge : e'.1 = e.1 := congrArg Prod.fst hpair
                    have hTime : t = s := congrArg Prod.snd hpair
                    have hleft :
                        liftedEdgeIndexOfPoint boundary X e.1 s
                          (liftedEdgePath boundary X e s)
                          (congrFun (liftedEdgePath_lifts boundary X e) s) = e :=
                      liftedEdgeIndexOfPoint_eq boundary X e s
                    have hpoint :
                        liftedEdgePath boundary X e s = liftedEdgePath boundary X e' t := by
                      simpa [coverGraphRealizationRaw] using hab
                    have hright :
                        liftedEdgeIndexOfPoint boundary X e.1 s
                          (liftedEdgePath boundary X e s)
                          (congrFun (liftedEdgePath_lifts boundary X e) s) = e' := by
                      have hEdge : e.1 = e'.1 := hBaseEdge.symm
                      simpa [hEdge, hTime, hpoint] using
                        liftedEdgeIndexOfPoint_eq boundary X e' t
                    have heq : e = e' := hleft.symm.trans hright
                    cases heq
                    cases hTime
                    rfl

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the lifted boundary function records
the chosen initial lifted vertex at `0` and the canonical lifted terminal vertex at `1`. -/
noncomputable def sourceFaithfulLiftedBoundaryMap (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) :
    Fin 2 → coverGraphVertexSet boundary X.obj.hom :=
  Fin.cases
    (coverGraphEdgeInitialVertex boundary X.obj.hom e)
    (fun _ ↦ sourceFaithfulLiftedEdgeTerminalVertex boundary X e)

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the lifted boundary function starts
at the prescribed initial lifted vertex. -/
@[simp] theorem sourceFaithfulLiftedBoundaryMap_zero (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) :
    sourceFaithfulLiftedBoundaryMap boundary X e 0 =
      coverGraphEdgeInitialVertex boundary X.obj.hom e :=
  rfl

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the lifted boundary function ends at
the canonical lifted terminal vertex. -/
@[simp] theorem sourceFaithfulLiftedBoundaryMap_one (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) :
    sourceFaithfulLiftedBoundaryMap boundary X e 1 =
      sourceFaithfulLiftedEdgeTerminalVertex boundary X e :=
  rfl

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the lifted boundary assignment is
injective, so it packages to the required embedding of lifted edges into endpoint pairs of lifted
vertices. -/
theorem sourceFaithfulLiftedBoundary_injective (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary)) :
    Function.Injective (sourceFaithfulLiftedBoundaryMap boundary X) := by
  intro e e' hEq
  -- Compare the two lifted boundaries at the initial endpoint to recover the chosen fiber point.
  have hstart : e.2.1 = e'.2.1 := by
    have h0 := congrArg (fun f ↦ (f 0).1) hEq
    simpa [sourceFaithfulLiftedBoundaryMap] using h0
  have hstartProjEq : X.obj.hom e.2.1 = X.obj.hom e'.2.1 := by
    exact congrArg X.obj.hom hstart
  have hstartProj : graphVertex boundary (boundary e.1 0) =
      graphVertex boundary (boundary e'.1 0) := by
    exact (coverGraphEdgeIndex_proj_eq_graphVertex boundary X.obj.hom e).symm.trans
      (hstartProjEq.trans (coverGraphEdgeIndex_proj_eq_graphVertex boundary X.obj.hom e'))
  have hstartBase : boundary e.1 0 = boundary e'.1 0 :=
    graphVertex_injective boundary hstartProj
  -- Compare the terminal lifted vertices to recover the terminal base endpoint as well.
  have hend :
      (sourceFaithfulLiftedEdgeTerminalVertex boundary X e).1 =
        (sourceFaithfulLiftedEdgeTerminalVertex boundary X e').1 := by
    have h1 := congrArg (fun f ↦ (f 1).1) hEq
    simpa [sourceFaithfulLiftedBoundaryMap] using h1
  have hendProjEq :
      X.obj.hom (sourceFaithfulLiftedEdgeTerminalVertex boundary X e).1 =
        X.obj.hom (sourceFaithfulLiftedEdgeTerminalVertex boundary X e').1 := by
    exact congrArg X.obj.hom hend
  have hendProj : graphVertex boundary (boundary e.1 1) =
      graphVertex boundary (boundary e'.1 1) := by
    exact
      (sourceFaithfulLiftedEdgeTerminalVertex_proj_eq_graphVertex boundary X e).symm.trans
        (hendProjEq.trans
          (sourceFaithfulLiftedEdgeTerminalVertex_proj_eq_graphVertex boundary X e'))
  have hendBase : boundary e.1 1 = boundary e'.1 1 :=
    graphVertex_injective boundary hendProj
  have hEdge : e.1 = e'.1 := by
    apply boundary.injective
    ext i
    fin_cases i
    · simpa using hstartBase
    · simpa using hendBase
  -- Once the base edge matches, the equality of initial lift points identifies the sigma data.
  cases e with
  | mk j ej =>
      cases e' with
      | mk j' ej' =>
          dsimp at hstart hEdge
          cases hEdge
          have hej : ej = ej' := by
            apply Subtype.ext
            exact hstart
          cases hej
          rfl

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the lifted boundary embedding
attached to the covering `X`. -/
noncomputable def sourceFaithfulLiftedBoundary (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary)) :
    coverGraphEdgeIndex boundary X.obj.hom ↪ Fin 2 → coverGraphVertexSet boundary X.obj.hom :=
  ⟨sourceFaithfulLiftedBoundaryMap boundary X, sourceFaithfulLiftedBoundary_injective boundary X⟩

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the source-level map sends each
lifted vertex to its underlying point of `X.obj.left` and each lifted edge point to the
corresponding lifted path point. -/
noncomputable def sourceFaithfulCoverGraphRealizationRaw (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary)) :
    coverGraphVertexSet boundary X.obj.hom ⊕
        (coverGraphEdgeIndex boundary X.obj.hom × I) →
      X.obj.left
  | Sum.inl x => x.1
  | Sum.inr (e, t) => liftedEdgePathSourceFaithful boundary X e t

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the source-level realization map is
constant on the quotient relation defining `graphRealization (sourceFaithfulLiftedBoundary
boundary X)`. -/
theorem sourceFaithfulCoverGraphRealizationRaw_respectsBoundary (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary))
    (a b :
      coverGraphVertexSet boundary X.obj.hom ⊕
        (coverGraphEdgeIndex boundary X.obj.hom × I))
    (hab : graphRealizationSetoid (sourceFaithfulLiftedBoundary boundary X) a b) :
    sourceFaithfulCoverGraphRealizationRaw boundary X a =
      sourceFaithfulCoverGraphRealizationRaw boundary X b := by
  induction hab with
  | rel a b hrel =>
      cases a with
      | inl x =>
          cases b with
          | inl y =>
              cases hrel
          | inr et =>
              rcases et with ⟨e, t⟩
              rcases hrel with hzero | hone
              · rcases hzero with ⟨hx, ht⟩
                subst hx
                subst ht
                calc
                  ((sourceFaithfulLiftedBoundary boundary X) e 0).1 = e.2.1 := by
                    rfl
                  _ = liftedEdgePathSourceFaithful boundary X e 0 := by
                    exact (liftedEdgePathSourceFaithful_zero boundary X e).symm
              · rcases hone with ⟨hx, ht⟩
                subst hx
                subst ht
                rfl
      | inr edgeData =>
          rcases edgeData with ⟨e, t⟩
          cases b with
          | inl x =>
              rcases hrel with hzero | hone
              · rcases hzero with ⟨ht, hx⟩
                subst ht
                subst hx
                calc
                  liftedEdgePathSourceFaithful boundary X e 0 = e.2.1 :=
                    liftedEdgePathSourceFaithful_zero boundary X e
                  _ = ((sourceFaithfulLiftedBoundary boundary X) e 0).1 := by
                    rfl
              · rcases hone with ⟨ht, hx⟩
                subst ht
                subst hx
                rfl
          | inr bt =>
              cases hrel
  | refl a =>
      rfl
  | symm a b hab ih =>
      exact ih.symm
  | trans a b c hab hbc ihab ihbc =>
      exact ihab.trans ihbc

/-- Helper for Theorem 4.4.5: in the source-faithful owner, if a lifted vertex representative and
a lifted edge representative have the same raw image in `X.obj.left`, then they are related by
the lifted-boundary setoid. -/
theorem sourceFaithfulCoverGraphRealizationRaw_eq_vertex_edge (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary))
    (x : coverGraphVertexSet boundary X.obj.hom)
    (e : coverGraphEdgeIndex boundary X.obj.hom) (t : I)
    (h :
      sourceFaithfulCoverGraphRealizationRaw boundary X (Sum.inl x) =
        sourceFaithfulCoverGraphRealizationRaw boundary X (Sum.inr (e, t))) :
    graphRealizationSetoid (sourceFaithfulLiftedBoundary boundary X)
      (Sum.inl x) (Sum.inr (e, t)) := by
  rcases coverGraphVertexSet_exists_vertex boundary X.obj.hom x with ⟨b, hb⟩
  have hbase :
      graphVertex boundary b = graphEdgePoint boundary e.1 t := by
    have hproj :
        X.obj.hom (liftedEdgePathSourceFaithful boundary X e t) =
          graphEdgePoint boundary e.1 t := by
      exact congrFun (liftedEdgePathSourceFaithful_lifts boundary X e) t
    exact hb.symm.trans ((congrArg X.obj.hom h).trans hproj)
  have hsetoidBase :
      graphRealizationSetoid boundary (Sum.inl b) (Sum.inr (e.1, t)) := by
    exact Quotient.eq'.1 hbase
  rcases graphRealizationSetoid_vertex_cases boundary b hsetoidBase with
      hvertex | hzero | hone
  · cases hvertex
  · rcases hzero with ⟨j, hjt, hjb⟩
    cases hjt
    have hx :
        x = coverGraphEdgeInitialVertex boundary X.obj.hom e := by
      apply Subtype.ext
      simpa [coverGraphEdgeInitialVertex] using
        h.trans (liftedEdgePathSourceFaithful_zero boundary X e)
    subst hx
    simpa [sourceFaithfulLiftedBoundary] using
      graphRealizationSetoid_vertex_boundary_zero (sourceFaithfulLiftedBoundary boundary X) e
  · rcases hone with ⟨j, hjt, hjb⟩
    cases hjt
    have hx :
        x = sourceFaithfulLiftedEdgeTerminalVertex boundary X e := by
      apply Subtype.ext
      simpa [sourceFaithfulLiftedEdgeTerminalVertex] using h
    subst hx
    simpa [sourceFaithfulLiftedBoundary] using
      graphRealizationSetoid_vertex_boundary_one (sourceFaithfulLiftedBoundary boundary X) e

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the previous vertex-edge comparison
is symmetric. -/
theorem sourceFaithfulCoverGraphRealizationRaw_eq_edge_vertex (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) (t : I)
    (x : coverGraphVertexSet boundary X.obj.hom)
    (h :
      sourceFaithfulCoverGraphRealizationRaw boundary X (Sum.inr (e, t)) =
        sourceFaithfulCoverGraphRealizationRaw boundary X (Sum.inl x)) :
    graphRealizationSetoid (sourceFaithfulLiftedBoundary boundary X)
      (Sum.inr (e, t)) (Sum.inl x) := by
  exact
    (sourceFaithfulCoverGraphRealizationRaw_eq_vertex_edge boundary X x e t h.symm).symm

/-- Helper for Theorem 4.4.5: in the source-faithful owner, equality of raw lifted-graph
representatives is exactly the graph-realization setoid relation for the lifted boundary. -/
theorem sourceFaithfulCoverGraphRealizationRaw_eq_iff_setoid (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary))
    (a b :
      coverGraphVertexSet boundary X.obj.hom ⊕
        (coverGraphEdgeIndex boundary X.obj.hom × I)) :
    graphRealizationSetoid (sourceFaithfulLiftedBoundary boundary X) a b ↔
      sourceFaithfulCoverGraphRealizationRaw boundary X a =
        sourceFaithfulCoverGraphRealizationRaw boundary X b := by
  constructor
  · exact sourceFaithfulCoverGraphRealizationRaw_respectsBoundary boundary X a b
  · intro hab
    cases a with
    | inl x =>
        cases b with
        | inl y =>
            have hxy : x = y := by
              apply Subtype.ext
              simpa using hab
            subst hxy
            rfl
        | inr bt =>
            rcases bt with ⟨e, t⟩
            exact sourceFaithfulCoverGraphRealizationRaw_eq_vertex_edge boundary X x e t hab
    | inr edgeData =>
        rcases edgeData with ⟨e, s⟩
        cases b with
        | inl x =>
            exact sourceFaithfulCoverGraphRealizationRaw_eq_edge_vertex boundary X e s x hab
        | inr bt =>
            rcases bt with ⟨e', t⟩
            by_cases hs0 : s = 0
            · subst hs0
              have hleft :
                  graphRealizationSetoid (sourceFaithfulLiftedBoundary boundary X)
                    (Sum.inr (e, 0))
                    (Sum.inl (coverGraphEdgeInitialVertex boundary X.obj.hom e)) := by
                simpa [sourceFaithfulLiftedBoundary] using
                  (graphRealizationSetoid_vertex_boundary_zero
                    (sourceFaithfulLiftedBoundary boundary X) e).symm
              have hvertexEq :
                  sourceFaithfulCoverGraphRealizationRaw boundary X
                      (Sum.inl (coverGraphEdgeInitialVertex boundary X.obj.hom e)) =
                    sourceFaithfulCoverGraphRealizationRaw boundary X (Sum.inr (e', t)) := by
                simpa [sourceFaithfulCoverGraphRealizationRaw, coverGraphEdgeInitialVertex,
                  liftedEdgePathSourceFaithful_zero] using hab
              have hright :
                  graphRealizationSetoid (sourceFaithfulLiftedBoundary boundary X)
                    (Sum.inl (coverGraphEdgeInitialVertex boundary X.obj.hom e))
                    (Sum.inr (e', t)) := by
                exact sourceFaithfulCoverGraphRealizationRaw_eq_vertex_edge boundary X
                  (coverGraphEdgeInitialVertex boundary X.obj.hom e) e' t hvertexEq
              exact Relation.EqvGen.trans _ _ _ hleft hright
            · by_cases hs1 : s = 1
              · subst hs1
                have hleft :
                    graphRealizationSetoid (sourceFaithfulLiftedBoundary boundary X)
                      (Sum.inr (e, 1))
                      (Sum.inl (sourceFaithfulLiftedEdgeTerminalVertex boundary X e)) := by
                  simpa [sourceFaithfulLiftedBoundary] using
                    (graphRealizationSetoid_vertex_boundary_one
                      (sourceFaithfulLiftedBoundary boundary X) e).symm
                have hvertexEq :
                    sourceFaithfulCoverGraphRealizationRaw boundary X
                        (Sum.inl (sourceFaithfulLiftedEdgeTerminalVertex boundary X e)) =
                      sourceFaithfulCoverGraphRealizationRaw boundary X (Sum.inr (e', t)) := by
                  simpa [sourceFaithfulCoverGraphRealizationRaw,
                    sourceFaithfulLiftedEdgeTerminalVertex] using hab
                have hright :
                    graphRealizationSetoid (sourceFaithfulLiftedBoundary boundary X)
                      (Sum.inl (sourceFaithfulLiftedEdgeTerminalVertex boundary X e))
                      (Sum.inr (e', t)) := by
                  exact sourceFaithfulCoverGraphRealizationRaw_eq_vertex_edge boundary X
                    (sourceFaithfulLiftedEdgeTerminalVertex boundary X e) e' t hvertexEq
                exact Relation.EqvGen.trans _ _ _ hleft hright
              · by_cases ht0 : t = 0
                · subst ht0
                  have hvertexEq :
                      sourceFaithfulCoverGraphRealizationRaw boundary X (Sum.inr (e, s)) =
                        sourceFaithfulCoverGraphRealizationRaw boundary X
                          (Sum.inl (coverGraphEdgeInitialVertex boundary X.obj.hom e')) := by
                    simpa [sourceFaithfulCoverGraphRealizationRaw, coverGraphEdgeInitialVertex,
                      liftedEdgePathSourceFaithful_zero] using hab
                  have hleft :
                      graphRealizationSetoid (sourceFaithfulLiftedBoundary boundary X)
                        (Sum.inr (e, s))
                        (Sum.inl (coverGraphEdgeInitialVertex boundary X.obj.hom e')) := by
                    exact sourceFaithfulCoverGraphRealizationRaw_eq_edge_vertex boundary X e s
                      (coverGraphEdgeInitialVertex boundary X.obj.hom e') hvertexEq
                  have hright :
                      graphRealizationSetoid (sourceFaithfulLiftedBoundary boundary X)
                        (Sum.inl (coverGraphEdgeInitialVertex boundary X.obj.hom e'))
                        (Sum.inr (e', 0)) := by
                    simpa [sourceFaithfulLiftedBoundary] using
                      graphRealizationSetoid_vertex_boundary_zero
                        (sourceFaithfulLiftedBoundary boundary X) e'
                  exact Relation.EqvGen.trans _ _ _ hleft hright
                · by_cases ht1 : t = 1
                  · subst ht1
                    have hvertexEq :
                        sourceFaithfulCoverGraphRealizationRaw boundary X (Sum.inr (e, s)) =
                          sourceFaithfulCoverGraphRealizationRaw boundary X
                            (Sum.inl (sourceFaithfulLiftedEdgeTerminalVertex boundary X e')) := by
                      simpa [sourceFaithfulCoverGraphRealizationRaw,
                        sourceFaithfulLiftedEdgeTerminalVertex] using hab
                    have hleft :
                        graphRealizationSetoid (sourceFaithfulLiftedBoundary boundary X)
                          (Sum.inr (e, s))
                          (Sum.inl (sourceFaithfulLiftedEdgeTerminalVertex boundary X e')) := by
                      exact sourceFaithfulCoverGraphRealizationRaw_eq_edge_vertex boundary X e s
                        (sourceFaithfulLiftedEdgeTerminalVertex boundary X e') hvertexEq
                    have hright :
                        graphRealizationSetoid (sourceFaithfulLiftedBoundary boundary X)
                          (Sum.inl (sourceFaithfulLiftedEdgeTerminalVertex boundary X e'))
                          (Sum.inr (e', 1)) := by
                      simpa [sourceFaithfulLiftedBoundary] using
                        graphRealizationSetoid_vertex_boundary_one
                          (sourceFaithfulLiftedBoundary boundary X) e'
                    exact Relation.EqvGen.trans _ _ _ hleft hright
                  · have hbase :
                        graphEdgePoint boundary e.1 s = graphEdgePoint boundary e'.1 t := by
                      have hleftProj :
                          graphEdgePoint boundary e.1 s =
                            X.obj.hom (liftedEdgePathSourceFaithful boundary X e s) := by
                        symm
                        exact congrFun (liftedEdgePathSourceFaithful_lifts boundary X e) s
                      have hrightProj :
                          X.obj.hom (liftedEdgePathSourceFaithful boundary X e' t) =
                            graphEdgePoint boundary e'.1 t := by
                        exact congrFun (liftedEdgePathSourceFaithful_lifts boundary X e') t
                      exact hleftProj.trans ((congrArg X.obj.hom hab).trans hrightProj)
                    have hsetoidBase :
                        graphRealizationSetoid boundary
                          (Sum.inr (e.1, s)) (Sum.inr (e'.1, t)) := by
                      exact Quotient.eq'.1 hbase
                    have hpair :
                        (e'.1, t) = (e.1, s) := by
                      injection
                        (graphRealizationSetoid_interior_eq boundary e.1 s hs0 hs1 hsetoidBase)
                    have hBaseEdge : e'.1 = e.1 := congrArg Prod.fst hpair
                    have hTime : t = s := congrArg Prod.snd hpair
                    have hleft :
                        liftedEdgeIndexOfPointSourceFaithful boundary X e.1 s
                          (liftedEdgePathSourceFaithful boundary X e s)
                          (congrFun (liftedEdgePathSourceFaithful_lifts boundary X e) s) = e :=
                      liftedEdgeIndexOfPointSourceFaithful_eq boundary X e s
                    have hpoint :
                        liftedEdgePathSourceFaithful boundary X e s =
                          liftedEdgePathSourceFaithful boundary X e' t := by
                      simpa [sourceFaithfulCoverGraphRealizationRaw] using hab
                    have hright :
                        liftedEdgeIndexOfPointSourceFaithful boundary X e.1 s
                          (liftedEdgePathSourceFaithful boundary X e s)
                          (congrFun (liftedEdgePathSourceFaithful_lifts boundary X e) s) = e' := by
                      have hEdge : e.1 = e'.1 := hBaseEdge.symm
                      simpa [hEdge, hTime, hpoint] using
                        liftedEdgeIndexOfPointSourceFaithful_eq boundary X e' t
                    have heq : e = e' := hleft.symm.trans hright
                    cases heq
                    cases hTime
                    rfl

/-- Helper for Theorem 4.4.5: the quotient of `coverGraphRealizationRaw` gives the canonical
realization function from the lifted graph to the total space `X.obj.left`. -/
noncomputable def coverGraphRealizationToTotalSpace (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary)) :
    graphRealization (liftedBoundary boundary X) → X.obj.left :=
  Quotient.lift (coverGraphRealizationRaw boundary X)
    (coverGraphRealizationRaw_respectsBoundary boundary X)

/-- Helper for Theorem 4.4.5: the quotient-level realization function sends each lifted graph
vertex to the underlying point of `X.obj.left`. -/
@[simp] theorem coverGraphRealizationToTotalSpace_graphVertex (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary))
    (x : coverGraphVertexSet boundary X.obj.hom) :
    coverGraphRealizationToTotalSpace boundary X
        (graphVertex (liftedBoundary boundary X) x) = x.1 := by
  -- Evaluate the descended function on the vertex representative `Sum.inl x`.
  rfl

/-- Helper for Theorem 4.4.5: the quotient-level realization function sends each lifted graph edge
point to the corresponding point on the canonical lifted edge path. -/
@[simp] theorem coverGraphRealizationToTotalSpace_graphEdgePoint (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) (t : I) :
    coverGraphRealizationToTotalSpace boundary X
        (graphEdgePoint (liftedBoundary boundary X) e t) =
      liftedEdgePath boundary X e t := by
  -- Evaluate the descended function on the edge representative `Sum.inr (e, t)`.
  rfl

/-- Helper for Theorem 4.4.5: the quotient-level realization function still projects each lifted
edge point to the corresponding base-edge point. -/
theorem coverGraphRealizationToTotalSpace_proj_graphEdgePoint (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) (t : I) :
    X.obj.hom
        (coverGraphRealizationToTotalSpace boundary X
          (graphEdgePoint (liftedBoundary boundary X) e t)) =
      graphEdgePoint boundary e.1 t := by
  -- Rewrite to the lifted path and then apply the pointwise projection identity.
  rw [coverGraphRealizationToTotalSpace_graphEdgePoint]
  exact congrFun (liftedEdgePath_lifts boundary X e) t

/-- Helper for Theorem 4.4.5: the quotient-level lifted graph projects back to the base graph by
forgetting which point of the covering fiber chose the lifted edge. -/
noncomputable def coverGraphProjection (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary)) :
    graphRealization (liftedBoundary boundary X) → graphRealization boundary :=
  X.obj.hom ∘ coverGraphRealizationToTotalSpace boundary X

/-- Helper for Theorem 4.4.5: on lifted vertices, `coverGraphProjection` agrees with the original
covering map `X.obj.hom`. -/
@[simp] theorem coverGraphProjection_graphVertex (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary))
    (x : coverGraphVertexSet boundary X.obj.hom) :
    coverGraphProjection boundary X
        (graphVertex (liftedBoundary boundary X) x) = X.obj.hom x.1 := by
  -- The projection first realizes the lifted vertex in the total space and then applies the
  -- covering map back to the base.
  rfl

/-- Helper for Theorem 4.4.5: every lifted vertex projects to an actual base vertex of
`graphRealization boundary`. -/
theorem coverGraphProjection_graphVertex_eq_graphVertex (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary))
    (x : coverGraphVertexSet boundary X.obj.hom) :
    ∃ b : B₀,
      coverGraphProjection boundary X
          (graphVertex (liftedBoundary boundary X) x) = graphVertex boundary b := by
  -- Unpack the defining fiber condition on `x` and rewrite the normalized projection formula.
  rcases coverGraphVertexSet_exists_vertex boundary X.obj.hom x with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  simpa using (coverGraphProjection_graphVertex boundary X x).trans hb

/-- Helper for Theorem 4.4.5: on lifted edge points, `coverGraphProjection` forgets the chosen
lift and returns the corresponding base-edge point. -/
@[simp] theorem coverGraphProjection_graphEdgePoint (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) (t : I) :
    coverGraphProjection boundary X
        (graphEdgePoint (liftedBoundary boundary X) e t) =
      graphEdgePoint boundary e.1 t := by
  -- The lifted edge already projects pointwise to the underlying base edge.
  exact coverGraphRealizationToTotalSpace_proj_graphEdgePoint boundary X e t

/-- Helper for Theorem 4.4.5: `coverGraphProjection` is definitionally the composition of the
canonical realization map to the total space with the covering projection. -/
theorem coverGraphProjection_eq_comp (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary)) :
    coverGraphProjection boundary X =
      X.obj.hom ∘ coverGraphRealizationToTotalSpace boundary X :=
  rfl

/-- Helper for Theorem 4.4.5: with the source-faithful discrete topology on lifted vertices and
edge indices, the raw realization map is continuous on the disjoint source sum. -/
theorem coverGraphRealizationRaw_continuous_sourceFaithful (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary)) :
    let _ : TopologicalSpace (coverGraphVertexSet boundary X.obj.hom) := ⊥
    let _ : TopologicalSpace (coverGraphEdgeIndex boundary X.obj.hom) := ⊥
    Continuous (coverGraphRealizationRaw boundary X) := by
  let _ : TopologicalSpace (coverGraphVertexSet boundary X.obj.hom) := ⊥
  let _ : TopologicalSpace (coverGraphEdgeIndex boundary X.obj.hom) := ⊥
  let _ : DiscreteTopology (coverGraphVertexSet boundary X.obj.hom) :=
    discreteTopology_bot (coverGraphVertexSet boundary X.obj.hom)
  let _ : DiscreteTopology (coverGraphEdgeIndex boundary X.obj.hom) :=
    discreteTopology_bot (coverGraphEdgeIndex boundary X.obj.hom)
  -- The vertex branch is continuous on a discrete source, and each right summand is the lifted
  -- edge path attached to a fixed lifted edge index.
  rw [continuous_sum_dom]
  constructor
  · exact continuous_of_discreteTopology
  · rw [continuous_prod_of_discrete_left]
    intro e
    simpa [coverGraphRealizationRaw] using (liftedEdgePath boundary X e).continuous

/-- Helper for Theorem 4.4.5: in the source-faithful quotient topology on the lifted graph, the
quotient-level realization map is obtained by descending the continuous raw realization map. -/
theorem coverGraphRealizationToTotalSpace_continuous (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary)) :
    let _ : TopologicalSpace (graphRealization (liftedBoundary boundary X)) :=
      graphRealizationSourceFaithfulTopologicalSpace (liftedBoundary boundary X)
    Continuous (coverGraphRealizationToTotalSpace boundary X) := by
  let _ : TopologicalSpace (coverGraphVertexSet boundary X.obj.hom) := ⊥
  let _ : TopologicalSpace (coverGraphEdgeIndex boundary X.obj.hom) := ⊥
  let _ : TopologicalSpace (graphRealization (liftedBoundary boundary X)) :=
    graphRealizationSourceFaithfulTopologicalSpace (liftedBoundary boundary X)
  -- Descend the continuous source-level realization map through the quotient defining the lifted
  -- graph realization.
  exact
    (coverGraphRealizationRaw_continuous_sourceFaithful boundary X).quotient_lift
      (coverGraphRealizationRaw_respectsBoundary boundary X)

/-- Helper for Theorem 4.4.5: the forgetful projection from the lifted graph realization to the
base graph is continuous in the source-faithful quotient topologies on both realizations. -/
theorem coverGraphProjection_continuous (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary)) :
    let _ : TopologicalSpace (graphRealization (liftedBoundary boundary X)) :=
      graphRealizationSourceFaithfulTopologicalSpace (liftedBoundary boundary X)
    Continuous (coverGraphProjection boundary X) := by
  let _ : TopologicalSpace (graphRealization (liftedBoundary boundary X)) :=
    graphRealizationSourceFaithfulTopologicalSpace (liftedBoundary boundary X)
  -- The projection factors through the canonical realization into the total space and then the
  -- original covering projection back to the base.
  simpa [coverGraphProjection_eq_comp] using
    (coveringMap_objHom boundary X).continuous.comp
      (coverGraphRealizationToTotalSpace_continuous boundary X)

/-- Helper for Theorem 4.4.5: every point of the total space lies on the realized lifted graph. -/
theorem coverGraphRealizationToTotalSpace_surjective (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary)) :
    Function.Surjective (coverGraphRealizationToTotalSpace boundary X) := by
  intro x
  obtain ⟨z, hz⟩ := Quotient.mk''_surjective (X.obj.hom x)
  cases z with
  | inl b =>
      -- A point over a base vertex is already represented by the corresponding lifted vertex.
      have hx : X.obj.hom x = graphVertex boundary b := by
        simpa [graphVertex, graphRealizationPoint] using hz.symm
      let xLift : coverGraphVertexSet boundary X.obj.hom := ⟨x, ⟨b, hx.symm⟩⟩
      refine ⟨graphVertex (liftedBoundary boundary X) xLift, ?_⟩
      simpa [xLift] using
        coverGraphRealizationToTotalSpace_graphVertex boundary X xLift
  | inr jt =>
      rcases jt with ⟨j, t⟩
      -- A point over an edge is recovered by the canonical lifted edge through that point.
      have hx : X.obj.hom x = graphEdgePoint boundary j t := by
        simpa [graphEdgePoint, graphRealizationPoint] using hz.symm
      let e : coverGraphEdgeIndex boundary X.obj.hom :=
        liftedEdgeIndexOfPoint boundary X j t x hx
      refine ⟨graphEdgePoint (liftedBoundary boundary X) e t, ?_⟩
      simpa [e] using liftedEdgeIndexOfPoint_spec boundary X j t x hx

/-- Helper for Theorem 4.4.5: the descended realization map is injective because the quotient
kernel has already been identified combinatorially. -/
theorem coverGraphRealizationToTotalSpace_injective (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary)) :
    Function.Injective (coverGraphRealizationToTotalSpace boundary X) := by
  intro q₁ q₂ hq
  refine Quotient.inductionOn₂ q₁ q₂ ?_ hq
  intro a b hab
  -- Equal images of representatives force the lifted-boundary setoid relation, hence equality in
  -- the quotient graph realization.
  exact Quotient.sound ((coverGraphRealizationRaw_eq_iff_setoid boundary X a b).2 hab)

/-- Helper for Theorem 4.4.5: once the descended realization map is known to be a local
homeomorphism, the already-proved bijectivity upgrades it to a homeomorphism. -/
theorem coverGraphRealizationToTotalSpace_homeomorph_of_isLocalHomeomorph
    (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary))
    (hLocal : IsLocalHomeomorph (coverGraphRealizationToTotalSpace boundary X)) :
    ∃ hE : graphRealization (liftedBoundary boundary X) ≃ₜ X.obj.left,
      (hE : graphRealization (liftedBoundary boundary X) → X.obj.left) =
        coverGraphRealizationToTotalSpace boundary X := by
  let e :
      graphRealization (liftedBoundary boundary X) ≃ X.obj.left :=
    Equiv.ofBijective (coverGraphRealizationToTotalSpace boundary X)
      ⟨coverGraphRealizationToTotalSpace_injective boundary X,
        coverGraphRealizationToTotalSpace_surjective boundary X⟩
  -- A bijective local homeomorphism is a homeomorphism with the same underlying map.
  refine ⟨hLocal.toHomeomorphOfBijective e.bijective, ?_⟩
  rfl

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the quotient of the raw lifted-graph
comparison map gives the canonical realization map into the total space. -/
noncomputable def sourceFaithfulCoverGraphRealizationToTotalSpace
    (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary)) :
    graphRealization (sourceFaithfulLiftedBoundary boundary X) → X.obj.left :=
  Quotient.lift (sourceFaithfulCoverGraphRealizationRaw boundary X)
    (sourceFaithfulCoverGraphRealizationRaw_respectsBoundary boundary X)

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the descended realization map sends
each lifted graph vertex to its underlying point of `X.obj.left`. -/
@[simp] theorem sourceFaithfulCoverGraphRealizationToTotalSpace_graphVertex
    (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary))
    (x : coverGraphVertexSet boundary X.obj.hom) :
    sourceFaithfulCoverGraphRealizationToTotalSpace boundary X
        (graphVertex (sourceFaithfulLiftedBoundary boundary X) x) = x.1 := by
  -- Evaluate the descended function on the vertex representative `Sum.inl x`.
  rfl

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the descended realization map sends
each lifted graph edge point to the corresponding point on the canonical lifted edge. -/
@[simp] theorem sourceFaithfulCoverGraphRealizationToTotalSpace_graphEdgePoint
    (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) (t : I) :
    sourceFaithfulCoverGraphRealizationToTotalSpace boundary X
        (graphEdgePoint (sourceFaithfulLiftedBoundary boundary X) e t) =
      liftedEdgePathSourceFaithful boundary X e t := by
  -- Evaluate the descended function on the edge representative `Sum.inr (e, t)`.
  rfl

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the descended realization map still
projects each lifted graph edge point to the corresponding base-edge point. -/
theorem sourceFaithfulCoverGraphRealizationToTotalSpace_proj_graphEdgePoint
    (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) (t : I) :
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    X.obj.hom
        (sourceFaithfulCoverGraphRealizationToTotalSpace boundary X
          (graphEdgePoint (sourceFaithfulLiftedBoundary boundary X) e t)) =
      graphEdgePoint boundary e.1 t := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  -- Rewrite to the lifted edge formula and then apply the pointwise projection identity.
  rw [sourceFaithfulCoverGraphRealizationToTotalSpace_graphEdgePoint]
  exact congrFun (liftedEdgePathSourceFaithful_lifts boundary X e) t

/-- Helper for Theorem 4.4.5: in the source-faithful owner, projecting a fixed lifted open edge
segment recovers exactly the corresponding base open edge segment. -/
theorem sourceFaithfulCoverGraphProjection_image_edgeOpenSegment
    (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary))
    (e : coverGraphEdgeIndex boundary X.obj.hom) (a b : I) :
    let boundaryE := sourceFaithfulLiftedBoundary boundary X
    (fun q : graphRealization boundaryE ↦
        X.obj.hom (sourceFaithfulCoverGraphRealizationToTotalSpace boundary X q)) ''
        edgeOpenSegmentSet boundaryE e a b =
      edgeOpenSegmentSet boundary e.1 a b := by
  let boundaryE := sourceFaithfulLiftedBoundary boundary X
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases hq with ⟨z, hz, rfl⟩
    rcases hz with ⟨t, ht, rfl⟩
    rcases ht with ⟨u, hu, rfl⟩
    -- Normalize the projected lifted edge point to the underlying base edge point.
    change
      (fun q : graphRealization boundaryE ↦
          X.obj.hom (sourceFaithfulCoverGraphRealizationToTotalSpace boundary X q))
        (graphEdgePoint boundaryE e u) ∈
        edgeOpenSegmentSet boundary e.1 a b
    have hproj :
        (fun q : graphRealization boundaryE ↦
            X.obj.hom (sourceFaithfulCoverGraphRealizationToTotalSpace boundary X q))
          (graphEdgePoint boundaryE e u) =
          graphEdgePoint boundary e.1 u := by
      simpa [boundaryE] using
        sourceFaithfulCoverGraphRealizationToTotalSpace_proj_graphEdgePoint boundary X e u
    rw [hproj]
    exact graphEdgePoint_mem_edgeOpenSegment boundary e.1 hu.1 hu.2
  · intro hy
    rcases hy with ⟨z, hz, rfl⟩
    rcases hz with ⟨t, ht, rfl⟩
    rcases ht with ⟨u, hu, rfl⟩
    -- Reuse the same edge parameter on the chosen lifted edge index upstairs.
    refine ⟨graphEdgePoint boundaryE e u, ?_, ?_⟩
    · exact graphEdgePoint_mem_edgeOpenSegment boundaryE e hu.1 hu.2
    · have hproj :
          (fun q : graphRealization boundaryE ↦
              X.obj.hom (sourceFaithfulCoverGraphRealizationToTotalSpace boundary X q))
            (graphEdgePoint boundaryE e u) =
            graphEdgePoint boundary e.1 u := by
        simpa [boundaryE] using
          sourceFaithfulCoverGraphRealizationToTotalSpace_proj_graphEdgePoint boundary X e u
      simpa [graphEdgePoint, graphRealizationPoint] using hproj

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the raw comparison map is continuous
on the disjoint source sum with discrete lifted vertices and lifted edge indices. -/
theorem sourceFaithfulCoverGraphRealizationRaw_continuous_sourceFaithful
    (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary)) :
    let _ : TopologicalSpace (coverGraphVertexSet boundary X.obj.hom) := ⊥
    let _ : TopologicalSpace (coverGraphEdgeIndex boundary X.obj.hom) := ⊥
    Continuous (sourceFaithfulCoverGraphRealizationRaw boundary X) := by
  let _ : TopologicalSpace (coverGraphVertexSet boundary X.obj.hom) := ⊥
  let _ : TopologicalSpace (coverGraphEdgeIndex boundary X.obj.hom) := ⊥
  let _ : DiscreteTopology (coverGraphVertexSet boundary X.obj.hom) :=
    discreteTopology_bot (coverGraphVertexSet boundary X.obj.hom)
  let _ : DiscreteTopology (coverGraphEdgeIndex boundary X.obj.hom) :=
    discreteTopology_bot (coverGraphEdgeIndex boundary X.obj.hom)
  -- The vertex branch is discrete, and each edge slice is the canonical lifted edge path.
  rw [continuous_sum_dom]
  constructor
  · exact continuous_of_discreteTopology
  · rw [continuous_prod_of_discrete_left]
    intro e
    simpa [sourceFaithfulCoverGraphRealizationRaw] using
      (liftedEdgePathSourceFaithful boundary X e).continuous

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the descended realization map is
continuous for the source-faithful quotient topology on the lifted graph. -/
theorem sourceFaithfulCoverGraphRealizationToTotalSpace_continuous
    (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary)) :
    let _ : TopologicalSpace (graphRealization (sourceFaithfulLiftedBoundary boundary X)) :=
      graphRealizationSourceFaithfulTopologicalSpace (sourceFaithfulLiftedBoundary boundary X)
    Continuous (sourceFaithfulCoverGraphRealizationToTotalSpace boundary X) := by
  let _ : TopologicalSpace (coverGraphVertexSet boundary X.obj.hom) := ⊥
  let _ : TopologicalSpace (coverGraphEdgeIndex boundary X.obj.hom) := ⊥
  let _ : TopologicalSpace (graphRealization (sourceFaithfulLiftedBoundary boundary X)) :=
    graphRealizationSourceFaithfulTopologicalSpace (sourceFaithfulLiftedBoundary boundary X)
  -- Descend the continuous raw comparison map through the source-faithful quotient realization.
  exact
    (sourceFaithfulCoverGraphRealizationRaw_continuous_sourceFaithful boundary X).quotient_lift
      (sourceFaithfulCoverGraphRealizationRaw_respectsBoundary boundary X)

/-- Helper for Theorem 4.4.5: in the source-faithful owner, every point of the total space lies on
the realized lifted graph. -/
theorem sourceFaithfulCoverGraphRealizationToTotalSpace_surjective
    (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary)) :
    Function.Surjective (sourceFaithfulCoverGraphRealizationToTotalSpace boundary X) := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  intro x
  obtain ⟨z, hz⟩ := Quotient.mk''_surjective (X.obj.hom x)
  cases z with
  | inl b =>
      -- A point over a base vertex is represented by the corresponding lifted vertex.
      have hx : X.obj.hom x = graphVertex boundary b := by
        simpa [graphVertex, graphRealizationPoint] using hz.symm
      let xLift : coverGraphVertexSet boundary X.obj.hom := ⟨x, ⟨b, hx.symm⟩⟩
      refine ⟨graphVertex (sourceFaithfulLiftedBoundary boundary X) xLift, ?_⟩
      simpa [xLift] using
        sourceFaithfulCoverGraphRealizationToTotalSpace_graphVertex boundary X xLift
  | inr jt =>
      rcases jt with ⟨j, t⟩
      -- A point over an edge is recovered by the canonical lifted edge through that point.
      have hx : X.obj.hom x = graphEdgePoint boundary j t := by
        simpa [graphEdgePoint, graphRealizationPoint] using hz.symm
      let e : coverGraphEdgeIndex boundary X.obj.hom :=
        liftedEdgeIndexOfPointSourceFaithful boundary X j t x hx
      refine ⟨graphEdgePoint (sourceFaithfulLiftedBoundary boundary X) e t, ?_⟩
      simpa [e] using liftedEdgeIndexOfPointSourceFaithful_spec boundary X j t x hx

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the raw source-sum comparison map is
already surjective before quotienting by the lifted-boundary relation. -/
theorem sourceFaithfulCoverGraphRealizationRaw_surjective
    (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary)) :
    let _ : TopologicalSpace (coverGraphVertexSet boundary X.obj.hom) := ⊥
    let _ : TopologicalSpace (coverGraphEdgeIndex boundary X.obj.hom) := ⊥
    Function.Surjective (sourceFaithfulCoverGraphRealizationRaw boundary X) := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  let _ : TopologicalSpace (coverGraphVertexSet boundary X.obj.hom) := ⊥
  let _ : TopologicalSpace (coverGraphEdgeIndex boundary X.obj.hom) := ⊥
  show Function.Surjective (sourceFaithfulCoverGraphRealizationRaw boundary X)
  intro x
  obtain ⟨q, hq⟩ := sourceFaithfulCoverGraphRealizationToTotalSpace_surjective boundary X x
  -- Peel off one quotient representative to witness surjectivity already on the raw source sum.
  refine Quotient.inductionOn q ?_ hq
  intro a ha
  refine ⟨a, ?_⟩
  simpa [sourceFaithfulCoverGraphRealizationToTotalSpace] using ha

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the descended realization map is
injective because the quotient kernel has already been identified combinatorially. -/
theorem sourceFaithfulCoverGraphRealizationToTotalSpace_injective
    (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary)) :
    Function.Injective (sourceFaithfulCoverGraphRealizationToTotalSpace boundary X) := by
  intro q₁ q₂ hq
  refine Quotient.inductionOn₂ q₁ q₂ ?_ hq
  intro a b hab
  -- Equal images of representatives force the source-faithful lifted-boundary setoid relation.
  exact Quotient.sound
    ((sourceFaithfulCoverGraphRealizationRaw_eq_iff_setoid boundary X a b).2 hab)

/-- Helper for Theorem 4.4.5: the remaining topological step is to show that the raw source-sum
comparison map is the quotient map for the lifted-boundary relation. -/
theorem sourceFaithfulCoverGraphRealizationRaw_isQuotientMap
    (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary)) :
    let _ : TopologicalSpace (coverGraphVertexSet boundary X.obj.hom) := ⊥
    let _ : TopologicalSpace (coverGraphEdgeIndex boundary X.obj.hom) := ⊥
    Topology.IsQuotientMap (sourceFaithfulCoverGraphRealizationRaw boundary X) := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  let _ : TopologicalSpace (coverGraphVertexSet boundary X.obj.hom) := ⊥
  let _ : TopologicalSpace (coverGraphEdgeIndex boundary X.obj.hom) := ⊥
  -- Route correction: the remaining work belongs on the raw source sum, not on the descended map.
  -- TODO: prove the quotient criterion by combining raw edge-slice and raw vertex-star image-open
  -- lemmas with `sourceFaithfulCoverGraphRealizationRaw_eq_iff_setoid` to saturate neighborhoods.
  sorry

/-- Helper for Theorem 4.4.5: in the source-faithful owner, the descended realization map should
be the required graph-realization package for the total space. -/
theorem sourceFaithfulCoverGraphRealizationToTotalSpace_homeomorph
    (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary)) :
    let boundaryE := sourceFaithfulLiftedBoundary boundary X
    let _ : TopologicalSpace (graphRealization boundaryE) :=
      graphRealizationSourceFaithfulTopologicalSpace boundaryE
    ∃ hE : graphRealization boundaryE ≃ₜ X.obj.left,
      IsCoverGraphRealization boundary X.obj.hom boundaryE hE ∧
        ConnectedSpace (graphRealization boundaryE) := by
  let boundaryE := sourceFaithfulLiftedBoundary boundary X
  let _ : TopologicalSpace (coverGraphVertexSet boundary X.obj.hom) := ⊥
  let _ : TopologicalSpace (coverGraphEdgeIndex boundary X.obj.hom) := ⊥
  let _ : TopologicalSpace (graphRealization boundaryE) :=
    graphRealizationSourceFaithfulTopologicalSpace boundaryE
  let qRaw :
      C(coverGraphVertexSet boundary X.obj.hom ⊕
          (coverGraphEdgeIndex boundary X.obj.hom × I), X.obj.left) :=
    ⟨sourceFaithfulCoverGraphRealizationRaw boundary X,
      sourceFaithfulCoverGraphRealizationRaw_continuous_sourceFaithful boundary X⟩
  have hqRaw :
      Topology.IsQuotientMap (sourceFaithfulCoverGraphRealizationRaw boundary X) :=
    sourceFaithfulCoverGraphRealizationRaw_isQuotientMap boundary X
  let hE : graphRealization boundaryE ≃ₜ X.obj.left :=
    quotientHomeomorphOfRelIff qRaw hqRaw
      (graphRealizationSetoid boundaryE)
      (fun a b ↦ sourceFaithfulCoverGraphRealizationRaw_eq_iff_setoid boundary X a b)
  have hhE :
      (hE : graphRealization boundaryE → X.obj.left) =
        sourceFaithfulCoverGraphRealizationToTotalSpace boundary X := by
    funext q
    -- Both maps descend the same raw comparison map, so they agree on every quotient class.
    refine Quotient.inductionOn q ?_
    intro a
    exact
      quotientHomeomorphOfRelIff_apply_mk qRaw hqRaw
        (graphRealizationSetoid boundaryE)
        (fun a b ↦ sourceFaithfulCoverGraphRealizationRaw_eq_iff_setoid boundary X a b) a
  refine ⟨hE, ?_⟩
  constructor
  · constructor
    · intro x
      -- Rewrite the quotient homeomorphism back to the descended comparison map on vertices.
      exact
        (congrArg
            (fun f : graphRealization boundaryE → X.obj.left ↦
              f (graphVertex boundaryE x))
            hhE).trans
          (sourceFaithfulCoverGraphRealizationToTotalSpace_graphVertex boundary X x)
    constructor
    · intro e
      -- The lifted boundary was defined to start each lifted edge at its chosen fiber point.
      exact sourceFaithfulLiftedBoundaryMap_zero boundary X e
    · intro e t
      -- Rewrite the homeomorphism back to the descended map and then project to the base edge.
      exact
        (congrArg X.obj.hom
            (congrArg
              (fun f : graphRealization boundaryE → X.obj.left ↦
                f (graphEdgePoint boundaryE e t))
              hhE)).trans
          (sourceFaithfulCoverGraphRealizationToTotalSpace_proj_graphEdgePoint boundary X e t)
  · let _ : ConnectedSpace X.obj.left := PathConnectedSpace.connectedSpace
    -- Transport connectedness back across the inverse homeomorphism.
    let hSurj : Function.Surjective hE.symm := hE.symm.surjective
    exact hSurj.connectedSpace hE.symm.continuous

/-- Helper for Theorem 4.4.5: once the canonical quotient-level map is upgraded to a
homeomorphism, the lifted boundary data automatically satisfies the required graph-realization
equations and connectedness conclusion. -/
theorem coverGraphRealizationData_ofHomeomorph (boundary : J ↪ Fin 2 → B₀)
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary))
    (hE : graphRealization (liftedBoundary boundary X) ≃ₜ X.obj.left)
    (hhE : (hE : graphRealization (liftedBoundary boundary X) → X.obj.left) =
      coverGraphRealizationToTotalSpace boundary X) :
    IsCoverGraphRealization boundary X.obj.hom (liftedBoundary boundary X) hE ∧
      ConnectedSpace (graphRealization (liftedBoundary boundary X)) := by
  constructor
  · constructor
    · intro x
      -- Rewrite the homeomorphism to the canonical quotient-level realization map on vertices.
      exact
        (congrArg
            (fun f :
              graphRealization (liftedBoundary boundary X) → X.obj.left ↦
                f (graphVertex (liftedBoundary boundary X) x))
            hhE).trans
          (coverGraphRealizationToTotalSpace_graphVertex boundary X x)
    constructor
    · intro e
      -- The lifted boundary was defined to start each lifted edge at its chosen fiber point.
      exact liftedBoundaryMap_zero boundary X e
    · intro e t
      -- Rewrite to the canonical lifted-edge formula and project back to the base graph.
      exact
        congrArg X.obj.hom
            (congrArg
              (fun f :
                graphRealization (liftedBoundary boundary X) → X.obj.left ↦
                  f (graphEdgePoint (liftedBoundary boundary X) e t))
              hhE) |>.trans
          (coverGraphRealizationToTotalSpace_proj_graphEdgePoint boundary X e t)
  · let _ : ConnectedSpace X.obj.left := PathConnectedSpace.connectedSpace
    -- Transport connectedness back across the inverse homeomorphism.
    let hSurj : Function.Surjective hE.symm := hE.symm.surjective
    exact hSurj.connectedSpace hE.symm.continuous

/-- Theorem 4.4.5::statement_repair::1. If
`X : ConnectedCoveringSpace (graphRealization boundary)` is a connected covering of the connected
graph `graphRealization boundary` equipped with the source-faithful quotient topology, then the
total space `X.obj.left` admits a connected graph realization whose vertex set is
`coverGraphVertexSet boundary X.obj.hom` and whose edges are indexed by
`coverGraphEdgeIndex boundary X.obj.hom`, i.e. by pairs `(j, e)` with `j : J` and
`e ∈ X.obj.hom ⁻¹' {graphVertex boundary (boundary j 0)}`. -/
theorem exists_coverGraphRealization
    (boundary : J ↪ Fin 2 → B₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)]
    (X :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedCoveringSpace (graphRealization boundary)) :
    ∃ boundaryE :
        coverGraphEdgeIndex boundary X.obj.hom ↪ Fin 2 → coverGraphVertexSet boundary X.obj.hom,
      let _ : TopologicalSpace (graphRealization boundaryE) :=
        graphRealizationSourceFaithfulTopologicalSpace boundaryE
      ∃ hE : graphRealization boundaryE ≃ₜ X.obj.left,
        IsCoverGraphRealization boundary X.obj.hom boundaryE hE ∧
          ConnectedSpace (graphRealization boundaryE) := by
  -- Route correction: stay entirely in the source-faithful owner and package the already-closed
  -- descended source-faithful realization map. The remaining blocker is now the single
  -- source-faithful homeomorphism theorem above.
  refine ⟨sourceFaithfulLiftedBoundary boundary X, ?_⟩
  let boundaryE := sourceFaithfulLiftedBoundary boundary X
  let _ : TopologicalSpace (graphRealization boundaryE) :=
    graphRealizationSourceFaithfulTopologicalSpace boundaryE
  simpa [boundaryE] using
    sourceFaithfulCoverGraphRealizationToTotalSpace_homeomorph boundary X

end ConnectedCoveringSpace
