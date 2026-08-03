module

public import Topology_Munkres_2000.Book.Exercise_20_2
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.ChartedSpace

public section

open Set

namespace RealProdLex

/-- The standard homeomorphism from `ℝ` to one-dimensional Euclidean space. -/
noncomputable def realHomeomorphEuclideanOne :
    ℝ ≃ₜ EuclideanSpace ℝ (Fin 1) :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr.toHomeomorph

/-- Helper for Exercise 8.99.4: the fiber coordinate sends its source into all of
one-dimensional Euclidean space. -/
lemma fiberCoordinate_mapsToTarget (x y : ℝ ×ₗ ℝ) :
    y ∈ {z : ℝ ×ₗ ℝ | z.1 = x.1} → realHomeomorphEuclideanOne y.2 ∈ univ := by
  intro _
  exact mem_univ _

/-- Helper for Exercise 8.99.4: the inverse fiber coordinate has the prescribed first
coordinate. -/
lemma fiberParameterization_mapsToSource (x : ℝ ×ₗ ℝ)
    (t : EuclideanSpace ℝ (Fin 1)) :
    t ∈ univ → (x.1, realHomeomorphEuclideanOne.symm t) ∈
      {z : ℝ ×ₗ ℝ | z.1 = x.1} := by
  intro _
  rfl

/-- Helper for Exercise 8.99.4: parameterizing a point of a vertical fiber by its second
coordinate recovers that point. -/
lemma fiberParameterization_leftInv (x y : ℝ ×ₗ ℝ) :
    y ∈ {z : ℝ ×ₗ ℝ | z.1 = x.1} →
      (x.1, realHomeomorphEuclideanOne.symm (realHomeomorphEuclideanOne y.2)) = y := by
  intro hy
  apply Prod.ext
  · exact hy.symm
  · exact realHomeomorphEuclideanOne.symm_apply_apply y.2

/-- Helper for Exercise 8.99.4: taking the coordinate of a parameterized vertical-fiber point
recovers the parameter. -/
lemma fiberParameterization_rightInv (x : ℝ ×ₗ ℝ)
    (t : EuclideanSpace ℝ (Fin 1)) :
    t ∈ univ →
      realHomeomorphEuclideanOne (x.1, realHomeomorphEuclideanOne.symm t).2 = t := by
  intro _
  exact realHomeomorphEuclideanOne.apply_symm_apply t

/-- Helper for Exercise 8.99.4: every vertical fiber in the lexicographically ordered real
plane is open. -/
lemma isOpen_verticalFiber (x : ℝ ×ₗ ℝ) :
    IsOpen {y : ℝ ×ₗ ℝ | y.1 = x.1} := by
  -- Vertical intervals form a neighborhood basis and stay inside the fiber.
  rw [isOpen_iff_mem_nhds]
  intro y hy
  refine (realProdLex_nhds_basis_verticalIntervals y).mem_iff.mpr ?_
  have hlower : (ofLex y).2 - 1 < (ofLex y).2 := sub_lt_self _ zero_lt_one
  have hupper : (ofLex y).2 < (ofLex y).2 + 1 := lt_add_of_pos_right _ zero_lt_one
  refine ⟨((ofLex y).2 - 1, (ofLex y).2 + 1),
    ⟨hlower, hupper⟩, ?_⟩
  intro z hz
  exact hz.1.trans hy

/-- Helper for Exercise 8.99.4: the Euclidean coordinate is continuous on every vertical
fiber. -/
lemma continuousOn_fiberCoordinate (x : ℝ ×ₗ ℝ) :
    ContinuousOn (fun y : ℝ ×ₗ ℝ ↦ realHomeomorphEuclideanOne y.2)
      {y : ℝ ×ₗ ℝ | y.1 = x.1} := by
  -- The second coordinate is continuous through the discrete-first-coordinate embedding.
  exact (realHomeomorphEuclideanOne.continuous.comp
    (continuous_snd.comp realProdLex_isEmbedding_discreteProduct.continuous)).continuousOn

/-- Helper for Exercise 8.99.4: the vertical-fiber parameterization by one-dimensional
Euclidean space is continuous. -/
lemma continuousOn_fiberParameterization (x : ℝ ×ₗ ℝ) :
    ContinuousOn (fun t : EuclideanSpace ℝ (Fin 1) ↦
      toLex (x.1, realHomeomorphEuclideanOne.symm t)) univ := by
  -- Check continuity after the inducing embedding into a discrete-real product.
  apply Continuous.continuousOn
  apply realProdLex_isEmbedding_discreteProduct.isInducing.continuous_iff.mpr
  have hfirst : Continuous (fun _ : EuclideanSpace ℝ (Fin 1) ↦
      WithTopology.toTopology (⊥ : TopologicalSpace ℝ) x.1) := continuous_const
  simpa only [Function.comp_def, ofLex_toLex] using
    (hfirst.prodMk realHomeomorphEuclideanOne.symm.continuous)

/-- The vertical fiber through `x` is a chart for the lexicographically ordered real plane. -/
noncomputable def fiberChart (x : ℝ ×ₗ ℝ) :
    OpenPartialHomeomorph (ℝ ×ₗ ℝ) (EuclideanSpace ℝ (Fin 1)) where
  toPartialEquiv :=
    { toFun := fun y ↦ realHomeomorphEuclideanOne y.2
      invFun := fun t ↦ (x.1, realHomeomorphEuclideanOne.symm t)
      source := {y | y.1 = x.1}
      target := univ
      map_source' := fiberCoordinate_mapsToTarget x
      map_target' := fiberParameterization_mapsToSource x
      left_inv' := fiberParameterization_leftInv x
      right_inv' := fiberParameterization_rightInv x }
  open_source := isOpen_verticalFiber x
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_fiberCoordinate x
  continuousOn_invFun := continuousOn_fiberParameterization x

/-- Helper for Exercise 8.99.4: each point lies in the source of its own vertical-fiber chart. -/
lemma mem_fiberChart_source (x : ℝ ×ₗ ℝ) : x ∈ (fiberChart x).source := by
  rfl

/-- Helper for Exercise 8.99.4: each selected vertical-fiber chart belongs to the fiber-chart
atlas. -/
lemma fiberChart_mem_atlas (x : ℝ ×ₗ ℝ) : fiberChart x ∈ range fiberChart := by
  exact mem_range_self x

/-- The lexicographically ordered real plane is locally modeled on one-dimensional
Euclidean space. -/
noncomputable instance instChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 1)) (ℝ ×ₗ ℝ) where
  atlas := range fiberChart
  chartAt := fiberChart
  mem_chart_source := mem_fiberChart_source
  chart_mem_atlas := fiberChart_mem_atlas

end RealProdLex
