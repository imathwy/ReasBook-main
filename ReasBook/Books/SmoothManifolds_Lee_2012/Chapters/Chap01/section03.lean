import Mathlib.Data.Set.Prod
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Tactic.Recall
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Homeomorph.Lemmas

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_3_extra_1 (from Chap01/Sec01_03) -/
noncomputable section

open Set
open scoped Manifold Topology

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M]

/-- A smooth coordinate ball is the source of a smooth chart whose image is an open metric ball in
the model space. -/
def IsSmoothCoordinateBall (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M] (B : Set M) : Prop :=
  ∃ φ : OpenPartialHomeomorph M E,
    φ ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M ∧
      φ.source = B ∧ φ.IsCoordinateBall

/-- Definition 1.3-extra-1: a regular coordinate ball is a subset whose closure is contained in a
larger smooth chart whose image is a larger Euclidean ball and which sends the subset and its
closure to the corresponding concentric open and closed balls. -/
def IsRegularCoordinateBall (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M] (B : Set M) : Prop :=
  ∃ chart : OpenPartialHomeomorph M E,
    chart ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M ∧
      closure B ⊆ chart.source ∧
      ∃ r r' : ℝ,
        0 < r ∧
          r < r' ∧
          chart '' B = Metric.ball (0 : E) r ∧
          chart '' closure B = Metric.closedBall (0 : E) r ∧
          chart.target = Metric.ball (0 : E) r'

/-- A regular coordinate ball is contained in a surrounding smooth coordinate ball. -/
theorem IsRegularCoordinateBall.exists_smoothCoordinateBall_superset {B : Set M}
    (hB : IsRegularCoordinateBall E B) :
    ∃ B' : Set M, IsSmoothCoordinateBall E B' ∧ closure B ⊆ B' :=
  by
    rcases hB with ⟨chart, hchart, hclosure, r, r', hr, hr', -, -, htarget⟩
    refine ⟨chart.source, ⟨chart, hchart, rfl, ?_⟩, hclosure⟩
    exact chart.isCoordinateBall_of_target_eq_ball (0 : E) r' (lt_trans hr hr') htarget

/-! ### Definition_1_extra_3 (from Chap01/Sec01) -/
universe u

/- Definition 1-extra-3: the canonical mathlib notions for the recalled properties of a
topological space are `ConnectedSpace X`, `PathConnectedSpace X`, and
`LocPathConnectedSpace X`. -/
recall ConnectedSpace (X : Type u) [TopologicalSpace X] : Prop
recall PathConnectedSpace (X : Type u) [TopologicalSpace X] : Prop
recall LocPathConnectedSpace (X : Type u) [TopologicalSpace X] : Prop

/-! ### Example_1_3 (from Chap01/Sec01) -/
universe u v

open Set Topology

variable {X : Type u} {Y : Type v}

/-- The canonical graph parametrization of `f` over `U`. -/
def graphMap (U : Set X) (f : X → Y) : U → X × Y := fun x ↦ ((x : X), f x)

/-- The range of the canonical graph parametrization is exactly the graph over `U`. -/
theorem range_graphMap_eq_graphOn (U : Set X) (f : X → Y) :
    range (graphMap U f) = U.graphOn f := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    simp [graphMap]
  · intro hp
    rcases mem_graphOn.1 hp with ⟨hpU, hpgraph⟩
    refine ⟨⟨p.1, hpU⟩, ?_⟩
    ext <;> simp [graphMap, hpgraph]

section

variable [TopologicalSpace X] [TopologicalSpace Y]

/-- Continuity on `U` makes the canonical graph parametrization into an embedding. -/
theorem graphMap_isEmbedding (U : Set X) (f : X → Y) (hf : ContinuousOn f U) :
    IsEmbedding (graphMap U f) := by
  have hcont : Continuous (fun x : U ↦ f x) :=
    continuousOn_iff_continuous_restrict.1 hf
  have hgraph : IsEmbedding (fun x : U ↦ (x, f x)) :=
    isEmbedding_graph hcont
  have hprod : IsEmbedding (Prod.map ((↑) : U → X) (id : Y → Y)) :=
    IsEmbedding.subtypeVal.prodMap .id
  simpa [graphMap, Function.comp] using hprod.comp hgraph

/-- Example 1.3: graph coordinates identify the graph of a continuous function on `U` with the
domain `U` itself. -/
noncomputable def graph_coordinates (U : Set X) (f : X → Y) (hf : ContinuousOn f U) :
    U.graphOn f ≃ₜ U where
  toFun p := ⟨p.1.1, (mem_graphOn.1 p.2).1⟩
  invFun x := ⟨graphMap U f x, by
    simp [graphMap, mem_graphOn, x.2]⟩
  left_inv p := by
    apply Subtype.ext
    ext <;> simp [graphMap, (mem_graphOn.1 p.2).2]
  right_inv x := by
    rfl
  continuous_toFun := continuous_subtype_val.fst.subtype_mk _
  continuous_invFun := by
    have hcont : Continuous (fun x : U ↦ f x) :=
      continuousOn_iff_continuous_restrict.1 hf
    exact (continuous_subtype_val.prodMk hcont).subtype_mk _

/-- The inverse of graph coordinates sends `x` to `(x, f x)` on the graph. -/
theorem graph_coordinates_symm_apply (U : Set X) (f : X → Y) (hf : ContinuousOn f U)
    (x : U) :
    ((graph_coordinates U f hf).symm x : X × Y) = ((x : X), f x) :=
  rfl

/-- The graph-coordinate homeomorphism is projection to the first coordinate. -/
theorem graph_coordinates_apply (U : Set X) (f : X → Y) (hf : ContinuousOn f U)
    (p : U.graphOn f) :
    ((graph_coordinates U f hf p : U) : X) = p.1.1 :=
  rfl

end

/-! ### Problem_1_3 (from Chap01/Sec01_07) -/
universe u

/-- A `σ`-compact Hausdorff space locally modelled on `ℝ^n` carries the canonical
`TopologicalManifold` structure. -/
@[reducible] def topologicalManifold_of_sigmaCompactSpace (n : ℕ) {M : Type u}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [SigmaCompactSpace M] : TopologicalManifold n M :=
  let _ : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin n)) M
  topologicalManifoldOfChartedSpace n M

/-- A topological manifold is `σ`-compact. -/
theorem sigmaCompactSpace_of_topologicalManifold (n : ℕ) {M : Type u} [TopologicalSpace M]
    [TopologicalManifold n M] : SigmaCompactSpace M := by
  letI : LocallyCompactSpace M :=
    TopologicalManifold.locallyCompactSpace_of_topologicalManifold n M
  infer_instance

/-- Problem 1-3: for a Hausdorff space locally modelled on `ℝ^n`, second countability is
equivalent to `σ`-compactness. -/
theorem secondCountableTopology_iff_sigmaCompactSpace_of_t2_euclidean_chartedSpace {n : ℕ}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    SecondCountableTopology M ↔ SigmaCompactSpace M := by
  constructor
  · intro hM
    letI : SecondCountableTopology M := hM
    letI : TopologicalManifold n M := topologicalManifoldOfChartedSpace n M
    exact sigmaCompactSpace_of_topologicalManifold n
  · intro hM
    letI : SigmaCompactSpace M := hM
    letI : TopologicalManifold n M := topologicalManifold_of_sigmaCompactSpace n
    infer_instance
