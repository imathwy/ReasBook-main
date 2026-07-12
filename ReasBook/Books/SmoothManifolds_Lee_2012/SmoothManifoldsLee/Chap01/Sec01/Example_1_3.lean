import Mathlib.Data.Set.Prod
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Homeomorph.Lemmas

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
