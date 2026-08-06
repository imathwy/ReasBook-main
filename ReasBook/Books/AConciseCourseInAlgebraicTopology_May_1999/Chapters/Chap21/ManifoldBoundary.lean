import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.Dimension.Finrank

open scoped Manifold

universe u

/-- The boundary subtype `∂M` of an `n`-manifold with boundary `M`. -/
abbrev manifoldBoundary (n : ℕ) [NeZero n] (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] : Set M :=
  (𝓡∂ n).boundary M

/-- Scoped notation for the canonical boundary object `∂[n] M`. -/
scoped[Manifold] notation "∂[" n "]" M:max => manifoldBoundary n M

namespace ManifoldBoundary

/-- The boundary hyperplane `x₀ = 0` inside `ℝ^(n + 1)`, used as a concrete boundary model for
`∂W`. -/
def boundaryHyperplane (n : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1))) where
  carrier := { x | x 0 = 0 }
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change x 0 = 0 at hx
    change y 0 = 0 at hy
    change x 0 + y 0 = 0
    simpa [hx, hy]
  smul_mem' := by
    intro a x hx
    change x 0 = 0 at hx
    change a * x 0 = 0
    simpa [hx]

/-- The boundary hyperplane sits inside the Euclidean half-space by the obvious inclusion. -/
def boundaryHyperplaneToHalfSpace (n : ℕ) :
    boundaryHyperplane n → EuclideanHalfSpace (n + 1) :=
  fun x ↦ ⟨x.1, by
    have hx : x.1 0 = 0 := x.2
    simpa [hx]⟩

@[simp] theorem boundaryHyperplaneToHalfSpace_val (n : ℕ) (x : boundaryHyperplane n) :
    (boundaryHyperplaneToHalfSpace n x).1 = x.1 :=
  rfl

theorem continuous_boundaryHyperplaneToHalfSpace (n : ℕ) :
    Continuous fun x : boundaryHyperplane n ↦ boundaryHyperplaneToHalfSpace n x :=
  Continuous.subtype_mk continuous_subtype_val fun x ↦ by
    have hx : x.1 0 = 0 := x.2
    simpa [hx]

section BoundaryChartedSpace

variable {n : ℕ} {W : Type u} [TopologicalSpace W]
variable [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
variable [IsManifold (𝓡∂ (n + 1)) (n + 1) W]

noncomputable abbrev boundaryAmbientChart (x : manifoldBoundary (n + 1) W) :
    OpenPartialHomeomorph W (EuclideanHalfSpace (n + 1)) :=
  chartAt (EuclideanHalfSpace (n + 1)) x.1

lemma boundaryChart_firstCoordinate_zero (x z : manifoldBoundary (n + 1) W)
    (hz : z.1 ∈ (boundaryAmbientChart x).source) :
    0 = ((boundaryAmbientChart x z.1 : EuclideanHalfSpace (n + 1)).1 0) := by
  sorry

lemma boundaryPoint_of_boundaryTarget (x : manifoldBoundary (n + 1) W)
    {v : boundaryHyperplane n}
    (hv : boundaryHyperplaneToHalfSpace n v ∈ (boundaryAmbientChart x).target) :
    (𝓡∂ (n + 1)).IsBoundaryPoint
      ((boundaryAmbientChart x).symm (boundaryHyperplaneToHalfSpace n v)) := by
  sorry

/-- The preferred boundary chart obtained by restricting the ambient chart at a boundary point to
the boundary hyperplane model. -/
noncomputable def boundaryChartAt (x : manifoldBoundary (n + 1) W) :
    OpenPartialHomeomorph (manifoldBoundary (n + 1) W) (boundaryHyperplane n) := by
  classical
  let e := boundaryAmbientChart x
  let sourceSet : Set (manifoldBoundary (n + 1) W) := { z | z.1 ∈ e.source }
  let targetSet : Set (boundaryHyperplane n) := { y | boundaryHyperplaneToHalfSpace n y ∈ e.target }
  refine
    { source := sourceSet
      target := targetSet
      toFun := fun z ↦
        if hz : z ∈ sourceSet then
          ⟨(e z.1).1, (boundaryChart_firstCoordinate_zero x z hz).symm⟩
        else
          0
      invFun := fun y ↦
        if hy : y ∈ targetSet then
          ⟨e.symm (boundaryHyperplaneToHalfSpace n y), boundaryPoint_of_boundaryTarget x hy⟩
        else
          x
      map_source' := by
        sorry
      map_target' := by
        sorry
      left_inv' := by
        sorry
      right_inv' := by
        sorry
      open_source := by
        simpa [sourceSet] using e.open_source.preimage continuous_subtype_val
      open_target := by
        simpa [targetSet] using e.open_target.preimage (continuous_boundaryHyperplaneToHalfSpace n)
      continuousOn_toFun := by
        sorry
      continuousOn_invFun := by
        sorry
    }

/-- The boundary of a manifold-with-boundary carries the charted-space structure induced from the
ambient charts, using the boundary hyperplane as model space. -/
noncomputable instance boundaryChartedSpace :
    ChartedSpace (boundaryHyperplane n) (manifoldBoundary (n + 1) W) where
  atlas := Set.range boundaryChartAt
  chartAt := boundaryChartAt
  mem_chart_source := by
    intro x
    change x.1 ∈ (boundaryAmbientChart x).source
    exact mem_chart_source (EuclideanHalfSpace (n + 1)) x.1
  chart_mem_atlas := by
    intro x
    exact ⟨x, rfl⟩

/-- The boundary hyperplane model is canonically homeomorphic to `EuclideanSpace ℝ (Fin n)` by
deleting the distinguished boundary coordinate. -/
noncomputable def boundaryHyperplaneLinearEquivEuclidean (n : ℕ) :
    boundaryHyperplane n ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun x := WithLp.toLp 2 (fun i : Fin n ↦ x.1.ofLp i.succ)
  map_add' x y := by
    rfl
  map_smul' a x := by
    rfl
  invFun v :=
    ⟨WithLp.toLp 2
        (fun i : Fin (n + 1) ↦ if h : i = 0 then 0 else v.ofLp (i.pred h)), by
      change
        (WithLp.toLp 2
          (fun i : Fin (n + 1) ↦ if h : i = 0 then 0 else v.ofLp (i.pred h))).ofLp 0 = 0
      simp⟩
  left_inv x := by
    apply Subtype.ext
    apply (WithLp.equiv 2 _).injective
    funext i
    by_cases h : i = 0
    · simpa [h] using x.2.symm
    · simp [h]
  right_inv v := by
    apply (WithLp.equiv 2 _).injective
    funext i
    simp

/-- The boundary hyperplane model is canonically homeomorphic to `EuclideanSpace ℝ (Fin n)` by
deleting the distinguished boundary coordinate. -/
noncomputable def boundaryHyperplaneHomeomorph (n : ℕ) :
    boundaryHyperplane n ≃ₜ EuclideanSpace ℝ (Fin n) where
  toFun := boundaryHyperplaneLinearEquivEuclidean n
  invFun := (boundaryHyperplaneLinearEquivEuclidean n).symm
  left_inv := (boundaryHyperplaneLinearEquivEuclidean n).left_inv
  right_inv := (boundaryHyperplaneLinearEquivEuclidean n).right_inv
  continuous_toFun := by
    sorry
  continuous_invFun := by
    sorry

/-- The boundary chart transported through `boundaryHyperplaneHomeomorph`, so the boundary is
presented in the canonical Euclidean model `𝓡 n`. -/
noncomputable def boundaryEuclideanChartAt (x : manifoldBoundary (n + 1) W) :
    OpenPartialHomeomorph (manifoldBoundary (n + 1) W) (EuclideanSpace ℝ (Fin n)) :=
  (boundaryChartAt x).trans ((boundaryHyperplaneHomeomorph n).toOpenPartialHomeomorph)

/-- The boundary of a manifold-with-boundary carries the charted-space structure induced from the
ambient charts and transported to the canonical Euclidean model `EuclideanSpace ℝ (Fin n)`. -/
noncomputable instance boundaryEuclideanChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (manifoldBoundary (n + 1) W) where
  atlas := Set.range boundaryEuclideanChartAt
  chartAt := boundaryEuclideanChartAt
  mem_chart_source := by
    intro x
    simp [boundaryEuclideanChartAt, OpenPartialHomeomorph.trans, boundaryChartAt,
      mem_chart_source]
  chart_mem_atlas := by
    intro x
    exact ⟨x, rfl⟩

/-- With the canonical Euclidean boundary model installed, the boundary of an `(n + 1)`-manifold
with boundary is itself an `n`-manifold. -/
instance boundary_isManifold [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n)] :
    IsManifold (𝓡 n) ⊤ (manifoldBoundary (n + 1) W) := by
  sorry

/-- The boundary of a compact manifold-with-boundary is compact. -/
instance boundaryCompactSpace [CompactSpace W] :
    CompactSpace (manifoldBoundary (n + 1) W) := by
  have hclosed : IsClosed (manifoldBoundary (n + 1) W) := by
    simpa [manifoldBoundary] using
      (ModelWithCorners.isClosed_boundary (I := 𝓡∂ (n + 1)) (n := n + 1) (M := W) (by simp))
  exact hclosed.isClosedEmbedding_subtypeVal.compactSpace

end BoundaryChartedSpace

end ManifoldBoundary
