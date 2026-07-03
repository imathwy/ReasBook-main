import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_1_36 (from Chap01/Sec01_04) -/
noncomputable section

-- Semantic search note: no `lean_leansearch` tool was available in this environment.
-- The statement surface below was checked against mathlib's `LinearMap.graph`,
-- `Submodule.prodEquivOfIsCompl`, `Submodule.projectionOnto`, and
-- `Mathlib/RingTheory/Grassmannian.lean`; the latter uses the algebraic-geometry quotient
-- convention rather than Lee's `k`-plane convention, so this file keeps the source-faithful
-- `Submodule`-based owner.

open scoped BigOperators

universe u

/-- The Grassmannian of `k`-planes in a real vector space `V`, in the sense of Lee's text: its
points are the `k`-dimensional linear subspaces of `V`. -/
def grassmannian (V : Type u) [AddCommGroup V] [Module ℝ V] (k : ℕ) :=
  { S : Submodule ℝ V // Module.finrank ℝ S = k }

namespace grassmannian

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {k : ℕ}
variable {P Q P' Q' : Submodule ℝ V}

/-- For a fixed complementary subspace `Q`, the corresponding Grassmannian chart domain consists
of the `k`-planes meeting `Q` trivially. -/
def chart_domain (Q : Submodule ℝ V) : Set (grassmannian V k) :=
  { S | Disjoint S.1 Q }

/-- The graph of a linear map `X : P → Q`, transported across a decomposition `V = P ⊕ Q`, has the
same dimension as `P`. -/
theorem graph_finrank
    (hPQ : IsCompl P Q) (hP : Module.finrank ℝ P = k) (X : P →ₗ[ℝ] Q) :
    Module.finrank ℝ
        ((LinearMap.graph X).map (P.prodEquivOfIsCompl Q hPQ).toLinearMap) = k := sorry

/-- The graph of a linear map `X : P → Q`, viewed as a `k`-plane in `V` through a complementary
decomposition `V = P ⊕ Q`. -/
def graph (hPQ : IsCompl P Q) (hP : Module.finrank ℝ P = k) (X : P →ₗ[ℝ] Q) :
    grassmannian V k :=
  ⟨(LinearMap.graph X).map (P.prodEquivOfIsCompl Q hPQ).toLinearMap,
    graph_finrank hPQ hP X⟩

/-- The graph of a linear map `X : P → Q` meets the complementary subspace `Q` trivially, so it
lies in the chart domain determined by `Q`. -/
theorem graph_mem_chart_domain
    (hPQ : IsCompl P Q) (hP : Module.finrank ℝ P = k) (X : P →ₗ[ℝ] Q) :
    graph hPQ hP X ∈ chart_domain Q := sorry

/-- If `S` is a `k`-plane whose intersection with `Q` is trivial, then projection onto `P` along
`Q` restricts to a linear isomorphism from `S` to `P`. -/
theorem chart_projection_bijective
    (hPQ : IsCompl P Q) (hP : Module.finrank ℝ P = k)
    (S : grassmannian V k) (hS : S ∈ chart_domain Q) :
    Function.Bijective (((P.projectionOnto Q hPQ).comp S.1.subtype)) := sorry

/-- The inverse to the restricted projection `S → P` for a `k`-plane `S` in the chart domain of
`Q`. -/
noncomputable def chart_linear_equiv
    (hPQ : IsCompl P Q) (hP : Module.finrank ℝ P = k)
    (S : grassmannian V k) (hS : S ∈ chart_domain Q) :
    S.1 ≃ₗ[ℝ] P :=
  LinearEquiv.ofBijective (((P.projectionOnto Q hPQ).comp S.1.subtype))
    (chart_projection_bijective hPQ hP S hS)

/-- The coordinate of a `k`-plane `S` in the chart determined by `V = P ⊕ Q`, obtained by writing
`S` as the graph of a linear map `P → Q`. -/
noncomputable def chart_fun
    (hPQ : IsCompl P Q) (hP : Module.finrank ℝ P = k)
    (S : grassmannian V k) (hS : S ∈ chart_domain Q) :
    P →ₗ[ℝ] Q :=
  (Q.projectionOnto P hPQ.symm).comp
    (S.1.subtype.comp (chart_linear_equiv hPQ hP S hS).symm.toLinearMap)

/-- Applying the graph construction to the coordinate map of a plane in the `Q`-chart recovers
that plane. -/
theorem chart_equiv_left_inv
    (hPQ : IsCompl P Q) (hP : Module.finrank ℝ P = k) :
    Function.LeftInverse
      (fun S : { S : grassmannian V k // S ∈ chart_domain Q } ↦
        chart_fun hPQ hP S.1 S.2)
      (fun X : P →ₗ[ℝ] Q ↦
        ⟨graph hPQ hP X, graph_mem_chart_domain hPQ hP X⟩) := sorry

/-- Applying the coordinate map to the graph of `X : P → Q` recovers the original linear map. -/
theorem chart_equiv_right_inv
    (hPQ : IsCompl P Q) (hP : Module.finrank ℝ P = k) :
    Function.RightInverse
      (fun S : { S : grassmannian V k // S ∈ chart_domain Q } ↦
        chart_fun hPQ hP S.1 S.2)
      (fun X : P →ₗ[ℝ] Q ↦
        ⟨graph hPQ hP X, graph_mem_chart_domain hPQ hP X⟩) := sorry

/-- Example 1.36: if `V = P ⊕ Q` with `P` a `k`-plane, then the `k`-planes in `V` that intersect
`Q` trivially are in canonical bijection with the linear maps `P → Q`, via the graph
construction. -/
noncomputable def chart_equiv
    (hPQ : IsCompl P Q) (hP : Module.finrank ℝ P = k) :
    { S : grassmannian V k // S ∈ chart_domain Q } ≃ (P →ₗ[ℝ] Q) where
  toFun := fun S ↦ chart_fun hPQ hP S.1 S.2
  invFun := fun X ↦ ⟨graph hPQ hP X, graph_mem_chart_domain hPQ hP X⟩
  left_inv := chart_equiv_right_inv hPQ hP
  right_inv := chart_equiv_left_inv hPQ hP

/-- The linear model space of the `Q`-chart has the expected dimension `k (n - k)`, where
`n = dim V`. -/
theorem chart_model_finrank
    (hPQ : IsCompl P Q) (hP : Module.finrank ℝ P = k) :
    Module.finrank ℝ (P →ₗ[ℝ] Q) = k * (Module.finrank ℝ V - k) := sorry

end grassmannian

end
