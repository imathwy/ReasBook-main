module

import Mathlib.Analysis.InnerProductSpace.PiL2

/- Definition 20.7: On `ℝⁿ`, the Euclidean norm and metric are the `L²` norm and
metric, while the square metric is the `L∞` metric transported along the canonical
linear isometric equivalence with coordinate functions. -/
#check fun {n : Type*} [Fintype n] (x : EuclideanSpace ℝ n) ↦
  EuclideanSpace.norm_eq x
#check fun {n : Type*} [Fintype n] (x y : EuclideanSpace ℝ n) ↦
  EuclideanSpace.dist_eq x y
#check fun {n : Type*} [Fintype n] (x y : PiLp ⊤ (fun _ : n ↦ ℝ)) ↦
  PiLp.dist_eq_iSup x y
#check fun {n : Type*} [Fintype n] ↦
  (PiLp.equivₗᵢ (fun _ : n ↦ ℝ) : PiLp ⊤ (fun _ : n ↦ ℝ) ≃ₗᵢ[ℝ] (n → ℝ))
