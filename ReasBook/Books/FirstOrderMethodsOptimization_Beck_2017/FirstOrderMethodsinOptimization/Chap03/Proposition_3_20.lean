import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_15
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_19

-- Declarations for this item will be appended below by the statement pipeline.

section

open InnerProductSpace
open Metric

variable {m n : ℕ}

local notation "Em" => EuclideanSpace ℝ (Fin m)
local notation "En" => EuclideanSpace ℝ (Fin n)

/- Proposition 3.20 is a `bridge/view` item in the chapter real-valued subdifferential API. Its
core owner abstraction is the canonical `subdifferentialAt` from Theorem 3.4, and its Euclidean
bridge/view owner is `euclideanSubdifferentialAt`. The affine pullback step is governed upstream
by the source-facing owner theorem `subdifferential_precompose_affineMap_eq` from
Theorem 3.19, while the concrete norm-side case split already belongs to Proposition 3.15. The
primitive data here are just the affine map `y ↦ A y + b` and the owner Euclidean-norm
subdifferential; the transpose-image and piecewise singleton/ball formulas are derived API. -/

recall euclideanSubdifferentialAt
recall subdifferential_precompose_affineMap_eq
recall euclidean_subdifferentialAt_l2_norm_eq_piecewise

-- Proof sketch: apply the affine chain rule to `g(z) = ‖z‖`, so the dual subgradients pull back
-- along `A` by the owner theorem on `subdifferential`, then transport that canonical dual pullback
-- through the chapter bridges `strongDualSubdifferential` and `euclideanSubdifferentialAt`. In
-- Euclidean coordinates the pullback is represented by applying `Aᵀ`, and `toDualMap` converts
-- the dual-valued statement into the vector-valued image formula.
/-- Pulling back the Euclidean norm subdifferential along the affine map `y ↦ A y + b` gives the
vector-form chain-rule description `Aᵀ ∂‖·‖(A x + b)`. -/
theorem euclidean_subdifferentialAt_affine_l2_norm_eq_transpose_image_subdifferentialAt_norm
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Em) (x : En) :
    euclideanSubdifferentialAt (fun y ↦ ‖A.toEuclideanLin y + b‖) x =
      A.transpose.toEuclideanLin ''
        euclideanSubdifferentialAt (fun z : Em ↦ ‖z‖) (A.toEuclideanLin x + b) := sorry

-- Proof sketch: first rewrite the affine subdifferential through the transpose-image formula
-- above. Then specialize Proposition 3.15 at the residual vector `A.toEuclideanLin x + b`; the
-- zero case gives the transpose image of the closed unit ball, and the nonzero case gives the
-- transpose of the singleton containing the normalized residual.
/-- Proposition 3.20: for `f(x) = ‖A x + b‖₂` on `ℝ^n`, the Euclidean/vector-side
subdifferential is the singleton containing `Aᵀ ((A x + b) / ‖A x + b‖₂)` when
`A x + b ≠ 0`, and it is the image of the closed Euclidean unit ball under `Aᵀ` when
`A x + b = 0`. This is the concrete specialization of
`euclidean_subdifferentialAt_affine_l2_norm_eq_transpose_image_subdifferentialAt_norm` using the
norm formula from Proposition 3.15. -/
theorem euclidean_subdifferentialAt_affine_l2_norm_eq_piecewise
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Em) (x : En) :
    euclideanSubdifferentialAt (fun y ↦ ‖A.toEuclideanLin y + b‖) x =
      if A.toEuclideanLin x + b = 0 then
        A.transpose.toEuclideanLin '' closedBall (0 : Em) 1
      else
        {A.transpose.toEuclideanLin
          (‖A.toEuclideanLin x + b‖⁻¹ • (A.toEuclideanLin x + b))} := sorry

end
