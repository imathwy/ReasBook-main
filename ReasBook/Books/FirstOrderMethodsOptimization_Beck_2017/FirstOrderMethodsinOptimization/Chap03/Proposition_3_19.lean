import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Proposition_3_18
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Theorem_3_19

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open WithLp (toLp)

section

variable {m n : ℕ}

local notation "Em" => EuclideanSpace ℝ (Fin m)
local notation "En" => EuclideanSpace ℝ (Fin n)

/- Proposition 3.19 is a `bridge/view` item in the chapter real-valued extendedRealSubdifferential API. The
core owner abstraction is `subdifferentialAt`, and the canonical vector-side bridge owner is
`euclideanSubdifferentialAt`. The affine pullback is already owned upstream by
`subdifferential_precompose_affineMap_eq`, while the source-facing `ℓ₁` subgradient set is
already packaged by `l1CoordinateSubgradientVectors` together with
`subdifferentialAt_l1_norm_eq_coordinatewise_sign_constraints`. This file keeps only the affine
matrix specialization of that owner stack rather than a parallel rowwise decomposition API. -/

recall euclideanSubdifferentialAt
recall l1CoordinateSubgradientVectors
recall subdifferentialAt_l1_norm_eq_coordinatewise_sign_constraints
recall sign_vector_mem_subdifferentialAt_l1_norm
recall subdifferential_precompose_affineMap_eq
recall sgn

-- Proof sketch: apply the affine chain rule from Theorem 3.19 to the `ℓ₁` norm
-- `z ↦ ∑ i, |z i|`, then transport the resulting pullback through the Euclidean bridge
-- `euclideanSubdifferentialAt`. Proposition 3.17 already identifies the target-side
-- extendedRealSubdifferential with `l1CoordinateSubgradientVectors`, so the affine formula is exactly the
-- transpose image of that canonical source-facing set.
/-- Proposition 3.19 (1): for the affine `ℓ¹` objective
`x ↦ ∑ i, |(A.toEuclideanLin x + b) i|`, the Euclidean/vector-side extendedRealSubdifferential is the
transpose image of the canonical coordinatewise `ℓ₁` subgradient set at the residual
`A.toEuclideanLin x + b`. -/
theorem euclidean_subdifferentialAt_affine_l1_eq_transpose_image_l1CoordinateSubgradientVectors
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Em) (x : En) :
    euclideanSubdifferentialAt
        (fun y : En ↦ ∑ i : Fin m, |(A.toEuclideanLin y + b) i|) x =
      A.transpose.toEuclideanLin ''
        l1CoordinateSubgradientVectors (A.toEuclideanLin x + b) := sorry

-- Proof sketch: Proposition 3.18 provides the canonical sign vector
-- `toLp 2 (sgn (fun i ↦ (A.toEuclideanLin x + b) i))` as an element of the `ℓ₁` extendedRealSubdifferential
-- at the residual `A.toEuclideanLin x + b`. Pull that vector back through the affine chain rule
-- above; in Euclidean coordinates the pullback is represented by `A.transpose.toEuclideanLin`.
/-- Proposition 3.19 (2): taking the coordinatewise sign vector from Definition 1.27, which uses
`sgn 0 = 1`, yields a concrete element of the Euclidean/vector-side extendedRealSubdifferential of the affine
`ℓ¹` objective, namely `Aᵀ *ᵥ sgn (fun i ↦ (A.toEuclideanLin x + b) i)`. -/
theorem transpose_sgn_mem_subdifferentialAt_affine_l1
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Em) (x : En) :
    A.transpose.toEuclideanLin
        (toLp 2 (sgn (fun i ↦ (A.toEuclideanLin x + b) i))) ∈
      euclideanSubdifferentialAt
        (fun y : En ↦ ∑ i : Fin m, |(A.toEuclideanLin y + b) i|) x := sorry

end
