import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_24
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_19

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open WithLp (toLp ofLp)

section

variable {m n : ℕ}

local notation "Em" => EuclideanSpace ℝ (Fin m)
local notation "En" => EuclideanSpace ℝ (Fin n)

/- Proposition 3.26 is a `bridge/view` item in the chapter's coordinate `ℓ∞` extendedRealSubdifferential
API. The owner abstractions already live upstream: Theorem 3.19 gives the affine-map pullback
rule on `extendedRealSubdifferential`, and Proposition 3.24 gives the vector-side owner formula through
`euclideanSubdifferentialAt` for the residual `ℓ∞` norm on `Fin m → ℝ`. The only primitive data
here are the affine matrix map `A.mulVecLin` and the offset `b`; the transpose-image formula is
derived from those owners. -/

recall subdifferential_precompose_affineMap_eq
recall euclidean_subdifferentialAt_linf_eq_piecewise

-- Proof sketch: apply the affine chain rule to the `ℓ∞` norm, then reuse the source-facing
-- residual formula from Proposition 3.24. The owner-level affine pullback step is the transpose
-- image description below; Proposition 3.26 is its source-facing zero/nonzero case split.
private theorem euclidean_subdifferentialAt_affine_linf_eq_transpose_image
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : En) :
    euclideanSubdifferentialAt (fun y : En ↦ ‖A.mulVecLin (ofLp y) + b‖) x =
      A.transpose.toEuclideanLin ''
        euclideanSubdifferentialAt (fun y : Em ↦ ‖ofLp y‖) (toLp 2 (A.mulVecLin (ofLp x) + b)) :=
  sorry

-- Proof sketch: first rewrite the affine `ℓ∞` extendedRealSubdifferential using the owner-level transpose
-- coordinate description from Proposition 3.24. When the residual `A.mulVecLin x + b` vanishes,
-- the `ℓ∞` extendedRealSubdifferential is the canonical `WithLp 1` unit ball `{z | ‖toLp 1 z‖ ≤ 1}`, whose
-- pullback along `A` is the transpose image `Aᵀ.mulVecLin '' {z | ‖toLp 1 z‖ ≤ 1}`. Otherwise,
-- the active signed-coordinate image from Proposition 3.24 pulls back along `A` to the transpose
-- image of those active combinations.
/-- Proposition 3.26: for the affine `ℓ∞` objective `x ↦ ‖A x + b‖∞`, the Euclidean/vector-side
extendedRealSubdifferential is the transpose image of the `ℓ₁` unit ball `{z | ‖toLp 1 z‖ ≤ 1}` when
`A x + b = 0`, and otherwise it is the transpose image of the active signed-coordinate image from
Proposition 3.24, evaluated at the residual `A x + b`. -/
theorem euclidean_subdifferentialAt_affine_linf_eq_piecewise
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : En) :
    euclideanSubdifferentialAt (fun y : En ↦ ‖A.mulVecLin (ofLp y) + b‖) x =
      if A.mulVecLin (ofLp x) + b = 0 then
        A.transpose.toEuclideanLin '' {z : Em | ‖toLp 1 (ofLp z)‖ ≤ 1}
      else
        A.transpose.toEuclideanLin ''
          ((fun coeff : Fin m → ℝ ↦
              toLp 2 fun i ↦ coeff i * Real.sign ((A.mulVecLin (ofLp x) + b) i)) ''
            activeCoordinateFace (fun i ↦ |(A.mulVecLin (ofLp x) + b) i|)) :=
by
  let r : Em := toLp 2 (A.mulVecLin (ofLp x) + b)
  rw [euclidean_subdifferentialAt_affine_linf_eq_transpose_image]
  change A.transpose.toEuclideanLin '' euclideanSubdifferentialAt (fun y : Em ↦ ‖ofLp y‖) r =
    if A.mulVecLin (ofLp x) + b = 0 then
      A.transpose.toEuclideanLin '' {z : Em | ‖toLp 1 (ofLp z)‖ ≤ 1}
    else
      A.transpose.toEuclideanLin ''
        ((fun coeff : Fin m → ℝ ↦
            toLp 2 fun i ↦ coeff i * Real.sign ((A.mulVecLin (ofLp x) + b) i)) ''
          activeCoordinateFace (fun i ↦ |(A.mulVecLin (ofLp x) + b) i|))
  have hr :
      A.transpose.toEuclideanLin '' euclideanSubdifferentialAt (fun y : Em ↦ ‖ofLp y‖) r =
        A.transpose.toEuclideanLin '' (
          if r = 0 then
            {z : Em | ‖toLp 1 (ofLp z)‖ ≤ 1}
          else
            (fun coeff : Fin m → ℝ ↦ toLp 2 fun i ↦ coeff i * Real.sign (r i)) ''
              activeCoordinateFace (fun i ↦ |r i|)) := by
    exact congrArg (fun s : Set Em ↦ A.transpose.toEuclideanLin '' s)
      (euclidean_subdifferentialAt_linf_eq_piecewise r)
  by_cases hr0 : r = 0
  · have h : A.mulVecLin (ofLp x) + b = 0 := by
      simpa [r] using congrArg ofLp hr0
    rw [if_pos h, hr0]
    have hr' := hr
    simp [hr0] at hr'
    simpa using hr'
  · have h : ¬A.mulVecLin (ofLp x) + b = 0 := by
      intro h'
      apply hr0
      simpa [r] using congrArg (toLp 2) h'
    rw [if_neg h]
    have hr' := hr
    simp [hr0] at hr'
    simpa [r] using hr'

end
