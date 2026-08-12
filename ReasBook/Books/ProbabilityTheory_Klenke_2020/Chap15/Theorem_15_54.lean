import ProbabilityTheory_Klenke_2020.Chap15.Definition_15_53

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

noncomputable section

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} {d : ℕ}
variable {X : Ω → EuclideanSpace ℝ (Fin d)}
variable {μ : EuclideanSpace ℝ (Fin d)} {C : Matrix (Fin d) (Fin d) ℝ}

-- Proof sketch: this is the coordinate projection of the canonical mean identity
-- `HasMultivariateNormalLaw.integral_eq_mean`.
/-- Theorem 15.54 (1): Item (i). If `X` has multivariate Gaussian law `N_{μ,C}`, then the
expectation of its `i`th coordinate is `μ i`. -/
theorem integral_coord_eq_mean_of_hasMultivariateNormalLaw
    (hX : HasMultivariateNormalLaw X P μ C) (i : Fin d) :
    ∫ ω, X ω i ∂P = μ i := sorry

-- Proof sketch: this is exactly `HasMultivariateNormalLaw.covariance_eval_eq`.
/-- Theorem 15.54 (2): Item (ii). If `X` has multivariate Gaussian law `N_{μ,C}` and `C` is
positive definite, then the covariance of coordinates `i` and `j` is `C i j`. -/
theorem covariance_coord_eq_of_hasMultivariateNormalLaw
    (hX : HasMultivariateNormalLaw X P μ C) (i j : Fin d) :
    cov[fun ω ↦ X ω i, fun ω ↦ X ω j; P] = C i j :=
  hX.covariance_eval_eq i j

-- Proof sketch: push the law of `X` forward along the continuous linear functional
-- `x ↦ ⟪λ, x⟫`; the image of `multivariateGaussian μ C` under that map is the one-dimensional
-- Gaussian law with mean `⟪λ, μ⟫` and variance `λᵀ C λ`.
/-- Theorem 15.54 (3): Item (iii). Every linear functional of a multivariate Gaussian random
vector is a one-dimensional Gaussian with the corresponding mean and variance. -/
theorem hasLaw_inner_eq_gaussianReal_of_hasMultivariateNormalLaw
    (hX : HasMultivariateNormalLaw X P μ C) (v : EuclideanSpace ℝ (Fin d)) :
    HasLaw (fun ω ↦ ⟪v, X ω⟫)
      (gaussianReal ⟪v, μ⟫ (Real.toNNReal (dotProduct v (Matrix.mulVec C v)))) P := sorry

-- Proof sketch: identify the law of `X` with `multivariateGaussian μ C` via `hX`, then rewrite
-- the characteristic function using `charFun_multivariateGaussian`.
/-- Theorem 15.54 (4): Item (iv). The characteristic function of a multivariate Gaussian random
vector with mean `μ` and covariance `C` is `t ↦ exp (i⟪t, μ⟫ - ⟪t, Ct⟫ / 2)`. -/
theorem charFun_eq_exp_of_hasMultivariateNormalLaw
    (hX : HasMultivariateNormalLaw X P μ C) (t : EuclideanSpace ℝ (Fin d)) :
    MeasureTheory.charFun (P.map X) t =
      Complex.exp (⟪t, μ⟫ * Complex.I - dotProduct t (Matrix.mulVec C t) / 2) := sorry

-- Proof sketch: for the forward implication, unpack `HasMultivariateNormalLaw` and apply the
-- previous linear-image Gaussian theorem. For the converse implication, combine `hC` with the
-- Gaussianity of all linear functionals to identify `P.map X` with `multivariateGaussian μ C`.
/-- Theorem 15.54 (5): `X` has multivariate normal law `N_{μ,C}` exactly when `C` is positive
definite and every linear functional `⟪λ, X⟫` has the corresponding one-dimensional Gaussian law.
-/
theorem hasMultivariateNormalLaw_iff_all_linearForms_gaussian :
    HasMultivariateNormalLaw X P μ C ↔
      C.PosDef ∧
        ∀ v : EuclideanSpace ℝ (Fin d),
          HasLaw (fun ω ↦ ⟪v, X ω⟫)
            (gaussianReal ⟪v, μ⟫ (Real.toNNReal (dotProduct v (Matrix.mulVec C v)))) P := sorry

-- Proof sketch: the forward implication is `charFun_eq_exp_of_hasMultivariateNormalLaw`. For the
-- converse implication, the displayed formula identifies the characteristic function of `P.map X`
-- with that of `multivariateGaussian μ C`; together with `hC`, this yields the owner law.
/-- Theorem 15.54 (6): `X` has multivariate normal law `N_{μ,C}` exactly when `C` is positive
definite and the characteristic function of `P.map X` is
`t ↦ exp (i⟪t, μ⟫ - ⟪t, Ct⟫ / 2)`. -/
theorem hasMultivariateNormalLaw_iff_charFun_eq :
    HasMultivariateNormalLaw X P μ C ↔
      C.PosDef ∧
        ∀ t : EuclideanSpace ℝ (Fin d),
          MeasureTheory.charFun (P.map X) t =
            Complex.exp (⟪t, μ⟫ * Complex.I - dotProduct t (Matrix.mulVec C t) / 2) := sorry
