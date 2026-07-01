import Mathlib
import FirstOrderMethodsinOptimization.Chap03.Definition_3_10
import FirstOrderMethodsinOptimization.Chap15.Algorithm_15_4
import FirstOrderMethodsinOptimization.Chap15.Definition_15_1
import FirstOrderMethodsinOptimization.Chap15.Definition_15_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

open scoped BigOperators

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [AddCommGroup X] [Module ℝ X]
variable [AddCommGroup Z] [Module ℝ Z]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

section

variable {h₁ : X → EReal} {h₂ : Z → EReal}
variable {A : X →ₗ[ℝ] Y} {B : Z →ₗ[ℝ] Y} {c : Y}
variable {ρ : PosReal}
variable {G : QuadraticForm ℝ X} {Q : QuadraticForm ℝ Z}
variable {x0 : X} {z0 : Z} {y0 : Y}
variable {x : ℕ → X} {z : ℕ → Z} {y : ℕ → Y}

/- Domain sampling for Theorem 15.2:
- `source-facing`: the textbook ergodic averages `x^(n)` and `z^(n)`, together with the displayed
  averaged primal-gap and feasibility estimate;
- `core/canonical`: `Finset.centerMass` for constant-weight finite averages and
  `admm_dual_objective` from Definition 15.2 for the Chapter 15 dual maximization owner on
  `Module.Dual ℝ Y`;
- `bridge/view`: the direct restriction of that canonical dual owner to `StrongDual ℝ Y`, needed
  here because the theorem also uses the multiplier norm `‖yStar‖`.

This file is therefore `bridge/view`: it keeps the source-facing ergodic averages visible in the
theorem surface, reuses `Finset.centerMass` for the averaging data, and uses the one-off
`StrongDual` restriction of the Chapter 15 dual owner directly in the theorem hypotheses rather
than introducing a second named dual owner. -/
/-- The ergodic average
`(1 / (n + 1)) ∑_{k=0}^n u^(k+1)` of the first `n + 1` shifted iterates of `u`. -/
def ergodicAverage {E : Type*} [AddCommGroup E] [Module ℝ E] (u : ℕ → E) (n : ℕ) : E :=
  Finset.centerMass (Finset.range (n + 1)) (fun _ ↦ (1 : ℝ)) (fun k ↦ u (k + 1))

-- Proof sketch: sum the one-step primal-dual gap inequality along the AD-PMM trajectory, use the
-- explicit convexity assumptions on `h₁` and `h₂` together with the positive semidefiniteness of
-- `G` and `Q`, average the iterates, and then combine primal and dual
-- optimality with the bound `2 ‖y*‖ ≤ γ` to package the two displayed inequalities into the
-- equivalent scaled-`max` estimate. The `toReal` objective-gap term is read only under the direct
-- finiteness hypotheses
-- `(ergodicAverage x n, ergodicAverage z n), (xStar, zStar) ∈ finite_domain (H[h₁, h₂])`.
/-- Theorem 15.2: assuming convexity of `h₁` and `h₂`, if `x`, `z`, and `y` form an AD-PMM
trajectory, if `(xStar, zStar)` is an optimal primal solution, and if `yStar` is an optimal dual
multiplier with `2 ‖yStar‖ ≤ γ`, and if both displayed objective values are finite, then the
ergodic averages `x^(n) = (1 / (n + 1)) ∑_{k=0}^n x^(k+1)` and
`z^(n) = (1 / (n + 1)) ∑_{k=0}^n z^(k+1)` satisfy the combined `O(1 / n)` bound controlling both
the primal objective gap and the `γ`-scaled feasibility residual. -/
theorem ad_pmm_ergodic_rate_max_le
    (hh₁_convex : is_convex_function h₁)
    (hh₂_convex : is_convex_function h₂)
    (hG_nonneg : ∀ x' : X, 0 ≤ G x')
    (hQ_nonneg : ∀ z' : Z, 0 ≤ Q z')
    (hTraj : IsADPMMTrajectory ρ h₁ h₂ A B c G Q x0 z0 y0 x z y)
    {xStar : X} {zStar : Z}
    (hPrimalOpt :
      IsMinOn H[h₁, h₂] (admm_feasible_set A B c) (xStar, zStar))
    {yStar : StrongDual ℝ Y}
    (hDualOpt : IsMaxOn (fun y : StrongDual ℝ Y ↦ admm_dual_objective h₁ h₂ A B c y)
      Set.univ yStar)
    {γ : PosReal} (hγ : 2 * ‖yStar‖ ≤ (γ : ℝ))
    (n : ℕ)
    (hAvg_finite : (ergodicAverage x n, ergodicAverage z n) ∈ finite_domain (H[h₁, h₂]))
    (hStar_finite : (xStar, zStar) ∈ finite_domain (H[h₁, h₂])) :
    max
        ((H[h₁, h₂] (ergodicAverage x n, ergodicAverage z n)).toReal -
          (H[h₁, h₂] (xStar, zStar)).toReal)
        (((γ : ℝ) / 2) * ‖A (ergodicAverage x n) + B (ergodicAverage z n) - c‖) ≤
      (G (xStar - x0) +
          ((ρ : ℝ) * ‖B (zStar - z0)‖ ^ (2 : ℕ) + Q (zStar - z0)) +
          (1 / (ρ : ℝ)) * ((γ : ℝ) + ‖y0‖) ^ (2 : ℕ)) /
        (2 * ((n : ℝ) + 1)) := sorry

-- Proof sketch: apply `le_max_left` to `ad_pmm_ergodic_rate_max_le`; this is exactly the
-- objective-gap half of the combined estimate, using the same direct finite-domain hypotheses for
-- the two displayed objective values.
/-- If both displayed objective values are finite, then the ergodic average objective value
satisfies the bound
`H(x^(n), z^(n)) - H(x^*, z^*) ≤
 (‖x^* - x^0‖_G^2 + ‖z^* - z^0‖_C^2 + (1 / ρ) (γ + ‖y^0‖)^2) / (2 (n + 1))`. -/
theorem ad_pmm_ergodic_objective_gap_le
    (hh₁_convex : is_convex_function h₁)
    (hh₂_convex : is_convex_function h₂)
    (hG_nonneg : ∀ x' : X, 0 ≤ G x')
    (hQ_nonneg : ∀ z' : Z, 0 ≤ Q z')
    (hTraj : IsADPMMTrajectory ρ h₁ h₂ A B c G Q x0 z0 y0 x z y)
    {xStar : X} {zStar : Z}
    (hPrimalOpt :
      IsMinOn H[h₁, h₂] (admm_feasible_set A B c) (xStar, zStar))
    {yStar : StrongDual ℝ Y}
    (hDualOpt : IsMaxOn (fun y : StrongDual ℝ Y ↦ admm_dual_objective h₁ h₂ A B c y)
      Set.univ yStar)
    {γ : PosReal} (hγ : 2 * ‖yStar‖ ≤ (γ : ℝ))
    (n : ℕ)
    (hAvg_finite : (ergodicAverage x n, ergodicAverage z n) ∈ finite_domain (H[h₁, h₂]))
    (hStar_finite : (xStar, zStar) ∈ finite_domain (H[h₁, h₂])) :
    (H[h₁, h₂] (ergodicAverage x n, ergodicAverage z n)).toReal -
        (H[h₁, h₂] (xStar, zStar)).toReal ≤
      (G (xStar - x0) +
          ((ρ : ℝ) * ‖B (zStar - z0)‖ ^ (2 : ℕ) + Q (zStar - z0)) +
          (1 / (ρ : ℝ)) * ((γ : ℝ) + ‖y0‖) ^ (2 : ℕ)) /
        (2 * ((n : ℝ) + 1)) := sorry

-- Proof sketch: this is the feasibility-residual half of the same averaged primal-dual estimate
-- as `ad_pmm_ergodic_rate_max_le`, but it does not need the additional finite-domain hypotheses
-- used to read the objective term through `EReal.toReal`.
/-- The ergodic average feasibility residual satisfies the bound
`‖A x^(n) + B z^(n) - c‖ ≤
 (‖x^* - x^0‖_G^2 + ‖z^* - z^0‖_C^2 + (1 / ρ) (γ + ‖y^0‖)^2) / (γ (n + 1))`. -/
theorem ad_pmm_ergodic_feasibility_residual_le
    (hh₁_convex : is_convex_function h₁)
    (hh₂_convex : is_convex_function h₂)
    (hG_nonneg : ∀ x' : X, 0 ≤ G x')
    (hQ_nonneg : ∀ z' : Z, 0 ≤ Q z')
    (hTraj : IsADPMMTrajectory ρ h₁ h₂ A B c G Q x0 z0 y0 x z y)
    {xStar : X} {zStar : Z}
    (hPrimalOpt :
      IsMinOn H[h₁, h₂] (admm_feasible_set A B c) (xStar, zStar))
    {yStar : StrongDual ℝ Y}
    (hDualOpt : IsMaxOn (fun y : StrongDual ℝ Y ↦ admm_dual_objective h₁ h₂ A B c y)
      Set.univ yStar)
    {γ : PosReal} (hγ : 2 * ‖yStar‖ ≤ (γ : ℝ))
    (n : ℕ) :
    ‖A (ergodicAverage x n) + B (ergodicAverage z n) - c‖ ≤
      (G (xStar - x0) +
          ((ρ : ℝ) * ‖B (zStar - z0)‖ ^ (2 : ℕ) + Q (zStar - z0)) +
          (1 / (ρ : ℝ)) * ((γ : ℝ) + ‖y0‖) ^ (2 : ℕ)) /
        ((γ : ℝ) * ((n : ℝ) + 1)) := sorry

end

end
