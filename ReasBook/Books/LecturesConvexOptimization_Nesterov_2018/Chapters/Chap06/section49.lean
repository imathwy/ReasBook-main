import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_49 (from Chap06) -/
noncomputable section

open Metric
open scoped Matrix.Norms.L2Operator RealSymmetricMatrixSpace

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Definition 6.49 lies in the operator-norm / symmetric-matrix spectral-norm domain.

Primary domain:
- operator norms of continuous linear maps into the real symmetric-matrix space `𝕊^n`;
- the ambient matrix spectral norm in the scoped `Matrix.Norms.L2Operator` owner.

Sampled owner-style declarations:
- mathlib `ContinuousLinearMap.opNorm`;
- mathlib `ContinuousLinearMap.sSup_sphere_eq_norm`;
- Chapter 5 `𝕊^n`.

Best owner abstraction:
- source-facing: the operator norm of `A : E →L[ℝ] 𝕊^n`, where `E` models the chosen normed
  structure on `ℝ^m`;
- core/canonical: the ambient norm `‖A‖`;
- bridge/view: the unit-sphere spectral-norm formula and, in finite dimensions, existence of a
  maximizing unit vector.

Primitive data:
- a real normed space `E`;
- a continuous linear map `A : E →L[ℝ] 𝕊^n`.

Derived API:
- the canonical operator norm `‖A‖`;
- the source-facing sphere formula in terms of the ambient matrix spectral norm;
- the finite-dimensional attainment statement recovering the textbook maximum.

Source/core/bridge triage:
- source-facing: Definition 6.49 as the operator norm induced by the source norm and the spectral
  norm on symmetric matrices;
- core/canonical: `ContinuousLinearMap.opNorm`;
- bridge/view: the symmetric-matrix-to-matrix coercion inside the sphere formula.
-/

/- The canonical owner note for this item: the operator norm induced by the chosen norm on the
source and the spectral norm on `S_n` is the canonical norm on `E →L[ℝ] 𝕊^n`. -/
set_option linter.hashCommand false in
#check (‖·‖ : (E →L[ℝ] 𝕊^n) → ℝ)

-- Proof sketch: specialize `ContinuousLinearMap.sSup_sphere_eq_norm` to the symmetric-matrix
-- codomain, then rewrite the codomain norm as the ambient matrix spectral norm under the coercion
-- `𝕊^n ↪ Matrix (Fin n) (Fin n) ℝ`.
/-- Definition 6.49: the canonical operator norm of a symmetric-matrix-valued map is the supremum
of the ambient matrix spectral norm of `A h` over the unit sphere of the source space. -/
theorem operatorNorm_eq_sSup_spectralNorm_unitSphere
    (A : E →L[ℝ] 𝕊^n) :
    ‖A‖ =
      sSup ((fun h : E ↦ ‖((A h : 𝕊^n) : Mat)‖) '' sphere (0 : E) 1) := sorry

-- Proof sketch: the unit sphere of a finite-dimensional real normed space is compact, the map
-- `h ↦ ‖((A h : 𝕊^n) : Mat)‖` is continuous, and
-- `operatorNorm_eq_sSup_spectralNorm_unitSphere` identifies `‖A‖` with the resulting maximum.
/-- In finite dimensions, the operator norm of `A` is attained at some unit vector of the source
space. This recovers the textbook maximum formulation of Definition 6.49. -/
theorem operatorNorm_exists_unitSphere_spectralNorm_maximizer
    [FiniteDimensional ℝ E] (A : E →L[ℝ] 𝕊^n) :
    ∃ h ∈ sphere (0 : E) 1, ‖A‖ = ‖((A h : 𝕊^n) : Mat)‖ := sorry

end

end

/-! ### Proposition_6_49 (from Chap06) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 6.49 lies in the strong-convexity / affine-perturbation minimization domain on
real inner-product spaces.

Mandatory domain-style sampling:
- project `StrongConvexOn.quadratic_growth_of_isMinOn_of_mem` in `Chap02/Theorem_2_30`, the
  canonical quadratic-growth owner at a feasible minimizer;
- project `StrongConvexOn.add_convexOn` in `Chap02/Proposition_2_3`, the canonical bridge adding
  a convex perturbation to a strongly convex objective;
- mathlib `LinearMap.convexOn`, the owner convexity API for linear functionals;
- mathlib `innerSL`, the canonical linear functional `x ↦ ⟪g, x⟫`.

Best owner abstraction:
- source-facing: Proposition 6.49's strengthened variational inequality for an affine perturbation
  of a strongly convex objective;
- core/canonical: `StrongConvexOn Q σΨ Ψ` together with `IsMinOn`;
- bridge/view: the affine perturbation `x ↦ Ψ x + inner ℝ g x`.

Primitive data:
- the feasible set `Q`, strong-convexity owner `hΨ_strong`, perturbation vector `g`, minimizer
  candidate `v_t`, and comparison point `x`.

Derived API:
- convexity of `x ↦ inner ℝ g x`;
- strong convexity of the affine perturbation via `StrongConvexOn.add_convexOn`;
- quadratic growth of the perturbed objective at the feasible minimizer `v_t`.

The previous version duplicated the owner proof locally, repeated redundant convexity/positivity
binders already subsumed by the owner abstraction, and fixed the statement to `EuclideanSpace`
coordinates although only the real inner-product-space owner layer is used. This refinement keeps
the source-facing proposition, makes feasibility of `v_t` explicit because `IsMinOn` does not
include membership, and derives the inequality directly from the Chapter 2 owner theorem.
-/

-- Proof sketch: set `Φ x = Ψ x + inner ℝ g x`. The linear term is affine, so `Φ` remains
-- `σΨ`-strongly convex on `Q`. Apply strong convexity to the segment from `v_t` to any feasible
-- `x`, use the minimizing property of `v_t` to compare `Φ v_t` with the segment value, rearrange,
-- divide by the segment parameter, and let the parameter tend to `0`.
/-- Proposition 6.49: if `Ψ` is `σΨ`-strongly convex on the feasible set `Q` and the feasible
point `v_t ∈ Q` minimizes the affine perturbation `x ↦ Ψ x + ⟪g, x⟫` over `Q`, then every
feasible point satisfies the strengthened variational inequality
`Ψ x + ⟪g, x - v_t⟫ ≥ Ψ v_t + (σΨ / 2) * ‖x - v_t‖²`. -/
theorem strongConvexOn_variational_inequality_of_affine_isMinOn
    {Q : Set E} {Ψ : E → ℝ} {σΨ : ℝ} {g v_t x : E}
    (hΨ_strong : StrongConvexOn Q σΨ Ψ)
    (hv_t_mem : v_t ∈ Q)
    (hv_t : IsMinOn (fun y ↦ Ψ y + inner ℝ g y) Q v_t)
    (hx : x ∈ Q) :
    Ψ x + inner ℝ g (x - v_t) ≥
      Ψ v_t + (σΨ / 2) * ‖x - v_t‖ ^ (2 : ℕ) := by
  have hinner_convex : ConvexOn ℝ Q (fun y : E ↦ inner ℝ g y) := by
    simpa using (innerSL ℝ g).convexOn hΨ_strong.1
  have hperturbed_strong : StrongConvexOn Q σΨ (fun y : E ↦ inner ℝ g y + Ψ y) := by
    simpa [Pi.add_apply, add_comm] using hΨ_strong.add_convexOn hinner_convex
  have hv_t' : IsMinOn (fun y : E ↦ inner ℝ g y + Ψ y) Q v_t := by
    simpa [add_comm] using hv_t
  have hquad :
      inner ℝ g x + Ψ x ≥
        inner ℝ g v_t + Ψ v_t + (σΨ / 2) * ‖x - v_t‖ ^ (2 : ℕ) :=
    hperturbed_strong.quadratic_growth_of_isMinOn_of_mem hv_t_mem hv_t' x hx
  have hinner_sub : inner ℝ g (x - v_t) = inner ℝ g x - inner ℝ g v_t := by
    rw [inner_sub_right]
  nlinarith [hquad, hinner_sub]

end
