import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Theorem_4_1_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open scoped CubicRegularizedDiagonalInvariants

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 4.1.11 lies in the diagonal cubic-regularized quadratic / scalar-duality domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticDualFunction` and `cubicRegularizedQuadraticDualDomain` in
  `Theorem_4_1_11`, the chapter owners of the scalar dual value and its effective domain;
* `cubicRegularizedDiagonalResolvent_apply` in `Proposition_4_1_10`, the diagonal coordinate
  formula for the canonical resolvent point;
* `cubicRegularizedQuadratic_resolvent_norm_eq_of_dualMaximizer` in `Proposition_4_1_13`, the
  generic owner theorem equating the resolvent norm with `(2 / M) λ*` at a dual maximizer;
* `cubicRegularizedMinimalDiagonalIndices` and
  `cubicRegularizedMinimalDiagonalGradientSquare` in `Definition_4_1_15`, the diagonal source
  invariants `I*` and `G²`.

Best owner abstraction:
* source-facing: the perturbed diagonal model `v_δ(h) = v(h) + δ h^(k)` and the resulting
  boundary equation for an optimal perturbed dual point;
* core/canonical: `cubicRegularizedQuadraticDualFunction`,
  `cubicRegularizedQuadraticDualDomain`, and `IsMaxOn` for the perturbed dual problem;
* bridge/view: the diagonal resolvent coordinate formula together with the generic dual-maximizer
  norm identity.

Primitive data:
* the diagonal data `Hdiag`, the gradient `g`, the cubic parameter `M`, and the active index
  `k ∈ I*`;
* the source-facing perturbed gradient `g + δ e_k`.

Derived API:
* the scalar dual function and dual domain, already owned upstream;
* the generic resolvent norm identity at a dual maximizer, already owned upstream;
* dual optimality on the nonnegative feasible set `dom ψ ∩ ℝ₊`, which should reuse the chapter
  owner `IsMaxOn` rather than restating feasibility and order as a second local wrapper API.

This file therefore keeps the perturbation owner `cubicRegularizedDiagonalPerturbedGradient`, but
deletes the redundant local diagonal scalar-dual function/domain and the one-off dual-maximizer
wrapper in favor of the existing chapter owners; the main proposition is only the diagonal bridge
expansion of the upstream resolvent norm identity. -/

/-- The perturbed linear term obtained from `g` by adding `δ` to the coordinate `k`, encoding
the textbook objective perturbation `v_δ(h) = v(h) + δ h^(k)`. -/
def cubicRegularizedDiagonalPerturbedGradient
    (g : E) (k : Fin n) (δ : ℝ) : E :=
  g + EuclideanSpace.single k δ

/-- Expanding `cubicRegularizedDiagonalPerturbedGradient` gives the coordinatewise perturbation
`g^(i) + δ` at `i = k` and `g^(i)` elsewhere. -/
-- Proof sketch: unfold `cubicRegularizedDiagonalPerturbedGradient` and split on `i = k`.
@[simp]
theorem cubicRegularizedDiagonalPerturbedGradient_apply
    (g : E) (k i : Fin n) (δ : ℝ) :
    cubicRegularizedDiagonalPerturbedGradient g k δ i =
      g i + if i = k then δ else 0 := by
  simp [cubicRegularizedDiagonalPerturbedGradient]

-- Proof sketch: for `gδ = cubicRegularizedDiagonalPerturbedGradient g k δ`, the perturbed dual
-- maximizer hypothesis is exactly `IsMaxOn ψδ Dplusδ lamDelta`. Because `k ∈ I*`,
-- `cubicRegularizedMinimalDiagonalGradientSquare g Hdiag = 0`, and `δ ≠ 0`, the perturbed active
-- squared mass becomes `δ² > 0`, so the perturbed problem is nondegenerate. Apply the upstream
-- owner theorem
-- `cubicRegularizedQuadratic_resolvent_norm_eq_of_dualMaximizer` to `gδ`, then expand the
-- diagonal resolvent coordinates with `cubicRegularizedDiagonalResolvent_apply`; on `I* \\ {k}`
-- the terms vanish, at `k` the numerator is `δ²`, and off `I*` the numerators remain `(g i)²`.

section

variable (g : E) (Hdiag : Fin n → ℝ) (M : ℝ)

local notation "H" => Matrix.diagonal Hdiag
local notation "Dplus(" g' ")" =>
  cubicRegularizedQuadraticDualDomain g' H M ∩ Set.Ici (0 : ℝ)
variable {δ : ℝ} {k : Fin n}
local notation "gδ" => cubicRegularizedDiagonalPerturbedGradient g k δ
local notation "ψδ" => cubicRegularizedQuadraticDualFunction gδ H M
local notation "Dplusδ" => Dplus(gδ)

/-- Proposition 4.1.11: in the degenerate case `G² = 0`, perturbing the objective by `δ h^(k)`
for `k ∈ I*` and `δ ≠ 0` forces every optimal dual maximizer `λ_δ*` on `dom ψ_δ ∩ ℝ₊` to satisfy
`δ² / (H_min + λ_δ*)² + ∑_{i ∉ I*} (g^(i))² / (H_i + λ_δ*)² = 4 (λ_δ*)² / M²`. -/
theorem perturbedDiagonalDualMaximizer_satisfies_boundaryEquation
    {δ : ℝ} (hM : 0 < M) (hδ : δ ≠ 0) {k : Fin n}
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    {lamDelta : ℝ}
    (hopt_max : IsMaxOn ψδ Dplusδ lamDelta) :
    δ ^ (2 : ℕ) / (H_min[Hdiag] + lamDelta) ^ (2 : ℕ) +
        Finset.sum
          (Finset.univ.filter fun i : Fin n ↦
            i ∉ I*[Hdiag])
          (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lamDelta) ^ (2 : ℕ)) =
      (4 : ℝ) * lamDelta ^ (2 : ℕ) / M ^ (2 : ℕ) := sorry

end
