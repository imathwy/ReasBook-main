import LecturesConvexOptimization_Nesterov_2018.Chap04.Proposition_4_1_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Topology
open scoped CubicRegularizedDiagonalInvariants

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 4.1.12 lies in the diagonal cubic-regularized quadratic / boundary-degeneration
domain.

Sampled owner declarations:
* `cubicRegularizedDiagonalPerturbedGradient` in `Proposition_4_1_11`, the source-facing owner of
  the perturbation `g + δ e_k`;
* `cubicRegularizedQuadraticObjective` in `Theorem_4_1_11`, the chapter owner of the primal cubic
  model;
* `cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos` in
  `Proposition_4_1_9`, the nondegenerate dual-domain owner for `G² > 0`;
* `cubicRegularizedQuadraticDiagonal_primalMinimizer_of_dualMaximizer_of_minimalGradientSquare_pos`
  in `Theorem_4_1_10`, the diagonal owner theorem sending a nondegenerate dual maximizer to the
  corresponding primal minimizer;
* `cubicRegularizedDiagonalResolvent_apply` in `Proposition_4_1_10`, the coordinate bridge for
  the canonical diagonal resolvent point;
* `cubicRegularizedDiagonalResolvent_isMinOn` in `Proposition_4_1_10`, the owner-level minimizer
  theorem for that same resolvent point.

Best owner abstraction:
* source-facing: the explicit boundary limit point in the degenerate case;
* core/canonical: the diagonal resolvent point
  `-((Matrix.diagonal fun i ↦ Hdiag i + lam)⁻¹).mulVec g'`;
* bridge/view: the coordinate formulas identifying that resolvent with the textbook entrywise
  description.

Primitive data:
* `g`, `Hdiag`, `M`, the active index `k`, and the perturbed gradient
  `cubicRegularizedDiagonalPerturbedGradient g k δ`.

Derived API:
* the canonical diagonal resolvent expression above, already supported upstream by the existing
  owner-level minimizer theorems;
* the strict interior fact `-H_min < λ_δ*`, derived upstream from perturbed dual optimality in the
  nondegenerate `G² > 0` regime;
* the source-facing boundary limit point `cubicRegularizedDiagonalBoundaryMinimizer`.

This file therefore keeps the boundary-point owner, but deletes the redundant local perturbed
minimizer wrapper and rewrites the proposition surface directly in terms of the canonical
resolvent point and the existing perturbed dual-maximizer-to-primal-minimizer API. -/

/-- The boundary point obtained by letting the perturbed minimizers approach the degenerate dual
boundary `λ = -H_min` while keeping the `k`-th active coordinate negative. -/
def cubicRegularizedDiagonalBoundaryMinimizer
    (g : E) (Hdiag : Fin n → ℝ) (M : ℝ) (k : Fin n) : E :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm fun i ↦
    if i = k then
      -Real.sqrt
        ((4 : ℝ) * H_min[Hdiag] ^ (2 : ℕ) / M ^ (2 : ℕ) -
          Finset.sum
            (Finset.univ.filter fun j : Fin n ↦
              j ∉ I*[Hdiag])
            (fun j ↦
              (g j) ^ (2 : ℕ) /
                (Hdiag j - H_min[Hdiag]) ^ (2 : ℕ)))
    else if i ∈ I*[Hdiag] then
      0
    else
      -g i / (Hdiag i - H_min[Hdiag])

/-- Evaluating `cubicRegularizedDiagonalBoundaryMinimizer` gives the inactive-coordinate formula
`-g^(i) / (H_i - H_min)`, the zero coordinates on `I* \\ {k}`, and the negative square-root value
for the distinguished active coordinate `k`. -/
-- Proof sketch: unfold `cubicRegularizedDiagonalBoundaryMinimizer`.
theorem cubicRegularizedDiagonalBoundaryMinimizer_apply
    (g : E) (Hdiag : Fin n → ℝ) (M : ℝ) (k i : Fin n) :
    cubicRegularizedDiagonalBoundaryMinimizer g Hdiag M k i =
      if i = k then
        -Real.sqrt
          ((4 : ℝ) * H_min[Hdiag] ^ (2 : ℕ) / M ^ (2 : ℕ) -
            Finset.sum
              (Finset.univ.filter fun j : Fin n ↦
                j ∉ I*[Hdiag])
              (fun j ↦
                (g j) ^ (2 : ℕ) /
                  (Hdiag j - H_min[Hdiag]) ^ (2 : ℕ)))
      else if i ∈ I*[Hdiag] then
        0
      else
        -g i / (Hdiag i - H_min[Hdiag]) := by
  simp [cubicRegularizedDiagonalBoundaryMinimizer]

section

variable (g : E) (Hdiag : Fin n → ℝ) (M : ℝ) (k : Fin n)

local notation "H" => Matrix.diagonal Hdiag
local notation "Dplus(" g' ")" =>
  cubicRegularizedQuadraticDualDomain g' H M ∩ Set.Ici (0 : ℝ)
local notation "gδ(" δ ")" => cubicRegularizedDiagonalPerturbedGradient g k δ
local notation "Aδ(" lamDelta "," δ ")" => Matrix.diagonal fun i ↦ Hdiag i + lamDelta δ
local notation "hδ(" lamDelta "," δ ")" => -Matrix.mulVec ((Aδ(lamDelta, δ))⁻¹) (gδ(δ))

-- Proof sketch: for each `δ > 0`, the perturbed active squared mass is `δ² > 0`, so the
-- perturbed problem is in the nondegenerate `G² > 0` regime. The Chapter 4 domain owner then
-- puts `λ_δ*` in the strict interior region `-H_min < λ_δ*`. Combining that with
-- `perturbedDiagonalDualMaximizer_satisfies_boundaryEquation` from `Proposition_4_1_11`, one
-- rules out every cluster point strictly larger than `-H_min`, leaving `-H_min` as the only
-- possible limit as `δ → 0+`.
/-- Under the hypotheses of Proposition 4.1.12, the perturbed optimal dual parameters satisfy
`λ_δ* → -H_min` as `δ → 0+`. -/
theorem cubicRegularizedDiagonalPerturbedDualMaximizer_tendsto_boundary
    (lamDelta : ℝ → ℝ)
    (hM : 0 < M)
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    (hopt_max :
      ∀ {δ : ℝ}, 0 < δ →
        IsMaxOn
          (cubicRegularizedQuadraticDualFunction (gδ(δ)) H M)
          Dplus(gδ(δ))
          (lamDelta δ)) :
    Filter.Tendsto lamDelta (𝓝[>] (0 : ℝ))
      (𝓝 (-H_min[Hdiag])) := sorry

-- Proof sketch: first apply
-- `cubicRegularizedDiagonalPerturbedDualMaximizer_tendsto_boundary` to obtain
-- `λ_δ* → -H_min`. For each `δ > 0`, the same perturbed optimality hypothesis gives the scalar
-- boundary equation from `Proposition_4_1_11` and places `λ_δ*` in the strict interior region
-- `-H_min < λ_δ*`. These derived facts identify the inactive-coordinate limits from the canonical
-- perturbed resolvent formula, while the boundary equation determines the limiting value of
-- the distinguished active coordinate. For global minimality, route each perturbed dual maximizer
-- through the existing Chapter 4 owner theorem to identify the same resolvent point as a global
-- minimizer of the perturbed objective, then compare with the unperturbed objective and pass to
-- the limit as `δ → 0+`.
/-- Proposition 4.1.12: in the degenerate boundary case `G² = 0`, if `k ∈ I*` and each perturbed
objective `v_δ(h) = v(h) + δ h^(k)` has optimal dual point `λ_δ*`, then the corresponding
perturbed minimizers `h_*(δ) = -(H + λ_δ* I)⁻¹ (g + δ e_k)` converge as `δ → 0+` to the explicit
boundary point whose inactive coordinates are `-g^(i) / (H_i - H_min)` and whose `k`-th
coordinate is the negative square root appearing in the textbook formula; moreover, this boundary
point is a global minimizer of the original cubic-regularized quadratic objective. -/
theorem
    cubicRegularizedDiagonalPerturbedMinimizer_tendsto_boundary_and_isMinimizer
    (lamDelta : ℝ → ℝ)
    (hM : 0 < M)
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    (hopt_max :
      ∀ {δ : ℝ}, 0 < δ →
        IsMaxOn
          (cubicRegularizedQuadraticDualFunction (gδ(δ)) H M)
          Dplus(gδ(δ))
          (lamDelta δ)) :
    Filter.Tendsto (fun δ : ℝ ↦ hδ(lamDelta, δ))
        (𝓝[>] (0 : ℝ))
        (𝓝 (cubicRegularizedDiagonalBoundaryMinimizer g Hdiag M k)) ∧
      IsMinOn
        (cubicRegularizedQuadraticObjective g H M)
        Set.univ
        (cubicRegularizedDiagonalBoundaryMinimizer g Hdiag M k) := sorry

/-- Under the hypotheses of Proposition 4.1.12, the corresponding perturbed minimizers
`h_*(δ) = -(H + λ_δ* I)⁻¹ (g + δ e_k)` converge as `δ → 0+` to the explicit boundary point whose
inactive coordinates are `-g^(i) / (H_i - H_min)` and whose `k`-th coordinate is the negative
square root appearing in the textbook formula. -/
theorem cubicRegularizedDiagonalPerturbedMinimizer_tendsto_boundaryMinimizer
    (lamDelta : ℝ → ℝ)
    (hM : 0 < M)
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    (hopt_max :
      ∀ {δ : ℝ}, 0 < δ →
        IsMaxOn
          (cubicRegularizedQuadraticDualFunction (gδ(δ)) H M)
          Dplus(gδ(δ))
          (lamDelta δ)) :
    Filter.Tendsto (fun δ : ℝ ↦ hδ(lamDelta, δ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (cubicRegularizedDiagonalBoundaryMinimizer g Hdiag M k)) := by
  exact
    (cubicRegularizedDiagonalPerturbedMinimizer_tendsto_boundary_and_isMinimizer
      g Hdiag M k lamDelta hM hk hGzero hopt_max).1

/-- The boundary limit point is a global minimizer of the original cubic-regularized quadratic
problem once the perturbed dual maximizers are routed through the existing owner-level primal
minimizer API. -/
theorem cubicRegularizedDiagonalBoundaryMinimizer_isMinimizer_of_perturbedMinimizers
    (lamDelta : ℝ → ℝ)
    (hM : 0 < M)
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    (hopt_max :
      ∀ {δ : ℝ}, 0 < δ →
        IsMaxOn
          (cubicRegularizedQuadraticDualFunction (gδ(δ)) H M)
          Dplus(gδ(δ))
          (lamDelta δ)) :
    IsMinOn
      (cubicRegularizedQuadraticObjective g H M)
      Set.univ
      (cubicRegularizedDiagonalBoundaryMinimizer g Hdiag M k) := by
  exact
    (cubicRegularizedDiagonalPerturbedMinimizer_tendsto_boundary_and_isMinimizer
      g Hdiag M k lamDelta hM hk hGzero hopt_max).2

end
