import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap11.Algorithm_11_4
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap11.Lemma_11_4
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap11.Theorem_11_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v

open scoped Gradient

section

variable {p : ℕ} {Ei : Fin p → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, ProperSpace (Ei i)]
variable [InnerProductSpace ℝ ((i : Fin p) → Ei i)]
variable [ProperSpace ((i : Fin p) → Ei i)]

section

variable {f : ((i : Fin p) → Ei i) → EReal} {g : (i : Fin p) → Ei i → EReal}
variable {block_gradient : (i : Fin p) → ((j : Fin p) → Ei j) → Ei i}
variable {XStar : Set ((i : Fin p) → Ei i)} {FOpt : ℝ}
variable {Lf : NNReal} {Li : (i : Fin p) → PosReal}
variable [Nonempty (Fin p)]

variable (hproblem : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
variable (x0 : effective_domain (separableSum g))

/- Theorem 11.12 is `source-facing`: it states asymptotic properties of the CBPG outer sequence.
Domain sampling against the surrounding Chapter 11 files identifies the relevant owner
abstractions:
- `IsBlockProximalGradientProblem.interior_effective_domain_point` from Definition 11.4 is the
  canonical bridge from the primitive initial datum `x0 ∈ effective_domain (separableSum g)` to
  the initial interior-domain point needed by the CBPG iterate owner;
- `IsBlockProximalGradientProblem.gradient_mapping`, used through the owner notation
  `G[L; hproblem.toIsBlockProximalGradientProblem]`, is the canonical Chapter 11 residual owner
  attached to the block data;
- `cyclic_block_proximal_gradient_method` from Algorithm 11.4 is the owner of the outer-iterate
  sequence;
- `cbpg_min_block_stepsize` and `cbpg_max_block_stepsize` from Lemma 11.4 are the canonical
  owners for the block-step extrema entering the source constant.

Layer triage:
- `source-facing`: the vanishing-residual, best-residual, and cluster-point stationarity
  consequences below;
- `core/canonical`: the effective-domain initial datum together with the canonical bridge
  `x0 ↦ x0I`;
- `bridge/view`: any proof-level passage between this residual tuple and equivalent full-gradient
  presentations. -/

local notation "x0I" => hproblem.interior_effective_domain_point x0
local notation "x[" k "]" => cyclic_block_proximal_gradient_method hproblem x0I k
local notation "hcore" => hproblem.toIsBlockProximalGradientProblem
local notation "Lmin" => cbpg_min_block_stepsize Li
local notation "Lmax" => cbpg_max_block_stepsize Li
local notation "F" => composite_model_objective f (separableSum g)
local notation "Ccbpg" =>
  (Lmin : ℝ) / (2 * (((Lf : ℝ) + 2 * (Lmax : ℝ) + Real.sqrt ((Lmin : ℝ) * (Lmax : ℝ))) ^ (2 : ℕ)))
set_option quotPrecheck false in
local notation "Gcbpg" =>
  fun k i ↦ G[Lmin; hcore] x[k] i
local notation "R[" k "]" =>
  best_achieved_function_value (fun y ↦ ‖y‖) Gcbpg k

-- Proof sketch: combine the Chapter 11 sufficient-decrease estimate with monotonicity of the
-- `‖G_{L_min}(x^k)‖² / p`. Since `F(x^k)` is nonincreasing and bounded below by `F_opt`, the
-- consecutive differences tend to `0`, forcing the residual sequence to converge to `0`.
/-- Theorem 11.12 (1): clause (a). Under Assumption 11.1, the Chapter 11 residual tuple
`i ↦ G^i_{L_min}(x^k)` converges to `0` along the outer iterates. -/
theorem cbpg_gradient_mapping_tendsto_zero :
    Filter.Tendsto Gcbpg Filter.atTop (nhds 0) := sorry

-- Proof sketch: sum the sufficient-decrease inequality over `n = 0, ..., k`,
-- telescope the objective values, then bound the sum below by `(k + 1)` times the squared running
-- minimum of the residual norms.
/-- Theorem 11.12 (2): clause (b), written in the squared form used by the chapter API. The
running minimum of `‖(G^i_{L_min}(x^n))_i‖` over `0 ≤ n ≤ k` satisfies
`C (k + 1) (min_{0 ≤ n ≤ k} ‖(G^i_{L_min}(x^n))_i‖)^2 ≤ p (F(x^0) - F_opt)`. -/
theorem cbpg_best_gradient_mapping_norm_sq_le_objective_gap
    (k : ℕ) :
    (((Ccbpg * (k + 1 : ℝ) * R[k] ^ (2 : ℕ) : ℝ) :
        EReal)) ≤
      (p : EReal) * (F x0 - (FOpt : EReal)) := sorry

end

section

variable {f : ((i : Fin p) → Ei i) → EReal} {g : (i : Fin p) → Ei i → EReal}
variable {block_gradient : (i : Fin p) → ((j : Fin p) → Ei j) → Ei i}
variable {XStar : Set ((i : Fin p) → Ei i)} {FOpt : ℝ}
variable {Lf : NNReal} {Li : (i : Fin p) → PosReal}
local instance : NormedSpace ℝ ((i : Fin p) → Ei i) := InnerProductSpace.toNormedSpace
local instance : Module ℝ ((i : Fin p) → Ei i) := NormedSpace.toModule
variable [FiniteDimensional ℝ ((i : Fin p) → Ei i)]

variable (hproblem : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
variable (x0 : effective_domain (separableSum g))

local notation "x0I" => hproblem.interior_effective_domain_point x0
local notation "xSeq" => cyclic_block_proximal_gradient_method hproblem x0I
local notation "x[" k "]" => cyclic_block_proximal_gradient_method hproblem x0I k

-- Proof sketch: apply Theorem 11.1 with the constant block stepsize family
-- `M i = cbpg_min_block_stepsize Li`. Along a subsequence `x^{k_j} → xBar`, clause (1) gives
-- the vanishing of the Chapter 11 block owner `G^i_{L_min}(x^{k_j})` for every block `i`; the
-- block-Lipschitz data in `hproblem` lets these one-block residuals pass to the limit at `xBar`,
-- yielding `G^i_{L_min}(xBar) = 0` for all `i`, which is exactly the stationarity criterion from
-- Theorem 11.1.
/-- Theorem 11.12 (3): clause (c). Every sequential limit point of the CBPG outer sequence is a
stationary point of the composite problem with smooth term `f` and block-separable regularizer
`x ↦ ∑ i, g_i(x_i)`. -/
theorem cbpg_cluster_point_is_stationary
    {xBar : (i : Fin p) → Ei i}
    (hxBar : MapClusterPt xBar Filter.atTop xSeq) :
    is_stationary_point f (separableSum g) xBar := sorry

end

end

end
