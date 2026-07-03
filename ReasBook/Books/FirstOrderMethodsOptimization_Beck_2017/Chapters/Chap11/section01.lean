import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_11_1 (from Chap11) -/
/- Definition 11.1 is a `bridge/view` recall of the Chapter 8 finite-sum model. Domain sampling:
- `finite_sum_objective` is the upstream chapter owner for the aggregate objective
  `x ↦ ∑ i, f i x`;
- `finite_sum_objective_apply` is its pointwise evaluation formula;
- `isMinOn_finite_sum_objective_iff` is the canonical feasible-set bridge to the explicit sum.

The primitive data here is only the finite family `f : Fin m → E → α`; the aggregate objective
and the minimization reformulation are already owned upstream with the exact interface needed for
Definition 11.1. This file therefore recalls those declarations directly instead of keeping a
parallel Chapter 11 alias. -/
recall finite_sum_objective
recall finite_sum_objective_apply
recall isMinOn_finite_sum_objective_iff

/-! ### Lemma_11_1 (from Chap11) -/
noncomputable section

universe u v

open scoped Gradient

section

variable {ι : Type u} [Fintype ι] {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]

variable {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
variable {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}

section Bridge

variable [∀ i, ProperSpace (Ei i)]
variable [InnerProductSpace ℝ ((i : ι) → Ei i)]
variable [ProperSpace ((i : ι) → Ei i)]

local instance : NormedSpace ℝ ((i : ι) → Ei i) := InnerProductSpace.toNormedSpace
local instance : Module ℝ ((i : ι) → Ei i) := NormedSpace.toModule

/-
Lemma 11.1 is `bridge/view`: it compares the Chapter 10 full prox-gradient operator and gradient
mapping for the separable regularizer `separableSum g` with the tuple of Chapter 11 one-block prox
points and residuals. Domain sampling for this bridge uses the existing owners:
- `prox_grad_operator` / `gradient_mapping` from Chapter 10 for the aggregate operators;
- `block_partial_prox_grad_point` / `block_partial_gradient_mapping` from Definition 11.4 for the
  blockwise operators;
- `separableSum` from Chapter 6 for the regularizer itself.

The primitive bridge data are the block penalties together with an ambient product-space gradient
identification `∇ (fun y ↦ (f y).toReal) x = (block_gradient i x)_i` at the evaluation point. The
aggregate proper/closed/convex regularity of `separableSum g` already comes canonically from the
Chapter 11 API in Definition 11.4, so this file should reuse those upstream instances rather than
rebuild a parallel local instance layer. The full-residual identity is derived API once the
prox-point identity is known, so only the prox-point theorem should carry independent proof
content.
-/

variable [∀ i, IsProperExtendedRealFunction (g i)]
variable [∀ i, Fact (LowerSemicontinuous (g i))]
variable [∀ i, Fact (is_convex_function (g i))]

local notation "blockProper" => fun i ↦ (inferInstance : IsProperExtendedRealFunction (g i))
local notation "blockClosed" => fun i ↦ (Fact.out : LowerSemicontinuous (g i))
local notation "blockConvex" => fun i ↦ (Fact.out : is_convex_function (g i))

/-- Lemma 11.1 (1): for the aggregate regularizer `separableSum g`, the Chapter 10
proximal-gradient step at `x` is the singleton whose unique point is the tuple of the canonical
Chapter 11 block prox-gradient points `T_L^i(x)` under an explicit ambient gradient
identification hypothesis. -/
theorem proximal_gradient_step_eq_singleton_block_partial_prox_grad_point
    (L : PosReal)
    (x : interior (effective_domain f))
    (hgradient :
      HasGradientAt
        (fun y : (j : ι) → Ei j ↦ (f y).toReal)
        (fun i ↦ block_gradient i (x : (j : ι) → Ei j))
        (x : (j : ι) → Ei j)) :
    proximal_gradient_step f (separableSum g) (x : (j : ι) → Ei j) L =
      {fun i ↦ T[L; g, block_gradient, blockProper, blockClosed, blockConvex] x i} := by
  sorry

section FullOwner

variable [IsProperExtendedRealFunction (separableSum g)]
variable [Fact (LowerSemicontinuous (separableSum g))]
variable [Fact (is_convex_function (separableSum g))]

-- Proof sketch: compare the two singleton descriptions of the full Chapter 10 proximal-gradient
-- step, namely `prox_grad_operator_eq_singleton` and part (1), to identify the canonical full
-- prox point with the tuple of block prox points.
/-- Under the ambient gradient identification hypothesis, the Chapter 10 prox-gradient operator for
`(f, separableSum g)` equals the tuple of the Chapter 11 block prox-gradient points `T_L^i(x)`. -/
theorem full_prox_grad_operator_eq_block_partial_prox_grad_point
    (L : PosReal)
    (x : interior (effective_domain f))
    (hgradient :
      HasGradientAt
        (fun y : (j : ι) → Ei j ↦ (f y).toReal)
        (fun i ↦ block_gradient i (x : (j : ι) → Ei j))
        (x : (j : ι) → Ei j)) :
    prox_grad_operator f (separableSum g) L x =
      fun i ↦ T[L; g, block_gradient, blockProper, blockClosed, blockConvex] x i := by
  apply Set.singleton_injective
  calc
    ({prox_grad_operator f (separableSum g) L x} : Set ((j : ι) → Ei j)) =
        proximal_gradient_step f (separableSum g) (x : (j : ι) → Ei j) L := by
      symm
      exact prox_grad_operator_eq_singleton f (separableSum g) L x
    _ = {fun i ↦ T[L; g, block_gradient, blockProper, blockClosed, blockConvex] x i} :=
      proximal_gradient_step_eq_singleton_block_partial_prox_grad_point L x hgradient

-- Proof sketch: rewrite the Chapter 10 owner `G[L, f, separableSum g] x` by
-- `gradient_mapping_apply`, replace the full prox point by the tuple of block prox points via the
-- previous bridge, and then collapse the right-hand side coordinatewise with
-- `block_partial_gradient_mapping_def`.
/-- Lemma 11.1 (2): under the same ambient gradient identification hypothesis, the Chapter 10
gradient mapping for the separable regularizer `separableSum g` equals the tuple of the Chapter 11
block partial gradient mappings `G_L^i(x)`. -/
theorem full_gradient_mapping_eq_block_partial_gradient_mapping
    (L : PosReal)
    (x : interior (effective_domain f))
    (hgradient :
      HasGradientAt
        (fun y : (j : ι) → Ei j ↦ (f y).toReal)
        (fun i ↦ block_gradient i (x : (j : ι) → Ei j))
        (x : (j : ι) → Ei j)) :
    gradient_mapping f (separableSum g) L x =
      fun i ↦ G[L; g, block_gradient, blockProper, blockClosed, blockConvex] x i := by
  sorry

end FullOwner

-- Proof sketch: this is just the pointwise defining identity
-- `G_L^i(x) = L • (x_i - T_L^i(x))`, assembled back into the product space.
omit [Fintype ι] [InnerProductSpace ℝ ((i : ι) → Ei i)] [ProperSpace ((i : ι) → Ei i)] in
/-- Derived residual form of Lemma 11.1 (2): the full Chapter 10 residual equals the tuple of the
Chapter 11 block partial gradient mappings. -/
theorem full_residual_eq_block_partial_gradient_mapping
    (L : PosReal)
    (x : interior (effective_domain f)) :
    (L : ℝ) •
        ((x : (j : ι) → Ei j) -
          fun i ↦ T[L; g, block_gradient, blockProper, blockClosed, blockConvex] x i) =
      fun i ↦ G[L; g, block_gradient, blockProper, blockClosed, blockConvex] x i := by
  ext i
  simp [block_partial_gradient_mapping_def]

end Bridge

end

/-! ### Proposition_11_1 (from Chap11) -/
noncomputable section

universe u v

open scoped Gradient

/- Proposition 11.1 is `bridge/view` in the Chapter 11 block proximal-gradient domain. The owner
objects already live upstream in `Definition_11_4`:
- `BlockProximalGradientAssumptions` is the ambient block-problem owner;
- `block_coordinate_update` is the canonical one-block update map;
- `IsBlockProximalGradientProblem.gradient_mapping_def` is the canonical residual formula.

The primitive data here are only the owner `hproblem`, the selected block `i`, and the current
point `x`. The step-norm inequality is derived API: it rewrites the canonical sufficient-decrease
estimate from the gradient-mapping form into the full-update norm form. -/

section

variable {ι : Type u} [Fintype ι] {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable {Lf : NNReal} {Li : (i : ι) → PosReal}
variable {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
variable {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
variable {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}

local notation "F" => composite_model_objective f (separableSum g)

namespace BlockProximalGradientAssumptions

-- Proof sketch: apply the owner theorem
-- `BlockProximalGradientAssumptions.block_partial_gradient_sufficient_decrease` at the textbook
-- stepsize `M = L_i`. Rewrite the residual through the canonical owner theorem
-- `IsBlockProximalGradientProblem.gradient_mapping_def`, so the factor
-- `(1 / (2 L_i)) ‖G^i_{L_i}(x)‖²` becomes `(L_i / 2) ‖x_i - T_{L_i}^i(x)‖²`. Then identify the
-- full one-block update with `block_coordinate_update x i (T_{L_i}^i(x) - x_i)` and use
-- `Pi.norm_single` to rewrite that block residual norm as the full-step norm `‖x - x⁺‖`.
/-- Proposition 11.1: under the standing assumptions of the block proximal-gradient method, the
sufficient decrease inequality can be written in terms of the full one-block updated vector
`x⁺ = block_coordinate_update x i (T[Li i; hproblem] x i - x i)`, as
`F(x) - F(x⁺) ≥ (L_i / 2) ‖x - x⁺‖²`. -/
theorem block_partial_gradient_sufficient_decrease_step_norm
    (hproblem : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
    (i : ι) [ProperSpace (Ei i)] (x : effective_domain (separableSum g)) :
    let hcore : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li :=
      hproblem.toIsBlockProximalGradientProblem;
    let xPlus :=
      block_coordinate_update x.1 i (T[Li i; hcore] x.1 i - x.1 i);
    F x.1 - F xPlus ≥
      ((((Li i : ℝ) / 2) * ‖x.1 - xPlus‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  let hcore : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li :=
    hproblem.toIsBlockProximalGradientProblem
  let x' : (j : ι) → Ei j := x
  let xPlus := block_coordinate_update x' i (T[Li i; hcore] x' i - x' i)
  have hdecrease :
      F x' - F xPlus ≥
        ((((1 : ℝ) / (2 * (Li i : ℝ))) *
            ‖G[Li i; hcore] x' i‖ ^ (2 : ℕ) : ℝ) : EReal) := by
    simpa [hcore, x', xPlus] using hproblem.block_partial_gradient_sufficient_decrease i x
  have hdecrease' :
      F x' - F xPlus ≥
        ((((1 : ℝ) / (2 * (Li i : ℝ))) *
            ‖(Li i : ℝ) • (x' i - T[Li i; hcore] x' i)‖ ^ (2 : ℕ) : ℝ) : EReal) := by
    simpa only [IsBlockProximalGradientProblem.gradient_mapping_def] using hdecrease
  have hstep :
      x' - xPlus = 𝒰[i] (x' i - T[Li i; hcore] x' i) := by
    classical
    ext j
    by_cases hj : j = i
    · subst j
      simp [xPlus, block_coordinate_update_apply_same]
    · simp [xPlus, block_coordinate_update_apply_ne, hj]
  have hnorm :
      ‖x' - xPlus‖ = ‖x' i - T[Li i; hcore] x' i‖ := by
    classical
    rw [hstep]
    have hsingle :
        ‖Pi.single i (x' i - T[Li i; hcore] x' i)‖ =
          ‖x' i - T[Li i; hcore] x' i‖ := by
      simpa using (Pi.norm_single (x' i - T[Li i; hcore] x' i))
    simpa using hsingle
  have hcoeff :
      (((1 : ℝ) / (2 * (Li i : ℝ))) *
          ‖(Li i : ℝ) • (x' i - T[Li i; hcore] x' i)‖ ^ (2 : ℕ) : ℝ) =
        (((Li i : ℝ) / 2) * ‖x' - xPlus‖ ^ (2 : ℕ) : ℝ) := by
    have hLi_ne : (Li i : ℝ) ≠ 0 := ne_of_gt (Li i).2
    rw [norm_smul, Real.norm_of_nonneg (show 0 ≤ (Li i : ℝ) by exact le_of_lt (Li i).2), hnorm]
    field_simp [hLi_ne]
  have hcoeffE :
      (((((1 : ℝ) / (2 * (Li i : ℝ))) *
            ‖(Li i : ℝ) • (x' i - T[Li i; hcore] x' i)‖ ^ (2 : ℕ) : ℝ)) : EReal) =
        ((((Li i : ℝ) / 2) * ‖x' - xPlus‖ ^ (2 : ℕ) : ℝ) : EReal) :=
    congrArg (fun r : ℝ ↦ (r : EReal)) hcoeff
  rw [hcoeffE] at hdecrease'
  simpa [hcore, x', xPlus] using hdecrease'

end BlockProximalGradientAssumptions

end

/-! ### Theorem_11_1 (from Chap11) -/
open scoped Gradient Pointwise

noncomputable section

universe u v

section

variable {ι : Type u} [Fintype ι] {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [instBlockInner : InnerProductSpace ℝ ((i : ι) → Ei i)]
local instance : NormedSpace ℝ ((i : ι) → Ei i) := InnerProductSpace.toNormedSpace
local instance : Module ℝ ((i : ι) → Ei i) := NormedSpace.toModule
variable [FiniteDimensional ℝ ((i : ι) → Ei i)]

-- Proof sketch: unfold the Chapter 3 owner `is_stationary_point` for the composite problem
-- `f + separableSum g`, keeping the source-faithful finite-domain interior condition from
-- Definition 3.10. Derive the block restrictions of the ambient gradient from the source-facing
-- block-slice hypotheses
-- `HasFDerivAt (block_coordinate_slice f x i)
--    (InnerProductSpace.toDualMap ℝ (Ei i) (block_gradient i x)) 0`, and rewrite the
-- block-separable subdifferential into its coordinatewise Euclidean/vector-side form.
/-- Theorem 11.1 (1): under the blockwise proper/closed/convex hypotheses on `g_i`, stationarity
of the composite problem with regularizer `x ↦ ∑ i, g_i(x_i)` is equivalent to the coordinatewise
block condition `-∇ᵢ f(x) ∈ ∂ g_i(x_i)`, expressed through the Chapter 3 vector-side bridge
`euclideanSubdifferential`; the chosen block gradients are assumed to be the gradients of the
one-block slices `d ↦ f(x + Pi.single i d)` at `d = 0`, at points where `f` is finite-valued as
required by the Chapter 3 stationarity owner. -/
theorem is_stationary_point_iff_coordinatewise_negative_block_gradient_mem_euclideanSubdifferential
    {f : ((i : ι) → Ei i) → EReal}
    {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_closed : ∀ i, LowerSemicontinuous (g i))
    (hg_convex : ∀ i, is_convex_function (g i))
    (hblock_fderiv_spec : ∀ (i : ι) {x : ((j : ι) → Ei j)},
        x ∈ interior (finite_domain f) →
          HasFDerivAt (block_coordinate_slice f x i)
            (InnerProductSpace.toDualMap ℝ (Ei i) (block_gradient i x)) 0)
    (x : interior (finite_domain f)) :
    is_stationary_point f (separableSum g) (x : ((i : ι) → Ei i)) ↔
      ∀ i : ι,
        -(block_gradient i (x : ((i : ι) → Ei i))) ∈
          euclideanSubdifferential (g i) ((x : ((i : ι) → Ei i)) i) :=
  -- TODO: the source-faithful proof rewrites stationarity using the ambient gradient of
  -- `fun y ↦ (f y).toReal` and then splits `∂ (separableSum g)` coordinatewise. As written, the
  -- hypotheses only provide separate block-slice Fréchet derivatives, which do not suffice to
  -- recover `DifferentiableAt` of the ambient product-space map.
  sorry

end

section

variable {ι : Type u} [Fintype ι] {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, ProperSpace (Ei i)]

end

section

variable {ι : Type u} {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, ProperSpace (Ei i)]

-- Proof sketch: positive scaling by `1 / M` preserves properness, lower semicontinuity, and
-- convexity of `g i`; then `prox_eq_singleton_of_proper_closed_convex` identifies the relevant
-- proximal set as a singleton, and `block_partial_prox_grad_point` is defined to be its unique
-- point.
/-- The one-block proximal-gradient point is the unique proximal point of `(1 / M) g_i` at
`x_i - (1 / M) • block_gradient_i(x)`. -/
theorem block_partial_prox_grad_point_eq_singleton
    (g : (i : ι) → Ei i → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_closed : ∀ i, LowerSemicontinuous (g i))
    (hg_convex : ∀ i, is_convex_function (g i))
    (M : PosReal) (x : ((i : ι) → Ei i)) (i : ι) :
    prox[((((1 / M : PosReal) : EReal) • g i))]
      (x i - (1 / M : ℝ) • block_gradient i x) =
        {T[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i} :=
  by
    let hscaled :=
      scaled_function_proper_closed_convex_of_pos
        (g i) (hg_proper i) (hg_closed i) (hg_convex i) (1 / M)
    -- The Chapter 11 block prox point is defined by choosing the unique element of this singleton.
    simpa [block_partial_prox_grad_point, hscaled] using
      (Classical.choose_spec <|
        prox_eq_singleton_of_proper_closed_convex
          ((((1 / M : PosReal) : EReal) • g i))
          hscaled.1
          hscaled.2.1
          hscaled.2.2
          (x i - (1 / M : ℝ) • block_gradient i x))

end

section

variable {ι : Type u} [Fintype ι] {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, ProperSpace (Ei i)]

-- Proof sketch: rewrite `G^i_{M_i}(x) = 0` via the defining residual formula, apply the second
-- prox theorem blockwise to identify the proximal fixed-point condition with blockwise
-- subdifferential membership, and then invoke part (1) at the same finite-domain interior point.
section

variable [instBlockInner : InnerProductSpace ℝ ((i : ι) → Ei i)]
local instance : NormedSpace ℝ ((i : ι) → Ei i) := InnerProductSpace.toNormedSpace
local instance : Module ℝ ((i : ι) → Ei i) := NormedSpace.toModule
variable [FiniteDimensional ℝ ((i : ι) → Ei i)]

/-- Helper for Theorem 11.1: for a fixed block, vanishing of the block gradient mapping is
equivalent to the negative block gradient belonging to the Euclidean subdifferential of the
corresponding block penalty. -/
theorem block_partial_gradient_mapping_eq_zero_iff_negative_block_gradient_mem_euclideanSubdifferential
    {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_closed : ∀ i, LowerSemicontinuous (g i))
    (hg_convex : ∀ i, is_convex_function (g i))
    (M : PosReal) (x : ((i : ι) → Ei i)) (i : ι) :
    G[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i = 0 ↔
      -(block_gradient i x) ∈ euclideanSubdifferential (g i) (x i) := by
  have hfixed :
      G[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i = 0 ↔
        T[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i = x i := by
    constructor
    · intro hG
      have hM_ne : (M : ℝ) ≠ 0 := ne_of_gt (PosReal.coe_pos M)
      have hres :
          x i - T[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i = 0 := by
        rw [block_partial_gradient_mapping_def] at hG
        exact (smul_eq_zero.mp hG).resolve_left hM_ne
      -- A zero residual means the prox point is already the current block.
      exact (sub_eq_zero.mp hres).symm
    · intro hT
      -- Conversely, a blockwise fixed point makes the residual formula collapse to zero.
      rw [block_partial_gradient_mapping_def, hT]
      simp
  have hprox_self :
      T[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i = x i ↔
        prox[((((1 / M : PosReal) : EReal) • g i))]
          (x i - (1 / M : ℝ) • block_gradient i x) = {x i} := by
    constructor
    · intro hT
      -- Rewrite only the singleton target, leaving the forward point unchanged.
      simpa [hT] using
        block_partial_prox_grad_point_eq_singleton
          g block_gradient hg_proper hg_closed hg_convex M x i
    · intro hprox
      have hsingleton :
          ({T[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i} : Set (Ei i)) =
            ({x i} : Set (Ei i)) := by
        calc
          ({T[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i} : Set (Ei i)) =
              prox[((((1 / M : PosReal) : EReal) • g i))]
                (x i - (1 / M : ℝ) • block_gradient i x) := by
            symm
            exact
              block_partial_prox_grad_point_eq_singleton
                g block_gradient hg_proper hg_closed hg_convex M x i
          _ = ({x i} : Set (Ei i)) := hprox
      have hmem :
          T[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i ∈
            ({x i} : Set (Ei i)) := by
        simpa [hsingleton] using
          (show T[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i ∈
              ({T[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i} : Set (Ei i)) by
            simp)
      simpa using hmem
  have hprox_sub :
      prox[((((1 / M : PosReal) : EReal) • g i))]
          (x i - (1 / M : ℝ) • block_gradient i x) = {x i} ↔
        (((1 / M : ℝ) •
            (-InnerProductSpace.toDual ℝ (Ei i) (block_gradient i x) :
              Module.Dual ℝ (Ei i))) :
              Module.Dual ℝ (Ei i)) ∈
          subdifferential ((((1 / M : PosReal) : EReal) • g i)) (x i) := by
    have hscaled :=
      scaled_function_proper_closed_convex_of_pos
        (g i) (hg_proper i) (hg_closed i) (hg_convex i) (1 / M)
    have hprox :
        prox[((((1 / M : PosReal) : EReal) • g i))]
            (x i - (1 / M : ℝ) • block_gradient i x) = {x i} ↔
          InnerProductSpace.toDualMap ℝ (Ei i)
              ((x i - (1 / M : ℝ) • block_gradient i x) - x i) ∈
            strongDualSubdifferential ((((1 / M : PosReal) : EReal) • g i)) (x i) := by
      -- Apply the second prox theorem to the scaled block penalty at the forward block-gradient
      -- point.
      simpa using
        (prox_eq_singleton_iff_toDualMap_sub_mem_strongDualSubdifferential
          ((((1 / M : PosReal) : EReal) • g i))
          hscaled.1
          hscaled.2.2
          (x i - (1 / M : ℝ) • block_gradient i x)
          (x i))
    -- Rewrite the strong-dual conclusion into the Chapter 3 owner `subdifferential`.
    simpa [mem_strongDualSubdifferential, InnerProductSpace.toDual_apply_eq_toDualMap_apply,
      sub_eq_add_neg, smul_neg, neg_smul] using hprox
  have hscaled_sub :
      (((1 / M : ℝ) •
          (-InnerProductSpace.toDual ℝ (Ei i) (block_gradient i x) :
            Module.Dual ℝ (Ei i))) :
            Module.Dual ℝ (Ei i)) ∈
        subdifferential ((((1 / M : PosReal) : EReal) • g i)) (x i) ↔
      (-InnerProductSpace.toDual ℝ (Ei i) (block_gradient i x) :
          Module.Dual ℝ (Ei i)) ∈
        subdifferential (g i) (x i) := by
    have hM_pos : 0 < (1 / M : ℝ) := one_div_pos.mpr (PosReal.coe_pos M)
    have hscaled :
        subdifferential ((((1 / M : PosReal) : EReal) • g i)) (x i) =
          (1 / M : ℝ) • subdifferential (g i) (x i) := by
      simpa [Pi.smul_apply, smul_eq_mul] using
        (subdifferential_pos_real_mul (g i) (1 / M : ℝ) hM_pos (x i))
    have hM_ne : (1 / M : ℝ) ≠ 0 := ne_of_gt hM_pos
    -- Positive scaling of the block penalty scales the owner subdifferential by the same scalar.
    constructor
    · intro hmem
      rw [hscaled, Set.mem_smul_set] at hmem
      rcases hmem with ⟨y, hy, hy_eq⟩
      have hy' :
          y =
            (-InnerProductSpace.toDual ℝ (Ei i) (block_gradient i x) :
              Module.Dual ℝ (Ei i)) := by
        have hM0 : (M : ℝ) ≠ 0 := ne_of_gt (PosReal.coe_pos M)
        have happly :=
          congrArg (fun z : Module.Dual ℝ (Ei i) ↦ ((1 / M : ℝ)⁻¹) • z) hy_eq
        simpa [smul_smul, one_div, hM0] using happly
      simpa [hy'] using hy
    · intro hmem
      rw [hscaled, Set.mem_smul_set]
      refine ⟨(-InnerProductSpace.toDual ℝ (Ei i) (block_gradient i x) :
          Module.Dual ℝ (Ei i)), hmem, ?_⟩
      simp
  have heuclidean :
      (-InnerProductSpace.toDual ℝ (Ei i) (block_gradient i x) :
          Module.Dual ℝ (Ei i)) ∈
        subdifferential (g i) (x i) ↔
      -(block_gradient i x) ∈ euclideanSubdifferential (g i) (x i) := by
    -- The owner subdifferential and the Euclidean/block-vector view are the same via Riesz.
    simpa [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential,
      InnerProductSpace.toDual_apply_eq_toDualMap_apply]
  calc
    G[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i = 0 ↔
        T[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i = x i := hfixed
    _ ↔
        prox[((((1 / M : PosReal) : EReal) • g i))]
          (x i - (1 / M : ℝ) • block_gradient i x) = {x i} := hprox_self
    _ ↔
        (((1 / M : ℝ) •
            (-InnerProductSpace.toDual ℝ (Ei i) (block_gradient i x) :
              Module.Dual ℝ (Ei i))) :
              Module.Dual ℝ (Ei i)) ∈
          subdifferential ((((1 / M : PosReal) : EReal) • g i)) (x i) := hprox_sub
    _ ↔
        (-InnerProductSpace.toDual ℝ (Ei i) (block_gradient i x) :
            Module.Dual ℝ (Ei i)) ∈
          subdifferential (g i) (x i) := hscaled_sub
    _ ↔ -(block_gradient i x) ∈ euclideanSubdifferential (g i) (x i) := heuclidean

/-- Theorem 11.1 (2): for any positive block stepsizes `M i`, stationarity of the block-separable
composite problem is equivalent to vanishing of every block gradient mapping `G^i_{M_i}(x)`,
assuming only the blockwise proper/closed/convex hypotheses needed to define `G^i_{M_i}` and the
block-slice Fréchet-derivative specification for the chosen block partial gradients, again at
points in the interior of the finite domain of `f` required by the stationarity owner. -/
theorem is_stationary_point_iff_block_partial_gradient_mapping_eq_zero
    {f : ((i : ι) → Ei i) → EReal}
    {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_closed : ∀ i, LowerSemicontinuous (g i))
    (hg_convex : ∀ i, is_convex_function (g i))
    (hblock_fderiv_spec : ∀ (i : ι) {x : ((j : ι) → Ei j)},
        x ∈ interior (finite_domain f) →
          HasFDerivAt (block_coordinate_slice f x i)
            (InnerProductSpace.toDualMap ℝ (Ei i) (block_gradient i x)) 0)
    (M : (i : ι) → PosReal) (x : interior (finite_domain f)) :
    is_stationary_point f (separableSum g) (x : ((i : ι) → Ei i)) ↔
      ∀ i : ι,
        G[M i; g, block_gradient, hg_proper, hg_closed, hg_convex]
          (x : ((i : ι) → Ei i)) i = 0 :=
  -- TODO: part (b) is reduced blockwise by
  -- `block_partial_gradient_mapping_eq_zero_iff_negative_block_gradient_mem_euclideanSubdifferential`,
  -- then closed using part (a). The remaining blocker is the missing ambient differentiability
  -- hypothesis needed to justify part (a) as stated.
  sorry

end

end
