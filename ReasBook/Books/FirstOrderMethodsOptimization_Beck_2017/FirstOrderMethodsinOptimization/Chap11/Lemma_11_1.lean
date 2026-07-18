import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Theorem_6_6
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap10.Definition_10_5
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap11.Definition_11_4

-- Declarations for this item will be appended below by the statement pipeline.

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

local instance instNormedSpaceRealForallLemma11_1 : NormedSpace ℝ ((i : ι) → Ei i) :=
  InnerProductSpace.toNormedSpace
local instance instModuleRealForallLemma11_1 : Module ℝ ((i : ι) → Ei i) :=
  NormedSpace.toModule

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
