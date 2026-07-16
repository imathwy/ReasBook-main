import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap01.Definition_1_37
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap11.Definition_11_13
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap11.Theorem_11_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped BigOperators

section

variable {ι : Type u} {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, NormedSpace ℝ (Ei i)]

/-- The realized block-index history `ξ_{k-1}` encoded as the first `k` sampled indices. -/
def randomized_block_history (sampled_block : ℕ → ι) (k : ℕ) : Fin k → ι :=
  fun t ↦ sampled_block t

-- Proof sketch: unfold `randomized_block_history`; the `t`-th coordinate of the prefix history is
-- definitionally the sampled block `sampled_block t`.
/-- Evaluating the realized history `ξ_{k-1}` at the time `t < k` returns the sampled block
`i_t`. -/
@[simp] theorem randomized_block_history_apply
    (sampled_block : ℕ → ι) (k : ℕ) (t : Fin k) :
    randomized_block_history sampled_block k t = sampled_block t := rfl

variable [Fintype ι]

scoped[RBPG] notation "‖" x "‖_[" L "]" =>
  compositeWeightedL2Norm L x

scoped[RBPG] notation "‖" x "‖_[" L ",*]" =>
  compositeWeightedL2Norm (fun i ↦ (L i)⁻¹) x

open scoped RBPG

-- Proof sketch: rewrite the Chapter 11 notation `‖x‖_[L]` to the Chapter 1 owner
-- `compositeWeightedL2Norm`, then apply `compositeWeightedL2Norm_def`.
/-- The weighted block norm has the textbook formula `√(∑ i, L_i ‖x_i‖²)`. -/
theorem randomized_block_weighted_norm_def
    (L : ι → PosReal) (x : (i : ι) → Ei i) :
    ‖x‖_[L] = √(∑ i, (L i : ℝ) * ‖x i‖ ^ (2 : ℕ)) := by
  simpa using compositeWeightedL2Norm_def L x

-- Proof sketch: rewrite the Chapter 11 notation `‖x‖_[L,*]` to the Chapter 1 owner
-- `compositeWeightedL2Norm`, then apply `compositeWeightedL2Norm_def`.
/-- The dual weighted block norm has the textbook formula
`√(∑ i, (1 / L_i) ‖x_i‖²)`. -/
theorem randomized_block_weighted_dual_norm_def
    (L : ι → PosReal) (x : (i : ι) → Ei i) :
    ‖x‖_[L,*] = √(∑ i, ((L i : ℝ)⁻¹) * ‖x i‖ ^ (2 : ℕ)) := by
  simpa using compositeWeightedL2Norm_def (fun i ↦ (L i)⁻¹) x

end

section

open scoped Gradient RBPG

variable {ι : Type u} [Fintype ι] {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, ProperSpace (Ei i)]
variable {Li : ι → PosReal}

variable {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
variable {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
variable {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}

namespace IsBlockProximalGradientProblem

/-- Definition 11.14: the coordinatewise randomized block gradient mapping `\tilde G(x)` whose
`i`-th block is the partial gradient mapping `G^i_{L_i}(x)`. -/
abbrev randomized_gradient_mapping
    (hproblem : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li) :
    interior (effective_domain f) → ((i : ι) → Ei i) :=
  fun x i ↦ hproblem.gradient_mapping (Li i) i (x : (j : ι) → Ei j)

-- Proof sketch: unfold `randomized_gradient_mapping`; its `i`-th coordinate is definitionally
-- `G^i_{L_i}(x)`.
/-- Evaluating the `i`-th coordinate of `\tilde G(x)` gives the partial gradient mapping
`G^i_{L_i}(x)`. -/
@[simp] theorem randomized_gradient_mapping_apply
    (hproblem : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (x : interior (effective_domain f)) (i : ι) :
    hproblem.randomized_gradient_mapping x i =
      hproblem.gradient_mapping (Li i) i (x : (j : ι) → Ei j) := rfl

end IsBlockProximalGradientProblem

end
