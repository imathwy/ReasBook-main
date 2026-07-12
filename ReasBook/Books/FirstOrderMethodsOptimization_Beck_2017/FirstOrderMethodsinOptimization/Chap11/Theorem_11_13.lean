import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_10
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Algorithm_11_5
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_13
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Lemma_11_2
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Theorem_11_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped Gradient

section

variable {ι : Type u} {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
variable {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
variable {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}

/- 
Theorem 11.13 has two nearby abstraction layers. The one-step decrease estimate is
`source-facing` and depends on `RandomizedBlockProximalGradientAssumptions`. The iterate-domain
persistence statement below is only a `bridge/view`: it uses the Chapter 11
`core/canonical` owner `IsBlockProximalGradientProblem`, together with the pathwise iterate owner
`randomized_block_proximal_gradient_method` and the canonical bridge from a primitive initial
datum `x0 ∈ effective_domain (separableSum g)` to an interior-domain starting point,
`IsBlockProximalGradientProblem.interior_effective_domain_point`.
-/

/-- Helper for Theorem 11.13: affine combinations of two one-block updates at the same block are
again the one-block update of the affine-combined displacements. -/
lemma block_coordinate_update_combo
    (x : (j : ι) → Ei j) (i : ι) (d e : Ei i) {a b : ℝ} (hab : a + b = 1) :
    a • block_coordinate_update x i d + b • block_coordinate_update x i e =
      block_coordinate_update x i (a • d + b • e) := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    calc
      a • block_coordinate_update x i d i + b • block_coordinate_update x i e i
          = (a • x i + b • x i) + (a • d + b • e) := by
              simp [block_coordinate_update, smul_add, add_assoc, add_left_comm, add_comm]
      _ = (a + b) • x i + (a • d + b • e) := by
            rw [← add_smul]
      _ = x i + (a • d + b • e) := by
            simp [hab]
      _ = block_coordinate_update x i (a • d + b • e) i := by
            simp [block_coordinate_update]
  · calc
      a • block_coordinate_update x i d j + b • block_coordinate_update x i e j
          = a • x j + b • x j := by
              simp [block_coordinate_update, hji]
      _ = (a + b) • x j := by
            rw [← add_smul]
      _ = block_coordinate_update x i (a • d + b • e) j := by
            simp [block_coordinate_update, hji, hab]

/-- Helper for Theorem 11.13: convexity of `effective_domain f` makes the admissible one-block
slice domain `{d | x + 𝒰[i] d ∈ interior (effective_domain f)}` convex. -/
lemma block_coordinate_slice_domain_convex_of_effective_domain_convex
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (i : ι) {x : (j : ι) → Ei j} :
    Convex ℝ {d : Ei i | x + 𝒰[i] d ∈ interior (effective_domain f)} := by
  let hinterior : Convex ℝ (interior (effective_domain f)) :=
    hf_effective_domain_convex.interior
  intro d hd e he a b ha hb hab
  have hcomb := hinterior hd he ha hb hab
  have hcomb' :
      a • block_coordinate_update x i d + b • block_coordinate_update x i e ∈
        interior (effective_domain f) := by
    simpa [block_coordinate_update] using hcomb
  have hcomb'' :
      block_coordinate_update x i (a • d + b • e) ∈ interior (effective_domain f) := by
    simpa [block_coordinate_update_combo x i d e hab] using hcomb'
  simpa [block_coordinate_update] using hcomb''

end

section

variable {ι : Type u} [Fintype ι] {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable {Li : (i : ι) → PosReal}

variable {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
variable {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
variable {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}

/-- Helper for Theorem 11.13: a finite block-separable value is the coercion of the sum of the
coordinatewise real values. -/
lemma separableSum_eq_coe_toReal_sum
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    {x : (i : ι) → Ei i} (hx : x ∈ effective_domain (separableSum g)) :
    separableSum g x = (((∑ i, (g i (x i)).toReal : ℝ) : EReal)) := by
  sorry

namespace IsBlockProximalGradientProblem

/-- Helper for Theorem 11.13: at a point of `effective_domain (separableSum g)`, the composite
objective is the coercion of the real smooth value plus the sum of the coordinatewise real penalty
values. -/
lemma composite_model_objective_eq_coe_toReal_sum
    (hproblem : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    {x : (i : ι) → Ei i} (hx : x ∈ effective_domain (separableSum g)) :
    composite_model_objective f (separableSum g) x =
      ((((f x).toReal + ∑ i, (g i (x i)).toReal : ℝ)) : EReal) := by
  sorry

end IsBlockProximalGradientProblem

section

variable [∀ i, ProperSpace (Ei i)]

namespace IsBlockProximalGradientProblem

/-- Helper for Theorem 11.13: the singleton proximal optimality condition bounds the selected
block linear term by the change in the selected block penalty. -/
lemma prox_point_linear_term_le_toReal
    (hproblem : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (M : PosReal) (i : ι) (x : effective_domain (separableSum g)) :
    let x' : (j : ι) → Ei j := x
    let xPlus := hproblem.prox_point M i x'
    inner ℝ (block_gradient i x') (xPlus - x' i) ≤
      -(M : ℝ) * ‖xPlus - x' i‖ ^ (2 : ℕ) +
        (g i (x' i)).toReal - (g i xPlus).toReal := by
  sorry

variable (hproblem : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
variable (x0 : effective_domain (separableSum g))
variable (sampled_block : ℕ → ι)

local notation "x0I" => hproblem.interior_effective_domain_point x0
local notation "i[" k "]" => sampled_block k
local notation "x[" k "]" =>
  randomized_block_proximal_gradient_method hproblem x0I sampled_block k

-- Proof sketch: argue by induction on `k`. The base case is `x0.2`. For the inductive step,
-- `x[k + 1]` is obtained from `x[k]` by one realized RBPG update, and
-- `block_coordinate_update_prox_point_mem_effective_domain` preserves the effective domain of the
-- block-separable regularizer.
/-- Every realized RBPG iterate remains in the effective domain of the block-separable
regularizer, provided the initial point does. -/
theorem randomized_block_proximal_gradient_iterate_mem_effective_domain
    (k : ℕ) :
    x[k] ∈ effective_domain (separableSum g) := by
  induction k with
  | zero =>
      exact x0.2
  | succ k hk =>
      rw [randomized_block_proximal_gradient_method_succ]
      simpa using
        hproblem.block_coordinate_update_prox_point_mem_effective_domain
          (Li i[k])
          ⟨x[k], hk⟩
          i[k]

end IsBlockProximalGradientProblem

namespace RandomizedBlockProximalGradientAssumptions

variable (hproblem : RandomizedBlockProximalGradientAssumptions f g block_gradient XStar FOpt Li)
variable (x0 : effective_domain (separableSum g))
variable (sampled_block : ℕ → ι)

local notation "hcore" => hproblem.toIsBlockProximalGradientProblem
local notation "x0I" => hproblem.interior_effective_domain_point x0
local notation "i[" k "]" => sampled_block k
local notation "x[" k "]" =>
  randomized_block_proximal_gradient_method hcore x0I sampled_block k
local notation "F" => composite_model_objective f (separableSum g)

/-- Helper for Theorem 11.13: every owner-level one-block RBPG update satisfies the textbook
sufficient-decrease estimate at points of `effective_domain (separableSum g)`. -/
lemma block_update_sufficient_decrease
    (x : effective_domain (separableSum g)) (i : ι) :
    let x' : (j : ι) → Ei j := x
    let d : Ei i :=
      T[Li i; hproblem.toIsBlockProximalGradientProblem] x' i - x' i
    let xPlus := block_coordinate_update x' i d
    F x' - F xPlus ≥
      ((((1 : ℝ) / (2 * (Li i : ℝ))) *
          ‖G[Li i; hcore] x' i‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  sorry

-- Proof sketch: combine the iterate-domain theorem with the one-block decrease estimate above,
-- specialized to the current iterate `x[k]` and the realized sampled block `i_k = sampled_block
-- k`.
/-- Theorem 11.13: along any realized RBPG sample path, each step decreases the composite
objective by at least `(1 / (2 L_{i_k})) ‖G^{i_k}_{L_{i_k}}(x^k)‖^2`. -/
theorem randomized_block_proximal_gradient_sufficient_decrease
    (k : ℕ) :
    F x[k] - F x[k + 1] ≥
      ((((1 : ℝ) / (2 * (Li i[k] : ℝ))) *
          ‖G[Li i[k]; hcore] x[k] i[k]‖ ^
            (2 : ℕ) :
          ℝ) :
        EReal) := by
  sorry

end RandomizedBlockProximalGradientAssumptions

end

end
