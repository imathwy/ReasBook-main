import Mathlib
import FirstOrderMethodsinOptimization.Chap11.Definition_11_4
import FirstOrderMethodsinOptimization.Chap11.Lemma_11_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped Gradient

section

variable {ι : Type u} {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]

variable [Fintype ι]

-- Proof sketch: let `x⁺ = x + 𝒰_i(T_M^i(x) - x_i)`. The block descent lemma gives the quadratic
-- upper bound on `f x⁺` because `x ∈ effective_domain (separableSum g)` implies
-- `x ∈ interior (effective_domain f)`, and the updated point stays in the effective domain of the
-- block-separable regularizer, hence also in `interior (effective_domain f)`. The second prox
-- theorem controls the linear term together with the change in `g i`, while the remaining block
-- penalties are unchanged. Finally rewrite the residual `M • (x_i - T_M^i(x))` as `G_M^i(x)`.

namespace IsBlockProximalGradientProblem

variable {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
variable {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
variable {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
variable {Li : (i : ι) → PosReal}

local notation "F" => composite_model_objective f (separableSum g)

/- Domain sampling for this refinement:
- `IsBlockProximalGradientProblem.prox_point` and `gradient_mapping` from `Definition_11_4` are
  the canonical owner-level one-block update and residual.
- `IsBlockProximalGradientProblem.block_coordinate_update_prox_point_mem_effective_domain` from
  `Definition_11_4` is the canonical owner-level domain-preservation bridge for that update.
- `BlockProximalGradientAssumptions` is the source-facing owner extending the core block-problem
  owner by the convexity data used in Lemma 11.3.
- `BlockProximalGradientAssumptions.block_coordinate_descent_lemma` from `Lemma_11_2` is the
  upstream one-block quadratic upper-model bridge.

Lemma 11.3 is `source-facing`: it proves the textbook sufficient-decrease inequality for one block.
Its best owner layer is still the Chapter 11 block-problem owner; the convexity and arbitrary
block-Lipschitz constant `M` remain theorem hypotheses rather than new packaged data. -/

/-- Lemma 11.3: if the `i`-th block partial gradient is `M`-Lipschitz along block updates and
the block-separable effective domain lies in `interior (effective_domain f)`, then replacing the
`i`-th block by its one-block proximal-gradient update decreases the composite objective by at
least `(1 / (2 M)) ‖G_M^i(x)‖^2`. -/
theorem block_partial_gradient_sufficient_decrease_of_block_lipschitz
    (hproblem : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (i : ι) [ProperSpace (Ei i)] (M : PosReal)
    (h_block_gradient_lipschitz :
      ∀ (x : (i : ι) → Ei i) (d : Ei i)
        (_ : x ∈ interior (effective_domain f))
        (_ : block_coordinate_update x i d ∈ interior (effective_domain f)),
          ‖block_gradient i x - block_gradient i (block_coordinate_update x i d)‖ ≤
            (M : ℝ) * ‖d‖)
    (x : effective_domain (separableSum g)) :
    let x' : (j : ι) → Ei j := x;
    let xPlus := block_coordinate_update x' i (T[M; hproblem] x' i - x' i);
    F x' - F xPlus ≥
      ((((1 : ℝ) / (2 * (M : ℝ))) *
          ‖G[M; hproblem] x' i‖ ^ (2 : ℕ) : ℝ) : EReal) :=
  sorry

end IsBlockProximalGradientProblem

namespace BlockProximalGradientAssumptions

variable {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
variable {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
variable {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
variable {Lf : NNReal} {Li : (i : ι) → PosReal}

local notation "F" => composite_model_objective f (separableSum g)

/-- Under the Chapter 11 owner assumptions, the textbook one-block update with stepsize `L_i`
satisfies the sufficient-decrease estimate from Lemma 11.3. -/
theorem block_partial_gradient_sufficient_decrease
    (hproblem : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
    (i : ι) [ProperSpace (Ei i)] (x : effective_domain (separableSum g)) :
    let hcore : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li :=
      hproblem.toIsBlockProximalGradientProblem;
    let x' : (j : ι) → Ei j := x;
    let xPlus := block_coordinate_update x' i (T[Li i; hcore] x' i - x' i);
    F x' - F xPlus ≥
      ((((1 : ℝ) / (2 * (Li i : ℝ))) *
          ‖G[Li i; hcore] x' i‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  let hcore : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li :=
    hproblem.toIsBlockProximalGradientProblem
  simpa [hcore] using
    IsBlockProximalGradientProblem.block_partial_gradient_sufficient_decrease_of_block_lipschitz
      hcore
      hproblem.f_effective_domain_convex
      i
      (Li i)
      (fun x d hx hxd ↦ hproblem.block_partial_gradient_lipschitz i hx hxd)
      x

end BlockProximalGradientAssumptions

end
