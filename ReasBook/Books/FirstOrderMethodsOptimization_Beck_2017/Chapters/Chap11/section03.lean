import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_11_3 (from Chap11) -/
noncomputable section

open scoped BigOperators Gradient

universe u v

/- Definition 11.3 is recall-only in the block-coordinate composite-model setup.

Domain sampling identifies the existing owner abstractions:
- Chapter 10's `composite_model_objective` for the source-facing composite objective `F = f + g`;
- Chapter 6's owner `separableSum`, used on `PiLp 2 E` through the bridge `PiLp.separableSum`,
  for the block-separable term `x ↦ ∑ i, g_i (x_i)`;
- mathlib's `PiLp.single` for the block insertion map `𝒰ᵢ`;
- the ambient gradient `∇` on `PiLp 2 E`, with block coordinates as derived API;
- mathlib's `PiLp.norm_eq_of_L2` for the `L²` product norm formula.

The primitive data are only the smooth term `f`, the block penalties `g_i`, and the ambient
product space `PiLp (2 : ENNReal) E`. The block insertion map is canonical singleton data, while
the block gradients are derived from the ambient gradient rather than primitive fields. The old
local declarations were exact-interface wrappers around these owners, so the file should recall
those owners directly and keep only thin source-facing bridges for the textbook surfaces
`𝒰ᵢ`, `∇ᵢ f`, and `F(x) = f(x) + ∑ i, g_i(x_i)`. -/

/- Definition 11.3: on the block product `PiLp (2 : ENNReal) E`, the objective
`F(x) = f(x) + ∑ i, g_i(x_i)` is the canonical composite objective
`composite_model_objective f (PiLp.separableSum g)`, the block insertion map `𝒰ᵢ` is the canonical
singleton insertion `PiLp.single 2 i`, the block partial gradient `∇ᵢ f(x)` is the `i`-th
coordinate of `∇ f(x)`, and the block norm formula is `PiLp.norm_eq_of_L2`. -/
recall PiLp.separableSum
recall composite_model_objective
recall PiLp.single
recall PiLp.single_eq_same
recall PiLp.single_eq_of_ne
recall PiLp.norm_eq_of_L2

scoped[Gradient] notation "𝒰[" i "]" => @PiLp.single (2 : ENNReal) _ _ (Classical.decEq _) _ i

section

variable {ι : Type v} [Fintype ι]
variable {E : ι → Type u}

/-- Evaluating the Chapter 11 block composite objective means evaluating the Chapter 10 composite
objective with the Chapter 6 block-separable regularizer. -/
@[simp] theorem composite_model_objective_separableSum_apply
    (f : PiLp (2 : ENNReal) E → EReal) (g : ∀ i, E i → EReal) (x : PiLp (2 : ENNReal) E) :
    composite_model_objective f (PiLp.separableSum g) x = f x + ∑ i, g i (x i) := by
  simp

end

section

variable {ι : Type v}
variable {E : ι → Type u}
variable [∀ i, Zero (E i)]

/-- Definition 11.3 uses the canonical block insertion map `𝒰ᵢ : Eᵢ → PiLp 2 E`, implemented by
`PiLp.single`. At the distinguished block it returns the inserted vector. -/
@[simp] theorem block_coordinate_embedding_apply_same
    (i : ι) (d : E i) :
    (𝒰[i] d) i = d := by
  classical
  simp [PiLp.single_eq_same]

/-- Away from the distinguished block, the canonical insertion map `𝒰ᵢ` vanishes. -/
@[simp] theorem block_coordinate_embedding_apply_ne
    {i j : ι} (h : j ≠ i) (d : E i) :
    (𝒰[i] d) j = 0 := by
  classical
  simp [PiLp.single_eq_of_ne, h]

end

section

variable {ι : Type v} [Fintype ι]
variable {E : ι → Type u}
variable [∀ i, NormedAddCommGroup (E i)]
variable [∀ i, InnerProductSpace ℝ (E i)]
variable [∀ i, CompleteSpace (E i)]

/-- Definition 11.3's block partial gradient `∇ᵢ f(x)` is the `i`-th coordinate of the ambient
gradient `∇ f(x)` on `PiLp 2 E`. This bridge only needs the ambient Hilbert-space structure used
to form `∇ f x`, not finite-dimensional block coordinates. -/
abbrev block_partial_gradient
    (i : ι) (f : PiLp (2 : ENNReal) E → ℝ) : PiLp (2 : ENNReal) E → E i :=
  fun x ↦ (∇ f x) i

notation "∇[" i "] " f:arg => block_partial_gradient i f

/-- Evaluating the source-facing block-gradient notation gives the corresponding coordinate of the
ambient gradient. -/
@[simp] theorem block_partial_gradient_eq_gradient
    (f : PiLp (2 : ENNReal) E → ℝ) (x : PiLp (2 : ENNReal) E) (i : ι) :
    (∇[i] f) x = (∇ f x) i :=
  rfl

/-- The full gradient decomposes into its block partial gradients:
`∇ f(x) = (∇₁ f(x), …, ∇ₚ f(x))`. -/
theorem gradient_eq_block_partial_gradient
    (f : PiLp (2 : ENNReal) E → ℝ) (x : PiLp (2 : ENNReal) E) :
    ∇ f x = fun i ↦ (∇[i] f) x :=
  rfl

end

/-! ### Lemma_11_3 (from Chap11) -/
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
