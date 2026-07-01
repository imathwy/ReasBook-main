import Mathlib
import FirstOrderMethodsinOptimization.Chap10.Definition_10_5
import FirstOrderMethodsinOptimization.Chap11.Algorithm_11_4
import FirstOrderMethodsinOptimization.Chap11.Lemma_11_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v

open scoped Gradient

section

variable {p : ℕ} {Ei : Fin p → Type v}
variable [Nonempty (Fin p)]

variable {Li : (i : Fin p) → PosReal}

/- Lemma 11.5 is a `bridge/view` statement in the Chapter 11 CBPG domain.

Domain sampling identifies:
- `cbpg_min_block_stepsize` and `cbpg_max_block_stepsize` from Lemma 11.4 as the owner
  abstractions for the finite block-step family extrema;
- `G[L, f, g]` from Definition 10.5 as the owner of the full gradient mapping residual;
- `BlockProximalGradientAssumptions.toIsCompositeSmoothMinimizationProblem` from
  Definition 11.4 as the canonical bridge from the blockwise Chapter 11 owner to the Chapter 10
  composite-problem owner supplying proper/closed/convex regularity for `separableSum g`;
- `cyclic_block_proximal_gradient_method` from Algorithm 11.4 as the owner of the outer iterate
  sequence;
- `cbpg_sufficient_decrease_outer_step` from Lemma 11.4 as the previous one-cycle decrease owner.

Primitive data here are only `Lf` and the block-step family `Li`. The scalar coefficient below is
derived API for Lemma 11.5, so the file should reuse the extrema owners from Lemma 11.4 instead
of redefining a parallel local maximum owner. -/

/-- The constant `C` appearing in the version-II sufficient-decrease estimate for the cyclic
block proximal gradient method. -/
def cbpg_sufficient_decrease_constant (Lf : NNReal) (Li : (i : Fin p) → PosReal) : ℝ :=
  (cbpg_min_block_stepsize Li : ℝ) /
    (2 *
      (((Lf : ℝ) + 2 * (cbpg_max_block_stepsize Li : ℝ) +
            Real.sqrt
              ((cbpg_min_block_stepsize Li : ℝ) * (cbpg_max_block_stepsize Li : ℝ))) ^
        (2 : ℕ)))

@[simp] theorem cbpg_sufficient_decrease_constant_def
    (Lf : NNReal) (Li : (i : Fin p) → PosReal) :
    cbpg_sufficient_decrease_constant Lf Li =
      (cbpg_min_block_stepsize Li : ℝ) /
        (2 *
          (((Lf : ℝ) + 2 * (cbpg_max_block_stepsize Li : ℝ) +
                Real.sqrt
                  ((cbpg_min_block_stepsize Li : ℝ) * (cbpg_max_block_stepsize Li : ℝ))) ^
            (2 : ℕ))) :=
  rfl

end

section

variable {p : ℕ} {Ei : Fin p → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, ProperSpace (Ei i)]

variable {f : ((i : Fin p) → Ei i) → EReal} {g : (i : Fin p) → Ei i → EReal}
variable {block_gradient : (i : Fin p) → ((j : Fin p) → Ei j) → Ei i}
variable {XStar : Set ((i : Fin p) → Ei i)} {FOpt : ℝ}
variable {Lf : NNReal} {Li : (i : Fin p) → PosReal}

theorem cbpg_outer_iterate_mem_effective_domain
    (hproblem : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
    (x0 : effective_domain (separableSum g)) (k : ℕ) :
    cyclic_block_proximal_gradient_method hproblem (hproblem.interior_effective_domain_point x0) k ∈
      effective_domain (separableSum g) := by
  simpa using cbpg_auxiliary_iterate_mem_effective_domain hproblem x0 k 0 (Nat.zero_le p)

theorem cbpg_outer_iterate_mem_interior
    (hproblem : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
    (x0 : effective_domain (separableSum g)) (k : ℕ) :
    cyclic_block_proximal_gradient_method hproblem (hproblem.interior_effective_domain_point x0) k ∈
      interior (effective_domain f) :=
  hproblem.mem_interior_effective_domain_of_mem_g_effective_domain
    (cbpg_outer_iterate_mem_effective_domain hproblem x0 k)

section

variable [InnerProductSpace ℝ ((i : Fin p) → Ei i)]
variable [ProperSpace ((i : Fin p) → Ei i)]
variable [Nonempty (Fin p)]

variable (hproblem : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
variable (x0 : effective_domain (separableSum g))

local notation "F" => composite_model_objective f (separableSum g)
local notation "Lmin" => cbpg_min_block_stepsize Li
local notation "x0I" => hproblem.interior_effective_domain_point x0
local notation "x[" k "]" => cyclic_block_proximal_gradient_method hproblem x0I k
set_option quotPrecheck false in
local notation "xI[" k "]" =>
  (⟨x[k], cbpg_outer_iterate_mem_interior hproblem x0 k⟩ : interior (effective_domain f))
private abbrev cbpg_full_gradient_mapping
    (h : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
    (hg_convex :
      @is_convex_function
        ((i : Fin p) → Ei i)
        NormedAddCommGroup.toENormedAddCommMonoid.toAddCommMonoid
        ((inferInstance : InnerProductSpace ℝ ((i : Fin p) → Ei i)).toModule)
        (separableSum g))
    (L : PosReal) :
    interior (effective_domain f) → ((i : Fin p) → Ei i) :=
  @gradient_mapping
    ((i : Fin p) → Ei i)
    _
    inferInstance
    _
    f
    (separableSum g)
    h.separableSum_proper
    ⟨h.separableSum_closed⟩
    ⟨hg_convex⟩
    L

theorem cbpg_sufficient_decrease_gradient_mapping
    (hg_convex :
      @is_convex_function
        ((i : Fin p) → Ei i)
        NormedAddCommGroup.toENormedAddCommMonoid.toAddCommMonoid
        ((inferInstance : InnerProductSpace ℝ ((i : Fin p) → Ei i)).toModule)
        (separableSum g))
    (k : ℕ) :
    F x[k] - F x[k + 1] ≥
      (((cbpg_sufficient_decrease_constant Lf Li / (p : ℝ)) *
          ‖cbpg_full_gradient_mapping hproblem hg_convex Lmin xI[k]‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  sorry

end

end
