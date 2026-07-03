import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_11_5 (from Chap11) -/
/- Definition 11.5 is recall-only in the Chapter 11 proximal-gradient toolbox.

Domain sampling identifies the Chapter 10 proximal-gradient stack as:
- `source-facing`: `prox_gradient_mapping`, the real-valued smooth-term surface `G[L; f, g]`;
- `core/canonical`: `gradient_mapping`, the residual owner on
  `interior (effective_domain f.toEReal)`;
- `bridge/view`: `prox_grad_operator`, the owner of the auxiliary notation `T_L^{f,g}`.

This item therefore introduces no new owner-level data, wrapper, or chapter-local surrogate. -/

/- Definition 11.5: the Chapter 11 gradient mapping is the previously defined Chapter 10
proximal-gradient mapping `prox_gradient_mapping`, whose core owner is `gradient_mapping` with
residual formula `G_L^{f,g}(x) = L • (x - T_L^{f,g}(x))`. The auxiliary update
`T_L^{f,g}` is already owned upstream by `prox_grad_operator`. -/
recall gradient_mapping
recall prox_gradient_mapping

/-! ### Lemma_11_5 (from Chap11) -/
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

/-! ### Theorem_11_5 (from Chap11) -/
noncomputable section

universe v

section

variable {p : ℕ} {Ei : Fin p → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, ProperSpace (Ei i)]

variable {f : ((i : Fin p) → Ei i) → EReal} {g : (i : Fin p) → Ei i → EReal}
variable {block_gradient : (i : Fin p) → ((j : Fin p) → Ei j) → Ei i}
variable {XStar : Set ((i : Fin p) → Ei i)} {FOpt : ℝ}
variable {Lf : NNReal} {Li : (i : Fin p) → PosReal}

/- Theorem 11.5 is a `bridge/view` consequence of the CBPG outer-step sufficient-decrease owner
`cbpg_sufficient_decrease_outer_step` from Lemma 11.4.

Primitive data are the Chapter 11 CBPG assumption package and the initial point in the effective
domain of the block-separable regularizer. The monotonicity and equality characterization below
are derived API, so this file reuses the owner descent estimate directly instead of restating it
as a parallel raw hypothesis. -/

section

variable (hproblem : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
variable (x0 : effective_domain (separableSum g))

local notation "x0I" => hproblem.interior_effective_domain_point x0
local notation "Lmin" => cbpg_min_block_stepsize Li
local notation "toPiLp" =>
  ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)
local notation "x[" k "]" =>
  cyclic_block_proximal_gradient_method hproblem x0I k

local notation "F" =>
  composite_model_objective f (separableSum g)

local notation "Δ[" k "]" =>
  ((((Lmin : ℝ) / 2) *
      ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) : ℝ) : EReal)

private theorem cbpg_outer_step_eq_of_no_blocks
    (hp : p = 0) (k : ℕ) :
    x[k + 1] = x[k] := by
  rw [cyclic_block_proximal_gradient_method_succ]
  simp [hp]

private theorem cbpg_outer_step_descent_term_nonneg
    [Nonempty (Fin p)] (k : ℕ) :
    (0 : EReal) ≤ Δ[k] := by
  have hreal_nonneg :
      0 ≤ ((Lmin : ℝ) / 2) * ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) := by
    refine mul_nonneg ?_ (sq_nonneg _)
    exact div_nonneg (le_of_lt (PosReal.coe_pos Lmin)) (by positivity)
  exact_mod_cast hreal_nonneg

-- Proof sketch: apply the CBPG owner descent estimate
-- `cbpg_sufficient_decrease_outer_step` at the outer step `k`; the right-hand side is
-- nonnegative because it is a positive constant times a squared norm.
/-- Theorem 11.5: the outer-step sufficient-decrease estimate from Lemma 11.4 implies that each
CBPG outer step weakly decreases the composite objective value `F(x^k)`. -/
theorem cbpg_objective_step_monotone
    (k : ℕ) :
    F x[k + 1] ≤ F x[k] := by
  by_cases hp : p = 0
  · have hxsucc : x[k + 1] = x[k] := by
      exact cbpg_outer_step_eq_of_no_blocks hproblem x0 hp k
    simp [hxsucc]
  · letI : Nonempty (Fin p) := ⟨⟨0, Nat.pos_of_ne_zero hp⟩⟩
    have hΔ_nonneg : (0 : EReal) ≤ Δ[k] :=
      cbpg_outer_step_descent_term_nonneg hproblem x0 k
    have hstep :
        F x[k + 1] + Δ[k] ≤ F x[k] := by
      simpa only [add_comm] using
        (EReal.add_le_of_le_sub (cbpg_sufficient_decrease_outer_step hproblem x0 k) :
          Δ[k] + F x[k + 1] ≤ F x[k])
    exact (le_add_of_nonneg_right hΔ_nonneg).trans hstep

-- Proof sketch: if the consecutive iterates agree, the objective values agree by substitution.
-- Conversely, combine equality of the objective values with
-- `cbpg_sufficient_decrease_outer_step`; the coefficient is positive because `L_min` is now the
-- positive owner `cbpg_min_block_stepsize Li` of the nonempty finite block family.
/-- Under the same outer-step sufficient-decrease estimate, equality of two consecutive CBPG
objective values is equivalent to equality of the corresponding outer iterates. -/
theorem cbpg_objective_step_eq_iff_eq
    (k : ℕ) :
    F x[k + 1] = F x[k] ↔ x[k] = x[k + 1] := by
  constructor
  · intro hF
    by_cases hp : p = 0
    · have hxsucc : x[k + 1] = x[k] := by
        exact cbpg_outer_step_eq_of_no_blocks hproblem x0 hp k
      exact hxsucc.symm
    · letI : Nonempty (Fin p) := ⟨⟨0, Nat.pos_of_ne_zero hp⟩⟩
      have hsub_nonpos : F x[k] - F x[k + 1] ≤ 0 := by
        simpa [hF] using
          (EReal.sub_self_le_zero : F x[k] - F x[k] ≤ 0)
      have hΔ_nonpos : Δ[k] ≤ 0 := by
        exact (cbpg_sufficient_decrease_outer_step hproblem x0 k).trans hsub_nonpos
      have hΔ_eq_zero : Δ[k] = 0 := by
        exact le_antisymm hΔ_nonpos (cbpg_outer_step_descent_term_nonneg hproblem x0 k)
      have hreal_eq_zero :
          ((Lmin : ℝ) / 2) * ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) = 0 := by
        exact_mod_cast hΔ_eq_zero
      have hcoef_pos : 0 < (Lmin : ℝ) / 2 := by
        have hmin_pos : 0 < (Lmin : ℝ) :=
          PosReal.coe_pos Lmin
        positivity
      have hpow_eq_zero : ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) = 0 := by
        refine (mul_eq_zero.mp hreal_eq_zero).resolve_left ?_
        linarith
      have hnorm_eq_zero : ‖toPiLp x[k] - toPiLp x[k + 1]‖ = 0 := by
        exact eq_zero_of_pow_eq_zero hpow_eq_zero
      have hxPiLp : toPiLp x[k] = toPiLp x[k + 1] := by
        exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_eq_zero)
      have hxraw :=
        congrArg (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei) hxPiLp
      simpa using hxraw
  · intro hx
    simp [hx]

end

end
