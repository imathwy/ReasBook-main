import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_13_6 (from Chap13) -/
universe u

noncomputable section

section

/- Definition 13.6 is `source-facing`: the textbook lists three concrete stepsize strategies for
the generalized conditional-gradient method.

Domain sampling against the local optimization API gives the relevant canonical shapes already used
in the project:
- explicit scalar-valued rules such as `polyak_stepsize`;
- constant strategy sequences such as `proximal_gradient_constant_stepsize_strategy`;
- exact-line-search minimizer sets such as `exact_line_search_stepsizes` and
  `non_euclidean_exact_line_search_stepsizes`.

The clean public interface is therefore three primitive owners:
- two explicit scalar rules for the predefined diminishing and adaptive cases;
- one set-valued exact-line-search owner recording the admissible minimizers on `[0, 1]`.

The trajectory-level predicates saying that a generalized conditional-gradient method uses one of
these rules are derived API, so they belong below and are stated directly in terms of these
owners rather than as parallel local formulas inside later theorem files.

No extra wrapper or package is introduced, since the mathematics here is exactly the displayed
formulas. -/

/-- Definition 13.6 (1): the predefined diminishing stepsize strategy for the generalized
conditional-gradient method uses the scalar `t_k = 2 / (k + 2)` at iteration `k`. -/
def conditional_gradient_predefined_diminishing_stepsize (k : ℕ) : ℝ :=
  2 / (k + 2 : ℝ)

/-- Evaluating the predefined diminishing conditional-gradient stepsize reproduces the textbook
formula `2 / (k + 2)`. -/
@[simp] theorem conditional_gradient_predefined_diminishing_stepsize_eq (k : ℕ) :
    conditional_gradient_predefined_diminishing_stepsize k = 2 / (k + 2 : ℝ) :=
  rfl

end

section

variable {E : Type u} [NormedAddCommGroup E]

/-- Definition 13.6 (2): the adaptive stepsize strategy at the current iterate `x` and search
point `p` uses the current gap value `Sx` through the scalar
`min {1, Sx / (L_f ‖p - x‖²)}` on the nondegenerate branch `L_f ≠ 0` and `p ≠ x`, while the
degenerate cases `L_f = 0` or `‖p - x‖ = 0` are recorded explicitly by the fallback value `1`. -/
def conditional_gradient_adaptive_stepsize
    (Sx : ℝ) (Lf : NNReal) (x p : E) : ℝ :=
  if ‖p - x‖ = 0 ∨ Lf = 0 then 1
  else min (1 : ℝ) (Sx / ((Lf : ℝ) * ‖p - x‖ ^ (2 : ℕ)))

/-- Expanding the adaptive conditional-gradient stepsize exposes the guarded textbook formula. -/
@[simp] theorem conditional_gradient_adaptive_stepsize_eq
    (Sx : ℝ) (Lf : NNReal) (x p : E) :
    conditional_gradient_adaptive_stepsize Sx Lf x p =
      if ‖p - x‖ = 0 ∨ Lf = 0 then 1
      else min (1 : ℝ) (Sx / ((Lf : ℝ) * ‖p - x‖ ^ (2 : ℕ))) :=
  rfl

/-- If the search point agrees with the current iterate, the adaptive conditional-gradient
stepsize takes its explicit fallback value `1`. -/
@[simp] theorem conditional_gradient_adaptive_stepsize_eq_one_of_eq
    (Sx : ℝ) (Lf : NNReal) (x : E) :
    conditional_gradient_adaptive_stepsize Sx Lf x x = 1 := by
  simp [conditional_gradient_adaptive_stepsize]

/-- If `L_f = 0`, the adaptive conditional-gradient stepsize takes its explicit fallback
value `1`. -/
@[simp] theorem conditional_gradient_adaptive_stepsize_eq_one_of_Lf_eq_zero
    (Sx : ℝ) (x p : E) {Lf : NNReal} (hLf : Lf = 0) :
    conditional_gradient_adaptive_stepsize Sx Lf x p = 1 := by
  simp [conditional_gradient_adaptive_stepsize, hLf]

/-- On the nondegenerate branch `L_f ≠ 0` and `p ≠ x`, the adaptive conditional-gradient
stepsize is the textbook minimum `min {1, Sx / (L_f ‖p - x‖²)}`. -/
theorem conditional_gradient_adaptive_stepsize_of_ne
    (Sx : ℝ) {Lf : NNReal} {x p : E} (hp : p ≠ x) (hLf : Lf ≠ 0) :
    conditional_gradient_adaptive_stepsize Sx Lf x p =
      min (1 : ℝ) (Sx / ((Lf : ℝ) * ‖p - x‖ ^ (2 : ℕ))) := by
  have hnorm : ‖p - x‖ ≠ 0 := by
    intro hnorm
    apply hp
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  simp [conditional_gradient_adaptive_stepsize, hnorm, hLf]

end

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- Definition 13.6 (3): the exact line search stepsizes at the current iterate `x` and search
point `p` are the scalars `t ∈ [0, 1]` that minimize the one-dimensional restriction
`u ↦ F (x + u (p - x))`. -/
def conditional_gradient_exact_line_search_stepsizes
    (F : E → EReal) (x p : E) : Set ℝ :=
  Set.Icc (0 : ℝ) 1 ∩
    {t | IsMinOn (fun u ↦ F (x + u • (p - x))) (Set.Icc (0 : ℝ) 1) t}

/-- A scalar belongs to the conditional-gradient exact line search set exactly when it lies in
`[0, 1]` and minimizes `u ↦ F (x + u (p - x))` on that interval. -/
@[simp] theorem mem_conditional_gradient_exact_line_search_stepsizes_iff
    {F : E → EReal} {x p : E} {t : ℝ} :
    t ∈ conditional_gradient_exact_line_search_stepsizes F x p ↔
      t ∈ Set.Icc (0 : ℝ) 1 ∧
        IsMinOn (fun u ↦ F (x + u • (p - x))) (Set.Icc (0 : ℝ) 1) t :=
  by
    -- Expand the exact-line-search owner so membership becomes the feasibility/minimality
    -- conjunction displayed in Definition 13.6.
    simp [conditional_gradient_exact_line_search_stepsizes]

end

section

/-- A generalized conditional-gradient trajectory uses the predefined diminishing stepsize rule
when each stepsize is `tₖ = 2 / (k + 2)`. -/
def uses_generalized_conditional_gradient_predefined_stepsize_rule
    (t : ℕ → Set.Icc (0 : ℝ) 1) : Prop :=
  ∀ k : ℕ, (t k : ℝ) = conditional_gradient_predefined_diminishing_stepsize k

end

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable (f : E → ℝ) (g : E → EReal)

local notation "F" => composite_model_objective f.toEReal g

/-- A generalized conditional-gradient trajectory uses exact line search when each stepsize
belongs to the Definition 13.6 exact-line-search set for the composite objective along the segment
from `xᵏ` to `pᵏ`. -/
def uses_generalized_conditional_gradient_exact_line_search_rule
    (x p : ℕ → E) (t : ℕ → Set.Icc (0 : ℝ) 1) : Prop :=
  ∀ k : ℕ,
    (t k : ℝ) ∈ conditional_gradient_exact_line_search_stepsizes F (x k) (p k)

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (f : E → ℝ) (g : E → EReal)

/-- A generalized conditional-gradient trajectory uses the adaptive stepsize rule when each
stepsize is obtained by applying the Definition 13.6 adaptive owner to the Chapter 13 gap
quantity `S`, provided that this gap value is finite at the current iterate. -/
def uses_generalized_conditional_gradient_adaptive_stepsize_rule
    (Lf : NNReal) (x p : ℕ → E) (t : ℕ → Set.Icc (0 : ℝ) 1) : Prop :=
  ∀ k : ℕ,
    S[f, g](x k) ≠ ⊤ ∧
      S[f, g](x k) ≠ ⊥ ∧
      (t k : ℝ) =
        conditional_gradient_adaptive_stepsize (S[f, g](x k)).toReal Lf (x k) (p k)

/-- Theorem 13.9 uses either the adaptive rule or exact line search. -/
def uses_generalized_conditional_gradient_adaptive_or_exact_stepsize_rule
    (Lf : NNReal) (x p : ℕ → E) (t : ℕ → Set.Icc (0 : ℝ) 1) : Prop :=
  uses_generalized_conditional_gradient_adaptive_stepsize_rule f g Lf x p t ∨
    uses_generalized_conditional_gradient_exact_line_search_rule f g x p t

/-- A generalized conditional-gradient trajectory uses one of the three textbook stepsize
strategies when it uses either the predefined diminishing rule, the adaptive rule, or exact line
search. -/
def uses_generalized_conditional_gradient_standard_stepsize_rule
    (Lf : NNReal) (x p : ℕ → E) (t : ℕ → Set.Icc (0 : ℝ) 1) : Prop :=
  uses_generalized_conditional_gradient_predefined_stepsize_rule t ∨
    uses_generalized_conditional_gradient_adaptive_or_exact_stepsize_rule f g Lf x p t

end

/-! ### Theorem_13_6 (from Chap13) -/
noncomputable section

universe u

open InnerProductSpace (toDual)
open scoped Gradient

/- `prompt_add/` is absent in this workspace, so the statement design is checked against the local
owners for the actual mathematics of Theorem 13.6:

- `generalized_conditional_gradient_norm` and Lemma 13.5 for the Chapter 13 gap quantity `S(x)`;
- `fenchel_inequality` and `pairing_eq_add_conjugate_iff_mem_subdifferential` for the Chapter 4
  Fenchel/Fenchel--Young characterization;
- `is_stationary_point` for the finite-dimensional Chapter 3 stationarity owner.

This item is `source-facing`. The primitive data is the gap quantity `S[f₀, g](x)` together with
the `g`-side Fenchel/subdifferential hypotheses actually used by the characterization. Assumption
13.1 is not the owner of that characterization: it is only a `bridge/view` that later supplies the
pointwise differentiability hypothesis needed to rewrite the subdifferential condition as
stationarity. -/

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f g : E → EReal}

local notation "f₀" => fun y ↦ EReal.toReal (f y)

/-- Helper for Theorem 13.6: evaluating the negative-gradient Riesz functional at `x` gives the
negative inner-product term appearing in Lemma 13.5. -/
private lemma neg_gradient_pairing_eq_neg_inner (x : E) :
    (((-toDual ℝ E (∇ f₀ x) : Module.Dual ℝ E) x : EReal)) =
      -(((inner ℝ (∇ f₀ x) x : ℝ) : EReal)) := by
  -- Identify the Chapter 4 pairing with the Chapter 13 inner-product expression.
  simp [InnerProductSpace.toDual_apply_eq_toDualMap_apply,
    InnerProductSpace.toDualMap_apply_apply]

-- Proof sketch: rewrite `S(x)` by Lemma 13.5 as
-- `⟪∇f(x), x⟫ + g(x) + g∗(-∇f(x))`, then apply Fenchel's inequality to `g` at the pair
-- `(x, -∇ (fun y ↦ (f y).toReal) x)`.
/-- Theorem 13.6 (1): the generalized conditional-gradient norm `S(x)` is nonnegative for every
`x`, under the properness assumptions on `g` actually used by Fenchel's inequality. -/
theorem generalized_conditional_gradient_norm_nonneg
    (hg_proper : IsProperExtendedRealFunction g) (x : E) :
    0 ≤ S[f₀, g](x) := by
  have hfenchel :
      (((-toDual ℝ E (∇ f₀ x) : Module.Dual ℝ E) x : EReal)) ≤
        g x + conjugate_function g (-toDual ℝ E (∇ f₀ x) : Module.Dual ℝ E) := by
    -- Fenchel's inequality identifies the gap as a translated nonnegative residual.
    simpa [add_comm] using
      (fenchel_inequality g x (-toDual ℝ E (∇ f₀ x) : Module.Dual ℝ E) hg_proper)
  have hresidual :
      (0 : EReal) ≤
        g x + conjugate_function g (-toDual ℝ E (∇ f₀ x) : Module.Dual ℝ E) -
          (((-toDual ℝ E (∇ f₀ x) : Module.Dual ℝ E) x : EReal)) := by
    -- Subtract the pairing term to expose the nonnegative Fenchel residual.
    have hpair_ne_top :
        (((-toDual ℝ E (∇ f₀ x) : Module.Dual ℝ E) x : EReal)) ≠ ⊤ := by
      simp
    have hpair_ne_bot :
        (((-toDual ℝ E (∇ f₀ x) : Module.Dual ℝ E) x : EReal)) ≠ ⊥ := by
      simp
    exact
      (EReal.sub_nonneg (.inr hpair_ne_top) (.inr hpair_ne_bot)).2 hfenchel
  -- Rewrite the residual back into the Chapter 13 expression for `S(x)`.
  rw [generalized_conditional_gradient_norm_eq_inner_add_value_add_conjugate]
  simpa [neg_gradient_pairing_eq_neg_inner, conjugate_function_primal_apply,
    InnerProductSpace.toDual_apply_eq_toDualMap_apply, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm] using hresidual

/-- Helper for Theorem 13.6: vanishing of the conditional-gradient norm is exactly the
Fenchel--Young equality for `g` at `(x, -∇ f₀ x)`. -/
private lemma generalized_conditional_gradient_norm_eq_zero_iff_fenchel_young_equality
    (x : E) :
    S[f₀, g](x) = 0 ↔
      (((-toDual ℝ E (∇ f₀ x) : Module.Dual ℝ E) x : EReal)) =
        g x + conjugate_function g (-toDual ℝ E (∇ f₀ x) : Module.Dual ℝ E) := by
  constructor
  · intro hS
    rw [generalized_conditional_gradient_norm_eq_inner_add_value_add_conjugate] at hS
    let r : EReal := g x + conjugate_function g (-toDual ℝ E (∇ f₀ x) : Module.Dual ℝ E)
    have hshift :
        (((inner ℝ (∇ f₀ x) x : ℝ) : EReal) + r) = 0 := by
      -- Rewrite `S(x) = 0` into a single affine-plus-conjugate equality.
      simpa [conjugate_function_primal_apply, InnerProductSpace.toDual_apply_eq_toDualMap_apply,
        r, add_assoc] using hS
    have hcancel :
        r =
          -(((inner ℝ (∇ f₀ x) x : ℝ) : EReal)) := by
      -- Cancel the finite inner-product term from both sides.
      have htranslated := congrArg
        (fun z : EReal ↦ z - (inner ℝ (∇ f₀ x) x : ℝ)) hshift
      calc
        r = ((((inner ℝ (∇ f₀ x) x : ℝ) : EReal) + r) - (inner ℝ (∇ f₀ x) x : ℝ)) := by
              symm
              exact EReal.add_sub_cancel_left
        _ = -(((inner ℝ (∇ f₀ x) x : ℝ) : EReal)) := by
              simpa using htranslated
    simpa [r, neg_gradient_pairing_eq_neg_inner] using hcancel.symm
  · intro hfy
    rw [generalized_conditional_gradient_norm_eq_inner_add_value_add_conjugate]
    have hpair :
        g x + conjugate_function g (-toDual ℝ E (∇ f₀ x) : Module.Dual ℝ E) =
          -(((inner ℝ (∇ f₀ x) x : ℝ) : EReal)) := by
      -- Convert the Fenchel--Young equality back to the affine-plus-conjugate form.
      simpa [neg_gradient_pairing_eq_neg_inner] using hfy.symm
    -- Substitute the equality case into Lemma 13.5 and collapse the finite term.
    calc
      ((inner ℝ (∇ f₀ x) x : ℝ) : EReal) + g x + (g∗) (-∇ f₀ x) =
          ((inner ℝ (∇ f₀ x) x : ℝ) : EReal) +
            (g x + conjugate_function g (-toDual ℝ E (∇ f₀ x) : Module.Dual ℝ E)) := by
              simp [conjugate_function_primal_apply,
                InnerProductSpace.toDual_apply_eq_toDualMap_apply, add_assoc]
      _ = ((inner ℝ (∇ f₀ x) x : ℝ) : EReal) +
            (-(((inner ℝ (∇ f₀ x) x : ℝ) : EReal))) := by
              rw [hpair]
      _ = 0 := by
              simpa [sub_eq_add_neg] using
                (EReal.sub_self
                  (x := (((inner ℝ (∇ f₀ x) x : ℝ) : EReal)))
                  (h_top := by simp)
                  (h_bot := by simp))

-- Proof sketch: rewrite `S(xStar)` by Lemma 13.5. The equality `S(xStar) = 0` is exactly the
-- Fenchel--Young equality case for `g` at `(xStar, -∇ (fun y ↦ (f y).toReal) xStar)`, so Theorem
-- 4.10 rewrites it as subdifferential membership. Only the no-`⊥` hypothesis on `g` is active.
/-- Theorem 13.6 (2), source-facing form: the generalized
conditional-gradient norm vanishes if and only if the negative gradient belongs to the
subdifferential of `g` at `xStar`. -/
theorem generalized_conditional_gradient_norm_eq_zero_iff_neg_gradient_mem_subdifferential
    (hg_ne_bot : ∀ z, g z ≠ ⊥) (xStar : E) :
    S[f₀, g](xStar) = 0 ↔
      (-toDual ℝ E (∇ f₀ xStar) : Module.Dual ℝ E) ∈ ∂ g(xStar) := by
  -- Route correction: match the source proof through Fenchel--Young equality, not by unfolding
  -- the subdifferential definition directly.
  rw [generalized_conditional_gradient_norm_eq_zero_iff_fenchel_young_equality]
  -- The Chapter 4 equality criterion is exactly the required subdifferential characterization.
  simpa using
    (pairing_eq_add_conjugate_iff_mem_subdifferential g hg_ne_bot xStar
      (-toDual ℝ E (∇ f₀ xStar) : Module.Dual ℝ E))

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {f g : E → EReal}

local notation "f₀" => fun y ↦ EReal.toReal (f y)

local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

-- Proof sketch: use
-- `generalized_conditional_gradient_norm_eq_zero_iff_neg_gradient_mem_subdifferential`, then
-- combine the resulting subdifferential membership with the explicit differentiability hypothesis
-- and unfold `is_stationary_point`.
/-- The finite-dimensional Chapter 3 stationarity owner rewrites the vanishing gap condition as
stationarity once differentiability of `f` at `xStar` is supplied explicitly. -/
theorem
    generalized_conditional_gradient_norm_eq_zero_iff_is_stationary_point_of_is_differentiable_at
    (hg_ne_bot : ∀ z, g z ≠ ⊥) (xStar : E) (hdiff : is_differentiable_at f xStar) :
    S[f₀, g](xStar) = 0 ↔
      is_stationary_point f g xStar := by
  rw [is_stationary_point_iff]
  constructor
  · intro hx
    exact
      ⟨hdiff,
        (generalized_conditional_gradient_norm_eq_zero_iff_neg_gradient_mem_subdifferential
          hg_ne_bot xStar).1 hx⟩
  · rintro ⟨_, hxsub⟩
    exact
      (generalized_conditional_gradient_norm_eq_zero_iff_neg_gradient_mem_subdifferential
        hg_ne_bot xStar).2 hxsub

-- Proof sketch: Assumption 13.1 contributes only the pointwise differentiability hypothesis
-- through `IsGeneralizedConditionalGradientProblem.is_differentiable_at`, so the stationarity
-- equivalence is a direct bridge corollary from the owner-level theorem above.
/-- Under Assumption 13.1, the explicit differentiability hypothesis in the stationarity
reformulation is supplied automatically. -/
theorem generalized_conditional_gradient_norm_eq_zero_iff_is_stationary_point
    {Lf : NNReal} (hproblem : IsGeneralizedConditionalGradientProblem f g Lf)
    (xStar : effective_domain f) :
    S[f₀, g](xStar) = 0 ↔
      is_stationary_point f g xStar :=
  generalized_conditional_gradient_norm_eq_zero_iff_is_stationary_point_of_is_differentiable_at
    hproblem.ne_bot xStar (hproblem.is_differentiable_at xStar)

end
