import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_9 (from Chap10) -/
noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/-
Definition 10.9 is `bridge/view` in the Chapter 10 proximal-gradient stack:

- `prox[...]` from Chapter 6 remains the `core/canonical` proximal owner;
- `proximal_gradient_step` from Algorithm 10.1 is the Chapter 10 `source-facing` set-valued
  prox-gradient step;
- `prox_grad_operator` below is the single-valued bridge obtained when that step is known to be a
  singleton.

The public API should therefore reuse `proximal_gradient_step` rather than restating its defining
proximal-set expression.
-/

section CoeReal

variable {E : Type u} [NormedAddCommGroup E]

-- Proof sketch: a real-valued function has finite value everywhere after coercion to `EReal`, so
-- its effective domain is `Set.univ`; the interior of `Set.univ` is again `Set.univ`.
/-- Every point belongs to the interior of the effective domain of the `EReal` coercion of a
real-valued function. -/
theorem mem_interior_effective_domain_of_coe_real
    (f : E → ℝ) (x : E) :
    x ∈ interior (effective_domain (Function.toEReal f)) := by
  simp [effective_domain]

/-- A point of `E` canonically determines a point of the interior effective domain of the
`EReal` coercion of a real-valued function. -/
def interior_effective_domain_point_of_real
    (f : E → ℝ) (x : E) :
    interior (effective_domain (Function.toEReal f)) :=
  ⟨x, mem_interior_effective_domain_of_coe_real f x⟩

end CoeReal

-- Proof sketch: positive scaling by `1 / L` preserves properness, lower semicontinuity, and
-- convexity of `g` by `scaled_function_proper_closed_convex_of_pos`. Theorem 6.3 then makes the
-- source-facing prox-gradient step `proximal_gradient_step f g x L` a singleton.
/-- Under the proper closed convex hypotheses on `g`, the Chapter 10 prox-gradient step at `x` is
a singleton. -/
theorem proximal_gradient_step_eq_singleton
    (f g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (L : PosReal) (x : E) :
    ∃ y : E, proximal_gradient_step f g x L = {y} := by
  let hg_closed : LowerSemicontinuous g := Fact.out
  let hg_convex : is_convex_function g := Fact.out
  let hg_scaled :=
    scaled_function_proper_closed_convex_of_pos g inferInstance hg_closed hg_convex (1 / L)
  simpa [proximal_gradient_step] using
    prox_eq_singleton_of_proper_closed_convex
      ((((1 / L : PosReal) : EReal) • g))
      hg_scaled.1
      hg_scaled.2.1
      hg_scaled.2.2
      ((x : E) - (1 / L : ℝ) • ∇ (fun y ↦ (f y).toReal) (x : E))

/-- Definition 10.9: for a proper closed convex function `g` and a positive parameter `L`, the
prox-grad operator sends `x ∈ interior (dom f)` to the unique point of the Chapter 10 owner
`proximal_gradient_step f g x L`. -/
def prox_grad_operator (f g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)] (L : PosReal) :
    interior (effective_domain f) → E :=
  fun x ↦
    Classical.choose <|
      proximal_gradient_step_eq_singleton f g L (x : E)

/- Textbook notation for the Chapter 10 prox-gradient update `T_L^{f,g}`. The supporting
regularity assumptions on `g` are ordinary ambient instance data; in particular they can be
supplied directly by local hypotheses or via an ambient `IsCompositeSmoothMinimizationProblem`
instance from Definition 10.3. -/
@[inherit_doc] scoped[Gradient] notation:max "T[" L ", " f ", " g "]" =>
  prox_grad_operator f g L

-- Proof sketch: `prox_grad_operator` is defined by choosing the unique element of the singleton
-- `proximal_gradient_step f g x L`.
/-- The prox-grad operator is the unique point of the Chapter 10 prox-gradient step. -/
theorem prox_grad_operator_eq_singleton
    (f g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (L : PosReal) (x : interior (effective_domain f)) :
    proximal_gradient_step f g (x : E) L =
      {T[L, f, g] x} :=
  Classical.choose_spec <| proximal_gradient_step_eq_singleton f g L (x : E)

section CoeReal

variable (f : E → ℝ) (g : E → EReal)
variable [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
  [Fact (is_convex_function g)]

/- The core owner remains `prox_grad_operator` on `interior (effective_domain f)`. For a
real-valued smooth term, the source-facing Chapter 10 theorems use the canonical bridge
`interior_effective_domain_point_of_real` above to view that owner as a map on `E`. -/

/-- The proximal-gradient operator for a real-valued smooth term `f`, obtained by evaluating the
Chapter 10 owner `prox_grad_operator` of `f.toEReal` at the canonical interior-domain point
associated to `x`. -/
abbrev prox_gradient_operator
    (f : E → ℝ) (g : E → EReal)
    [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
    [Fact (is_convex_function g)] (L : PosReal) : E → E :=
  fun x ↦
    T[L, f.toEReal, g] (interior_effective_domain_point_of_real f x)

@[inherit_doc] scoped[Gradient] notation:max "T[" L "; " f ", " g "]" =>
  prox_gradient_operator f g L

/-- Evaluating `prox_gradient_operator` at `x` recovers the Chapter 10 prox-gradient operator of
`f.toEReal` at the canonical interior-domain point associated to `x`. -/
@[simp] theorem prox_gradient_operator_apply (L : PosReal) (x : E) :
    T[L; f, g] x = T[L, f.toEReal, g] (interior_effective_domain_point_of_real f x) := rfl

end CoeReal

end

/-! ### Theorem_10_9 (from Chap10) -/
noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable {f g : E → EReal} [IsProperExtendedRealFunction g]
  [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]

/- Theorem 10.9 is `source-facing` in the Chapter 10 proximal-gradient API.

Domain sampling:
- `prox_grad_operator` from Definition 10.9 is the Chapter 10 bridge from the singleton
  prox-gradient step to a concrete point;
- `gradient_mapping` from Definition 10.5 is the owner of the residual `G[L, f, g] x`;
- `prox_grad_step_gradient_mapping_norm_monotone` from Lemma 10.12 is a nearby one-step
  monotonicity theorem for the same owner, confirming that the residual itself is primitive and
  monotonicity statements are derived API;
- `block_partial_gradient_mapping_norm_monotone` in Chapter 11 reuses this theorem through the
  same owner on a frozen slice.

Owner abstraction:
- `core/canonical`: the fixed-point step-size profiles
  `L ↦ ‖G[L, f, g] x‖` and `L ↦ ‖G[L, f, g] x‖ / (L : ℝ)`;
- `source-facing`: the two monotonicity clauses of Theorem 10.9 for those profiles.

Primitive data are only the Chapter 10 owner `gradient_mapping` and the standard proper/closed/
convex regularity on `g`; the order-theoretic monotonicity predicates are derived API. -/

-- Proof sketch: apply the second prox theorem to the two scaled proximal points defining
-- `G[L₁, f, g] x` and `G[L₂, f, g] x`, add the resulting inequalities, and
-- rewrite the inner-product identity to obtain the quadratic bound that forces
-- `‖G_{L₂}(x)‖ ≤ ‖G_{L₁}(x)‖` whenever `L₂ ≤ L₁`.
/-- Helper for Theorem 10.9: the prox-gradient update is the identity minus the scaled gradient
mapping residual. -/
lemma prox_grad_operator_eq_sub_gradient_mapping
    (f g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (L : PosReal)
    (x : interior (effective_domain f)) :
    T[L, f, g] x = (x : E) - (1 / (L : ℝ)) • G[L, f, g] x := by
  have hL : (1 / (L : ℝ)) * (L : ℝ) = 1 := by
    field_simp [show (L : ℝ) ≠ 0 by exact L.2.ne']
  -- Solve the defining identity `G_L(x) = L • (x - T_L(x))` for `T_L(x)`.
  calc
    T[L, f, g] x = (x : E) - ((x : E) - T[L, f, g] x) := by
      exact (sub_sub_cancel (x : E) (T[L, f, g] x)).symm
    _ = (x : E) - (1 / (L : ℝ)) • G[L, f, g] x := by
      rw [gradient_mapping_apply, smul_smul, hL, one_smul]

/-- Helper for Theorem 10.9: the second prox theorem specialized to the forward point of the
prox-gradient step gives a real-valued support inequality for the residual
`G[L, f, g] x - ∇f(x)`. -/
lemma gradient_mapping_support_ineq_real
    (f g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (L : PosReal)
    (x : interior (effective_domain f)) :
    T[L, f, g] x ∈ effective_domain g ∧
      ∀ y ∈ effective_domain g,
        inner ℝ
            (G[L, f, g] x - ∇ (fun z ↦ (f z).toReal) (x : E))
            (y - T[L, f, g] x) ≤
          (g y).toReal - (g (T[L, f, g] x)).toReal := by
  let z : E := (x : E) - (1 / (L : ℝ)) • ∇ (fun y ↦ (f y).toReal) (x : E)
  let hg_convex : is_convex_function g := Fact.out
  have hprox :
      prox[((((1 / L : PosReal) : EReal) • g))] z = {T[L, f, g] x} := by
    -- Unfold the Chapter 10 prox-gradient operator back to the singleton proximal point.
    simpa [z, proximal_gradient_step] using prox_grad_operator_eq_singleton f g L x
  rcases scaled_prox_singleton_support_of_proper_convex
      (f := g)
      (μ := 1 / L)
      inferInstance
      hg_convex
      z
      (T[L, f, g] x)
      hprox with
    ⟨hTx_eff, hsupport⟩
  refine ⟨hTx_eff, ?_⟩
  intro y hy
  have hy_val :
      g y = (((g y).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hy).ne
        (‹IsProperExtendedRealFunction g›.ne_bot y)).symm
  have hTx_val :
      g (T[L, f, g] x) = ((((g (T[L, f, g] x)).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hTx_eff).ne
        (‹IsProperExtendedRealFunction g›.ne_bot _)).symm
  have hz :
      z - T[L, f, g] x =
        (1 / (L : ℝ)) •
          (G[L, f, g] x - ∇ (fun y ↦ (f y).toReal) (x : E)) := by
    -- Rewrite the forward point using `T_L(x) = x - (1 / L) G_L(x)`.
    calc
      z - T[L, f, g] x =
          ((x : E) - (1 / (L : ℝ)) • ∇ (fun y ↦ (f y).toReal) (x : E)) -
            ((x : E) - (1 / (L : ℝ)) • G[L, f, g] x) := by
              rw [prox_grad_operator_eq_sub_gradient_mapping]
      _ = (1 / (L : ℝ)) • G[L, f, g] x -
            (1 / (L : ℝ)) • ∇ (fun y ↦ (f y).toReal) (x : E) := by
              abel
      _ = (1 / (L : ℝ)) •
            (G[L, f, g] x - ∇ (fun y ↦ (f y).toReal) (x : E)) := by
              rw [smul_sub]
  have hLinv : (1 / (1 / L : PosReal) : ℝ) = (L : ℝ) := by
    simp [one_div]
  have hvector :
      ((1 / (1 / L : PosReal) : ℝ) • (z - T[L, f, g] x)) =
        G[L, f, g] x - ∇ (fun y ↦ (f y).toReal) (x : E) := by
    have hcancel : (L : ℝ) * (1 / (L : ℝ)) = 1 := by
      field_simp [show (L : ℝ) ≠ 0 by exact L.2.ne']
    -- The scaling coming from Chapter 6 cancels the stepsize `1 / L`.
    rw [hz, hLinv, smul_smul, hcancel, one_smul]
  have hsupportE := hsupport y hy
  rw [hvector, hy_val, hTx_val] at hsupportE
  have hsupportE' :
      (((inner ℝ
          (G[L, f, g] x - ∇ (fun z ↦ (f z).toReal) (x : E))
          (y - T[L, f, g] x) : ℝ)) : EReal) ≤
        (((((g y).toReal - (g (T[L, f, g] x)).toReal : ℝ)) : EReal)) := by
    simpa [EReal.coe_sub] using hsupportE
  -- Convert the extended-real inequality back to the real line once both values are finite.
  exact EReal.coe_le_coe_iff.mp hsupportE'

/-- Helper for Theorem 10.9: the two prox support inequalities combine into the scalar quadratic
bound `(10.8)` for the norms of the gradient mappings. -/
lemma gradient_mapping_quadratic_bound
    (f g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (L₁ L₂ : PosReal)
    (x : interior (effective_domain f)) :
    (1 / (L₁ : ℝ)) * ‖G[L₁, f, g] x‖ ^ (2 : ℕ) +
        (1 / (L₂ : ℝ)) * ‖G[L₂, f, g] x‖ ^ (2 : ℕ) ≤
      ((1 / (L₁ : ℝ)) + (1 / (L₂ : ℝ))) *
        ‖G[L₁, f, g] x‖ * ‖G[L₂, f, g] x‖ := by
  let grad := ∇ (fun z ↦ (f z).toReal) (x : E)
  let G₁ := G[L₁, f, g] x
  let G₂ := G[L₂, f, g] x
  let T₁ := T[L₁, f, g] x
  let T₂ := T[L₂, f, g] x
  rcases gradient_mapping_support_ineq_real (f := f) (g := g) L₁ x with
    ⟨hT₁_eff, hsupport₁⟩
  rcases gradient_mapping_support_ineq_real (f := f) (g := g) L₂ x with
    ⟨hT₂_eff, hsupport₂⟩
  have h₁ :
      inner ℝ (G₁ - grad) (T₂ - T₁) ≤
        (g T₂).toReal - (g T₁).toReal := by
    simpa [G₁, T₁, T₂, grad] using hsupport₁ T₂ hT₂_eff
  have h₂ :
      inner ℝ (G₂ - grad) (T₁ - T₂) ≤
        (g T₁).toReal - (g T₂).toReal := by
    simpa [G₂, T₁, T₂, grad] using hsupport₂ T₁ hT₁_eff
  have hsum :
      0 ≤ inner ℝ (G₁ - G₂) (T₁ - T₂) := by
    have hsum0 :
        inner ℝ (G₁ - grad) (T₂ - T₁) +
            inner ℝ (G₂ - grad) (T₁ - T₂) ≤
          0 := by
      linarith
    have hleft :
        inner ℝ (G₁ - grad) (T₂ - T₁) +
            inner ℝ (G₂ - grad) (T₁ - T₂) =
          -inner ℝ (G₁ - G₂) (T₁ - T₂) := by
      -- The gradient terms cancel after adding the two support inequalities.
      have hneg : T₂ - T₁ = -(T₁ - T₂) := by
        abel
      have hsub : (G₂ - grad) - (G₁ - grad) = -(G₁ - G₂) := by
        abel
      calc
        inner ℝ (G₁ - grad) (T₂ - T₁) + inner ℝ (G₂ - grad) (T₁ - T₂) =
            -inner ℝ (G₁ - grad) (T₁ - T₂) + inner ℝ (G₂ - grad) (T₁ - T₂) := by
              rw [hneg, inner_neg_right]
        _ = inner ℝ (G₂ - grad) (T₁ - T₂) -
              inner ℝ (G₁ - grad) (T₁ - T₂) := by
              ring
        _ = inner ℝ ((G₂ - grad) - (G₁ - grad)) (T₁ - T₂) := by
              rw [← inner_sub_left]
        _ = -inner ℝ (G₁ - G₂) (T₁ - T₂) := by
              rw [hsub, inner_neg_left]
    rw [hleft] at hsum0
    linarith
  have hstep :
      T₁ - T₂ = (1 / (L₂ : ℝ)) • G₂ - (1 / (L₁ : ℝ)) • G₁ := by
    -- Rewrite the prox points using `T_L(x) = x - (1 / L) G_L(x)`.
    dsimp [T₁, T₂]
    rw [prox_grad_operator_eq_sub_gradient_mapping, prox_grad_operator_eq_sub_gradient_mapping]
    abel
  have hinner :
      inner ℝ (G₁ - G₂) ((1 / (L₂ : ℝ)) • G₂ - (1 / (L₁ : ℝ)) • G₁) =
        ((1 / (L₁ : ℝ)) + (1 / (L₂ : ℝ))) * inner ℝ G₁ G₂ -
          (1 / (L₁ : ℝ)) * ‖G₁‖ ^ (2 : ℕ) -
          (1 / (L₂ : ℝ)) * ‖G₂‖ ^ (2 : ℕ) := by
    -- Expanding the inner product isolates the two norm squares and the mixed term.
    rw [inner_sub_right, inner_smul_right, inner_smul_right]
    have hleft :
        inner ℝ (G₁ - G₂) G₂ = inner ℝ G₁ G₂ - ‖G₂‖ ^ (2 : ℕ) := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq]
    have hright :
        inner ℝ (G₁ - G₂) G₁ = ‖G₁‖ ^ (2 : ℕ) - inner ℝ G₂ G₁ := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq]
    rw [hleft, hright, real_inner_comm G₂ G₁]
    ring
  have hcs : inner ℝ G₁ G₂ ≤ ‖G₁‖ * ‖G₂‖ := by
    -- Cauchy--Schwarz bounds the mixed inner product by the product of the norms.
    exact real_inner_le_norm G₁ G₂
  rw [hstep, hinner] at hsum
  have hcore :
      (1 / (L₁ : ℝ)) * ‖G₁‖ ^ (2 : ℕ) +
          (1 / (L₂ : ℝ)) * ‖G₂‖ ^ (2 : ℕ) ≤
        ((1 / (L₁ : ℝ)) + (1 / (L₂ : ℝ))) * inner ℝ G₁ G₂ := by
    nlinarith
  have hcoeff_nonneg : 0 ≤ (1 / (L₁ : ℝ)) + (1 / (L₂ : ℝ)) := by
    exact add_nonneg
      (one_div_nonneg.mpr (le_of_lt L₁.2))
      (one_div_nonneg.mpr (le_of_lt L₂.2))
  have hmul := mul_le_mul_of_nonneg_left hcs hcoeff_nonneg
  exact le_trans hcore <| by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Helper for Theorem 10.9: the quadratic norm inequality implies both the monotonicity of
`‖G_L(x)‖` and the antitonicity of `‖G_L(x)‖ / L`. -/
lemma gradient_mapping_norm_ratio_bounds
    (f g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    {L₁ L₂ : PosReal}
    (hL : L₁ ≤ L₂)
    (x : interior (effective_domain f)) :
    ‖G[L₁, f, g] x‖ ≤ ‖G[L₂, f, g] x‖ ∧
      ‖G[L₂, f, g] x‖ / (L₂ : ℝ) ≤ ‖G[L₁, f, g] x‖ / (L₁ : ℝ) := by
  let a : ℝ := ‖G[L₂, f, g] x‖
  let b : ℝ := ‖G[L₁, f, g] x‖
  have ha : 0 ≤ a := by
    dsimp [a]
    exact norm_nonneg _
  have hb : 0 ≤ b := by
    dsimp [b]
    exact norm_nonneg _
  have hquad :=
    gradient_mapping_quadratic_bound (f := f) (g := g) L₂ L₁ x
  have hquad_ab :
      (1 / (L₂ : ℝ)) * a ^ (2 : ℕ) + (1 / (L₁ : ℝ)) * b ^ (2 : ℕ) ≤
        ((1 / (L₂ : ℝ)) + (1 / (L₁ : ℝ))) * a * b := by
    simpa [a, b] using hquad
  have hquad' :
      (L₁ : ℝ) * a ^ (2 : ℕ) + (L₂ : ℝ) * b ^ (2 : ℕ) ≤
        ((L₂ : ℝ) + (L₁ : ℝ)) * a * b := by
    have hclear := hquad_ab
    -- Clear the denominators in the quadratic inequality.
    field_simp [show (L₁ : ℝ) ≠ 0 by exact L₁.2.ne',
      show (L₂ : ℝ) ≠ 0 by exact L₂.2.ne'] at hclear
    nlinarith
  have hmono : b ≤ a := by
    by_contra hba
    have hba' : a < b := lt_of_not_ge hba
    have hLb : (L₁ : ℝ) * a < (L₂ : ℝ) * b := by
      have h₁ : (L₁ : ℝ) * a < (L₁ : ℝ) * b := by
        exact mul_lt_mul_of_pos_left hba' L₁.2
      have h₂ : (L₁ : ℝ) * b ≤ (L₂ : ℝ) * b := by
        exact mul_le_mul_of_nonneg_right hL hb
      exact lt_of_lt_of_le h₁ h₂
    have hcontr :
        ((L₂ : ℝ) + (L₁ : ℝ)) * a * b <
          (L₁ : ℝ) * a ^ (2 : ℕ) + (L₂ : ℝ) * b ^ (2 : ℕ) := by
      nlinarith
    exact (not_lt_of_ge hquad') hcontr
  have hratio_num : (L₁ : ℝ) * a ≤ (L₂ : ℝ) * b := by
    by_contra hratio
    have hratio' : (L₂ : ℝ) * b < (L₁ : ℝ) * a := lt_of_not_ge hratio
    have hab_strict : b < a := by
      by_contra hab
      have hab' : a ≤ b := not_lt.mp hab
      have h₁ : (L₁ : ℝ) * a ≤ (L₁ : ℝ) * b := by
        exact mul_le_mul_of_nonneg_left hab' (le_of_lt L₁.2)
      have h₂ : (L₁ : ℝ) * b ≤ (L₂ : ℝ) * b := by
        exact mul_le_mul_of_nonneg_right hL hb
      exact (not_lt_of_ge (le_trans h₁ h₂)) hratio'
    have hcontr :
        ((L₂ : ℝ) + (L₁ : ℝ)) * a * b <
          (L₁ : ℝ) * a ^ (2 : ℕ) + (L₂ : ℝ) * b ^ (2 : ℕ) := by
      nlinarith
    exact (not_lt_of_ge hquad') hcontr
  refine ⟨?_, ?_⟩
  · simpa [a, b] using hmono
  · -- Divide the numerator inequality by the positive product `L₁ L₂`.
    refine (div_le_div_iff₀ L₂.2 L₁.2).2 ?_
    simpa [a, b, mul_comm] using hratio_num

/-- Theorem 10.9 (1): for a proper closed convex `g`, the norm of the gradient mapping
`G_L^{f,g}(x)` is monotone nondecreasing in the positive parameter `L`. In particular, if
`L₁ ≥ L₂ > 0`, then `‖G_{L₂}(x)‖ ≤ ‖G_{L₁}(x)‖`. -/
theorem gradient_mapping_norm_monotone
    (f g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (x : interior (effective_domain f)) :
    Monotone (fun L : PosReal ↦ ‖G[L, f, g] x‖) := by
  intro L₁ L₂ hL
  -- The shared scalar ratio lemma gives the norm monotonicity directly.
  exact (gradient_mapping_norm_ratio_bounds (f := f) (g := g) hL x).1

-- Proof sketch: start from the same quadratic inequality as in part (1), divide by the positive
-- quantity `‖G_{L₂}(x)‖` in the nontrivial case, and identify the resulting interval for
-- `‖G_{L₁}(x)‖ / ‖G_{L₂}(x)‖`; this gives
-- `‖G_{L₁}(x)‖ / L₁ ≤ ‖G_{L₂}(x)‖ / L₂`.
/-- Theorem 10.9 (2): after dividing by the positive parameter, the norm of the gradient mapping
`G_L^{f,g}(x)` is monotone nonincreasing in `L`. Thus if `L₁ ≥ L₂ > 0`, then
`‖G_{L₁}(x)‖ / L₁ ≤ ‖G_{L₂}(x)‖ / L₂`. -/
theorem gradient_mapping_norm_div_stepsize_antitone
    (f g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (x : interior (effective_domain f)) :
    Antitone (fun L : PosReal ↦ ‖G[L, f, g] x‖ / (L : ℝ)) := by
  intro L₁ L₂ hL
  -- The same ratio lemma also gives the normalized antitonicity.
  exact (gradient_mapping_norm_ratio_bounds (f := f) (g := g) hL x).2

end
