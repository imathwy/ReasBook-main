import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_12_5 (from Chap12) -/
universe u v

noncomputable section

section

variable {E : Type u} {Y : Type v}
variable [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup Y] [Module ℝ Y]

/- Definition 12.5 has two layers:
- `source-facing`: the textbook dual terms `F(y) = f*(Aᵀ y)` and `G(y) = g*(-y)`;
- `core/canonical`: Chapter 10's `composite_model_objective` for the split sum `F + G`;
- `bridge/view`: the identification of that split sum with the negated Chapter 12.4 dual
  maximization objective `-q`.

Domain sampling in the surrounding chapter/project identifies:
- `conjugate_function` as the owner of Fenchel conjugates;
- `LinearMap.dualMap` as the owner of the transpose pullback `Aᵀ y`;
- `composite_model_objective` as the chapter owner for pointwise sums;
- `dual_based_proximal_gradient_lagrange_dual_objective` as the maximization-side Chapter 12
  owner.

Primitive data are therefore only the two dual terms `F` and `G`; the combined minimization
objective is derived API from the existing owner `composite_model_objective`. -/

private theorem ereal_sInf_neg (s : Set EReal) :
    sInf (-s) = -sSup s := by
  refine le_antisymm ?_ ?_
  · have hsSup : sSup s ≤ -sInf (-s) := by
      refine sSup_le fun x hx ↦ ?_
      have hsInf : sInf (-s) ≤ -x := by
        exact sInf_le (by simpa [Set.mem_neg] using hx : -x ∈ -s)
      exact EReal.le_neg.mp hsInf
    exact EReal.le_neg.mpr hsSup
  · refine le_sInf fun z hz ↦ ?_
    exact EReal.neg_le.mpr (le_sSup (by simpa [Set.mem_neg] using hz : -z ∈ s))

/-- The textbook term `F(y) = f*(Aᵀ y)` in the dual-based proximal gradient dual model, expressed
through the canonical pullback `A.dualMap` on the algebraic dual. -/
def dual_based_proximal_gradient_dual_F_term
    (f : E → EReal) (A : E →ₗ[ℝ] Y) : Module.Dual ℝ Y → EReal :=
  conjugate_function f ∘ A.dualMap

-- Proof sketch: unfold `dual_based_proximal_gradient_dual_F_term`; its value at `y` is exactly the
-- Chapter 4 conjugate `f*` evaluated at the dual pullback `A.dualMap y`.
/-- Evaluating the textbook `F`-term gives `f*(Aᵀ y)` via `conjugate_function`. -/
@[simp] theorem dual_based_proximal_gradient_dual_F_term_apply
    (f : E → EReal) (A : E →ₗ[ℝ] Y) (y : Module.Dual ℝ Y) :
    dual_based_proximal_gradient_dual_F_term f A y =
      conjugate_function f (A.dualMap y) :=
  rfl

/-- The textbook term `G(y) = g*(-y)` in the dual-based proximal gradient dual model. -/
def dual_based_proximal_gradient_dual_G_term
    (g : Y → EReal) : Module.Dual ℝ Y → EReal :=
  conjugate_function g ∘ Neg.neg

-- Proof sketch: unfold `dual_based_proximal_gradient_dual_G_term`; this is exactly the Chapter 4
-- conjugate of `g` evaluated at the negated dual variable.
/-- Evaluating the textbook `G`-term gives `g*(-y)` via `conjugate_function`. -/
@[simp] theorem dual_based_proximal_gradient_dual_G_term_apply
    (g : Y → EReal) (y : Module.Dual ℝ Y) :
    dual_based_proximal_gradient_dual_G_term g y =
      conjugate_function g (-y) :=
  rfl

/- Definition 12.5: the dual minimization objective in textbook split form is the Chapter 10
owner `composite_model_objective` applied to the Chapter 12 dual terms `F` and `G`. -/
recall composite_model_objective
recall composite_model_objective_apply

-- Proof sketch: unfold the split terms `F` and `G` and the Chapter 12.4 owner `q`, then apply
-- `EReal.neg_sub` under the local non-`⊥` hypotheses that rule out the mixed infinite case.
/-- When the two split summands avoid `⊥`, their canonical Chapter 10 sum agrees pointwise with
the bridge/view `-q(y)`. -/
theorem dual_based_proximal_gradient_dual_terms_sum_eq_neg_lagrange_dual_objective
    (f : E → EReal) (g : Y → EReal) (A : E →ₗ[ℝ] Y) (y : Module.Dual ℝ Y)
    (hF : dual_based_proximal_gradient_dual_F_term f A y ≠ ⊥)
    (hG : dual_based_proximal_gradient_dual_G_term g y ≠ ⊥) :
    composite_model_objective
        (dual_based_proximal_gradient_dual_F_term f A)
        (dual_based_proximal_gradient_dual_G_term g) y =
      -dual_based_proximal_gradient_lagrange_dual_objective f g A y := by
  rw [composite_model_objective_apply, dual_based_proximal_gradient_dual_F_term_apply,
    dual_based_proximal_gradient_dual_G_term_apply,
    dual_based_proximal_gradient_lagrange_dual_objective_apply]
  have hF_top : -conjugate_function f (A.dualMap y) ≠ ⊤ := by
    intro h
    have h' : conjugate_function f (A.dualMap y) = ⊥ := by
      simpa using congrArg Neg.neg h
    exact hF h'
  have hneg :
      -(-conjugate_function f (A.dualMap y) - conjugate_function g (-y)) =
        - -conjugate_function f (A.dualMap y) + conjugate_function g (-y) :=
    EReal.neg_sub (Or.inr (by simpa using hG)) (Or.inl hF_top)
  simpa using hneg.symm

-- Proof sketch: use the bridge theorem to identify the source-facing split objective with the
-- negated Chapter 12.4 owner pointwise, rewrite its range as the negated range of `q`, and then
-- apply the order-duality identity `sInf (-s) = -sSup s`.
/-- If the split summands are never `⊥`, the infimum of the dual minimization objective is the
negation of the canonical dual maximization value from Definition 12.4. -/
theorem dual_based_proximal_gradient_dual_terms_infimum_eq_neg_lagrange_dual_problem_value
    (f : E → EReal) (g : Y → EReal) (A : E →ₗ[ℝ] Y)
    (hF : ∀ y, dual_based_proximal_gradient_dual_F_term f A y ≠ ⊥)
    (hG : ∀ y, dual_based_proximal_gradient_dual_G_term g y ≠ ⊥) :
    sInf
        (Set.range
          (composite_model_objective
            (dual_based_proximal_gradient_dual_F_term f A)
            (dual_based_proximal_gradient_dual_G_term g))) =
      -dual_based_proximal_gradient_lagrange_dual_problem_value f g A := by
  rw [dual_based_proximal_gradient_lagrange_dual_problem_value]
  have hrange :
      Set.range
          (composite_model_objective
            (dual_based_proximal_gradient_dual_F_term f A)
            (dual_based_proximal_gradient_dual_G_term g)) =
        -Set.range (dual_based_proximal_gradient_lagrange_dual_objective f g A) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      rw [dual_based_proximal_gradient_dual_terms_sum_eq_neg_lagrange_dual_objective
        f g A y (hF y) (hG y)]
      simp [Set.mem_neg]
    · intro hz
      have hz' : -z ∈ Set.range (dual_based_proximal_gradient_lagrange_dual_objective f g A) := by
        simpa [Set.mem_neg] using hz
      rcases hz' with ⟨y, hy⟩
      refine ⟨y, ?_⟩
      rw [dual_based_proximal_gradient_dual_terms_sum_eq_neg_lagrange_dual_objective
        f g A y (hF y) (hG y)]
      simpa using congrArg Neg.neg hy
  rw [hrange]
  exact ereal_sInf_neg
    (Set.range (dual_based_proximal_gradient_lagrange_dual_objective f g A))

end

/-! ### Lemma_12_5 (from Chap12) -/
noncomputable section

open scoped Gradient

universe u v

section

variable {E : Type u} {V : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Helper for Lemma 12.5: the gradient of the shifted pullback of `f∗` along `A.adjoint` is the
pushforward by `A` of the ambient conjugate gradient. -/
lemma gradient_conjugate_pullback_add_eq
    (σ : PosReal) (f : E → EReal) (A : E →ₗ[ℝ] V) (b : E)
    (hf_proper : IsProperExtendedRealFunction f) (hf_closed : LowerSemicontinuous f)
    (hf_strong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun x ↦ (f x).toReal))
    (v : V) :
    ∇ (fun z : V ↦ (((f∗) (A.adjoint z + b)).toReal)) v =
      A (∇ (fun x : E ↦ (((f∗) x).toReal)) (A.adjoint v + b)) := by
  let fStarReal : E → ℝ := fun x ↦ (((f∗) x).toReal)
  let fStarStrongDual : StrongDual ℝ E → ℝ := fun y ↦ (conjugate_function_strongDual f y).toReal
  have hsmooth :=
    is_l_smooth_on_toReal_conjugate_function_strongDual_of_proper_closed_strongConvexOn
      (σ : ℝ) σ.2 f hf_proper.ne_bot hf_proper.effective_domain_nonempty hf_closed hf_strong
  rw [is_l_smooth_on] at hsmooth
  have hdiffStrongDual :
      DifferentiableAt ℝ fStarStrongDual (InnerProductSpace.toDual ℝ E (A.adjoint v + b)) := by
    simpa [fStarStrongDual] using
      hsmooth.1 (InnerProductSpace.toDual ℝ E (A.adjoint v + b)) (by simp)
  have hdiffFStar : DifferentiableAt ℝ fStarReal (A.adjoint v + b) := by
    have hcomp :=
      hdiffStrongDual.comp (A.adjoint v + b)
        (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt
    simpa [fStarReal, fStarStrongDual, conjugate_function_primal_apply,
      conjugate_function_strongDual] using hcomp
  have hdiffShift : DifferentiableAt ℝ (fun x : E ↦ fStarReal (x + b)) (A.adjoint v) := by
    simpa [fStarReal] using hdiffFStar.comp (A.adjoint v) (differentiableAt_id.add_const b)
  have hderiv :
      fderiv ℝ (fun z : V ↦ fStarReal (A.adjoint z + b)) v =
        (fderiv ℝ fStarReal (A.adjoint v + b)).comp A.adjoint.toContinuousLinearMap := by
    -- Differentiate the affine pullback by first composing with `A.adjoint`, then shifting by `b`.
    change
      fderiv ℝ ((fun x : E ↦ fStarReal (x + b)) ∘ A.adjoint) v =
        (fderiv ℝ fStarReal (A.adjoint v + b)).comp A.adjoint.toContinuousLinearMap
    have hAderiv : fderiv ℝ (fun z : V ↦ A.adjoint z) v = A.adjoint.toContinuousLinearMap := by
      simpa using A.adjoint.toContinuousLinearMap.fderiv
    rw [fderiv_comp v hdiffShift A.adjoint.toContinuousLinearMap.differentiableAt]
    rw [hAderiv]
    rw [fderiv_comp_add_right b]
  have hgradMap :
      (fderiv ℝ fStarReal (A.adjoint v + b)).comp A.adjoint.toContinuousLinearMap =
        (InnerProductSpace.toDual ℝ V)
          (A (∇ (fun x : E ↦ (((f∗) x).toReal)) (A.adjoint v + b))) := by
    -- Identify the composed derivative with the Riesz image of `A (∇ f∗)`.
    have hgradFStar :
        fderiv ℝ fStarReal (A.adjoint v + b) =
          (InnerProductSpace.toDual ℝ E) (∇ (fun x : E ↦ (((f∗) x).toReal)) (A.adjoint v + b)) := by
      simpa [fStarReal] using hdiffFStar.hasGradientAt.hasFDerivAt.fderiv
    ext y
    calc
      ((fderiv ℝ fStarReal (A.adjoint v + b)).comp A.adjoint.toContinuousLinearMap) y
          = fderiv ℝ fStarReal (A.adjoint v + b) (A.adjoint y) := by
              rfl
      _ = inner ℝ (∇ (fun x : E ↦ (((f∗) x).toReal)) (A.adjoint v + b)) (A.adjoint y) := by
            rw [hgradFStar, InnerProductSpace.toDual_apply_apply]
      _ = inner ℝ (A (∇ (fun x : E ↦ (((f∗) x).toReal)) (A.adjoint v + b))) y := by
            rw [LinearMap.adjoint_inner_right]
      _ =
          (InnerProductSpace.toDual ℝ V)
            (A (∇ (fun x : E ↦ (((f∗) x).toReal)) (A.adjoint v + b))) y := by
            rfl
  -- Convert the derivative identity back to the gradient identity.
  simpa [gradient] using
    congrArg ((InnerProductSpace.toDual ℝ V).symm) (hderiv.trans hgradMap)

/-- Helper for Lemma 12.5: the proximal mapping of `z ↦ (g∗) (-z)` is the negated image of the
proximal mapping of the scaled conjugate. -/
lemma prox_negated_conjugate_eq_neg_image_scaled_conjugate_prox
    (g : V → EReal) (hg_proper : IsProperExtendedRealFunction g)
    (hg_convex : is_convex_function g) (L : PosReal) (w : V) :
    prox[((((1 / L : PosReal) : EReal) • fun z : V ↦ (g∗) (-z)))] w =
      (fun q : V ↦ -q) '' prox[((((1 / L : PosReal) : EReal) • (g∗)))] (-w) := by
  let gScaled : V → EReal := (((1 / L : PosReal) : EReal) • (g∗))
  let φ : V →ᴬ[ℝ] V := (-ContinuousLinearMap.id ℝ V).toContinuousAffineMap
  have hgConjProper : IsProperExtendedRealFunction (g∗) :=
    conjugate_function_primal_proper_of_proper_convex g hg_proper hg_convex
  have hgScaledProper : IsProperExtendedRealFunction gScaled :=
    scaled_function_proper_of_pos (f := (g∗)) (μ := (1 / L : PosReal)) hgConjProper
  have hφ :
      φ.contLinear ∘L ContinuousLinearMap.adjoint φ.contLinear = (1 : ℝ) • (1 : V →L[ℝ] V) := by
    -- The negation map is an isometry, so its adjoint-composition is the identity.
    ext z
    simp [φ]
  calc
    prox[((((1 / L : PosReal) : EReal) • fun z : V ↦ (g∗) (-z)))] w
        = prox[gScaled ∘ φ] w := by
            congr 1
    _ =
        (fun z : V ↦ w + ((1 : ℝ)⁻¹ • ContinuousLinearMap.adjoint φ.contLinear) (z - φ w)) ''
          prox[((1 : EReal) • gScaled)] (φ w) := by
            simpa using
              proximal_mapping_precompose_continuousAffineMap
                gScaled hgScaledProper φ 1 zero_lt_one hφ w
    _ = (fun q : V ↦ -q) '' prox[((((1 / L : PosReal) : EReal) • (g∗)))] (-w) := by
      -- Simplify the affine correction for `φ = -id`.
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨z, ?_, ?_⟩
        · simpa [gScaled, φ]
            using hz
        · simp [φ]
      · rintro ⟨z, hz, hy⟩
        refine ⟨z, ?_, ?_⟩
        · simpa [gScaled, φ]
            using hz
        · simpa [φ] using hy

/-- Helper for Lemma 12.5: the negated scaled-conjugate proximal point is equivalent to the
Chapter 12 primal `y`-step owner. -/
lemma neg_scaled_conjugate_prox_mem_iff_mem_dual_proximal_gradient_primal_y_step
    (g : V → EReal) (A : E →ₗ[ℝ] V) (x : E) (v y : V) (L : PosReal)
    (hg_proper : IsProperExtendedRealFunction g) (hg_closed : LowerSemicontinuous g)
    (hg_convex : is_convex_function g) :
    y ∈ (fun q : V ↦ -q) '' prox[((((1 / L : PosReal) : EReal) • (g∗)))] ((1 / L : ℝ) • A x - v) ↔
      y ∈ dual_proximal_gradient_primal_y_step g A x v L := by
  rcases scaled_function_proper_closed_convex_of_pos g hg_proper hg_closed hg_convex L with
    ⟨hgScaledProper, hgScaledClosed, hgScaledConvex⟩
  rcases prox_eq_singleton_of_proper_closed_convex
      (((L : EReal) • g)) hgScaledProper hgScaledClosed hgScaledConvex
      (A x - (L : ℝ) • v) with
    ⟨p, hpSingleton⟩
  have hdualSingleton :=
    dual_moreau_prox_eq_singleton
      g hg_proper hg_closed hg_convex L (A x - (L : ℝ) • v) p hpSingleton
  have hbase :
      ((L : ℝ)⁻¹ • (A x - (L : ℝ) • v)) = ((1 / L : ℝ) • A x - v) := by
    -- Normalize the Moreau base point into the textbook forward point.
    have hL : (L : ℝ) ≠ 0 := ne_of_gt L.2
    rw [smul_sub, smul_smul]
    simp [one_div, hL]
  have hdualSingletonBase :
      prox[((((1 / L : PosReal) : EReal) • (g∗)))] ((1 / L : ℝ) • A x - v) =
        {((L : ℝ)⁻¹ • ((A x - (L : ℝ) • v) - p))} := by
    simpa [hbase] using hdualSingleton
  have hnegResidual :
      -((L : ℝ)⁻¹ • ((A x - (L : ℝ) • v) - p)) =
        v - (1 / L : ℝ) • A x + (1 / L : ℝ) • p := by
    -- Expand the residual point into the Chapter 12 affine update.
    have hL : (L : ℝ) ≠ 0 := ne_of_gt L.2
    calc
      -((L : ℝ)⁻¹ • ((A x - (L : ℝ) • v) - p))
          = (L : ℝ)⁻¹ • p - (L : ℝ)⁻¹ • (A x - (L : ℝ) • v) := by
              rw [smul_sub, neg_sub]
      _ = v - (1 / L : ℝ) • A x + (1 / L : ℝ) • p := by
            rw [smul_sub, smul_smul]
            simp [one_div, hL, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hqSingleton :
        q = (L : ℝ)⁻¹ • ((A x - (L : ℝ) • v) - p) := by
      have : q ∈ ({((L : ℝ)⁻¹ • ((A x - (L : ℝ) • v) - p))} : Set V) := by
        rw [hdualSingletonBase] at hq
        exact hq
      simpa using this
    rw [mem_dual_proximal_gradient_primal_y_step_iff]
    refine ⟨p, ?_, ?_⟩
    · have hpMem : p ∈ ({p} : Set V) := by simp
      simpa [hpSingleton] using hpMem
    · simp [hqSingleton, hnegResidual]
  · intro hy
    rw [mem_dual_proximal_gradient_primal_y_step_iff] at hy
    rcases hy with ⟨p', hp', hyEq⟩
    have hp'Eq : p' = p := by
      have : p' ∈ ({p} : Set V) := by
        simpa [hpSingleton] using hp'
      simpa using this
    refine ⟨(L : ℝ)⁻¹ • ((A x - (L : ℝ) • v) - p), ?_, ?_⟩
    · rw [hdualSingletonBase]
      simp
    · simp [hyEq, hp'Eq, hnegResidual]

-- Proof sketch: render the source dual update through the Chapter 12 owner
-- `dual_based_proximal_gradient_dual_step` with the canonical nonsmooth term
-- `w ↦ (g∗) (-w)`. The smooth gradient is the affine-shifted
-- conjugate gradient `w ↦ ∇ (((f∗) (A.adjoint w + b)).toReal)`, and the source argmax point is the
-- canonical gradient point `xTilde = ∇ (fun x ↦ ((f∗) x).toReal) (A.adjoint v + b)`. Then apply
-- the negation transport of the proximal mapping together with the extended Moreau decomposition
-- to identify the dual-step owner with the canonical Algorithm 12.2 primal `y`-step owner at
-- `xTilde`.
/-- Lemma 12.5: if `F(w) = f^*(Aᵀ w + b)` and `G(w) = g^*(-w)` under assumptions (A), (B), and
(C) of Assumption 12.1, then the dual proximal-gradient relation
`y = prox_{(1 / L) G} (v - (1 / L) ∇ F(v))` is equivalent, rendered on the Chapter 12 step owner
`dual_based_proximal_gradient_dual_step`, to membership in the canonical Algorithm 12.2 owner
`dual_proximal_gradient_primal_y_step g A x̃ v L`, where
`x̃ = ∇ f^*(Aᵀ v + b)` is the canonical maximizer of
`x ↦ ⟪x, Aᵀ v + b⟫ - f(x)`. -/
theorem dual_based_proximal_gradient_dual_step_iff_mem_dual_proximal_gradient_primal_y_step
    (σ : PosReal) (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) (b : E)
    (hf_proper : IsProperExtendedRealFunction f) (hf_closed : LowerSemicontinuous f)
    (hf_strong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun x ↦ (f x).toReal))
    (hg_proper : IsProperExtendedRealFunction g) (hg_closed : LowerSemicontinuous g)
    (hg_convex : is_convex_function g) (y v : V) (L : PosReal) :
    y ∈ dual_based_proximal_gradient_dual_step
          (fun z : V ↦ (g∗) (-z))
          (fun w ↦ ∇ (fun z : V ↦ (((f∗) (A.adjoint z + b)).toReal)) w)
          L
          v ↔
      y ∈ dual_proximal_gradient_primal_y_step
        g
        A
        (∇ (fun x : E ↦ (((f∗) x).toReal)) (A.adjoint v + b))
        v
        L := by
  -- Rewrite the source owner into the proximal point with the explicit forward-gradient point.
  rw [mem_dual_based_proximal_gradient_dual_step_iff]
  -- Identify the smooth gradient term with the pushed-forward conjugate gradient `A x̃`.
  rw [gradient_conjugate_pullback_add_eq σ f A b hf_proper hf_closed hf_strong v]
  -- Transport the proximal set of `z ↦ (g∗) (-z)` through negation.
  rw [prox_negated_conjugate_eq_neg_image_scaled_conjugate_prox g hg_proper hg_convex L]
  -- Finish with the Moreau decomposition rendered on the Chapter 12 primal-step owner.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    neg_scaled_conjugate_prox_mem_iff_mem_dual_proximal_gradient_primal_y_step
      g A
      (∇ (fun x : E ↦ (((f∗) x).toReal)) (A.adjoint v + b))
      v y L hg_proper hg_closed hg_convex

end

/-! ### Proposition_12_5 (from Chap12) -/
noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius
open Matrix WithLp

section

variable (m n : ℕ)

local notation "M" => Matrix (Fin m) (Fin n) ℝ
local notation "P" => Matrix (Fin m) (Fin (n - 1)) ℝ
local notation "Q" => Matrix (Fin (m - 1)) (Fin n) ℝ
local notation "TVSpace" => WithLp 2 (P × Q)

/- Proposition 12.5 is `bridge/view` in the two-dimensional total-variation denoising API.

Domain sampling identifies the owner split:
- `core/canonical`: `two_dimensional_total_variation_difference : M →ₗ[ℝ] TVSpace` from
  Proposition 12.4;
- `core/canonical`: mathlib's `WithLp.linearEquiv`, `WithLp.fst`, and `WithLp.snd`, which equip
  `WithLp 2 (P × Q)` with the canonical `L²` product structure used for the TV dual pair;
- `core/canonical`: `LinearMap.adjoint`, once the source and target carry the Frobenius and `L²`
  Hilbert structures used in the chapter;
- `bridge/view`: the explicit boundary-value formula for `Aᵀ z`.

Primitive data here are only the Frobenius/`L²` Hilbert structures. The divergence formula is
derived API from the adjoint owner, not a second public operator parallel to `A.adjoint`. The
owner-level notation `A[m, n]` and `Aᵀ[m, n]` is imported from Proposition 12.4. -/

local instance : NormedAddCommGroup M := Matrix.frobeniusNormedAddCommGroup

local instance : NormedSpace ℝ M := Matrix.frobeniusNormedSpace

local instance : InnerProductSpace ℝ M := Matrix.frobeniusInnerProductSpace

local instance : NormedAddCommGroup P := Matrix.frobeniusNormedAddCommGroup

local instance : NormedSpace ℝ P := Matrix.frobeniusNormedSpace

local instance : InnerProductSpace ℝ P := Matrix.frobeniusInnerProductSpace

local instance : NormedAddCommGroup Q := Matrix.frobeniusNormedAddCommGroup

local instance : NormedSpace ℝ Q := Matrix.frobeniusNormedSpace

local instance : InnerProductSpace ℝ Q := Matrix.frobeniusInnerProductSpace

-- Proof sketch: identify `Aᵀ` with the unique map satisfying the Hilbert adjoint identity for the
-- Proposition 12.4 forward-difference operator, then compute the resulting coordinate formula by
-- summing the four boundary-adjusted contributions incident to the pixel `(i, j)`.
/-- Helper for Proposition 12.5: subtracting one from a positive `Fin n` index lands in
`Fin (n - 1)`. -/
lemma sub_one_val_lt_sub_one (j : Fin n) (h : 0 < j.1) : j.1 - 1 < n - 1 := by
  omega

/-- Helper for Proposition 12.5: the previous index in `Fin (n - 1)` attached to a positive
`Fin n` index. -/
abbrev pred_sub_index (j : Fin n) (h : 0 < j.1) : Fin (n - 1) :=
  ⟨j.1 - 1, sub_one_val_lt_sub_one n j h⟩

/-- Helper for Proposition 12.5: the real inner product on scalar entries is ordinary
multiplication. -/
lemma real_inner_eq_mul (a b : ℝ) : inner ℝ a b = a * b := by
  change b * a = a * b
  ring

/-- Helper for Proposition 12.5: casting a forward-difference index from `Fin n` into
`Fin (n + 1)` agrees with `Fin.castSucc`. -/
lemma castLE_sub_eq_castSucc (j : Fin n) :
    Fin.castLE (Nat.sub_le (n + 1) 1) j = j.castSucc := by
  -- Both constructions keep the same underlying natural-number value.
  apply Fin.ext
  rfl

/-- Helper for Proposition 12.5: adding one to the value of a `Fin n` index agrees with
`Fin.succ`. -/
lemma mk_add_one_eq_succ (j : Fin n) :
    (⟨(j : ℕ) + 1, by omega⟩ : Fin (n + 1)) = j.succ := by
  -- Both constructions represent the successor coordinate inside `Fin (n + 1)`.
  apply Fin.ext
  rfl

/-- Helper for Proposition 12.5: one-dimensional summation by parts rewrites the forward-difference
pairing as a zero-padded divergence pairing. -/
lemma forward_difference_sum_eq_zero_padded
    (x : Fin n → ℝ) (p : Fin (n - 1) → ℝ) :
    (∑ j : Fin (n - 1), (x (Fin.castLE (Nat.sub_le n 1) j) - x ⟨(j : ℕ) + 1, by omega⟩) * p j) =
      ∑ j : Fin n, x j *
        ((if h : j.1 < n - 1 then p (j.castLT h) else 0) -
          (if h : 0 < j.1 then p (pred_sub_index n j h) else 0)) := by
  cases n with
  | zero =>
      simp
  | succ n =>
      -- Split the forward-difference sum into the outgoing and incoming boundary contributions.
      calc
        (∑ j : Fin n, (x (Fin.castLE (Nat.sub_le (n + 1) 1) j) - x ⟨(j : ℕ) + 1, by omega⟩) * p j) =
            (∑ j : Fin n, x (Fin.castSucc j) * p j) - ∑ j : Fin n, x j.succ * p j := by
          simp_rw [sub_mul]
          rw [Finset.sum_sub_distrib]
          have h_cast :
              ∑ j : Fin n, x (Fin.castLE (Nat.sub_le (n + 1) 1) j) * p j =
                ∑ j : Fin n, x (Fin.castSucc j) * p j := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            -- Replace the source index by the canonical `castSucc` representative.
            rw [castLE_sub_eq_castSucc]
          have h_succ :
              ∑ j : Fin n, x ⟨(j : ℕ) + 1, by omega⟩ * p j =
                ∑ j : Fin n, x j.succ * p j := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            -- Rewrite the shifted target index into the canonical `succ` form.
            rw [mk_add_one_eq_succ]
          rw [h_cast, h_succ]
        _ =
            (∑ j : Fin (n + 1), x j * (if h : j.1 < n then p (j.castLT h) else 0)) -
              ∑ j : Fin (n + 1),
                x j * (if h : 0 < j.1 then p (pred_sub_index (n + 1) j h) else 0) := by
          rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
          simp [pred_sub_index]
        _ = ∑ j : Fin (n + 1), x j *
              ((if h : j.1 < n then p (j.castLT h) else 0) -
                (if h : 0 < j.1 then p (pred_sub_index (n + 1) j h) else 0)) := by
          simp_rw [mul_sub]
          rw [← Finset.sum_sub_distrib]

/-- Helper for Proposition 12.5: the horizontal inner-product term is the zero-padded horizontal
divergence contribution. -/
lemma horizontal_difference_inner_eq_zero_padded
    (x : M) (z : TVSpace) :
    inner ℝ (two_dimensional_total_variation_horizontal_difference x) z.fst =
      ∑ i : Fin m, ∑ j : Fin n,
        x i j *
          ((if h : j.1 < n - 1 then z.fst i (j.castLT h) else 0) -
            (if h : 0 < j.1 then z.fst i (pred_sub_index n j h) else 0)) := by
  -- Expand the Frobenius inner product rowwise, then apply the one-dimensional summation formula.
  change
    inner ℝ
        (WithLp.toLp 2 fun i : Fin m ↦
          WithLp.toLp 2 fun j : Fin (n - 1) ↦
            two_dimensional_total_variation_horizontal_difference x i j)
        (WithLp.toLp 2 fun i : Fin m ↦ WithLp.toLp 2 fun j : Fin (n - 1) ↦ z.fst i j) =
      ∑ i : Fin m, ∑ j : Fin n,
        x i j *
          ((if h : j.1 < n - 1 then z.fst i (j.castLT h) else 0) -
            (if h : 0 < j.1 then z.fst i (pred_sub_index n j h) else 0))
  calc
    inner ℝ
        (WithLp.toLp 2 fun i : Fin m ↦
          WithLp.toLp 2 fun j : Fin (n - 1) ↦
            two_dimensional_total_variation_horizontal_difference x i j)
        (WithLp.toLp 2 fun i : Fin m ↦ WithLp.toLp 2 fun j : Fin (n - 1) ↦ z.fst i j) =
      ∑ i : Fin m, ∑ j : Fin (n - 1),
        (two_dimensional_total_variation_horizontal_difference x i j) * z.fst i j := by
      simp_rw [PiLp.inner_apply, real_inner_eq_mul]
    _ = ∑ i : Fin m, ∑ j : Fin n,
          x i j *
            ((if h : j.1 < n - 1 then z.fst i (j.castLT h) else 0) -
              (if h : 0 < j.1 then z.fst i (pred_sub_index n j h) else 0)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simpa [two_dimensional_total_variation_horizontal_difference_apply] using
        forward_difference_sum_eq_zero_padded n (x := x i) (p := z.fst i)

/-- Helper for Proposition 12.5: the vertical inner-product term is the zero-padded vertical
divergence contribution. -/
lemma vertical_difference_inner_eq_zero_padded
    (x : M) (z : TVSpace) :
    inner ℝ (two_dimensional_total_variation_vertical_difference x) z.snd =
      ∑ i : Fin m, ∑ j : Fin n,
        x i j *
          ((if h : i.1 < m - 1 then z.snd (i.castLT h) j else 0) -
            (if h : 0 < i.1 then z.snd (pred_sub_index m i h) j else 0)) := by
  -- Commute the finite sums so each column can reuse the same one-dimensional summation formula.
  change
    inner ℝ
        (WithLp.toLp 2 fun i : Fin (m - 1) ↦
          WithLp.toLp 2 fun j : Fin n ↦
            two_dimensional_total_variation_vertical_difference x i j)
        (WithLp.toLp 2 fun i : Fin (m - 1) ↦ WithLp.toLp 2 fun j : Fin n ↦ z.snd i j) =
      ∑ i : Fin m, ∑ j : Fin n,
        x i j *
          ((if h : i.1 < m - 1 then z.snd (i.castLT h) j else 0) -
            (if h : 0 < i.1 then z.snd (pred_sub_index m i h) j else 0))
  calc
    inner ℝ
        (WithLp.toLp 2 fun i : Fin (m - 1) ↦
          WithLp.toLp 2 fun j : Fin n ↦
            two_dimensional_total_variation_vertical_difference x i j)
        (WithLp.toLp 2 fun i : Fin (m - 1) ↦ WithLp.toLp 2 fun j : Fin n ↦ z.snd i j) =
      ∑ i : Fin (m - 1), ∑ j : Fin n,
        (two_dimensional_total_variation_vertical_difference x i j) * z.snd i j := by
      simp_rw [PiLp.inner_apply, real_inner_eq_mul]
    _ = ∑ j : Fin n, ∑ i : Fin (m - 1),
          (two_dimensional_total_variation_vertical_difference x i j) * z.snd i j := by
      rw [Finset.sum_comm]
    _ =
      ∑ j : Fin n, ∑ i : Fin m,
        x i j *
          ((if h : i.1 < m - 1 then z.snd (i.castLT h) j else 0) -
            (if h : 0 < i.1 then z.snd (pred_sub_index m i h) j else 0)) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      simpa [two_dimensional_total_variation_vertical_difference_apply] using
        forward_difference_sum_eq_zero_padded m (x := fun i ↦ x i j) (p := fun i ↦ z.snd i j)
    _ = ∑ i : Fin m, ∑ j : Fin n,
          x i j *
            ((if h : i.1 < m - 1 then z.snd (i.castLT h) j else 0) -
              (if h : 0 < i.1 then z.snd (pred_sub_index m i h) j else 0)) := by
      rw [Finset.sum_comm]

/-- Helper for Proposition 12.5: the adjoint of the discrete TV difference operator is the
zero-padded discrete divergence. -/
abbrev zero_padded_divergence (z : TVSpace) : M :=
  fun i j ↦
    (if h : j.1 < n - 1 then z.fst i (j.castLT h) else 0) +
      (if h : i.1 < m - 1 then z.snd (i.castLT h) j else 0) -
      (if h : 0 < j.1 then z.fst i (pred_sub_index n j h) else 0) -
      (if h : 0 < i.1 then z.snd (pred_sub_index m i h) j else 0)

/-- Helper for Proposition 12.5: the Hilbert adjoint agrees with the zero-padded divergence matrix
on every entry. -/
lemma two_dimensional_total_variation_difference_adjoint_eq_zero_padded_divergence
    (z : TVSpace) :
    Aᵀ[m, n] z = zero_padded_divergence m n z := by
  apply ext_inner_left ℝ
  intro x
  -- Route correction: identify the adjoint globally by the Hilbert pairing before reading off a
  -- coordinate formula; this keeps the proof aligned with the textbook summation-by-parts route.
  calc
    inner ℝ x (Aᵀ[m, n] z) = inner ℝ (A[m, n] x) z := by
      simpa using (LinearMap.adjoint_inner_right (A[m, n]) x z)
    _ = inner ℝ ((A[m, n] x).fst) z.fst + inner ℝ ((A[m, n] x).snd) z.snd := by
      simp [WithLp.prod_inner_apply]
    _ = inner ℝ (two_dimensional_total_variation_horizontal_difference x) z.fst +
          inner ℝ (two_dimensional_total_variation_vertical_difference x) z.snd := by
      rw [two_dimensional_total_variation_difference_fst, two_dimensional_total_variation_difference_snd]
    _ =
        (∑ i : Fin m, ∑ j : Fin n,
          x i j *
            ((if h : j.1 < n - 1 then z.fst i (j.castLT h) else 0) -
              (if h : 0 < j.1 then z.fst i (pred_sub_index n j h) else 0))) +
          ∑ i : Fin m, ∑ j : Fin n,
            x i j *
              ((if h : i.1 < m - 1 then z.snd (i.castLT h) j else 0) -
                (if h : 0 < i.1 then z.snd (pred_sub_index m i h) j else 0)) := by
      rw [horizontal_difference_inner_eq_zero_padded, vertical_difference_inner_eq_zero_padded]
    _ = ∑ i : Fin m, ∑ j : Fin n,
          x i j *
            ((if h : j.1 < n - 1 then z.fst i (j.castLT h) else 0) +
              (if h : i.1 < m - 1 then z.snd (i.castLT h) j else 0) -
              (if h : 0 < j.1 then z.fst i (pred_sub_index n j h) else 0) -
              (if h : 0 < i.1 then z.snd (pred_sub_index m i h) j else 0)) := by
      -- Combine the horizontal and vertical contributions into the single divergence summand.
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j hj
      ring
    _ = inner ℝ x (zero_padded_divergence m n z) := by
      -- Re-expand the Frobenius pairing of matrices back into the entrywise double sum.
      change
        ∑ i : Fin m, ∑ j : Fin n,
          x i j *
            ((((if h : j.1 < n - 1 then z.fst i (j.castLT h) else 0) +
                  if h : i.1 < m - 1 then z.snd (i.castLT h) j else 0) -
                if h : 0 < j.1 then z.fst i (pred_sub_index n j h) else 0) -
              if h : 0 < i.1 then z.snd (pred_sub_index m i h) j else 0) =
          inner ℝ
            (WithLp.toLp 2 fun i : Fin m ↦ WithLp.toLp 2 fun j : Fin n ↦ x i j)
            (WithLp.toLp 2 fun i : Fin m ↦
              WithLp.toLp 2 fun j : Fin n ↦ zero_padded_divergence m n z i j)
      simp_rw [PiLp.inner_apply, real_inner_eq_mul]

/-- Proposition 12.5: the Hilbert adjoint `Aᵀ[m, n]` of the two-dimensional TV operator
`A[m, n]` has the divergence-style coordinate formula with zero-extended boundary terms. -/
@[simp]
theorem two_dimensional_total_variation_difference_adjoint_apply
    (z : TVSpace) (i : Fin m) (j : Fin n) :
    Aᵀ[m, n] z i j =
      (if h : j.1 < n - 1 then z.fst i ⟨j.1, h⟩ else 0) +
        (if h : i.1 < m - 1 then z.snd ⟨i.1, h⟩ j else 0) -
        (if h : 0 < j.1 then z.fst i ⟨j.1 - 1, by omega⟩ else 0) -
        (if h : 0 < i.1 then z.snd ⟨i.1 - 1, by omega⟩ j else 0) := by
  -- Read off the coordinate formula from the global adjoint identification.
  simpa [zero_padded_divergence, pred_sub_index] using
    congr_fun (congr_fun
      (two_dimensional_total_variation_difference_adjoint_eq_zero_padded_divergence m n z) i) j

-- Proof sketch: specialize `two_dimensional_total_variation_difference_adjoint_apply` to the
-- canonical `L²` owner point `WithLp.toLp 2 (p, q)`, then simplify the `fst`/`snd` projections.
/-- Evaluating `Aᵀ[m, n]` on the canonical dual pair `(p, q)` recovers the textbook divergence
formula `p_{i,j} + q_{i,j} - p_{i,j-1} - q_{i-1,j}` with zero boundary extension. -/
@[simp] theorem two_dimensional_total_variation_difference_adjoint_toLp_apply
    (p : P) (q : Q) (i : Fin m) (j : Fin n) :
    Aᵀ[m, n] (toLp 2 (p, q)) i j =
      (if h : j.1 < n - 1 then p i ⟨j.1, h⟩ else 0) +
        (if h : i.1 < m - 1 then q ⟨i.1, h⟩ j else 0) -
        (if h : 0 < j.1 then p i ⟨j.1 - 1, by omega⟩ else 0) -
        (if h : 0 < i.1 then q ⟨i.1 - 1, by omega⟩ j else 0) := by
  simpa only using
    two_dimensional_total_variation_difference_adjoint_apply m n (toLp 2 (p, q)) i j

end
