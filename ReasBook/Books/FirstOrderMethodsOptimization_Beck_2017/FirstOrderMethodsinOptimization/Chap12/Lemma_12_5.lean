import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Definition_6_10
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Theorem_6_15
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Theorem_6_67
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap05.Theorem_5_26
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap12.Algorithm_12_1
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap12.Algorithm_12_2

-- Declarations for this item will be appended below by the statement pipeline.

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
