import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Definition_3_10
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap09.Definition_9_6
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap09.Text_9_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Algorithm 10.67 has two local layers.

- `source-facing`: the one-step update predicate from the chapter text;
- `core/canonical`: Chapter 9's `mirror_c_update_objective`;
- `bridge/view`: the later Hilbert-space Bregman rewrite of that objective.

Domain sampling in the surrounding project points to:
- `mirror_c_update_objective` from Definition 9.6 as the owner of the specialized one-step
  Mirror-C minimization problem;
- `IsMinOn` for the argmin clause;
- `PosReal` for the positive curvature parameter `L_k`.

The source-facing owner here specializes the Chapter 9 Mirror-C objective to the functional
`fderiv ℝ (fun y ↦ (f y).toReal) xk` and reciprocal curvature `(Lk : ℝ)⁻¹`, but unlike the earlier
totalized set-valued draft it keeps the Chapter 3 regularity clause
`is_differentiable_at f xk` explicit in the owner itself. This is the primitive data needed for
the displayed derivative to have its genuine textbook meaning. The Bregman rewrite is derived API
and is kept separate in the stronger inner-product section below. -/

/-- Algorithm 10.67: a point `x⁺` is an admissible next iterate of the non-Euclidean
proximal-gradient method from `x^k` with curvature parameter `L_k` when `f` is differentiable at
`x^k` in the Chapter 3 sense and `x⁺` globally minimizes the Chapter 9 Mirror-C update objective
specialized to the functional `f'(x^k)` and reciprocal curvature `(Lk : ℝ)⁻¹`. -/
def non_euclidean_proximal_gradient_step
    (f g ω : E → EReal) (xk : E) (Lk : PosReal) (xNext : E) : Prop :=
  is_differentiable_at f xk ∧
    IsMinOn
      (mirror_c_update_objective g ω xk
        (fderiv ℝ (fun y ↦ (f y).toReal) xk) ((Lk : ℝ)⁻¹))
      Set.univ xNext

/-- Algorithm 10.67 is exactly the conjunction of the Chapter 3 differentiability condition at
`x^k` and the canonical Mirror-C global-minimizer condition for `x⁺`. -/
@[simp] theorem non_euclidean_proximal_gradient_step_iff
    {f g ω : E → EReal} {xk xNext : E} {Lk : PosReal} :
    non_euclidean_proximal_gradient_step f g ω xk Lk xNext ↔
      is_differentiable_at f xk ∧
      IsMinOn
        (mirror_c_update_objective g ω xk
          (fderiv ℝ (fun y ↦ (f y).toReal) xk) ((Lk : ℝ)⁻¹))
        Set.univ xNext :=
  Iff.rfl

/-- A non-Euclidean proximal-gradient step starts at a differentiability point of `f`. -/
theorem non_euclidean_proximal_gradient_step.differentiable_at
    {f g ω : E → EReal} {xk xNext : E} {Lk : PosReal}
    (hstep : non_euclidean_proximal_gradient_step f g ω xk Lk xNext) :
    is_differentiable_at f xk :=
  hstep.1

/-- A non-Euclidean proximal-gradient step is a global minimizer of the specialized Mirror-C
objective. -/
theorem non_euclidean_proximal_gradient_step.isMinOn
    {f g ω : E → EReal} {xk xNext : E} {Lk : PosReal}
    (hstep : non_euclidean_proximal_gradient_step f g ω xk Lk xNext) :
    IsMinOn
      (mirror_c_update_objective g ω xk
        (fderiv ℝ (fun y ↦ (f y).toReal) xk) ((Lk : ℝ)⁻¹))
      Set.univ xNext :=
  hstep.2

end

section

open scoped Gradient

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- The remainder of the file is a `bridge/view` layer.

The owner abstraction is still `mirror_c_update_objective`, but rewriting it into the textbook
Bregman model is already controlled upstream by Text 9.10. The source-facing textbook reading now
needs the explicit differentiability hypothesis
`hfxk : is_differentiable_at f xk`, so the displayed first-order term uses the genuine textbook
derivative of `f` at `x^k` and the added constant `f xk` is finite.

The Bregman model is therefore derived API for the same owner rather than a second root
definition. The Bregman-distance term itself is reused through Chapter 9's totalized owner `B[ω]`;
when `xk ∈ subdifferential_domain ω`, this coincides with the textbook base-point reading, but
that guard is not primitive data for the minimizer-equivalence statement here. -/

-- Proof sketch: first apply the owner-level Chapter 9 bridge
-- `isMinOn_mirror_c_update_objective_iff_isMinOn_bregman_update_objective` with
-- `s = fderiv ℝ (fun y ↦ (f y).toReal) xk` and `t = (Lk : ℝ)⁻¹`. Then use `hfxk` to rewrite the
-- linear term through the genuine gradient `∇ (fun y ↦ (f y).toReal) xk`, multiply the objective
-- by the positive constant `Lk`, and add the `x`-independent finite constant `f xk`.

omit [CompleteSpace E] in
/-- Helper for Algorithm 10.67: differentiability at `x^k` forces `f xk` to be a finite
extended-real value, so it can be rewritten through `toReal`. -/
lemma differentiable_at_value_eq_coe_toReal
    {f : E → EReal} {xk : E} (hfxk : is_differentiable_at f xk) :
    f xk = (((f xk).toReal : ℝ) : EReal) := by
  -- The interior finite-domain hypothesis supplies both `f xk ≠ ⊤` and `f xk ≠ ⊥`.
  have hxk_finite : xk ∈ finite_domain f := interior_subset hfxk.1
  have hxk_effective : xk ∈ effective_domain f := (mem_finite_domain.mp hxk_finite).1
  have hxk_ne_bot : f xk ≠ ⊥ := (mem_finite_domain.mp hxk_finite).2
  exact (EReal.coe_toReal (mem_effective_domain.mp hxk_effective).ne hxk_ne_bot).symm

/-- Helper for Algorithm 10.67: in the Hilbert-space setting, the displayed derivative acts by
the gradient pairing. -/
lemma fderiv_toReal_apply_eq_inner_gradient
    {f : E → EReal} {xk x : E} (hfxk : is_differentiable_at f xk) :
    fderiv ℝ (fun y ↦ (f y).toReal) xk x =
      inner ℝ (∇ (fun y ↦ (f y).toReal) xk) x := by
  -- Convert the Fréchet derivative supplied by differentiability into the Riesz-represented
  -- gradient and then evaluate both sides at `x`.
  simpa [InnerProductSpace.toDualMap_apply_apply] using
    congrArg (fun T : StrongDual ℝ E ↦ T x) hfxk.2.hasGradientAt.hasFDerivAt.fderiv

/-- Helper for Algorithm 10.67: the Chapter 9 Bregman-form objective specialized to the derivative
of `f` at `x^k` and reciprocal curvature `(L_k)⁻¹`. -/
def scaled_bregman_objective
    (f g ω : E → EReal) (xk : E) (Lk : PosReal) : E → EReal :=
  fun x ↦
    ((((Lk : ℝ)⁻¹ * fderiv ℝ (fun y ↦ (f y).toReal) xk x : ℝ) : EReal) +
      (((Lk : ℝ)⁻¹ : EReal) * g x) +
      ((B[ω] x xk : ℝ) : EReal))

/-- Helper for Algorithm 10.67: the textbook non-Euclidean proximal-gradient local model. -/
def non_euclidean_textbook_model
    (f g ω : E → EReal) (xk : E) (Lk : PosReal) : E → EReal :=
  fun x ↦
    ((f xk +
        ((inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (x - xk) : ℝ) : EReal)) +
      g x) +
      (((Lk : ℝ) * B[ω] x xk : ℝ) : EReal)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Helper for Algorithm 10.67: multiplying an objective by a positive real scalar and adding a
finite real constant preserves its global minimizers over `Set.univ`. -/
lemma isMinOn_univ_iff_of_pos_mul_add_constant
    {φ ψ : E → EReal} {z : E} {a c : ℝ} (ha : 0 < a)
    (hobj : ∀ x, φ x = (((a : ℝ) : EReal) * ψ x) + (c : EReal)) :
    IsMinOn φ Set.univ z ↔ IsMinOn ψ Set.univ z := by
  have hscale_pos : 0 < ((a : ℝ) : EReal) := by
    exact_mod_cast ha
  have hscale_top : ((a : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have hscale_bot : ((a : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
  have hscale_zero : ((a : ℝ) : EReal) ≠ 0 := by
    exact_mod_cast ha.ne'
  rw [isMinOn_univ_iff, isMinOn_univ_iff]
  constructor
  · intro hz x
    have hzx := hz x
    rw [hobj z, hobj x] at hzx
    have hscaled :
        (((a : ℝ) : EReal) * ψ z) ≤ (((a : ℝ) : EReal) * ψ x) :=
      ((EReal.addLECancellable_coe c).add_le_add_iff_right).mp hzx
    have hdiv :
        ((((a : ℝ) : EReal) * ψ z) / ((a : ℝ) : EReal)) ≤
          ((((a : ℝ) : EReal) * ψ x) / ((a : ℝ) : EReal)) :=
      EReal.monotone_div_right_of_nonneg hscale_pos.le hscaled
    rw [mul_comm (((a : ℝ) : EReal)) (ψ z), mul_comm (((a : ℝ) : EReal)) (ψ x)] at hdiv
    rw [← EReal.mul_div_right, ← EReal.mul_div_right,
      EReal.div_mul_cancel hscale_bot hscale_top hscale_zero,
      EReal.div_mul_cancel hscale_bot hscale_top hscale_zero] at hdiv
    exact hdiv
  · intro hz x
    have hscaled :
        (((a : ℝ) : EReal) * ψ z) ≤ (((a : ℝ) : EReal) * ψ x) :=
      mul_le_mul_of_nonneg_left (hz x) hscale_pos.le
    have hshifted := ((EReal.addLECancellable_coe c).add_le_add_iff_right).mpr hscaled
    calc
      φ z = (((a : ℝ) : EReal) * ψ z) + (c : EReal) := hobj z
      _ ≤ (((a : ℝ) : EReal) * ψ x) + (c : EReal) := hshifted
      _ = φ x := (hobj x).symm

/-- Helper for Algorithm 10.67: the textbook non-Euclidean proximal-gradient model is an
`x`-independent finite constant plus the positive scalar `L_k` times the Chapter 9 Bregman-form
objective specialized to `f'(x^k)` and `(L_k)⁻¹`. -/
lemma non_euclidean_model_eq_constant_add_scaled_bregman_objective
    (f g ω : E → EReal) (xk x : E) (Lk : PosReal)
    (hfxk : is_differentiable_at f xk) :
    non_euclidean_textbook_model f g ω xk Lk x =
      (((f xk).toReal - inner ℝ (∇ (fun y ↦ (f y).toReal) xk) xk : ℝ) : EReal) +
        (((Lk : ℝ) : EReal) * scaled_bregman_objective f g ω xk Lk x) := by
  let grad : E := ∇ (fun y ↦ (f y).toReal) xk
  let scalar : EReal := ((Lk : ℝ) : EReal)
  have hscalar_nonneg : (0 : EReal) ≤ scalar := by
    simpa [scalar] using
      (show (0 : EReal) ≤ ((Lk : ℝ) : EReal) by
        exact_mod_cast le_of_lt (PosReal.coe_pos Lk))
  have hscalar_ne_top : scalar ≠ ⊤ := EReal.coe_ne_top (Lk : ℝ)
  have hlinear_eval :
      fderiv ℝ (fun y ↦ (f y).toReal) xk x = inner ℝ grad x := by
    simpa [grad] using fderiv_toReal_apply_eq_inner_gradient (f := f) (xk := xk) (x := x) hfxk
  have hconstant_linear :
      ((((f xk).toReal - inner ℝ grad xk : ℝ) : EReal) +
          (((fderiv ℝ (fun y ↦ (f y).toReal) xk x : ℝ) : EReal))) =
        f xk + ((inner ℝ grad (x - xk) : ℝ) : EReal) := by
    -- Rewrite the finite constant through `toReal` and combine the linear pieces in `ℝ`.
    have hreal :
        (f xk).toReal - inner ℝ grad xk + inner ℝ grad x =
          (f xk).toReal + inner ℝ grad (x - xk) := by
      rw [inner_sub_right]
      ring
    rw [differentiable_at_value_eq_coe_toReal (f := f) (xk := xk) hfxk, hlinear_eval,
      ← EReal.coe_add, ← EReal.coe_add]
    exact congrArg (fun r : ℝ ↦ (r : EReal)) hreal
  have hscaled_linear :
      scalar *
          (((((Lk : ℝ)⁻¹) * (fderiv ℝ (fun y ↦ (f y).toReal) xk x) : ℝ) : EReal)) =
        (((fderiv ℝ (fun y ↦ (f y).toReal) xk x : ℝ) : EReal)) := by
    -- Cancel the reciprocal curvature on the finite linear term.
    rw [← EReal.coe_mul]
    congr 1
    field_simp [PosReal.coe_inv, show (Lk : ℝ) ≠ 0 by exact ne_of_gt (PosReal.coe_pos Lk)]
  have hscaled_penalty :
      scalar * ((((Lk : ℝ)⁻¹ : EReal) * g x)) = g x := by
    -- The same positive scalar cancellation works on the possibly infinite penalty term.
    have hone_real : (Lk : ℝ) * (Lk : ℝ)⁻¹ = 1 := by
      field_simp [show (Lk : ℝ) ≠ 0 by exact ne_of_gt (PosReal.coe_pos Lk)]
    have hone :
        scalar * (((Lk : ℝ)⁻¹ : EReal)) = 1 := by
      simpa [scalar] using congrArg (fun r : ℝ ↦ (r : EReal)) hone_real
    calc
      scalar * ((((Lk : ℝ)⁻¹ : EReal) * g x))
          = (scalar * (((Lk : ℝ)⁻¹ : EReal))) * g x := by rw [mul_assoc]
      _ = 1 * g x := by rw [hone]
      _ = g x := by rw [one_mul]
  have hscaled_bregman :
      scalar * (((B[ω] x xk : ℝ) : EReal)) =
        ((((Lk : ℝ) * B[ω] x xk : ℝ) : EReal)) := by
    -- The Bregman-distance term is finite, so the scaling remains inside `ℝ`.
    have hmul :
        (((Lk : ℝ) : EReal) * (((B[ω] x xk : ℝ) : EReal))) =
          ((((Lk : ℝ) * B[ω] x xk : ℝ) : EReal)) := by
      rw [← EReal.coe_mul]
    dsimp [scalar]
  -- Reassociate the model and distribute the positive scalar across the Chapter 9 objective.
  calc
    non_euclidean_textbook_model f g ω xk Lk x
        =
        (f xk + ((inner ℝ grad (x - xk) : ℝ) : EReal)) +
          (g x + ((((Lk : ℝ) * B[ω] x xk : ℝ) : EReal))) := by
            simp [non_euclidean_textbook_model]
            ac_rfl
    _ =
        ((((f xk).toReal - inner ℝ grad xk : ℝ) : EReal) +
          (((fderiv ℝ (fun y ↦ (f y).toReal) xk x : ℝ) : EReal))) +
          (g x + ((((Lk : ℝ) * B[ω] x xk : ℝ) : EReal))) := by
            rw [hconstant_linear]
    _ =
        ((((f xk).toReal - inner ℝ grad xk : ℝ) : EReal) +
          ((((fderiv ℝ (fun y ↦ (f y).toReal) xk x : ℝ) : EReal) +
            g x) +
            ((((Lk : ℝ) * B[ω] x xk : ℝ) : EReal)))) := by
              ac_rfl
    _ =
        ((((f xk).toReal - inner ℝ grad xk : ℝ) : EReal) +
          (scalar * scaled_bregman_objective f g ω xk Lk x)) := by
              rw [scaled_bregman_objective]
              rw [EReal.left_distrib_of_nonneg_of_ne_top hscalar_nonneg hscalar_ne_top,
                EReal.left_distrib_of_nonneg_of_ne_top hscalar_nonneg hscalar_ne_top,
                hscaled_linear, hscaled_penalty, hscaled_bregman]
    _ =
        (((f xk).toReal - inner ℝ (∇ (fun y ↦ (f y).toReal) xk) xk : ℝ) : EReal) +
          (((Lk : ℝ) : EReal) * scaled_bregman_objective f g ω xk Lk x) := by
            simp [scalar, grad]

/-- Helper for Algorithm 10.67: positive affine rescaling transports `IsMinOn` from the Chapter 9
Bregman-form objective to the textbook non-Euclidean proximal-gradient model and back. -/
lemma isMinOn_scaled_bregman_objective_iff_isMinOn_non_euclidean_model
    (f g ω : E → EReal) (xk xNext : E) (Lk : PosReal)
    (hfxk : is_differentiable_at f xk) :
    IsMinOn (scaled_bregman_objective f g ω xk Lk) Set.univ xNext ↔
      IsMinOn (non_euclidean_textbook_model f g ω xk Lk) Set.univ xNext := by
  have hobj :
      ∀ x,
        non_euclidean_textbook_model f g ω xk Lk x =
          (((Lk : ℝ) : EReal) * scaled_bregman_objective f g ω xk Lk x) +
            (((f xk).toReal - inner ℝ (∇ (fun y ↦ (f y).toReal) xk) xk : ℝ) : EReal) := by
    intro x
    simpa [add_comm, add_left_comm, add_assoc] using
      (non_euclidean_model_eq_constant_add_scaled_bregman_objective
        (f := f) (g := g) (ω := ω) (xk := xk) (x := x) (Lk := Lk) hfxk)
  simpa using
    (isMinOn_univ_iff_of_pos_mul_add_constant
      (E := E) (φ := non_euclidean_textbook_model f g ω xk Lk)
      (ψ := scaled_bregman_objective f g ω xk Lk)
      (z := xNext) (a := (Lk : ℝ))
      (c := (f xk).toReal - inner ℝ (∇ (fun y ↦ (f y).toReal) xk) xk)
      (ha := PosReal.coe_pos Lk) hobj).symm

/-- If `f` is differentiable at `x^k` in the Chapter 3 sense, then the specialized Mirror-C owner
for Algorithm 10.67 has exactly the same minimizers as the textbook Bregman-regularized local
model
`x ↦ f(x^k) + ⟪∇ f(x^k), x - x^k⟫ + g(x) + L_k B_ω(x, x^k)`. -/
theorem isMinOn_mirror_c_update_objective_iff_isMinOn_non_euclidean_proximal_gradient_model
    (f g ω : E → EReal) (xk xNext : E) (Lk : PosReal)
    (hfxk : is_differentiable_at f xk) :
    IsMinOn
      (mirror_c_update_objective g ω xk
        (fderiv ℝ (fun y ↦ (f y).toReal) xk) ((Lk : ℝ)⁻¹))
      Set.univ xNext ↔
      IsMinOn
        (fun x ↦
          ((f xk +
              ((inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (x - xk) : ℝ) : EReal)) +
            g x) +
            ((((Lk : ℝ) * B[ω] x xk : ℝ) : EReal)))
        Set.univ xNext := by
  -- First move from the owner-level Mirror-C objective to Chapter 9's canonical Bregman form.
  have hbridge :
      IsMinOn
          (mirror_c_update_objective g ω xk
            (fderiv ℝ (fun y ↦ (f y).toReal) xk) ((Lk : ℝ)⁻¹))
          Set.univ xNext ↔
        IsMinOn (scaled_bregman_objective f g ω xk Lk) Set.univ xNext := by
    simpa [scaled_bregman_objective] using
      (isMinOn_mirror_c_update_objective_iff_isMinOn_bregman_update_objective
        g ω xk xNext
        (fderiv ℝ (fun y ↦ (f y).toReal) xk) ((Lk : ℝ)⁻¹))
  -- Then normalize that Bregman-form objective by the positive scalar `L_k` and a fixed constant.
  have hmodel :
      IsMinOn (scaled_bregman_objective f g ω xk Lk) Set.univ xNext ↔
        IsMinOn (non_euclidean_textbook_model f g ω xk Lk) Set.univ xNext :=
    isMinOn_scaled_bregman_objective_iff_isMinOn_non_euclidean_model
      (f := f) (g := g) (ω := ω) (xk := xk) (xNext := xNext) (Lk := Lk) hfxk
  exact hbridge.trans (by simpa [non_euclidean_textbook_model] using hmodel)

/-- Under the Chapter 3 differentiability hypothesis, Algorithm 10.67 is equivalent to minimizing
the textbook Bregman-regularized local model at `x^k`. -/
theorem non_euclidean_proximal_gradient_step_iff_isMinOn_non_euclidean_proximal_gradient_model
    {f g ω : E → EReal} {xk xNext : E} {Lk : PosReal}
    (hfxk : is_differentiable_at f xk) :
    non_euclidean_proximal_gradient_step f g ω xk Lk xNext ↔
      IsMinOn
        (fun x ↦
          ((f xk +
              ((inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (x - xk) : ℝ) : EReal)) +
            g x) +
            ((((Lk : ℝ) * B[ω] x xk : ℝ) : EReal)))
        Set.univ xNext := by
  simpa [non_euclidean_proximal_gradient_step, hfxk, non_euclidean_textbook_model] using
    (isMinOn_mirror_c_update_objective_iff_isMinOn_non_euclidean_proximal_gradient_model
      f g ω xk xNext Lk hfxk)

end
