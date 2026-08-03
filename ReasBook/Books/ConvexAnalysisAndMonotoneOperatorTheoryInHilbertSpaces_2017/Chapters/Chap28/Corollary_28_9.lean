import BauschkeLean.Chap10.Definition_10_7
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap12.ScaledProximityOperator
import BauschkeLean.Chap12.Proposition_12_15
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Theorem_16_3
import BauschkeLean.Chap16.Corollary_16_50
import BauschkeLean.Chap17.Proposition_17_21
import BauschkeLean.Chap17.Corollary_17_42
import BauschkeLean.Chap18.Remark_18_16
import BauschkeLean.Chap18.Theorem_18_13
import BauschkeLean.Chap20.Theorem_20_25
import BauschkeLean.Chap22.Example_22_5
import BauschkeLean.Chap26.Proposition_26_25
import BauschkeLean.Chap26.Theorem_26_14

open Filter Set SetValuedOperator
open scoped Gradient InnerProductSpace Pointwise SetValuedOperator Topology

universe u

namespace ERealFunction

/- Source/core/bridge triage:
- `source-facing`: Corollary 28.9 is the relaxed proximal-gradient recursion `(28.33)` together
  with its weak-convergence, dual-limit, and strong-convergence consequences.
- `core/canonical`: the reusable operator owner is the Chapter 26 relaxed forward-backward
  iteration `forwardBackwardIteration`.
- `bridge/view`: the source two-sequence recursion `(x_n, y_n)` is kept explicit, and the
  companion theorem below identifies its `x`-sequence with the canonical Chapter 26 iteration for
  `A = ∂ f` and `B = ∇ g`. -/

section ForwardBackwardAlgorithm

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A pair of sequences `x` and `y` satisfies the relaxed forward-backward recursion `(28.33)` for
`f`, `g`, step size `γ`, relaxation parameters `lam`, and initial point `x0`. -/
structure IsRelaxedForwardBackwardProximalGradientOrbit
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (γ : PosReal) (lam : ℕ → ℝ) (x0 : H) (x y : ℕ → H) : Prop where
  /-- The orbit starts at the prescribed point `x0`. -/
  x_zero : x 0 = x0
  /-- The forward step is `y_n = x_n - γ ∇ g(x_n)`. -/
  y_eq : ∀ n : ℕ, y n = x n - (γ : ℝ) • ∇ g (x n)
  /-- The relaxed backward step is `x_(n+1) = x_n + λ_n (Prox_{γ f}(y_n) - x_n)`. -/
  x_succ_eq : ∀ n : ℕ,
    x (n + 1) = x n + lam n • (Prox[γ, f, hf] (y n) - x n)

namespace IsRelaxedForwardBackwardProximalGradientOrbit

variable {f : H → Set.Ioi (⊥ : EReal)} {hf : f ∈ Γ₀(H)} {g : H → ℝ}
variable {γ : PosReal} {lam : ℕ → ℝ} {x0 : H} {x y : ℕ → H}

local notation "hSub" => subdifferential_isMaximallyMonotone_of_mem_gammaZero hf

/-- The `x`-sequence of `(28.33)` is the Chapter 26 relaxed forward-backward iteration for
`A = ∂ f` and `B = ∇ g`. -/
theorem x_eq_forwardBackwardIteration
    (hOrbit : IsRelaxedForwardBackwardProximalGradientOrbit hf g γ lam x0 x y) :
    x = forwardBackwardIteration (∂ f) hSub (∇ g) γ lam x0 := by
  funext n
  induction n with
  | zero =>
      -- Both recursions start from the prescribed initial point `x0`.
      simpa [forwardBackwardIteration] using hOrbit.x_zero
  | succ n ih =>
      -- Rewrite the source update into the Chapter 26 forward-backward step at time `n`.
      calc
        x (n + 1) = x n + lam n • (Prox[γ, f, hf] (y n) - x n) := hOrbit.x_succ_eq n
        _ =
            forwardBackwardIteration (∂ f) hSub (∇ g) γ lam x0 n +
              lam n •
                (forwardBackwardSplittingOperator (∂ f) hSub (∇ g) γ
                    (forwardBackwardIteration (∂ f) hSub (∇ g) γ lam x0 n) -
                  forwardBackwardIteration (∂ f) hSub (∇ g) γ lam x0 n) := by
              rw [hOrbit.y_eq n, ih]
              simp [forwardBackwardSplittingOperator,
                resolventMap_subdifferential_eq_scaledProximityOperator (hf := hf),
                sub_eq_add_neg]
        _ = forwardBackwardIteration (∂ f) hSub (∇ g) γ lam x0 (n + 1) := by
              rw [forwardBackwardIteration, relaxedOperatorIteration_succ]

end IsRelaxedForwardBackwardProximalGradientOrbit

/-- Helper for Corollary 28.9: the quadratic control `s ↦ β s²` has remainder
`θ(s) = (β / 2) s²`. -/
lemma quadraticTheta_eq
    (β : Set.Ioi (0 : ℝ)) (r : ℝ) :
    θ (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ)) r = ((β : ℝ) / 2) * r ^ (2 : ℕ) := by
  rw [theta_apply]
  have hintegrand :
      (fun t : ℝ ↦ ((β : ℝ) * (r * t) ^ (2 : ℕ)) / t) =
        fun t : ℝ ↦ t * ((β : ℝ) * r ^ (2 : ℕ)) := by
    funext t
    by_cases ht : t = 0
    · subst ht
      simp
    · field_simp [ht]
  -- Rewrite the interval integral to the elementary integral of a linear function on `[0,1]`.
  rw [hintegrand, intervalIntegral.integral_mul_const, integral_id]
  ring

/-- Helper for Corollary 28.9: on nonnegative inputs, the conjugate quadratic remainder satisfies
`θ*(r) = r² / (2β)` as an `EReal` equality. -/
lemma quadraticThetaStar_asEReal_eq_of_nonneg
    (β : Set.Ioi (0 : ℝ)) {r : ℝ} (hr : 0 ≤ r) :
    thetaStar (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ)) r =
      ((((1 / (2 * (β : ℝ))) * r ^ (2 : ℕ) : ℝ) : EReal)) := by
  have hquadratic_even : Function.Even (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ)) := by
    intro s
    simp [pow_two]
  have hquadratic_conv :
      _root_.ConvexOn ℝ Set.univ (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ)) := by
    have hsqConv : _root_.ConvexOn ℝ Set.univ (fun s : ℝ ↦ s ^ (2 : ℕ)) := by
      simpa using (show Even (2 : ℕ) by decide).convexOn_pow
    simpa [smul_eq_mul] using hsqConv.smul β.2.le
  have hquadratic_zero :
      ∀ s : ℝ, (β : ℝ) * s ^ (2 : ℕ) = 0 ↔ s = 0 := by
    intro s
    constructor
    · intro hs
      have hβ_ne : (β : ℝ) ≠ 0 := ne_of_gt β.2
      have hsq : s ^ (2 : ℕ) = 0 := by
        exact (mul_eq_zero.mp hs).resolve_left hβ_ne
      exact eq_zero_of_pow_eq_zero hsq
    · intro hs
      simp [hs]
  have hasEReal :=
    thetaStar_asEReal_of_nonneg
      (φ := fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ))
      hquadratic_even hquadratic_conv hquadratic_zero hr
  have hconj :
      thetaConj (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ)) r =
        (((((1 / (2 * (β : ℝ))) * r ^ (2 : ℕ) : ℝ) : EReal))) := by
    -- Evaluate the public conjugate of the quadratic Moreau remainder.
    rw [thetaConj]
    have htheta :
        ((θ (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ))).toEReal.asEReal) =
          (moreauQuadraticKernel (H := ℝ) (β⁻¹ : PosReal)).asEReal := by
      funext s
      rw [Function.asEReal_apply, Function.toEReal_apply, Function.asEReal_apply,
        quadraticTheta_eq]
      have hreal :
          ((β : ℝ) / 2) * s ^ (2 : ℕ) =
            (1 / (2 * (((β⁻¹ : PosReal) : ℝ))) * ‖s‖ ^ (2 : ℕ) : ℝ) := by
        rw [Real.norm_eq_abs, sq_abs]
        have hcoeff :
            (1 / (2 * (((β⁻¹ : PosReal) : ℝ))) : ℝ) = (β : ℝ) / 2 := by
          change (1 / (2 * (β : ℝ)⁻¹) : ℝ) = (β : ℝ) / 2
          field_simp [show (β : ℝ) ≠ 0 from ne_of_gt β.2]
        rw [hcoeff]
      exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal
    rw [htheta]
    have hkernel :=
      congrFun
        (conjugate_moreauQuadraticKernel_eq_smul_halfSquaredNorm
          (H := ℝ) (γ := (β⁻¹ : PosReal)))
        r
    calc
      (moreauQuadraticKernel (H := ℝ) (β⁻¹ : PosReal)).asEReal∗ r =
          ((((((β⁻¹ : PosReal) : ℝ) * ((1 / 2 : ℝ) * r ^ (2 : ℕ)) : ℝ) : EReal))) := by
            simpa [Pi.smul_apply, Function.asEReal_apply, halfSquaredNorm_apply,
              Real.norm_eq_abs, sq_abs, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
              hkernel
      _ = (((((1 / (2 * (β : ℝ))) * r ^ (2 : ℕ) : ℝ) : EReal))) := by
            congr 1
            change ((β : ℝ)⁻¹) * ((1 / 2 : ℝ) * r ^ (2 : ℕ)) =
              (1 / (2 * (β : ℝ))) * r ^ (2 : ℕ)
            field_simp [show (β : ℝ) ≠ 0 from ne_of_gt β.2]
  rw [hasEReal, hconj]

/-- Helper for Corollary 28.9: a differentiable convex function with `β`-Lipschitz gradient has
`1 / β`-cocoercive gradient on `H`. -/
lemma gradient_lipschitz_imp_cocoercive_of_differentiable_convex
    (f : H → ℝ) (hdiff : Differentiable ℝ f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (β : Set.Ioi (0 : ℝ))
    (hLip : LipschitzWith (Real.toNNReal (β : ℝ)) (∇ f)) :
    CocoerciveOn (1 / (β : ℝ)) (Set.univ : Set H) (fun x : Set.univ ↦ ∇ f x) := by
  refine ⟨by simpa [one_div] using (show 0 < 1 / (β : ℝ) from one_div_pos.mpr β.2), ?_⟩
  intro x y
  have hquadratic_even : Function.Even (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ)) := by
    intro s
    simp [pow_two]
  have hquadratic_conv :
      _root_.ConvexOn ℝ Set.univ (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ)) := by
    have hsqConv : _root_.ConvexOn ℝ Set.univ (fun s : ℝ ↦ s ^ (2 : ℕ)) := by
      simpa using (show Even (2 : ℕ) by decide).convexOn_pow
    simpa [smul_eq_mul] using hsqConv.smul β.2.le
  have hquadratic_zero :
      ∀ s : ℝ, (β : ℝ) * s ^ (2 : ℕ) = 0 ↔ s = 0 := by
    intro s
    constructor
    · intro hs
      have hβ_ne : (β : ℝ) ≠ 0 := ne_of_gt β.2
      have hsq : s ^ (2 : ℕ) = 0 := by
        exact (mul_eq_zero.mp hs).resolve_left hβ_ne
      exact eq_zero_of_pow_eq_zero hsq
    · intro hs
      simp [hs]
  have hinner :
      ∀ a b : H, ⟪a - b, ∇ f a - ∇ f b⟫_ℝ ≤ (β : ℝ) * ‖a - b‖ ^ (2 : ℕ) := by
    intro a b
    have hgrad :
        ‖∇ f a - ∇ f b‖ ≤ (β : ℝ) * ‖a - b‖ := by
      simpa [dist_eq_norm, Real.toNNReal_of_nonneg β.2.le] using hLip.dist_le_mul a b
    calc
      ⟪a - b, ∇ f a - ∇ f b⟫_ℝ ≤ ‖a - b‖ * ‖∇ f a - ∇ f b‖ := by
        exact real_inner_le_norm _ _
      _ ≤ ‖a - b‖ * ((β : ℝ) * ‖a - b‖) := by
        gcongr
      _ = (β : ℝ) * ‖a - b‖ ^ (2 : ℕ) := by
        ring_nf
  have hdescent :
      ∀ a b : H,
        f b ≤ f a + ⟪b - a, ∇ f a⟫_ℝ +
          θ (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ)) ‖a - b‖ := by
    intro a b
    have hmodel :=
      le_gradient_quadratic_model_of_differentiable_convex_lipschitzGradient
        (f := f) (x := a) hdiff hconv hLip b
    have hmodel' :
        f b ≤ f a + ⟪b - a, ∇ f a⟫_ℝ + ((β : ℝ) / 2) * ‖a - b‖ ^ (2 : ℕ) := by
      calc
        f b ≤ gradientAffineModel f a b +
            (β : ℝ) *
              ContinuousLinearMap.quadraticPotential (ContinuousLinearMap.id ℝ H) (b - a) :=
          hmodel
        _ = f a + ⟪b - a, ∇ f a⟫_ℝ + ((β : ℝ) / 2) * ‖a - b‖ ^ (2 : ℕ) := by
            rw [gradientAffineModel, ContinuousLinearMap.quadraticPotential_apply,
              ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq, norm_sub_rev]
            ring
    rw [quadraticTheta_eq (β := β) (r := ‖a - b‖)]
    exact hmodel'
  have hpair :=
    gradient_inner_ge_two_thetaConjugate_of_conjugate_gradient_ge_affine_add_thetaConjugate
      (φ := fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ))
      (f := f) hdiff hconv hquadratic_even hquadratic_conv hquadratic_zero
      (conjugate_gradient_ge_affine_add_thetaConjugate_of_descent_le_linearization_add_theta
        (φ := fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ))
        (f := f) hdiff hconv hquadratic_even hquadratic_conv hquadratic_zero hdescent)
      (x : H) (y : H)
  have htheta :
      thetaStar (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ)) ‖∇ f (x : H) - ∇ f y‖ =
        ((((1 / (2 * (β : ℝ))) * ‖∇ f (x : H) - ∇ f y‖ ^ (2 : ℕ) : ℝ) : EReal)) :=
    quadraticThetaStar_asEReal_eq_of_nonneg β (norm_nonneg _)
  have hpair' :
      (((1 / (β : ℝ)) * ‖∇ f (x : H) - ∇ f y‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        (⟪(x : H) - y, ∇ f (x : H) - ∇ f y⟫_ℝ : EReal) := by
    calc
      (((1 / (β : ℝ)) * ‖∇ f (x : H) - ∇ f y‖ ^ (2 : ℕ) : ℝ) : EReal) =
          (2 : EReal) *
            thetaStar (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ)) ‖∇ f (x : H) - ∇ f y‖ := by
              rw [htheta]
              have hreal :
                  (1 / (β : ℝ)) * ‖∇ f (x : H) - ∇ f y‖ ^ (2 : ℕ) =
                    2 * ((1 / (2 * (β : ℝ))) * ‖∇ f (x : H) - ∇ f y‖ ^ (2 : ℕ)) := by
                field_simp [show (β : ℝ) ≠ 0 from ne_of_gt β.2]
              calc
                (((1 / (β : ℝ)) * ‖∇ f (x : H) - ∇ f y‖ ^ (2 : ℕ) : ℝ) : EReal) =
                    (((2 * ((1 / (2 * (β : ℝ))) *
                        ‖∇ f (x : H) - ∇ f y‖ ^ (2 : ℕ) : ℝ)) : EReal)) := by
                          exact congrArg (fun z : ℝ ↦ (z : EReal)) hreal
                _ =
                    (2 : EReal) *
                      ((((1 / (2 * (β : ℝ))) *
                          ‖∇ f (x : H) - ∇ f y‖ ^ (2 : ℕ) : ℝ) : EReal)) := by
                            rw [EReal.coe_mul]
      _ ≤ (⟪(x : H) - y, ∇ f (x : H) - ∇ f y⟫_ℝ : EReal) := by
            simpa using hpair
  exact_mod_cast hpair'

/-- Helper for Corollary 28.9: minimizing `f + g` is exactly the primal inclusion
`0 ∈ ∂ f x + {∇ g x}`. -/
theorem argmin_eq_primalForwardBackwardSolutionSet
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hconv : _root_.ConvexOn ℝ Set.univ g) (hdiff : Differentiable ℝ g) :
    Argmin (f + g.toEReal).asEReal =
      primal_inclusion_solution_set (∂ f) ((∇ g).toSetValuedOperator) := by
  have hg : g.toEReal ∈ Γ₀(H) :=
    real_toEReal_mem_gammaZero_of_continuous_convexOn_univ g hdiff.continuous hconv
  have hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g.toEReal) := by
    have hdom : effectiveDomain g.toEReal = (Set.univ : Set H) := by
      ext x
      simp [Function.effectiveDomain_toEReal]
    rw [hdom]
    have hsub : (effectiveDomain f - (Set.univ : Set H)) = Set.univ := by
      ext x
      constructor
      · intro hx
        simp
      · intro hx
        rcases hf.2.nonempty with ⟨y, hy⟩
        exact Set.mem_sub.mpr ⟨y, hy, y - x, by simp, by abel_nf⟩
    rw [hsub, Set.mem_strongRelativeInterior_iff]
    refine ⟨by simp, ?_⟩
    ext y
    constructor
    · intro hy
      simp
    · intro hy
      rw [Set.cone_def]
      exact ConvexCone.subset_hull (by simp)
  have hsub_sum :
      (∂ (f + g.toEReal) : SetValuedOperator H H) = (∂ f) + (∂ g.toEReal) :=
    subdifferential_add_eq_add_of_zero_mem_sri_sub_effectiveDomain hf hg hsri
  ext x
  have hargmin :
      x ∈ Argmin (f + g.toEReal).asEReal ↔
        x ∈ (∂ (f + g.toEReal) : SetValuedOperator H H).zeros := by
    -- The minimizers of a `Γ₀(H)` function are exactly the zeros of its subdifferential.
    simpa using
      congrArg (fun S : Set H ↦ x ∈ S) (argmin_eq_zeros_subdifferential (f := f + g.toEReal))
  have hsub :
      (∂ g.toEReal) x = ({∇ g x} : Set H) := by
    have hx : x ∈ interior (effectiveDomain g.toEReal) := by
      simp [Function.effectiveDomain_toEReal]
    have hgateaux :
        HasGateauxDerivativeAt
          (fun z ↦ (g.toEReal z : EReal).toReal)
          (InnerProductSpace.toDualMap ℝ H (∇ g x)) x := by
      -- The Fréchet gradient of `g` is the required Gâteaux derivative of `g.toEReal`.
      simpa [Function.toEReal_apply, InnerProductSpace.toDual_apply_eq_toDualMap_apply] using
        (((hdiff x).hasGradientAt).hasFDerivAt.hasGateauxDerivativeAt)
    -- The smooth summand has singleton subdifferential given by its gradient.
    exact
      subdifferential_eq_singleton_of_hasGateauxDerivativeAt_of_mem_interior_effectiveDomain
        hg hx hgateaux
  calc
    x ∈ Argmin (f + g.toEReal).asEReal ↔ x ∈ (∂ (f + g.toEReal) : SetValuedOperator H H).zeros :=
      hargmin
    _ ↔ x ∈ ((∂ f) + (∂ g.toEReal)).zeros := by rw [hsub_sum]
    _ ↔ (0 : H) ∈ (∂ f) x + (∂ g.toEReal) x := Iff.rfl
    _ ↔ (0 : H) ∈ (∂ f) x + ((∇ g).toSetValuedOperator x) := by
          simp [Function.toSetValuedOperator_apply, hsub]
    _ ↔ x ∈ primal_inclusion_solution_set (∂ f) ((∇ g).toSetValuedOperator) := Iff.rfl

/-- Helper for Corollary 28.9: uniform convexity of `g` on `S` yields uniform monotonicity of the
singleton-valued gradient operator on `S`. -/
theorem gradient_isUniformlyMonotoneOn_of_uniformlyConvexOn
    (g : H → ℝ) (hconv : _root_.ConvexOn ℝ Set.univ g) (hdiff : Differentiable ℝ g)
    {S : Set H} {φ : NNReal → EReal} (huniform : UniformlyConvexOn g.toEReal S φ) :
    ((∇ g).toSetValuedOperator).IsUniformlyMonotoneOn S := by
  have hg : g.toEReal ∈ Γ₀(H) :=
    real_toEReal_mem_gammaZero_of_continuous_convexOn_univ g hdiff.continuous hconv
  have hconv_toEReal : ConvexOn g.toEReal (effectiveDomain g.toEReal) :=
    (mem_gammaZero_iff.mp hg).2
  have hEq : (∂ g.toEReal) = ((∇ g).toSetValuedOperator) := by
    funext x
    ext u
    have hsub :
        (∂ g.toEReal) x = ({∇ g x} : Set H) := by
      have hx : x ∈ interior (effectiveDomain g.toEReal) := by
        simp [Function.effectiveDomain_toEReal]
      have hgateaux :
          HasGateauxDerivativeAt
            (fun z ↦ (g.toEReal z : EReal).toReal)
            (InnerProductSpace.toDualMap ℝ H (∇ g x)) x := by
        simpa [Function.toEReal_apply, InnerProductSpace.toDual_apply_eq_toDualMap_apply] using
          (((hdiff x).hasGradientAt).hasFDerivAt.hasGateauxDerivativeAt)
      exact
        subdifferential_eq_singleton_of_hasGateauxDerivativeAt_of_mem_interior_effectiveDomain
          hg hx hgateaux
    rw [hsub, Function.toSetValuedOperator_apply, Set.mem_singleton_iff]
  have hS_sub : S ⊆ (∂ g.toEReal).dom := by
    intro x hx
    rw [hEq]
    exact (SetValuedOperator.mem_dom_iff ((∇ g).toSetValuedOperator) x).2
      ⟨∇ g x, by simp [Function.toSetValuedOperator_apply]⟩
  -- Apply Example 22.5 to `g.toEReal`, then rewrite its graph back to the singleton gradient map.
  simpa [hEq] using
    (subdifferential_isUniformlyMonotoneOn_of_convexOn_of_uniformlyConvexOn
      g.toEReal hconv_toEReal hS_sub huniform)

/-- Corollary 28.9 (1): let `f ∈ Γ₀(H)`, let `β ∈ ℝ_{++}`, and let `g : H → ℝ` be convex and
differentiable with `1 / β`-Lipschitz gradient. Let `γ ∈ ]0, 2β[`, let `(λ_n)` lie in
`[0, 2 - γ / (2β)]` with `∑ λ_n (2 - γ / (2β) - λ_n) = +∞`, and let `x, y` satisfy the
forward-backward recursion `(28.33)` from `x0`. If `Argmin (f + g).asEReal` is nonempty, then
`(x_n)` converges weakly to a point of `Argmin (f + g).asEReal`. -/
theorem forwardBackwardAlgorithm_exists_weakLimit_mem_argmin
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hconv : _root_.ConvexOn ℝ Set.univ g) (hdiff : Differentiable ℝ g)
    (β γ : PosReal)
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) (∇ g))
    (hγ : (γ : ℝ) < 2 * (β : ℝ)) (lam : ℕ → ℝ)
    (hlam : ∀ n : ℕ, lam n ∈ Set.Icc (0 : ℝ) (2 - (γ : ℝ) / (2 * (β : ℝ))))
    (hdiv :
      Tendsto
        (fun N : ℕ ↦
          (Finset.range N).sum
            (fun n : ℕ ↦ lam n * ((2 - (γ : ℝ) / (2 * (β : ℝ))) - lam n)))
        atTop atTop)
    (hargmin : (Argmin (f + g.toEReal).asEReal).Nonempty) (x0 : H) {x y : ℕ → H}
    (hOrbit : IsRelaxedForwardBackwardProximalGradientOrbit hf g γ lam x0 x y) :
    ∃ z ∈ Argmin (f + g.toEReal).asEReal,
      Tendsto (fun n : ℕ ↦ toWeakSpace ℝ H (x n)) atTop (𝓝 (toWeakSpace ℝ H z)) := by
  let βInv : Set.Ioi (0 : ℝ) := ⟨(β : ℝ)⁻¹, inv_pos.mpr β.2⟩
  let hSub : Maximal IsMonotone (∂ f) :=
    subdifferential_isMaximallyMonotone_of_mem_gammaZero hf
  have hCoco :
      CocoerciveOn (β : ℝ) (Set.univ : Set H) (fun x : Set.univ ↦ ∇ g x) := by
    -- Corollary 18.17 upgrades the Lipschitz gradient bound to cocoercivity.
    simpa [βInv, one_div, inv_inv] using
      gradient_lipschitz_imp_cocoercive_of_differentiable_convex
        g hdiff hconv βInv hgrad_lipschitz
  have hzero :
      (primal_inclusion_solution_set (∂ f) ((∇ g).toSetValuedOperator)).Nonempty := by
    -- Rewrite the nonempty minimizer set as the Chapter 26 primal solution set.
    simpa [argmin_eq_primalForwardBackwardSolutionSet (hf := hf) (g := g) hconv hdiff] using
      hargmin
  -- Normalize the source recursion and apply Theorem 26.14 to `A = ∂ f` and `B = ∇ g`.
  simpa [argmin_eq_primalForwardBackwardSolutionSet (hf := hf) (g := g) hconv hdiff,
    hOrbit.x_eq_forwardBackwardIteration, SetValuedOperator.forwardBackwardRelaxationBound] using
    (SetValuedOperator.forwardBackwardAlgorithm_tendsto_weakly_to_zeroSet
      (∂ f) hSub (∇ g) β γ hCoco hγ lam
      (by
        simpa [SetValuedOperator.forwardBackwardRelaxationBound] using hlam)
      (by
        simpa [SetValuedOperator.forwardBackwardRelaxationBound] using hdiv)
      hzero x0)

/-- Any two minimizers of `f + g` have the same gradient under the Corollary 28.9 assumptions, so
the dual limit in clause `(2)` is independent of the chosen primal minimizer. -/
theorem forwardBackwardAlgorithm_gradient_eq_of_mem_argmin
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hconv : _root_.ConvexOn ℝ Set.univ g) (hdiff : Differentiable ℝ g)
    (β : PosReal)
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) (∇ g))
    {x z : H} (hx : x ∈ Argmin (f + g.toEReal).asEReal)
    (hz : z ∈ Argmin (f + g.toEReal).asEReal) :
    ∇ g x = ∇ g z := by
  let βInv : Set.Ioi (0 : ℝ) := ⟨(β : ℝ)⁻¹, inv_pos.mpr β.2⟩
  let hSub : Maximal IsMonotone (∂ f) :=
    subdifferential_isMaximallyMonotone_of_mem_gammaZero hf
  have hCoco :
      CocoerciveOn (β : ℝ) (Set.univ : Set H) (fun x : Set.univ ↦ ∇ g x) := by
    -- Route correction: uniqueness of the dual value needs the corollary's cocoercivity data.
    simpa [βInv, one_div, inv_inv] using
      gradient_lipschitz_imp_cocoercive_of_differentiable_convex
        g hdiff hconv βInv hgrad_lipschitz
  have hx' :
      x ∈ primal_inclusion_solution_set (∂ f) ((∇ g).toSetValuedOperator) := by
    simpa [argmin_eq_primalForwardBackwardSolutionSet (hf := hf) (g := g) hconv hdiff] using hx
  have hz' :
      z ∈ primal_inclusion_solution_set (∂ f) ((∇ g).toSetValuedOperator) := by
    simpa [argmin_eq_primalForwardBackwardSolutionSet (hf := hf) (g := g) hconv hdiff] using hz
  -- The Chapter 26 dual solution is unique on the primal solution set.
  simpa using
    (SetValuedOperator.eq_dualValue_of_mem_primalSolutions
      (∂ f) hSub (∇ g) β hCoco hx' hz')

/-- Corollary 28.9 (2): under the hypotheses of Corollary 28.9, if `x` minimizes `f + g`, then
`(∇ g(x_n))` converges strongly to `∇ g(x)`. This is the unique dual solution singled out by the
companion theorem `forwardBackwardAlgorithm_gradient_eq_of_mem_argmin`. -/
theorem forwardBackwardAlgorithm_gradient_tendsto_of_mem_argmin
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hconv : _root_.ConvexOn ℝ Set.univ g) (hdiff : Differentiable ℝ g)
    (β γ : PosReal)
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) (∇ g))
    (hγ : (γ : ℝ) < 2 * (β : ℝ)) (lam : ℕ → ℝ)
    (hlam : ∀ n : ℕ, lam n ∈ Set.Icc (0 : ℝ) (2 - (γ : ℝ) / (2 * (β : ℝ))))
    (hdiv :
      Tendsto
        (fun N : ℕ ↦
          (Finset.range N).sum
            (fun n : ℕ ↦ lam n * ((2 - (γ : ℝ) / (2 * (β : ℝ))) - lam n)))
        atTop atTop)
    (x0 : H) {xSeq y : ℕ → H}
    (hOrbit : IsRelaxedForwardBackwardProximalGradientOrbit hf g γ lam x0 xSeq y)
    {x : H} (hx : x ∈ Argmin (f + g.toEReal).asEReal) :
    Tendsto (fun n : ℕ ↦ ∇ g (xSeq n)) atTop (𝓝 (∇ g x)) := by
  let βInv : Set.Ioi (0 : ℝ) := ⟨(β : ℝ)⁻¹, inv_pos.mpr β.2⟩
  let hSub : Maximal IsMonotone (∂ f) :=
    subdifferential_isMaximallyMonotone_of_mem_gammaZero hf
  have hCoco :
      CocoerciveOn (β : ℝ) (Set.univ : Set H) (fun x : Set.univ ↦ ∇ g x) := by
    -- Corollary 18.17 supplies the cocoercive operator needed by Chapter 26.
    simpa [βInv, one_div, inv_inv] using
      gradient_lipschitz_imp_cocoercive_of_differentiable_convex
        g hdiff hconv βInv hgrad_lipschitz
  have hx' :
      x ∈ primal_inclusion_solution_set (∂ f) ((∇ g).toSetValuedOperator) := by
    simpa [argmin_eq_primalForwardBackwardSolutionSet (hf := hf) (g := g) hconv hdiff] using hx
  -- Clause `(2)` of Theorem 26.14 applies after normalizing the explicit recursion.
  simpa [hOrbit.x_eq_forwardBackwardIteration,
    SetValuedOperator.forwardBackwardRelaxationBound] using
    (SetValuedOperator.forwardBackwardAlgorithm_B_tendsto_to_unique_dual_solution
      (∂ f) hSub (∇ g) β γ hCoco hγ lam
      (by
        simpa [SetValuedOperator.forwardBackwardRelaxationBound] using hlam)
      (by
        simpa [SetValuedOperator.forwardBackwardRelaxationBound] using hdiv)
      x0 hx').1

/-- Corollary 28.9 (3): under the hypotheses of Corollary 28.9, suppose that either `f` is
uniformly convex on every nonempty bounded subset of `(∂ f).dom` or `g` is uniformly convex on
every nonempty bounded subset of `H`. Then `(x_n)` converges strongly to the unique minimizer of
`f + g`. -/
theorem forwardBackwardAlgorithm_exists_strongLimit_of_uniformlyConvexOnEveryBoundedSubset
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hconv : _root_.ConvexOn ℝ Set.univ g) (hdiff : Differentiable ℝ g)
    (β γ : PosReal)
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) (∇ g))
    (hγ : (γ : ℝ) < 2 * (β : ℝ)) (lam : ℕ → ℝ)
    (hlam : ∀ n : ℕ, lam n ∈ Set.Icc (0 : ℝ) (2 - (γ : ℝ) / (2 * (β : ℝ))))
    (hdiv :
      Tendsto
        (fun N : ℕ ↦
          (Finset.range N).sum
            (fun n : ℕ ↦ lam n * ((2 - (γ : ℝ) / (2 * (β : ℝ))) - lam n)))
        atTop atTop)
    (hargmin : (Argmin (f + g.toEReal).asEReal).Nonempty)
    (hUniform :
      (∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ (∂ f).dom →
          ∃ φ : NNReal → EReal, UniformlyConvexOn f S φ) ∨
        ∀ S : Set H,
          S.Nonempty → Bornology.IsBounded S →
            ∃ φ : NNReal → EReal, UniformlyConvexOn g.toEReal S φ)
    (x0 : H) {x y : ℕ → H}
    (hOrbit : IsRelaxedForwardBackwardProximalGradientOrbit hf g γ lam x0 x y) :
    ∃ z ∈ Argmin (f + g.toEReal).asEReal,
      Tendsto x atTop (𝓝 z) ∧
        Argmin (f + g.toEReal).asEReal = ({z} : Set H) := by
  let βInv : Set.Ioi (0 : ℝ) := ⟨(β : ℝ)⁻¹, inv_pos.mpr β.2⟩
  let hSub : Maximal IsMonotone (∂ f) :=
    subdifferential_isMaximallyMonotone_of_mem_gammaZero hf
  have hCoco :
      CocoerciveOn (β : ℝ) (Set.univ : Set H) (fun x : Set.univ ↦ ∇ g x) := by
    -- Corollary 18.17 packages the smooth term into the Chapter 26 cocoercive operator.
    simpa [βInv, one_div, inv_inv] using
      gradient_lipschitz_imp_cocoercive_of_differentiable_convex
        g hdiff hconv βInv hgrad_lipschitz
  have hzero :
      (primal_inclusion_solution_set (∂ f) ((∇ g).toSetValuedOperator)).Nonempty := by
    -- The minimizer set is the primal solution set for the inclusion `0 ∈ ∂ f x + ∇ g x`.
    simpa [argmin_eq_primalForwardBackwardSolutionSet (hf := hf) (g := g) hconv hdiff] using
      hargmin
  have hUniform' :
      (∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ (∂ f).dom →
          (∂ f).IsUniformlyMonotoneOn S) ∨
        ∀ S : Set H,
          S.Nonempty → Bornology.IsBounded S →
            ((∇ g).toSetValuedOperator).IsUniformlyMonotoneOn S := by
    cases hUniform with
    | inl hUniformF =>
        left
        intro S hS_nonempty hS_bounded hS_sub
        rcases hUniformF S hS_nonempty hS_bounded hS_sub with ⟨φ, hφ⟩
        -- Example 22.5 turns source uniform convexity of `f`
        -- into uniform monotonicity of `∂ f`.
        exact
          subdifferential_isUniformlyMonotoneOn_of_convexOn_of_uniformlyConvexOn
            f (mem_gammaZero_iff.mp hf).2 hS_sub hφ
    | inr hUniformG =>
        right
        intro S hS_nonempty hS_bounded
        rcases hUniformG S hS_nonempty hS_bounded with ⟨φ, hφ⟩
        -- The smooth branch is handled by rewriting `∂ g` to the singleton gradient operator.
        exact gradient_isUniformlyMonotoneOn_of_uniformlyConvexOn g hconv hdiff hφ
  have hStrongConv :
      ∃ z ∈ primal_inclusion_solution_set (∂ f) ((∇ g).toSetValuedOperator),
        Tendsto (forwardBackwardIteration (∂ f) hSub (∇ g) γ lam x0) atTop (𝓝 z) ∧
          primal_inclusion_solution_set (∂ f) ((∇ g).toSetValuedOperator) = ({z} : Set H) := by
    exact
      forwardBackwardAlgorithm_tendsto_to_unique_zero_of_uniformlyMonotoneOnEveryBoundedSubset
        (∂ f) hSub (∇ g) β γ hCoco hγ lam
        (by
          simpa [SetValuedOperator.forwardBackwardRelaxationBound] using hlam)
        (by
          simpa [SetValuedOperator.forwardBackwardRelaxationBound] using hdiv)
        hzero hUniform' x0
  -- Apply the strong-convergence upgrade from Theorem 26.14 and translate back to `Argmin`.
  simpa [argmin_eq_primalForwardBackwardSolutionSet (hf := hf) (g := g) hconv hdiff,
    hOrbit.x_eq_forwardBackwardIteration] using hStrongConv

end ForwardBackwardAlgorithm

end ERealFunction
