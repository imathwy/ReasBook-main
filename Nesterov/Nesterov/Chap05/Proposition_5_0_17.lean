import Mathlib
import Nesterov.Chap05.Definition_5_0_21
import Nesterov.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm SelfConcordantAuxiliaryFunction

noncomputable section

universe u

/- Proposition 5.0.17 lies in the Chapter 5 lower-remainder / self-concordance domain.

Sampled owner declarations in this domain:
* `thirdDirectionalDerivative` and `directionalSlice` from `Definition_5_0_10`, the chapter
  source-facing cubic-directional owner and its affine-line restriction;
* mathlib `iteratedDerivWithin`, the canonical one-variable owner for the auxiliary one-sided
  reverse-slice derivative on `Set.Ici (0 : ℝ)`;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` from `Definition_5_1_1`, the chapter owner
  for the local Hessian norm;
* `taylor_lower_bound_of_hessian_loewner_lower` from `Theorem_5_1_8`, the nearby owner-level
  lower-remainder theorem already stated on genuine interior data.

Source/core/bridge triage:
* source-facing: the cubic bound on `thirdDirectionalDerivative f x u` at points `x ∈ dom`;
* core/canonical: the chapter owners `thirdDirectionalDerivative f x u` and `‖u‖[f; x]`;
* bridge/view: the one-sided reverse-slice derivative
  `iteratedDerivWithin 3 (directionalSlice f x (-u)) (Set.Ici (0 : ℝ)) 0`.

Primitive data:
* an open domain `dom` and a `C³` function on `dom`;
* a positive self-concordance parameter `Mf`;
* the global lower remainder inequality with the source-facing `ω` term.

Derived API:
* the auxiliary one-sided reverse-slice cubic bound along a reverse ray inside `dom`;
* the source-facing cubic estimate for `thirdDirectionalDerivative`;
* its absolute-value companion and the resulting owner-level bridge to
  `IsSelfConcordantOnWith`.

The public proposition must therefore live on `thirdDirectionalDerivative`, with the reverse-slice
within-derivative kept only as a private bridge used to encode the one-sided proof route. The
parameter must also be positive: when `Mf = 0`, the nearby Chapter 5 remainder API switches to
the quadratic remainder `r² / 2`, so the cubic conclusion below is false. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Auxiliary bridge: the one-sided third derivative at the origin of the reverse directional slice
`α ↦ f (x - α • u)` agrees with the negative of `thirdDirectionalDerivative f x u` when `f` is
genuinely `C³` at `x`. -/
-- Proof sketch: apply the one-variable chain rule three times to the map
-- `α ↦ f (x - α • u)`. Each differentiation contributes a factor `-1`, so the third derivative
-- picks up the sign `(-1)^3 = -1`, and `iteratedDerivWithin` on `Set.Ici (0 : ℝ)` agrees with the
-- unrestricted derivative at `0` because `f` is `C³` there.
private theorem reverse_directionalSlice_thirdDerivWithin_eq_neg
    {f : E → ℝ} {x u : E} (hf : ContDiffAt ℝ 3 f x) :
    iteratedDerivWithin 3 (directionalSlice f x (-u)) (Set.Ici (0 : ℝ)) 0 =
      -thirdDirectionalDerivative f x u := sorry

/- Private reverse-slice bound used to prove Proposition 5.0.17: if the lower Taylor remainder
bound holds at the base point `x`, with positive parameter `M_f`, and the reverse ray from `x` in
direction `u` stays in `dom` near `0`, then the negative one-sided third derivative of
`α ↦ f (x - α • u)` at `0` is bounded above by `2 M_f ‖u‖_x^3`. -/
private theorem reverse_directionalSlice_thirdDerivWithin_bound_of_remainder_lower_bound
    {dom : Set E} {Mf : NNReal} {f : E → ℝ} {x u : E}
    (hf : ContDiffAt ℝ 3 f x)
    (hMf : 0 < Mf)
    (hremainder :
      ∀ ⦃y : E⦄, y ∈ dom →
        (1 / (Mf : ℝ) ^ (2 : ℕ)) *
            ω (selfConcordantOmegaArg Mf ‖y - x‖[f; x]
              (neg_one_lt_mf_mul_of_nonneg
                (hessianLocalNorm_nonneg f x (y - x)))) ≤
          f y - f x - inner ℝ (∇ f x) (y - x))
    (hline : ∃ ε > 0, Set.Icc (0 : ℝ) ε ⊆ (fun α : ℝ ↦ x - α • u) ⁻¹' dom) :
    -iteratedDerivWithin 3 (directionalSlice f x (-u)) (Set.Ici (0 : ℝ)) 0 ≤
      2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) := sorry

-- Proof sketch: openness of `dom` upgrades `ContDiffOn ℝ 3 f dom` to `ContDiffAt ℝ 3 f x`,
-- and provides a small two-sided ball around `x` inside `dom`; restricting that ball to the
-- reverse ray gives the private reverse-slice bound above. Rewriting the resulting one-sided
-- derivative by `reverse_directionalSlice_thirdDerivWithin_eq_neg` recovers the source-facing
-- cubic estimate on `thirdDirectionalDerivative f x u`.
/-- Proposition 5.0.17: if the global lower Taylor remainder bound from
`Theorem_5_1_8.taylor_lower_bound_of_hessian_loewner_lower` holds on an open domain `dom` for a
`C³` function `f`, with positive parameter `M_f`, then at every point `x ∈ dom` the chapter owner
`thirdDirectionalDerivative f x u` is bounded above by
`2 M_f ‖u‖_x^3`. -/
theorem thirdDirectionalDerivative_le_of_global_remainder_lower_bound
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hopen : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (hMf : 0 < Mf)
    (hremainder :
      ∀ ⦃x y : E⦄ (_ : x ∈ dom) (_ : y ∈ dom),
        (1 / (Mf : ℝ) ^ (2 : ℕ)) *
            ω (selfConcordantOmegaArg Mf ‖y - x‖[f; x]
              (neg_one_lt_mf_mul_of_nonneg
                (hessianLocalNorm_nonneg f x (y - x)))) ≤
          f y - f x - inner ℝ (∇ f x) (y - x))
    (x u : E) (hx : x ∈ dom) :
    thirdDirectionalDerivative f x u ≤
      2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) := sorry

/-- Under the same hypotheses as Proposition 5.0.17, the third directional derivative is bounded
in absolute value by `2 M_f ‖u‖_x^3`. This is the exact cubic field used by the chapter owner
`IsSelfConcordantOnWith`. -/
theorem thirdDirectionalDerivative_abs_le_of_global_remainder_lower_bound
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hopen : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (hMf : 0 < Mf)
    (hremainder :
      ∀ ⦃x y : E⦄ (_ : x ∈ dom) (_ : y ∈ dom),
        (1 / (Mf : ℝ) ^ (2 : ℕ)) *
            ω (selfConcordantOmegaArg Mf ‖y - x‖[f; x]
              (neg_one_lt_mf_mul_of_nonneg
                (hessianLocalNorm_nonneg f x (y - x)))) ≤
          f y - f x - inner ℝ (∇ f x) (y - x))
    (x u : E) (hx : x ∈ dom) :
    |thirdDirectionalDerivative f x u| ≤
      2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) := by
  have hupper :
      thirdDirectionalDerivative f x u ≤
        2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) :=
    thirdDirectionalDerivative_le_of_global_remainder_lower_bound
      hopen hcont hMf hremainder x u hx
  have hneg :
      -thirdDirectionalDerivative f x u ≤
        2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) := by
    simpa using
      (thirdDirectionalDerivative_le_of_global_remainder_lower_bound
        hopen hcont hMf hremainder x (-u) hx)
  rw [abs_le]
  constructor
  · linarith
  · exact hupper

namespace IsSelfConcordantOnWith

/-- If the global lower Taylor remainder bound from
`Theorem_5_1_8.taylor_lower_bound_of_hessian_loewner_lower` holds on an open domain with convex
underlying set for a `C³` function with positive parameter `M_f`, then the function is
self-concordant on that domain with constant `M_f`. This is the canonical owner-level bridge from
Proposition 5.0.17 to `IsSelfConcordantOnWith`. -/
theorem of_global_remainder_lower_bound
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hopen : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (hdom : Convex ℝ dom)
    (hMf : 0 < Mf)
    (hremainder :
      ∀ ⦃x y : E⦄ (_ : x ∈ dom) (_ : y ∈ dom),
        (1 / (Mf : ℝ) ^ (2 : ℕ)) *
            ω (selfConcordantOmegaArg Mf ‖y - x‖[f; x]
              (neg_one_lt_mf_mul_of_nonneg
                (hessianLocalNorm_nonneg f x (y - x)))) ≤
          f y - f x - inner ℝ (∇ f x) (y - x)) :
    IsSelfConcordantOnWith dom Mf f where
  isOpen_domain := hopen
  contDiffOn := hcont
  convexOn := by
    have hcont₁ : ContDiffOn ℝ 1 f dom := hcont.of_le (by norm_num)
    refine (convexOn_iff_lower_tangent_plane_of_contDiffOn hdom hcont₁).2 ?_
    intro x hx y hy
    have hMf' : 0 < (Mf : ℝ) := by
      exact_mod_cast hMf
    have hgrad :
        gradientWithin f dom x = ∇ f x := by
      rw [gradientWithin, gradient]
      congr
      exact fderivWithin_eq_fderiv (hopen.uniqueDiffWithinAt hx)
        ((hcont₁.contDiffAt (hopen.mem_nhds hx)).differentiableAt_one)
    have homega_nonneg :
        0 ≤ ω (selfConcordantOmegaArg Mf ‖y - x‖[f; x]
          (neg_one_lt_mf_mul_of_nonneg
            (hessianLocalNorm_nonneg f x (y - x)))) := by
      rw [selfConcordantOmega_apply, coe_selfConcordantOmegaArg]
      have harg_nonneg : 0 ≤ (Mf : ℝ) * ‖y - x‖[f; x] := by
        exact mul_nonneg hMf'.le (hessianLocalNorm_nonneg f x (y - x))
      have hlog :
          Real.log (1 + (Mf : ℝ) * ‖y - x‖[f; x]) ≤
            (Mf : ℝ) * ‖y - x‖[f; x] := by
        have hpos : 0 < 1 + (Mf : ℝ) * ‖y - x‖[f; x] := by positivity
        simpa using Real.log_le_sub_one_of_pos hpos
      linarith
    have hgap_nonneg :
        0 ≤ f y - f x - inner ℝ (∇ f x) (y - x) := by
      have hcoeff_nonneg : 0 ≤ 1 / (Mf : ℝ) ^ (2 : ℕ) := by positivity
      exact le_trans (mul_nonneg hcoeff_nonneg homega_nonneg) (hremainder hx hy)
    have hlower :
        f y ≥ f x + inner ℝ (∇ f x) (y - x) := by
      linarith
    simpa [hgrad] using hlower
  third_deriv_bound := fun {x} hx u ↦
    thirdDirectionalDerivative_abs_le_of_global_remainder_lower_bound
      hopen hcont hMf hremainder x u hx

end IsSelfConcordantOnWith

end
