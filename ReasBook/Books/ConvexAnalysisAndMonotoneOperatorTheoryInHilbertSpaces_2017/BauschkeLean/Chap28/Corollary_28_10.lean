import BauschkeLean.Chap28.Corollary_28_9
import BauschkeLean.Chap12.Example_12_25

open Filter
open InnerProductSpace
open scoped Gradient InnerProductSpace Topology

universe u

namespace ERealFunction

/- Source/core/bridge triage:
- `source-facing`: Corollary 28.10 is the projected-gradient recursion `(28.34)` together with its
  weak-convergence, gradient-limit, and strong-convergence consequences on a nonempty closed convex
  constraint set `C`.
- `core/canonical`: the reusable Chapter 28 owner is Corollary 28.9's relaxed forward-backward
  orbit for the nonsmooth term `ι[C]` and the smooth term `f`.
- `bridge/view`: the source recursion keeps the metric projection `P[C, hC]` explicit, while the
  shared Chapter 28 indicator-optimization bridge API identifies it with the canonical
  forward-backward orbit when `γ > 0` and rewrites the constrained minimizer set
  `Argmin[C] f.toEReal.asEReal` to the feasible global minimizer set of
  `(ι[C] + f.toEReal).asEReal`.

Semantic recall: the source step-size regime `γ ∈ [0, 2β[` is kept literally as the pair of
assumptions `0 ≤ γ` and `γ < 2β` in the recursion owner, while the convergence statements use the
repository's canonical positive-step surface `γ : PosReal` because their Chapter 28 bridge runs
through Corollary 28.9. -/

section ProjectionGradientAlgorithm

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A sequence `x` satisfies the projection-gradient recursion `(28.34)` for the differentiable
convex objective `f`, the nonempty closed convex set `C`, step size `γ`, relaxation parameters
`lam`, and initial point `x0`. -/
structure IsProjectionGradientOrbit
    (f : H → ℝ) (C : Set H) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (γ : ℝ) (lam : ℕ → ℝ) (x0 : H) (x : ℕ → H) : Prop where
  /-- The orbit starts at the prescribed point `x0`. -/
  x_zero : x 0 = x0
  /-- The next iterate is the relaxed projection-gradient step from `(28.34)`. -/
  x_succ_eq : ∀ n : ℕ,
    x (n + 1) =
      x n +
        lam n •
          (P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex]
              (x n - γ • ∇ f (x n)) -
            x n)

/-- Helper for Corollary 28.10: the indicator of a nonempty closed convex set belongs to `Γ₀(H)`.
-/
theorem indicatorMemGammaZeroOfNonemptyIsClosedConvex
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    ι[C] ∈ Γ₀(H) := by
  have hindicator_lsc :
      LowerSemicontinuous (fun y ↦ ((ι[C]) y : EReal)) := by
    -- The closedness of `C` is exactly the lower-semicontinuity criterion for its indicator.
    simpa using (lowerSemicontinuous_indicator_compl_top_iff_isClosed C).2 hC_closed
  have hindicator_dom : effectiveDomain (ι[C]) = C := by
    -- The indicator is finite precisely on the constraint set.
    ext y
    by_cases hy : y ∈ C <;> simp [ERealFunction.effectiveDomain, ERealFunction.indicator, hy]
  refine ⟨hindicator_lsc, ?_⟩
  refine ⟨by simpa [hindicator_dom] using hC_nonempty, fun _ hy ↦ hy, ?_⟩
  intro y hy z hz a ha0 ha1
  have hyC : y ∈ C := by
    simpa [hindicator_dom] using hy
  have hzC : z ∈ C := by
    simpa [hindicator_dom] using hz
  have hayzC : a • y + (1 - a) • z ∈ C :=
    hC_convex hyC hzC ha0.le (sub_nonneg.mpr ha1.le) (by ring)
  -- On feasible points, the indicator takes the convexity-preserving value `0`.
  simp [ERealFunction.indicator, hyC, hzC, hayzC]

/-- Helper for Corollary 28.10: the scaled proximal operator of `ι[C]` is the metric projection
onto `C`. -/
theorem scaledIndicatorProx_eq_projectionPoint
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (γ : PosReal) :
    Prox[γ, ι[C],
      indicatorMemGammaZeroOfNonemptyIsClosedConvex hC_nonempty hC_closed hC_convex] =
        P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex] := by
  -- Rewrite the scaled indicator back to the unscaled indicator, then apply Example 12.25.
  have hsmul_indicator : γ • ι[C] = ι[C] := by
    funext z
    apply Subtype.ext
    by_cases hz : z ∈ C
    · simp [ERealFunction.indicator, hz]
    · simpa [ERealFunction.indicator, hz] using
        (EReal.coe_mul_top_of_pos γ.2 : ((γ : ℝ) : EReal) * ⊤ = ⊤)
  change
      Prox[γ • ι[C],
        smul_mem_gammaZero (ι[C])
          (indicatorMemGammaZeroOfNonemptyIsClosedConvex
            hC_nonempty hC_closed hC_convex)
          γ] =
      P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex]
  ext z
  -- The pointwise equality is exactly the unscaled indicator/projection bridge.
  simpa [hsmul_indicator] using
    congrArg (fun T : H → H ↦ T z) <|
      proximityOperator_indicator_eq_projectionPoint_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex

namespace IsProjectionGradientOrbit

variable {f : H → ℝ} {C : Set H}
variable {hC_nonempty : C.Nonempty} {hC_closed : IsClosed C} {hC_convex : Convex ℝ C}
variable {γ : ℝ} {lam : ℕ → ℝ} {x0 : H} {x : ℕ → H}

/-- Under the additional source-compatible assumption `γ > 0`, a projection-gradient orbit
`(28.34)` is the relaxed forward-backward orbit from Corollary 28.9 for the indicator `ι[C]` and
the smooth term `f`. -/
theorem toIsRelaxedForwardBackwardProximalGradientOrbit
    (hγ_pos : 0 < γ)
    (hOrbit : IsProjectionGradientOrbit f C hC_nonempty hC_closed hC_convex γ lam x0 x) :
    IsRelaxedForwardBackwardProximalGradientOrbit
      (indicatorMemGammaZeroOfNonemptyIsClosedConvex hC_nonempty hC_closed hC_convex)
      f
      ⟨γ, hγ_pos⟩
      lam
      x0
      x
      (fun n ↦ x n - γ • ∇ f (x n)) := by
  refine ⟨hOrbit.x_zero, ?_, ?_⟩
  · intro n
    rfl
  · intro n
    rw [hOrbit.x_succ_eq n]
    -- Route correction: rewrite the explicit projector step through the local scaled-indicator
    -- bridge so the orbit matches Corollary 28.9 verbatim.
    rw [← scaledIndicatorProx_eq_projectionPoint
      hC_nonempty hC_closed hC_convex ⟨γ, hγ_pos⟩]

end IsProjectionGradientOrbit

section Statements

variable {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
variable (hC_convex : Convex ℝ C)
variable (f : H → ℝ)
variable (β : Set.Ioi (0 : ℝ))
variable (γ : PosReal)
variable (lam : ℕ → ℝ)
variable (x0 : H)

/-- Helper for Corollary 28.10: constrained minimizers of `f` on `C` are exactly the feasible
global minimizers of `(ι[C] + f.toEReal).asEReal`. -/
theorem argminOn_toEReal_eq_inter_indicatorAugmentedArgmin :
    (Argmin[C] f.toEReal.asEReal : Set H) = C ∩ Argmin ((ι[C] + f.toEReal).asEReal) := by
  -- Normalize the constrained argmin set with the canonical indicator-augmentation theorem.
  simpa [Function.asEReal_apply, add_comm, add_left_comm, add_assoc] using
    (argminOn_eq_inter_argmin_add_indicator
      f.toEReal.asEReal
      C
      (fun x _ ↦ by
        simpa [Function.asEReal_apply] using
          (ne_of_gt (f.toEReal x).2 : ((f.toEReal x : EReal) ≠ ⊥))))

/-- Helper for Corollary 28.10: once the constrained argmin set is nonempty, every global
minimizer of `(ι[C] + f.toEReal).asEReal` automatically lies in `C`. -/
theorem mem_constraint_of_mem_indicatorAugmentedArgmin
    (hargmin : (Argmin[C] f.toEReal.asEReal : Set H).Nonempty)
    {x : H} (hx : x ∈ Argmin ((ι[C] + f.toEReal).asEReal)) :
    x ∈ C := by
  rcases hargmin with ⟨y, hy⟩
  have hy' : y ∈ C ∩ Argmin ((ι[C] + f.toEReal).asEReal) := by
    simpa [argminOn_toEReal_eq_inter_indicatorAugmentedArgmin (C := C) (f := f)] using hy
  have hyC : y ∈ C := hy'.1
  have hxmin : IsMinOn ((ι[C] + f.toEReal).asEReal) Set.univ x := (mem_argmin_iff).1 hx
  by_contra hxC
  have hxy :
      ((ι[C] + f.toEReal).asEReal) x ≤ ((ι[C] + f.toEReal).asEReal) y :=
    (isMinOn_univ_iff.mp hxmin) y
  have hy_lt_top : ((ι[C] + f.toEReal).asEReal) y < ⊤ := by
    -- A feasible constrained minimizer has finite augmented objective value.
    simpa [Function.asEReal_apply, Function.toEReal_apply, indicator_apply, hyC] using
      (EReal.coe_lt_top (f y))
  have hx_lt_top : ((ι[C] + f.toEReal).asEReal) x < ⊤ := lt_of_le_of_lt hxy hy_lt_top
  -- Outside `C`, the indicator term forces the augmented objective to be `⊤`.
  simpa [Function.asEReal_apply, Function.toEReal_apply, indicator_apply, hxC] using hx_lt_top

/-- Corollary 28.10 (1): let `C` be a nonempty closed convex subset of `H`, let
`β ∈ ℝ_{++}`, let `f : H → ℝ` be convex and differentiable with `1 / β`-Lipschitz gradient, let
`γ` be a positive step size with `γ < 2β`, let `(λ_n)` lie in `[0, 2 - γ / (2β)]` with
`∑ λ_n (2 - γ / (2β) - λ_n) = +∞`, and let `x` satisfy the projection-gradient recursion
`(28.34)` from `x0`. If `Argmin[C] f.toEReal.asEReal` is nonempty, then `(x_n)` converges weakly
to a point of `Argmin[C] f.toEReal.asEReal`. -/
theorem projectionGradient_exists_weakLimit_mem_argminOn
    (hconv : _root_.ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) (∇ f))
    (hγ_lt : (γ : ℝ) < 2 * (β : ℝ))
    (hlam : ∀ n : ℕ, lam n ∈ Set.Icc (0 : ℝ) (2 - (γ : ℝ) / (2 * (β : ℝ))))
    (hdiv :
      Tendsto
        (fun N : ℕ ↦
          (Finset.range N).sum
            (fun n : ℕ ↦ lam n * ((2 - (γ : ℝ) / (2 * (β : ℝ))) - lam n)))
        atTop atTop)
    (hargmin : (Argmin[C] f.toEReal.asEReal : Set H).Nonempty) {x : ℕ → H}
    (hOrbit : IsProjectionGradientOrbit f C hC_nonempty hC_closed hC_convex (γ : ℝ) lam x0 x) :
    ∃ p ∈ Argmin[C] f.toEReal.asEReal,
      Tendsto (fun n : ℕ ↦ toWeakSpace ℝ H (x n)) atTop (𝓝 (toWeakSpace ℝ H p)) := by
  let hindicator : ι[C] ∈ Γ₀(H) :=
    indicatorMemGammaZeroOfNonemptyIsClosedConvex hC_nonempty hC_closed hC_convex
  have hargmin_aug : (Argmin ((ι[C] + f.toEReal).asEReal)).Nonempty := by
    rcases hargmin with ⟨p, hp⟩
    have hp' : p ∈ C ∩ Argmin ((ι[C] + f.toEReal).asEReal) := by
      simpa [argminOn_toEReal_eq_inter_indicatorAugmentedArgmin (C := C) (f := f)] using hp
    exact ⟨p, hp'.2⟩
  have hOrbit' :
      IsRelaxedForwardBackwardProximalGradientOrbit hindicator f γ lam x0 x
        (fun n ↦ x n - (γ : ℝ) • ∇ f (x n)) :=
    hOrbit.toIsRelaxedForwardBackwardProximalGradientOrbit γ.2
  -- Apply Corollary 28.9 to the indicator-augmented objective.
  rcases
      forwardBackwardAlgorithm_exists_weakLimit_mem_argmin
        hindicator
        f
        hconv
        hdiff
        β
        γ
        hgrad_lipschitz
        hγ_lt
        lam
        hlam
        hdiv
        hargmin_aug
        x0
        hOrbit'
    with ⟨p, hp, hp_tendsto⟩
  have hpC : p ∈ C :=
    mem_constraint_of_mem_indicatorAugmentedArgmin (C := C) (f := f) hargmin hp
  have hp_on : p ∈ Argmin[C] f.toEReal.asEReal := by
    -- Rewrite the owner argmin point back to the constrained argmin set.
    simpa [argminOn_toEReal_eq_inter_indicatorAugmentedArgmin (C := C) (f := f), hpC] using
      (show p ∈ C ∩ Argmin ((ι[C] + f.toEReal).asEReal) from ⟨hpC, hp⟩)
  exact ⟨p, hp_on, hp_tendsto⟩

/-- Corollary 28.10 (2): under the hypotheses of Corollary 28.10, if
`x ∈ Argmin[C] f.toEReal.asEReal`, then `(∇ f (x_n))` converges strongly to `∇ f x`. -/
theorem projectionGradient_gradient_tendsto_of_mem_argminOn
    (hconv : _root_.ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) (∇ f))
    (hγ_lt : (γ : ℝ) < 2 * (β : ℝ))
    (hlam : ∀ n : ℕ, lam n ∈ Set.Icc (0 : ℝ) (2 - (γ : ℝ) / (2 * (β : ℝ))))
    (hdiv :
      Tendsto
        (fun N : ℕ ↦
          (Finset.range N).sum
            (fun n : ℕ ↦ lam n * ((2 - (γ : ℝ) / (2 * (β : ℝ))) - lam n)))
        atTop atTop)
    {xSeq : ℕ → H}
    (hOrbit : IsProjectionGradientOrbit f C hC_nonempty hC_closed hC_convex (γ : ℝ) lam x0 xSeq)
    {x : H} (hx : x ∈ Argmin[C] f.toEReal.asEReal) :
    Tendsto (fun n : ℕ ↦ ∇ f (xSeq n)) atTop (𝓝 (∇ f x)) := by
  let hindicator : ι[C] ∈ Γ₀(H) :=
    indicatorMemGammaZeroOfNonemptyIsClosedConvex hC_nonempty hC_closed hC_convex
  have hOrbit' :
      IsRelaxedForwardBackwardProximalGradientOrbit hindicator f γ lam x0 xSeq
        (fun n ↦ xSeq n - (γ : ℝ) • ∇ f (xSeq n)) :=
    hOrbit.toIsRelaxedForwardBackwardProximalGradientOrbit γ.2
  have hx' : x ∈ Argmin ((ι[C] + f.toEReal).asEReal) := by
    -- Normalize the constrained minimizer hypothesis to the owner argmin set.
    have hx'' : x ∈ C ∩ Argmin ((ι[C] + f.toEReal).asEReal) := by
      simpa [argminOn_toEReal_eq_inter_indicatorAugmentedArgmin (C := C) (f := f)] using hx
    exact hx''.2
  -- Clause `(ii)` is the gradient-limit companion of Corollary 28.9.
  simpa using
    forwardBackwardAlgorithm_gradient_tendsto_of_mem_argmin
      hindicator
      f
      hconv
      hdiff
      β
      γ
      hgrad_lipschitz
      hγ_lt
      lam
      hlam
      hdiv
      x0
      hOrbit'
      hx'

/-- Corollary 28.10 (3): under the hypotheses of Corollary 28.10, suppose that `f` is uniformly
convex on every nonempty bounded subset of `H`. Then `(x_n)` converges strongly to the unique
minimizer of `f` over `C`, expressed here by convergence to a point of
`Argmin[C] f.toEReal.asEReal` whose argmin set is a singleton. -/
theorem projectionGradient_tendsto_to_unique_argminOn_of_uniformlyConvexOnEveryBoundedSubset
    (hconv : _root_.ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) (∇ f))
    (hγ_lt : (γ : ℝ) < 2 * (β : ℝ))
    (hlam : ∀ n : ℕ, lam n ∈ Set.Icc (0 : ℝ) (2 - (γ : ℝ) / (2 * (β : ℝ))))
    (hdiv :
      Tendsto
        (fun N : ℕ ↦
          (Finset.range N).sum
            (fun n : ℕ ↦ lam n * ((2 - (γ : ℝ) / (2 * (β : ℝ))) - lam n)))
        atTop atTop)
    (hargmin : (Argmin[C] f.toEReal.asEReal : Set H).Nonempty)
    (hUniform :
      ∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S →
          ∃ φ : NNReal → EReal, UniformlyConvexOn f.toEReal S φ)
    {x : ℕ → H}
    (hOrbit : IsProjectionGradientOrbit f C hC_nonempty hC_closed hC_convex (γ : ℝ) lam x0 x) :
    ∃ p ∈ Argmin[C] f.toEReal.asEReal,
      Tendsto x atTop (𝓝 p) ∧
        Argmin[C] f.toEReal.asEReal = ({p} : Set H) := by
  let hindicator : ι[C] ∈ Γ₀(H) :=
    indicatorMemGammaZeroOfNonemptyIsClosedConvex hC_nonempty hC_closed hC_convex
  have hargmin_aug : (Argmin ((ι[C] + f.toEReal).asEReal)).Nonempty := by
    rcases hargmin with ⟨p, hp⟩
    have hp' : p ∈ C ∩ Argmin ((ι[C] + f.toEReal).asEReal) := by
      simpa [argminOn_toEReal_eq_inter_indicatorAugmentedArgmin (C := C) (f := f)] using hp
    exact ⟨p, hp'.2⟩
  have hOrbit' :
      IsRelaxedForwardBackwardProximalGradientOrbit hindicator f γ lam x0 x
        (fun n ↦ x n - (γ : ℝ) • ∇ f (x n)) :=
    hOrbit.toIsRelaxedForwardBackwardProximalGradientOrbit γ.2
  have hUniform' :
      (∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ (∂ ι[C]).dom →
          ∃ φ : NNReal → EReal, UniformlyConvexOn (ι[C]) S φ) ∨
        ∀ S : Set H,
          S.Nonempty → Bornology.IsBounded S →
            ∃ φ : NNReal → EReal, UniformlyConvexOn f.toEReal S φ := by
    right
    exact hUniform
  -- Apply the strong-convergence branch of Corollary 28.9 to the indicator specialization.
  rcases
      forwardBackwardAlgorithm_exists_strongLimit_of_uniformlyConvexOnEveryBoundedSubset
        hindicator
        f
        hconv
        hdiff
        β
        γ
        hgrad_lipschitz
        hγ_lt
        lam
        hlam
        hdiv
        hargmin_aug
        hUniform'
        x0
        hOrbit'
    with ⟨p, hp, hx_tendsto, hsingle_aug⟩
  have hpC : p ∈ C :=
    mem_constraint_of_mem_indicatorAugmentedArgmin (C := C) (f := f) hargmin hp
  have hp_on : p ∈ Argmin[C] f.toEReal.asEReal := by
    -- The owner minimizer is feasible, so it is the constrained minimizer as well.
    simpa [argminOn_toEReal_eq_inter_indicatorAugmentedArgmin (C := C) (f := f), hpC] using
      (show p ∈ C ∩ Argmin ((ι[C] + f.toEReal).asEReal) from ⟨hpC, hp⟩)
  have hsingle_on : Argmin[C] f.toEReal.asEReal = ({p} : Set H) := by
    -- Collapse `C ∩ {p}` to `{p}` using feasibility of the unique owner minimizer.
    calc
      Argmin[C] f.toEReal.asEReal = C ∩ Argmin ((ι[C] + f.toEReal).asEReal) := by
        exact argminOn_toEReal_eq_inter_indicatorAugmentedArgmin (C := C) (f := f)
      _ = C ∩ ({p} : Set H) := by rw [hsingle_aug]
      _ = ({p} : Set H) := by
        ext z
        simp [hpC]
  exact ⟨p, hp_on, hx_tendsto, hsingle_on⟩

end Statements

end ProjectionGradientAlgorithm

end ERealFunction
