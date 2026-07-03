import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_5_3_3 (from Chap05) -/
noncomputable section

universe u

/- Corollary 5.3.3 lies in the Chapter 5 self-concordant-barrier / segment-growth domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the barrier owner;
* `IsSelfConcordantBarrierOnWith.concaveOn_exp_neg_div` from `Lemma_5_3_1`, the owner-level
  concavity theorem for the exponential transform;
* `isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div` from the same file, the canonical
  positive-parameter bridge to the textbook transform `x ↦ exp (-(F x / ν))`;
* mathlib `ConcaveOn` on convex combinations, the canonical segment-evaluation API.

Best owner abstraction:
* `IsSelfConcordantBarrierOnWith.segment_upper_bound_log_one_sub`.

Primitive data:
* the barrier owner `hF : IsSelfConcordantBarrierOnWith dom ν F`;
* points `x, y ∈ dom`;
* a segment parameter `α ∈ [0, 1)`.

Derived API:
* concavity of the barrier exponential transform on `dom`;
* the displayed logarithmic upper bound along the segment.

Source/core/bridge triage:
* source-facing: the textbook upper bound along the segment from `x` to `y`;
* core/canonical: the owner `IsSelfConcordantBarrierOnWith dom ν F`;
* bridge/view: the exponential-transform concavity bridge from `Lemma_5_3_1`.

This corollary carries genuine source-facing content, so it should not be collapsed into a
recall-only item. Its proof route should nevertheless stay owner-based: the segment bound is a
thin corollary of the existing concavity owner theorem, not a second standalone derivation. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace IsSelfConcordantBarrierOnWith

-- Proof sketch: use the owner theorem
-- `IsSelfConcordantBarrierOnWith.concaveOn_exp_neg_div` to make
-- `x ↦ exp (-(F x / p))` concave on `dom`, with `p = ν` when `ν > 0` and `p = 1` when `ν = 0`.
-- Evaluate concavity on the convex combination `(1 - α) • x + α • y = x + α • (y - x)`, drop the
-- nonnegative `α`-endpoint term, take logarithms, and rearrange. In the degenerate case `ν = 0`,
-- the same concavity argument with `p = 1` still yields the stronger monotonicity bound
-- `F (x + α • (y - x)) ≤ F x`, because `log (1 - α) ≤ 0`.
/-- Corollary 5.3.3: along the segment from `x` to `y` inside the domain of a
`ν`-self-concordant barrier, the barrier value at `x + α • (y - x)` is bounded above by
`F x - ν log (1 - α)` for every `α ∈ [0, 1)`. -/
theorem segment_upper_bound_log_one_sub
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom) {α : ℝ} (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    F (x + α • (y - x)) ≤ F x - (ν : ℝ) * Real.log (1 - α) := by
  rcases hα with ⟨hα0, hα1⟩
  by_cases hαzero : α = 0
  · subst hαzero
    simp
  set z : E := x + α • (y - x)
  have hz_eq : z = (1 - α) • x + α • y := by
    dsimp [z]
    rw [smul_sub]
    rw [show (1 - α : ℝ) • x = x - α • x by rw [sub_smul, one_smul]]
    abel
  have hαpos : 0 < α := by
    have h0α : 0 ≠ α := by
      simpa [eq_comm] using hαzero
    exact lt_of_le_of_ne hα0 h0α
  have h1α_nonneg : 0 ≤ 1 - α := by linarith
  have h1α_pos : 0 < 1 - α := by linarith
  have hab : (1 - α) + α = 1 := by ring
  have segment_upper_bound_of_posParameter
      {p : ℝ} (hp : 0 < p)
      (hconc : ConcaveOn ℝ dom (fun w ↦ Real.exp (-(F w / p)))) :
      F z ≤ F x - p * Real.log (1 - α) := by
    have hsegment := hconc.2 hx hy h1α_nonneg hα0 hab
    have hleft :
        (1 - α) * Real.exp (-(F x / p)) ≤ Real.exp (-(F z / p)) := by
      calc
        (1 - α) * Real.exp (-(F x / p)) ≤
            (1 - α) * Real.exp (-(F x / p)) + α * Real.exp (-(F y / p)) := by
          nlinarith [hα0, Real.exp_pos (-(F y / p))]
        _ ≤ Real.exp (-(F z / p)) := by
          simpa [hz_eq] using hsegment
    have hlog :
        Real.log ((1 - α) * Real.exp (-(F x / p))) ≤ -(F z / p) := by
      simpa using Real.log_le_log (mul_pos h1α_pos (Real.exp_pos _)) hleft
    rw [Real.log_mul h1α_pos.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
    have hfrac : F z / p + Real.log (1 - α) ≤ F x / p := by
      linarith
    have hscaled := mul_le_mul_of_nonneg_left hfrac hp.le
    have hp_ne : p ≠ 0 := by linarith
    field_simp [hp_ne] at hscaled
    linarith
  have segment_upper_bound_of_unitParameter
      {p : NNRealˣ}
      (hconc : ConcaveOn ℝ dom (barrierExponentialTransform p F)) :
      F z ≤ F x - (p : ℝ) * Real.log (1 - α) := by
    have hsegment := hconc.2 hx hy h1α_nonneg hα0 hab
    have hleft :
        (1 - α) * Real.exp (-F x / (p : ℝ)) ≤ Real.exp (-F z / (p : ℝ)) := by
      calc
        (1 - α) * Real.exp (-F x / (p : ℝ)) ≤
            (1 - α) * Real.exp (-F x / (p : ℝ)) +
              α * Real.exp (-F y / (p : ℝ)) := by
          nlinarith [hα0, Real.exp_pos (-F y / (p : ℝ))]
        _ ≤ Real.exp (-F z / (p : ℝ)) := by
          simpa [barrierExponentialTransform, hz_eq] using hsegment
    have hlog :
        Real.log ((1 - α) * Real.exp (-F x / (p : ℝ))) ≤ -F z / (p : ℝ) := by
      simpa using Real.log_le_log (mul_pos h1α_pos (Real.exp_pos _)) hleft
    rw [Real.log_mul h1α_pos.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
    have hp_nonneg : 0 ≤ (p : ℝ) := by positivity
    have hp_ne : (p : ℝ) ≠ 0 := by
      exact_mod_cast Units.ne_zero p
    have hp_pos : 0 < (p : ℝ) := lt_of_le_of_ne hp_nonneg (by simp [eq_comm, hp_ne])
    have hscaled := mul_le_mul_of_nonneg_left hlog hp_pos.le
    field_simp [hp_ne] at hscaled
    linarith
  by_cases hν : ν = 0
  · have hlog_neg : Real.log (1 - α) < 0 := by
      exact Real.log_neg h1α_pos (by linarith)
    by_contra hz_gt
    have hz_gt' : F x < F z := by
      simpa [hν] using hz_gt
    let p0 : ℝ := (F z - F x) / (-(2 * Real.log (1 - α)))
    have hp0_pos : 0 < p0 := by
      have hden_pos : 0 < -(2 * Real.log (1 - α)) := by
        nlinarith
      exact div_pos (by linarith) hden_pos
    have hpNN_ne : (⟨p0, le_of_lt hp0_pos⟩ : NNReal) ≠ 0 := by
      simpa using hp0_pos.ne'
    let p : NNRealˣ := Units.mk0 (⟨p0, le_of_lt hp0_pos⟩ : NNReal) hpNN_ne
    have hconc :
        ConcaveOn ℝ dom (barrierExponentialTransform p F) :=
      hF.concaveOn_exp_neg_div (by simp [hν])
    have hp_eq : (((p : NNReal) : ℝ)) = p0 := by
      change (((⟨p0, le_of_lt hp0_pos⟩ : NNReal) : ℝ)) = p0
      rfl
    have hz_le'' : F z ≤ F x - (p : ℝ) * Real.log (1 - α) := by
      exact segment_upper_bound_of_unitParameter hconc
    have hden_ne : -(2 * Real.log (1 - α)) ≠ 0 := by
      nlinarith [hlog_neg.ne]
    have hlog_ne : Real.log (1 - α) ≠ 0 := by
      linarith [hlog_neg.ne]
    have hfx : F x - p0 * Real.log (1 - α) = F x + (F z - F x) / 2 := by
      dsimp [p0]
      field_simp [hlog_ne]
      ring
    have hz_half : F z ≤ F x + (F z - F x) / 2 := by
      simpa [hp_eq, hfx] using hz_le''
    linarith
  · have hνpos : 0 < (ν : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr hν)
    have hconc :
        ConcaveOn ℝ dom (fun w ↦ Real.exp (-(F w / (ν : ℝ)))) :=
      (isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div
        hF.toIsStandardSelfConcordantOn hνpos).1 hF
    have hz_le : F z ≤ F x - (ν : ℝ) * Real.log (1 - α) :=
      segment_upper_bound_of_posParameter hνpos hconc
    simpa [z] using hz_le

end IsSelfConcordantBarrierOnWith

end

/-! ### Definition_5_3_3 (from Chap05) -/
universe u

variable {E : Type u}

/- This item lies in the Chapter 5 analytic-center / self-concordant-barrier domain.

Sampled owner-style declarations:
* `IsMinOn` in mathlib, the canonical minimizer predicate on a set;
* `Chap03/Definition_3_24`, where the project already treats whole-space minimizers by direct
  recall of `IsMinOn`;
* `Chap03/Definition_3_33`, where unconstrained convex minimizers are likewise expressed directly
  through `IsMinOn f Set.univ xStar`;
* `Chap03/Definition_3_62`, where analytic centers of logarithmic barriers are written as
  `IsMinOn (analyticBarrier a b) Set.univ y`.

Best owner abstraction:
* source-facing/core: `IsMinOn F dom (xStar : E)` for a domain point `xStar : dom`;
* bridge/view: any prose saying that `xStar` is the analytic center generated by `F`.

Primitive data:
* the domain `dom : Set E`;
* the barrier function `F : E → ℝ`;
* the domain point `xStar : dom`.

Derived API:
* the analytic-center condition itself, namely `IsMinOn F dom (xStar : E)`;
* any textbook pointwise inequality expansion, which is a companion view rather than a separate
  owner.

Source/core/bridge triage:
* source-facing: the statement that the analytic center is the minimizer of the barrier on `dom`;
* core/canonical: `IsMinOn F dom (xStar : E)`;
* bridge/view: prose or later lemmas that restate this minimizer condition in other equivalent
  forms.

This item adds no new owner alias: the project already uses `IsMinOn` as the canonical minimizer
predicate, including for analytic-center statements. Downstream Chapter 5 files should therefore
reuse `IsMinOn F dom (xStar : E)` directly rather than keeping a parallel
`IsAnalyticCenterOfBarrierOn` wrapper. Since the canonical owner needs only a type, a set, a
real-valued function, and a point of the set, this recall also drops the unused Hilbert-space and
finite-dimensional ambient structure. -/

section

variable (dom : Set E) (F : E → ℝ) (xStar : dom)

/- Definition 5.3.3: the analytic center of the convex set `dom`, generated by the barrier `F`,
is exactly a point `xStar ∈ dom` whose ambient point `(xStar : E)` minimizes `F` on `dom`. -/
recall IsMinOn

set_option linter.hashCommand false in
#check IsMinOn F dom (xStar : E)

end

/-! ### Lemma_5_3_3 (from Chap05) -/
open scoped BInducedNorm Gradient HessianDualLocalNorm

noncomputable section

universe u

open InnerProductSpace

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

/-
Lemma 5.3.3 lies in the Chapter 5 self-concordant-barrier / auxiliary-central-path /
analytic-center dual-norm domain.

Sampled owner declarations in this domain:
* `IsCentralPath` in `Definition_5_3_6_1`, the chapter owner for the auxiliary central path;
* `centralPath_stationarity_eq_zero` in `Proposition_5_3_1`, the canonical bridge from
  `IsCentralPath` to the pathwise stationarity equation;
* `IsSelfConcordantBarrierOnWith.dualLocalNorm_le_barrierParameter_add_two_sqrt_mul_of_isMinOn`
  in `Corollary_5_3_4`, the analytic-center comparison theorem for Hessian dual local norms;
* `HessianDualLocalNorm.ofPosDefMem` in `Definition_5_0_20`, the domain-level bridge to the local
  dual norm.

Best owner abstraction:
* source-facing: the dual-local-norm estimate along the auxiliary central path;
* core/canonical: the analytic-center comparison theorem under the barrier owner;
* bridge/view: the central-path stationarity identity and nonnegative scalar homogeneity of the
  induced dual norm.

Primitive data:
* the barrier owner and positive-definite-Hessian owner on `dom`;
* the initial point `y0`, the path `yStar`, and the analytic center `xFStar`;
* the analytic-center witness `IsMinOn F dom (xFStar : E)`;
* the source-facing path hypothesis `IsCentralPath dom (-∇ F (y0 : E)) F yStar`.

Derived API:
* the gradient identity `∇ F (yStar t : E) = (t : ℝ) • ∇ F (y0 : E)`;
* the pointwise dual-local-norm bound at `yStar t`;
* the owner-level homogeneity bridge `dualLocalNorm_smul_nonneg`.

Source/core/bridge triage:
* source-facing: the present lemma on the auxiliary central path owner;
* core/canonical: the analytic-center dual-local-norm comparison theorem;
* bridge/view: the local derivation of the gradient-scaling identity and owner-level scalar
  homogeneity.
-/

-- Proof sketch: Proposition 5.3.1 gives
-- `(t : ℝ) • (-∇ F(y₀)) + ∇ F(y*(t)) = 0` along the auxiliary central path, hence
-- `∇ F (y*(t)) = t • ∇ F(y₀)`. Apply
-- `IsSelfConcordantBarrierOnWith.dualLocalNorm_le_barrierParameter_add_two_sqrt_mul_of_isMinOn`
-- at the point
-- `y*(t)` with analytic center `x_F^*`, then use the positive homogeneity of the Hessian dual
-- norm and the nonnegativity built into `t : Set.Ici (0 : ℝ)` to pull out the factor `t`.
namespace IsSelfConcordantBarrierOnWith

/-- Lemma 5.3.3: along an auxiliary central path `y*(t)` for a bounded
`ν`-self-concordant barrier, the dual local norm of the gradient at time `t ≥ 0` is bounded by
`(ν + 2 √ν)` times the dual local norm of the initial gradient at the analytic center `x_F^*`,
multiplied by `t`. -/
theorem dualLocalNorm_gradient_auxiliaryCentralPath_le_barrierParameter_add_two_sqrt_mul_initial
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    [HasPositiveDefiniteHessianOn dom F]
    (y0 : dom) (yStar : Set.Ici (0 : ℝ) → dom)
    (xFStar : dom) (hxFStar : IsMinOn F dom (xFStar : E))
    (hpath : IsCentralPath dom (-∇ F (y0 : E)) F yStar)
    (t : Set.Ici (0 : ℝ)) :
    HessianDualLocalNorm.ofPosDefMem F (yStar t).2 (toDual ℝ E (∇ F (yStar t : E))) ≤
      (((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) *
          HessianDualLocalNorm.ofPosDefMem F xFStar.2 (toDual ℝ E (∇ F (y0 : E)))) *
        (t : ℝ) := by
  letI : IsSelfConcordantBarrierOnWith dom ν F := hF
  let hstd : IsStandardSelfConcordantOn dom F := inferInstance
  have hdiff : DifferentiableOn ℝ F dom := by
    intro x hx
    exact (hstd.contDiffOn x hx).differentiableWithinAt (by norm_num)
  have hgrad (s : Set.Ici (0 : ℝ)) :
      ∇ F (yStar s : E) = (s : ℝ) • ∇ F (y0 : E) := by
    have hzero :
        (s : ℝ) • (-∇ F (y0 : E)) + ∇ F (yStar s : E) = 0 :=
      centralPath_stationarity_eq_zero
        dom (-∇ F (y0 : E)) F yStar hpath s
        (hstd.isOpen_domain.mem_nhds (yStar s).2)
        ((hdiff (yStar s : E) (yStar s).2).differentiableAt
          (hstd.isOpen_domain.mem_nhds (yStar s).2))
    calc
      ∇ F (yStar s : E) = -((s : ℝ) • (-∇ F (y0 : E))) := by
        simpa using (eq_neg_of_add_eq_zero_left hzero).symm
      _ = (s : ℝ) • ∇ F (y0 : E) := by simp
  have hsmul :
      HessianDualLocalNorm.ofPosDefMem F xFStar.2 (toDual ℝ E ((t : ℝ) • ∇ F (y0 : E))) =
        (t : ℝ) *
          HessianDualLocalNorm.ofPosDefMem F xFStar.2 (toDual ℝ E (∇ F (y0 : E))) := by
    simpa [HessianDualLocalNorm.ofPosDefMem] using
      dualLocalNorm_smul_nonneg F (xFStar : E)
        (HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem xFStar.2)
        (hessian_isInvertible_of_det_ne_zero
          (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem xFStar.2))
        (toDual ℝ E (∇ F (y0 : E))) t.2
  calc
    HessianDualLocalNorm.ofPosDefMem F (yStar t).2 (toDual ℝ E (∇ F (yStar t : E))) =
        HessianDualLocalNorm.ofPosDefMem F (yStar t).2
          (toDual ℝ E ((t : ℝ) • ∇ F (y0 : E))) := by
      rw [hgrad t]
    _ ≤ ((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) *
          HessianDualLocalNorm.ofPosDefMem F xFStar.2
            (toDual ℝ E ((t : ℝ) • ∇ F (y0 : E))) :=
      hF.dualLocalNorm_le_barrierParameter_add_two_sqrt_mul_of_isMinOn
        xFStar hxFStar (yStar t) ((t : ℝ) • ∇ F (y0 : E))
    _ = (((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) *
          HessianDualLocalNorm.ofPosDefMem F xFStar.2
            (toDual ℝ E (∇ F (y0 : E)))) *
          (t : ℝ) := by
      rw [hsmul]
      ring_nf

end IsSelfConcordantBarrierOnWith

end

/-! ### Proposition_5_3_3 (from Chap05) -/
open scoped Gradient HessianLocalNorm

noncomputable section

universe u

/- Proposition 5.3.3 lies in the Chapter 5 barrier-parameter / local-Hessian-norm domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith.barrier_parameter_bound` in `Definition_5_3_2`, the source
  owner inequality for a `ν`-self-concordant barrier;
* `hessianLocalNorm` and the notation `‖u‖[F; x]` in `Definition_5_1_1`, the chapter owner for
  the Hessian-induced local norm;
* `hessianLocalNorm_def` in `Definition_5_1_1`, the canonical owner expansion;
* `sublevelLogBarrier_hessian_quadraticForm_ge_gradient_sq` in `Theorem_5_1_4`, the earlier
  quadratic-form inequality in the same Chapter 5 differential domain.

Source/core/bridge triage:
* source-facing: the fixed-point barrier inequality at `x`;
* core/canonical: the Hessian local norm `‖u‖[F; x]`;
* bridge/view: `hessianLocalNorm_def` together with `Real.sq_sqrt`, which recovers
  `inner ℝ u (hessian F x u)` from that owner.

Primitive data:
* a function `F`;
* a barrier parameter `ν`;
* a base point `x`.
* pointwise Hessian positivity at `x`.

Derived API:
* the equivalent local-norm-square estimate
  `⟪∇ F(x), u⟫² ≤ ν ‖u‖[F; x]^2`;
* the raw Hessian-quadratic-form presentation, recovered canonically from
  `hessianLocalNorm_def`.

This proposition therefore keeps the source-facing left-hand side from
`IsSelfConcordantBarrierOnWith.barrier_parameter_bound`, but refines the right-hand side to the
chapter owner `‖u‖[F; x]` instead of repeating the quadratic form inline. The pointwise theorem
below is the public bridge, and barrier-owner applications should use it with the Hessian
positivity already supplied by `IsSelfConcordantOnWith.hessian_isPositive`. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: for the forward implication, apply the bound to the scaled direction `t • u`,
-- obtaining a quadratic inequality in `t`; nonpositivity of its discriminant yields
-- `⟪∇ F(x), u⟫² ≤ ν ‖u‖[F; x]^2`. Conversely, from the squared bound, use
-- `2ab ≤ a² + b²` after normalizing by `ν`, or complete the square in
-- `2 * ⟪∇ F(x), u⟫ - ⟪∇² F(x)u, u⟫`, to recover the original inequality. The pointwise
-- positivity hypothesis is essential: without it, `‖u‖[F; x]` can vanish on directions where the
-- Hessian quadratic form is negative, so the squared local-norm bound no longer detects the
-- barrier inequality.
/-- Proposition 5.3.3, pointwise owner form: at a fixed point `x` with positive Hessian,
the barrier inequality `2 ⟪∇ F(x), u⟫ - ⟪∇² F(x)u, u⟫ ≤ ν` for every direction `u` is
equivalent to the quadratic-form bound `⟪∇ F(x), u⟫² ≤ ν ‖u‖[F; x]^2` for every `u`,
written on the canonical Chapter 5 local-norm surface. -/
theorem barrier_parameter_bound_iff_gradient_inner_sq_le
    {F : E → ℝ} {ν : NNReal} {x : E} (hPos : (hessian F x).IsPositive) :
    (∀ u : E,
      2 * inner ℝ (∇ F x) u - inner ℝ u (hessian F x u) ≤ (ν : ℝ)) ↔
      ∀ u : E,
        (inner ℝ (∇ F x) u) ^ (2 : ℕ) ≤
          (ν : ℝ) * ‖u‖[F; x] ^ (2 : ℕ) := sorry

end

/-! ### Theorem_5_3_3 (from Chap05) -/
universe u v

open scoped Gradient HessianLocalNorm

variable {E : Type u} {E₁ : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]

/- Theorem 5.3.3 lies in the Chapter 5 self-concordant-barrier affine-pullback calculus.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for
  self-concordant barriers;
* `IsSelfConcordantOnWith.comp_continuousAffineMap` from `Theorem_5_1_2`, the owner-level
  affine-pullback theorem for standard self-concordance;
* `IsSelfConcordantOnWith.comp_affineMap` from `Theorem_5_1_2`, the finite-dimensional
  specialization derived from the continuous-affine owner theorem;
* `IsSelfConcordantBarrierOnWith.isBarrierFunctionOn` from `Definition_5_3_2`, the canonical
  bridge from a self-concordant barrier to the Chapter 1 barrier owner.

Best owner abstraction:
* `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap`.

Primitive data:
* the owner witness `h : IsSelfConcordantBarrierOnWith dom ν F`;
* the continuous affine map `g : E →ᴬ[ℝ] E₁`.

Derived API:
* the owner-level pullback barrier `F ∘ g` on `g ⁻¹' dom`;
* the finite-dimensional specialization `comp_affineMap`;
* the coordinate presentation `x ↦ F (A x + b)` when `g x = A x + b`.

Source/core/bridge triage:
* source-facing: affine pullback closure of self-concordant barriers;
* core/canonical: `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap`;
* bridge/view: the finite-dimensional `comp_affineMap` specialization, then the textbook
  linear-plus-translation form `x ↦ F (A x + b)`.

The barrier owner is defined over complete real inner-product spaces, and the surrounding chapter
already organizes affine pullback calculus around continuous affine maps. This refinement therefore
keeps the numbered content in the barrier owner namespace at the `ContinuousAffineMap` level, with
`comp_affineMap` retained only as the finite-dimensional bridge. -/

namespace IsSelfConcordantBarrierOnWith

-- Proof sketch: apply `IsSelfConcordantOnWith.comp_continuousAffineMap` to the standard
-- self-concordance field of the barrier owner. For the barrier parameter, fix `x ∈ g ⁻¹' dom`
-- and rewrite the gradient and Hessian quadratic form of `F ∘ g` in the direction `u` through
-- the image direction `g.toAffineMap.linear u`; then apply the owner bound for `F` at `g x`.
/-- Theorem 5.3.3: if `F` is a `ν`-self-concordant barrier on `dom ⊆ E₁`, then its precomposition
with a continuous affine map `g : E →ᴬ[ℝ] E₁` is a `ν`-self-concordant barrier on the affine
preimage `g ⁻¹' dom`. This is the owner-level affine-pullback theorem. -/
theorem comp_continuousAffineMap
    {dom : Set E₁} {ν : NNReal} {F : E₁ → ℝ}
    (h : IsSelfConcordantBarrierOnWith dom ν F) (g : E →ᴬ[ℝ] E₁) :
    IsSelfConcordantBarrierOnWith (g ⁻¹' dom) ν (F ∘ g) := by
  let hstd : IsStandardSelfConcordantOn dom F := h.toIsStandardSelfConcordantOn
  refine
    { toIsStandardSelfConcordantOn := hstd.comp_continuousAffineMap g
      barrier_parameter_bound := ?_ }
  intro x hx u
  have hpull : IsStandardSelfConcordantOn (g ⁻¹' dom) (F ∘ g) :=
    hstd.comp_continuousAffineMap g
  have hPos : (hessian (F ∘ g) x).IsPositive := hpull.hessian_isPositive hx
  refine ((_root_.barrier_parameter_bound_iff_gradient_inner_sq_le hPos).2 ?_) u
  intro u
  have hx_dom : g x ∈ dom := hx
  have hcont :
      ContDiffAt ℝ 2 F (g x) := by
    exact (hstd.contDiffOn.of_le (by norm_num)).contDiffAt (hstd.isOpen_domain.mem_nhds hx_dom)
  have hdiff : DifferentiableAt ℝ F (g x) := hcont.differentiableAt (by norm_num)
  have hdiff_comp : DifferentiableAt ℝ (F ∘ g) x :=
    (hcont.comp x g.contDiff.contDiffAt).differentiableAt (by norm_num)
  have hsq :=
      (_root_.barrier_parameter_bound_iff_gradient_inner_sq_le
          (hstd.hessian_isPositive hx_dom)).mp
        (h.barrier_parameter_bound hx_dom)
  calc
    (inner ℝ (∇ (F ∘ g) x) u) ^ (2 : ℕ) = (fderiv ℝ (F ∘ g) x u) ^ (2 : ℕ) := by
      rw [inner_gradient_left hdiff_comp]
    _ = (fderiv ℝ F (g x) (g.contLinear u)) ^ (2 : ℕ) := by
      congr 1
      simpa using congrArg (fun A : E →L[ℝ] ℝ ↦ A u) (fderiv_comp x hdiff g.differentiableAt)
    _ = (inner ℝ (∇ F (g x)) (g.contLinear u)) ^ (2 : ℕ) := by
      rw [← inner_gradient_left hdiff]
    _ ≤ (ν : ℝ) * ‖g.contLinear u‖[F; g x] ^ (2 : ℕ) :=
      hsq (g.contLinear u)
    _ = (ν : ℝ) * ‖u‖[F ∘ g; x] ^ (2 : ℕ) := by
      rw [← hessianLocalNorm_comp_affine F g x u hcont]

/-- Theorem 5.3.3, finite-dimensional specialization: affine precomposition preserves the barrier
property on the affine preimage with the same barrier parameter. -/
theorem comp_affineMap
    [FiniteDimensional ℝ E]
    {dom : Set E₁} {ν : NNReal} {F : E₁ → ℝ}
    (h : IsSelfConcordantBarrierOnWith dom ν F) (g : E →ᵃ[ℝ] E₁) :
    IsSelfConcordantBarrierOnWith (g ⁻¹' dom) ν (F ∘ g) := by
  simpa using h.comp_continuousAffineMap ⟨g, g.continuous_of_finiteDimensional⟩

end IsSelfConcordantBarrierOnWith

/-! ### Corollary_5_3_4 (from Chap05) -/
open InnerProductSpace
open scoped Gradient HessianDualLocalNorm

noncomputable section

universe u

/-
Corollary 5.3.4 lies in the Chapter 5 self-concordant-barrier / analytic-center / dual-local-norm
domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for
  `ν`-self-concordant barriers;
* `IsMinOn` in `Definition_5_3_3`, the canonical analytic-center owner;
* `IsSelfConcordantBarrierOnWith.subset_dikinEllipsoid_barrierParameter_add_two_sqrt_of_isMinOn`
  in `Theorem_5_3_9`, the owner-level analytic-center inclusion theorem upstream in the same
  chapter;
* `HasPositiveDefiniteHessianOn` in `Definition_5_0_23`, the chapter owner for domain-level
  Hessian nondegeneracy;
* `HessianDualLocalNorm.ofPosDefMem` in `Definition_5_0_20`, the canonical bridge from
  `HasPositiveDefiniteHessianOn` to the Chapter 5 Hessian-metric dual local norm.

Best owner abstraction:
* source-facing: the analytic-center Hessian and dual-local-norm comparison bounds;
* core/canonical: `IsSelfConcordantBarrierOnWith dom ν F`;
* bridge/view: `HessianDualLocalNorm.ofPosDefMem`, which derives the local Hessian data needed to
  evaluate the dual norm from the positive-definite-Hessian owner.

Primitive data:
* the barrier owner `hF : IsSelfConcordantBarrierOnWith dom ν F`;
* the analytic-center witness `hcenter : IsMinOn F dom (xStar : E)`;
* for the dual-norm comparison only, the domain-level positive-definite-Hessian owner
  `HasPositiveDefiniteHessianOn dom F`.

Derived API:
* the Loewner lower bound comparing `hessian F x` to the Hessian at the analytic center;
* the corresponding comparison of Hessian dual local norms, stated through the canonical
  domain-level bridge `HessianDualLocalNorm.ofPosDefMem`.

Source/core/bridge triage:
* source-facing: the textbook analytic-center comparison corollaries;
* core/canonical: the barrier owner `IsSelfConcordantBarrierOnWith dom ν F`;
* bridge/view: `HessianDualLocalNorm.ofPosDefMem`.

These corollaries carry genuine source-facing content, so they should remain theorem-shaped rather
than a pure recall. Their public surface is nevertheless barrier-owner based: the surrounding
Chapter 5 API already organizes barrier consequences under `IsSelfConcordantBarrierOnWith`, and
the dual-norm comparison should use the domain-level dual-norm bridge instead of exposing raw
determinant witnesses in the public statement. -/

namespace IsSelfConcordantBarrierOnWith

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: for a chosen analytic center `xStar`, Theorem 5.3.9 bounds the
-- `xStar`-local distance of every `x ∈ dom`, and Theorem 5.1.5 then turns the inclusion of the
-- unit Dikin ball at `x` into the larger Dikin ball at `xStar` of radius `ν + 2 √ν`. Rewriting
-- that ellipsoid inclusion in Loewner order gives the displayed Hessian comparison.
/-- Corollary 5.3.4: if `xStar` is an analytic center of a `ν`-self-concordant barrier on `dom`,
then for every `x ∈ dom` the Hessian at `x` dominates the Hessian at `xStar` in Loewner order by
the factor `(ν + 2 √ν)⁻²`. -/
theorem hessian_loewner_lower_bound_of_isMinOn
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    (xStar : dom) (hcenter : IsMinOn F dom (xStar : E))
    (x : dom) :
    (1 / (((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) ^ (2 : ℕ))) •
        hessian F (xStar : E) ≤
      hessian F x := by
  letI : IsSelfConcordantBarrierOnWith dom ν F := hF
  sorry

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: use the support-function representation of the dual local norm as the supremum
-- of the pairing over the corresponding Dikin ellipsoid. The Loewner comparison from
-- `IsSelfConcordantBarrierOnWith.hessian_loewner_lower_bound_of_isMinOn` is equivalent to
-- inclusion of these ellipsoids,
-- which yields the stated comparison of inverse-Hessian dual norms after identifying vectors with
-- covectors through the Riesz map.
/-- The dual local norm of the covector corresponding to `v` at any point of a self-concordant
barrier domain is controlled by the corresponding dual local norm at an analytic center with
factor `ν + 2 √ν`. -/
theorem dualLocalNorm_le_barrierParameter_add_two_sqrt_mul_of_isMinOn
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [HasPositiveDefiniteHessianOn dom F]
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    (xStar : dom) (hcenter : IsMinOn F dom (xStar : E))
    (x : dom)
    (v : E) :
    HessianDualLocalNorm.ofPosDefMem F x.2 (toDual ℝ E v) ≤
      ((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) *
        HessianDualLocalNorm.ofPosDefMem F xStar.2 (toDual ℝ E v) := by
  letI : IsSelfConcordantBarrierOnWith dom ν F := hF
  sorry

end

end IsSelfConcordantBarrierOnWith

end

/-! ### Definition_5_3_4_1 (from Chap05) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Hessian dual norm at `x` of a vector `v`, computed by pairing `v` with the inverse
Hessian operator of `F` at `x`. -/
def hessianDualNormVector
    (F : E → ℝ) (x : E) (hH : (fderiv ℝ (∇ F) x).det ≠ 0) (v : E) : ℝ :=
  Real.sqrt (inner ℝ v ((hessian F x).inverse v))

-- Proof sketch: unfold `hessianDualNormVector`; the definition is exactly the inverse-Hessian
-- quadratic form associated with the vector `v`.
/-- Expanding `hessianDualNormVector F x hH v` gives the square root of the inverse-Hessian
quadratic form of `v` at `x`. -/
theorem hessianDualNormVector_def
    (F : E → ℝ) (x : E) (hH : (fderiv ℝ (∇ F) x).det ≠ 0) (v : E) :
    hessianDualNormVector F x hH v =
      Real.sqrt (inner ℝ v ((hessian F x).inverse v)) := sorry

/-- The local dual norm `‖c‖*ₓ` of the objective vector `c` in the Hessian metric of the barrier
`F` at `x`. -/
def barrierPathFollowingObjectiveNorm
    (F : E → ℝ) (c : E) (x : E) (hH : (fderiv ℝ (∇ F) x).det ≠ 0) : ℝ :=
  hessianDualNormVector F x hH c

-- Proof sketch: unfold `barrierPathFollowingObjectiveNorm`; it is just
-- `hessianDualNormVector F x hH c`.
/-- Expanding `barrierPathFollowingObjectiveNorm F c x hH` gives the textbook quantity
`‖c‖*ₓ`. -/
theorem barrierPathFollowingObjectiveNorm_def
    (F : E → ℝ) (c x : E) (hH : (fderiv ℝ (∇ F) x).det ≠ 0) :
    barrierPathFollowingObjectiveNorm F c x hH =
      hessianDualNormVector F x hH c := sorry

/-- The shifted residual norm `‖t c + ∇ F(x)‖*ₓ` used to define the intermediate Newton
correction in the main path-following step. -/
def barrierPathFollowingResidualNorm
    (F : E → ℝ) (c : E) (t : ℝ) (x : E) (hH : (fderiv ℝ (∇ F) x).det ≠ 0) : ℝ :=
  hessianDualNormVector F x hH ((t • c) + ∇ F x)

-- Proof sketch: unfold `barrierPathFollowingResidualNorm`; the result is the Hessian dual norm of
-- the shifted gradient `t c + ∇ F(x)`.
/-- Expanding `barrierPathFollowingResidualNorm F c t x hH` gives the textbook quantity
`‖t c + ∇ F(x)‖*ₓ`. -/
theorem barrierPathFollowingResidualNorm_def
    (F : E → ℝ) (c : E) (t : ℝ) (x : E) (hH : (fderiv ℝ (∇ F) x).det ≠ 0) :
    barrierPathFollowingResidualNorm F c t x hH =
      hessianDualNormVector F x hH ((t • c) + ∇ F x) := sorry

/-- The stopping threshold from `(5.3.29)` for obtaining an `ε`-accurate point along the
central-path approximation generated by a `ν`-self-concordant barrier. -/
def barrierPathFollowingStoppingThreshold
    (ν : NNReal) (β ε : ℝ) : ℝ :=
  ((ν : ℝ) + ((β + Real.sqrt (ν : ℝ)) * β) / (1 - β)) / ε

-- Proof sketch: unfold `barrierPathFollowingStoppingThreshold`; the expression is exactly the
-- right-hand side of display `(5.3.29)`.
/-- Expanding `barrierPathFollowingStoppingThreshold ν β ε` recovers the textbook stopping bound
`(1 / ε) (ν + ((β + √ν) β) / (1 - β))`. -/
theorem barrierPathFollowingStoppingThreshold_def
    (ν : NNReal) (β ε : ℝ) :
    barrierPathFollowingStoppingThreshold ν β ε =
      ((ν : ℝ) + ((β + Real.sqrt (ν : ℝ)) * β) / (1 - β)) / ε := sorry

/-- Definition 5.3.4.1: a main path-following scheme for minimizing `⟪c, x⟫` over the closure of
the domain of a `ν`-self-concordant barrier `F` starts from `t₀ = 0` and a point `x₀ ∈ dom`
with `‖∇ F(x₀)‖*_(x₀) ≤ β`, updates
`tₖ₊₁ = tₖ + γ / ‖c‖*_(xₖ)` and
`xₖ₊₁ = xₖ - (1 + ξₖ)⁻¹ [∇² F(xₖ)]⁻¹ (tₖ₊₁ c + ∇ F(xₖ))`
with `ξₖ = λₖ² / (1 + λₖ)` and `λₖ = ‖tₖ₊₁ c + ∇ F(xₖ)‖*_(xₖ)`, and stops at the first index
where `tₖ` reaches the threshold `(5.3.29)`. -/
structure BarrierPathFollowingScheme
    {dom : Set E} (c : E) (F : E → ℝ) (ν : NNReal)
    [IsSelfConcordantBarrierOnWith dom ν F]
    (x0 : dom) (β γ ε : ℝ) where
  /-- The scalar path parameters `t₀, t₁, t₂, ...`. -/
  t : ℕ → ℝ
  /-- The primal iterates `x₀, x₁, x₂, ...`. -/
  x : ℕ → E
  /-- Every iterate stays in the barrier domain. -/
  mem_domain : ∀ k : ℕ, x k ∈ dom
  /-- The Hessian at each iterate is nondegenerate, so the local dual norms and inverse-Hessian
  correction are defined. -/
  hessian_nondegenerate : ∀ k : ℕ, (fderiv ℝ (∇ F) (x k)).det ≠ 0
  /-- The initial centering parameter satisfies the textbook condition `β < 1`. -/
  beta_lt_one : β < 1
  /-- The requested accuracy is positive. -/
  epsilon_pos : 0 < ε
  /-- The scheme starts from `t₀ = 0`. -/
  t_zero : t 0 = 0
  /-- The initial iterate is the prescribed point `x₀`. -/
  x_zero : x 0 = x0
  /-- The starting point satisfies the initial centering condition
  `‖∇ F(x₀)‖*_(x₀) ≤ β`. -/
  initial_centering :
    hessianDualNormVector F (x 0) (hessian_nondegenerate 0) (∇ F (x 0)) ≤ β
  /-- The scalar update is `tₖ₊₁ = tₖ + γ / ‖c‖*_(xₖ)`. -/
  t_step :
    ∀ k : ℕ,
      t (k + 1) =
        t k + γ / barrierPathFollowingObjectiveNorm F c (x k) (hessian_nondegenerate k)
  /-- The iterate update is the intermediate Newton correction for the shifted gradient
  `tₖ₊₁ c + ∇ F(xₖ)`. -/
  x_step :
    ∀ k : ℕ,
      x (k + 1) =
        x k -
          (1 /
            (1 + selfConcordantNewtonShift SelfConcordantNewtonVariant.intermediate 1
              (barrierPathFollowingResidualNorm F c (t (k + 1)) (x k)
                (hessian_nondegenerate k)))) •
            (hessian F (x k)).inverse
              ((t (k + 1)) • c + ∇ F (x k))
  /-- The first index at which the stopping threshold `(5.3.29)` is reached. -/
  stopIndex : ℕ
  /-- Before the stopping index, the path parameter stays below the threshold from `(5.3.29)`. -/
  continue_condition :
    ∀ ⦃k : ℕ⦄, k < stopIndex →
      t k < barrierPathFollowingStoppingThreshold ν β ε
  /-- At the stopping index, the path parameter reaches the threshold from `(5.3.29)`. -/
  stop_condition :
    barrierPathFollowingStoppingThreshold ν β ε ≤ t stopIndex

namespace BarrierPathFollowingScheme

/-- A barrier path-following scheme can be used as its iterate sequence `k ↦ xₖ`. -/
instance
    {dom : Set E} {c : E} {F : E → ℝ} {ν : NNReal}
    [IsSelfConcordantBarrierOnWith dom ν F]
    {x0 : dom} {β γ ε : ℝ} :
    CoeFun (BarrierPathFollowingScheme c F ν x0 β γ ε) (fun _ ↦ ℕ → E) where
  coe scheme := scheme.x

end BarrierPathFollowingScheme

end

/-! ### Proposition_5_3_4 (from Chap05) -/
open InnerProductSpace
open scoped ConvexAnalysis Gradient WithTopConvexAnalysis

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Proposition 5.3.4 lies in the Chapter 5 dual-barrier / Fenchel-conjugacy domain.

Sampled owner-style declarations in this domain:
* `fenchelDual` / notation `f⋆` in `Definition_5_0_27`, the chapter owner for the canonical
  dual object `F_*`;
* `extendedRealRealPart (f⋆)`, the real-valued owner surface of that dual object used throughout
  the chapter;
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for barrier
  parameters on a standard self-concordant domain;
* `IsSelfConcordantOnWith.hessian_isPositive` in `Definition_5_1_1`, the canonical pointwise
  Hessian-positivity bridge on that owner surface;
* `fderiv_gradient_isSymmetric_of_contDiffAt` in `Chap01/Theorem_1_4_19`, the upstream symmetry
  owner behind the positive-Hessian quadratic-form argument.

Best owner abstraction:
* source-facing: the barrier criterion for the canonical dual object `F_*`, stated through the
  source relation `(5.1.34)` and the pairing `⟪s, ∇²F_*(s) s⟫`;
* core/canonical: `extendedRealRealPart (f⋆)` together with the barrier owner
  `IsSelfConcordantBarrierOnWith`;
* bridge/view: the pointwise completion-of-the-square argument on
  `⟪u - s, ∇²F_*(s) (u - s)⟫`, read through Hessian positivity and symmetry.

Primitive data:
* the primal extended-real owner `f : E → WithTop ℝ`;
* the source relation `(5.1.34)` on the canonical dual real part
  `∇ (extendedRealRealPart (f⋆)) s = ∇² (extendedRealRealPart (f⋆))(s) s`;
* standard self-concordance of `extendedRealRealPart (f⋆)` on `dom (f⋆)`;
* the source-facing bound `⟪s, ∇²F_*(s) s⟫ ≤ ν`.

Derived API:
* pointwise positivity and symmetry of the dual Hessian on `dom (f⋆)`;
* the completed-square estimate
  `2 ⟪∇F_*(s), u⟫ - ⟪u, ∇²F_*(s)u⟫ ≤ ⟪s, ∇²F_*(s)s⟫`;
* the `ν`-self-concordant barrier owner on `dom (f⋆)`.

This refinement keeps Proposition 5.3.4 source-facing on the canonical dual owner
`extendedRealRealPart (f⋆)`, but removes the bridge-level Fenchel maximizer branch and inverse-
Hessian machinery from the public statement. The barrier inequality is derived directly from
`(5.1.34)`, Hessian positivity, and the source bound `⟪s, ∇²F_*(s) s⟫ ≤ ν`. -/

section FenchelDualBarrier

variable {f : E → WithTop ℝ}

-- Proof sketch: for fixed `s ∈ dom (f⋆)` and direction `u`, positivity of
-- `hessian (extendedRealRealPart (f⋆)) s` gives
-- `0 ≤ ⟪u - s, ∇²F_*(s) (u - s)⟫`. Expanding this quadratic form and using the symmetry of a
-- positive Hessian shows
-- `2 ⟪∇²F_*(s) s, u⟫ - ⟪u, ∇²F_*(s) u⟫ ≤ ⟪s, ∇²F_*(s) s⟫`. Relation `(5.1.34)` rewrites the left
-- side as the barrier expression, so the assumed source bound is exactly the defining barrier
-- parameter inequality.
/-- Proposition 5.3.4: let `F_* = extendedRealRealPart (f⋆)`. Assume the canonical dual satisfies
relation `(5.1.34)`, namely `∇F_*(s) = ∇²F_*(s) s`, is standard self-concordant on `dom (f⋆)`,
and obeys `⟪s, ∇²F_*(s) s⟫ ≤ ν` on `dom (f⋆)`. Then `F_*` is a `ν`-self-concordant barrier on
its effective domain. -/
theorem fenchelConjugate_realPart_isSelfConcordantBarrierOnWith
    {ν : NNReal}
    (hdual_gradient_eq_hessian_apply_self :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        ∇ (extendedRealRealPart (f⋆)) s =
          hessian (extendedRealRealPart (f⋆)) s s)
    (hsc : IsStandardSelfConcordantOn (dom (f⋆)) (extendedRealRealPart (f⋆)))
    (hbound :
      ∀ s ∈ dom (f⋆),
        inner ℝ s (hessian (extendedRealRealPart (f⋆)) s s) ≤ (ν : ℝ)) :
    IsSelfConcordantBarrierOnWith (dom (f⋆)) ν (extendedRealRealPart (f⋆)) := by
  refine ⟨hsc, ?_⟩
  intro s hs u
  have hPos : (hessian (extendedRealRealPart (f⋆)) s).IsPositive := hsc.hessian_isPositive hs
  have hnonneg :
      0 ≤
        inner ℝ (u - s)
          (hessian (extendedRealRealPart (f⋆)) s (u - s)) := by
    simpa [real_inner_comm] using hPos.inner_nonneg_right (u - s)
  have hsymm := hPos.isSymmetric
  have hcross :
      inner ℝ s (hessian (extendedRealRealPart (f⋆)) s u) =
        inner ℝ (hessian (extendedRealRealPart (f⋆)) s s) u := by
    calc
      inner ℝ s (hessian (extendedRealRealPart (f⋆)) s u) =
          inner ℝ (hessian (extendedRealRealPart (f⋆)) s u) s := by
            rw [real_inner_comm]
      _ = inner ℝ u (hessian (extendedRealRealPart (f⋆)) s s) := hsymm u s
      _ = inner ℝ (hessian (extendedRealRealPart (f⋆)) s s) u := by
            rw [real_inner_comm]
  have hexpand :
      inner ℝ (u - s) (hessian (extendedRealRealPart (f⋆)) s (u - s)) =
        inner ℝ u (hessian (extendedRealRealPart (f⋆)) s u) -
          2 * inner ℝ (hessian (extendedRealRealPart (f⋆)) s s) u +
          inner ℝ s (hessian (extendedRealRealPart (f⋆)) s s) := by
    simp [sub_eq_add_neg, map_add, map_neg, inner_add_left, inner_add_right, inner_neg_left,
      inner_neg_right, hcross, real_inner_comm]
    ring
  rw [hdual_gradient_eq_hessian_apply_self hs]
  have hmajor :
      2 * inner ℝ (hessian (extendedRealRealPart (f⋆)) s s) u -
          inner ℝ u (hessian (extendedRealRealPart (f⋆)) s u) ≤
        inner ℝ s (hessian (extendedRealRealPart (f⋆)) s s) := by
    linarith [hnonneg, hexpand]
  linarith [hmajor, hbound s hs]

end FenchelDualBarrier

end

/-! ### Theorem_5_3_4 (from Chap05) -/
open Set Topology
open scoped Gradient HessianLocalNorm

noncomputable section

universe u

/- Theorem 5.3.4 lies in the Chapter 5 self-concordant sublevel-barrier domain.

Sampled owner-style declarations in this domain:
* `sublevelLogBarrier` from `Theorem_5_1_4`, the source-facing owner for barriers
  `x ↦ -log (β - f x)`;
* `sublevelLogBarrier_isSelfConcordantOnWith` and
  `IsSelfConcordantOnWith.sublevelLogBarrier_gradient_inner_sq_le` from `Theorem_5_1_4`, the
  canonical self-
  concordance and local-norm-square owners for the strict sublevel barrier;
* `IsSelfConcordantOnWith.pos_smul` from `Corollary_5_1_3`, the owner-level rescaling theorem for
  self-concordant functions;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for barrier
  parameter data;
* `_root_.barrier_parameter_bound_iff_gradient_inner_sq_le` from `Proposition_5_3_3`, the
  canonical bridge from the squared Hessian-gradient estimate to the barrier owner inequality.

Source/core/bridge triage:
* source-facing: the scaled logarithmic barrier `x ↦ -ν log (β - f x)` on the strict level set;
* core/canonical: `IsSelfConcordantOnWith` and `IsSelfConcordantBarrierOnWith`;
* bridge/view: the lower-bound estimate `fStar ≤ f x ≤ β`, used only to identify the owner
  constant from Theorem 5.1.4 with the textbook expression.

Primitive data:
* the source-facing owner `sublevelLogBarrier f β`;
* the self-concordance witness `hself : IsSelfConcordantOnWith dom Mf f`;
* the lower bound `h_lower` and the parameter comparison `hν`.

Derived API:
* the strict sublevel domain itself, kept as the direct set-builder owner used in Theorem 5.1.4;
* standard self-concordance of the scaled barrier, derived by combining
  `sublevelLogBarrier_isSelfConcordantOnWith` with `IsSelfConcordantOnWith.pos_smul`;
* the barrier inequality, obtained from the canonical Proposition 5.3.3 bridge together with the
  owner-level local-norm-square estimate from `Theorem_5_1_4`, instead of a second local barrier
  wrapper.

This file therefore keeps the source-facing scaled logarithmic barrier, but removes the duplicate
wheel proof route in favor of the chapter owners already established upstream. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: apply Theorem 5.1.4 to `φ x = -log (β - f x)` to obtain self-concordance of `φ`
-- on the strict sublevel domain. If `ν = 0`, then the lower bound and the parameter inequality
-- force the strict sublevel domain to be empty, so the barrier statement is vacuous. If `ν > 0`,
-- pick a point in the strict sublevel domain to deduce `β - fStar > 0`, rewrite the owner
-- constant from Theorem 5.1.4 without `Real.toNNReal`, rescale by `ν`, and use Corollary 5.1.3
-- to make the self-concordance constant standard. Finally, Proposition 5.3.3 upgrades the
-- Hessian-gradient inequality from Theorem 5.1.4 to the barrier parameter bound with parameter
-- `ν`.
/-- Theorem 5.3.4: if `f` is self-concordant on `dom` with constant `M_f` and if `f x ≥ f^*` on
`dom`, then for every `ν ≥ 1 + M_f^2 (β - f^*)` the scaled logarithmic barrier
`x ↦ -ν log (β - f x)` is a `ν`-self-concordant barrier on the strict level-set domain
`{x ∈ dom | f x < β}`. -/
theorem sublevelLogBarrier_smul_isSelfConcordantBarrierOnWith
    {dom : Set E} {Mf ν : NNReal} {f : E → ℝ} {β fStar : ℝ}
    (hself : IsSelfConcordantOnWith dom Mf f)
    (h_lower : ∀ ⦃x : E⦄, x ∈ dom → fStar ≤ f x)
    (hν : 1 + (Mf : ℝ) ^ (2 : ℕ) * (β - fStar) ≤ (ν : ℝ)) :
    IsSelfConcordantBarrierOnWith
      {x : E | x ∈ dom ∧ f x < β}
      ν
      ((ν : ℝ) • sublevelLogBarrier f β) := by
  let strictDom : Set E := {x : E | x ∈ dom ∧ f x < β}
  let barrier := sublevelLogBarrier f β
  change IsSelfConcordantBarrierOnWith strictDom ν ((ν : ℝ) • barrier)
  let c : NNReal := NNReal.sqrt (1 + Mf ^ (2 : ℕ) * Real.toNNReal (β - fStar))
  letI : IsSelfConcordantOnWith dom Mf f := hself
  have hsub :
      IsSelfConcordantOnWith strictDom c barrier := by
    simpa [strictDom, barrier, c] using
      sublevelLogBarrier_isSelfConcordantOnWith hself β fStar h_lower
  have hbarrier_bound {x : E} (hx : x ∈ strictDom) (u : E) :
      2 * inner ℝ (∇ (((ν : ℝ) • barrier)) x) u -
          inner ℝ u (hessian (((ν : ℝ) • barrier)) x u) ≤ (ν : ℝ) := by
    have hx_dom : x ∈ dom := hx.1
    have hx_strict : x ∈ strictDom := hx
    have hsub_pos :
        (hessian barrier x).IsPositive :=
      hsub.hessian_isPositive hx_strict
    have hbarrier_one :
        ∀ v : E,
          2 * inner ℝ (∇ barrier x) v -
              inner ℝ v (hessian barrier x v) ≤ ((1 : NNReal) : ℝ) := by
      refine (barrier_parameter_bound_iff_gradient_inner_sq_le hsub_pos).2 ?_
      intro v
      simpa [barrier] using
        (hself.sublevelLogBarrier_gradient_inner_sq_le β hx_dom hx.2 :
          (inner ℝ (∇ barrier x) v) ^ (2 : ℕ) ≤ ‖v‖[barrier; x] ^ (2 : ℕ))
    have hgrad_smul :
        ∇ ((ν : ℝ) • barrier) =
          (ν : ℝ) • ∇ barrier := by
      funext y
      unfold gradient
      rw [fderiv_const_smul_field]
      exact
        (InnerProductSpace.toDual ℝ E).symm.map_smul (ν : ℝ)
          (fderiv ℝ barrier y)
    have hhess_smul :
        hessian ((ν : ℝ) • barrier) =
          (ν : ℝ) • hessian barrier := by
      funext y
      unfold hessian
      rw [hgrad_smul, fderiv_const_smul_field]
    rw [hgrad_smul, hhess_smul]
    simp only [Pi.smul_apply, ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right]
    have hu : 2 * inner ℝ (∇ barrier x) u - inner ℝ u (hessian barrier x u) ≤ (1 : ℝ) := by
      simpa using hbarrier_one u
    calc
      2 * ((ν : ℝ) * inner ℝ (∇ barrier x) u) -
          (ν : ℝ) * inner ℝ u (hessian barrier x u)
          =
            (ν : ℝ) *
              (2 * inner ℝ (∇ barrier x) u - inner ℝ u (hessian barrier x u)) := by
            ring
      _ ≤ (ν : ℝ) * 1 := by
        gcongr
      _ = (ν : ℝ) := by ring
  have hstd :
      IsStandardSelfConcordantOn strictDom ((ν : ℝ) • barrier) := by
    by_cases hstrict_nonempty : strictDom.Nonempty
    · rcases hstrict_nonempty with ⟨x₀, hx₀⟩
      have hβfStar_pos : 0 < β - fStar := by
        nlinarith [h_lower hx₀.1, hx₀.2]
      have hβfStar_nonneg : 0 ≤ β - fStar := le_of_lt hβfStar_pos
      have hMf_term_nonneg : 0 ≤ (Mf : ℝ) ^ (2 : ℕ) * (β - fStar) := by
        positivity
      have hν_pos_real : (0 : ℝ) < (ν : ℝ) := by
        nlinarith [hν, hMf_term_nonneg]
      have hν_pos : 0 < ν := by
        exact_mod_cast hν_pos_real
      have hν_nnreal : 1 + Mf ^ (2 : ℕ) * Real.toNNReal (β - fStar) ≤ ν := by
        rw [Real.toNNReal_of_nonneg hβfStar_nonneg]
        exact_mod_cast hν
      let νu : NNRealˣ := Units.mk0 ν hν_pos.ne'
      letI : IsSelfConcordantOnWith strictDom c barrier := hsub
      have hscaled :
          IsSelfConcordantOnWith strictDom (c / NNReal.sqrt ν)
            ((ν : ℝ) • barrier) := by
        simpa [barrier, c] using
          IsSelfConcordantOnWith.pos_smul hsub νu
      have hscale_le : c / NNReal.sqrt ν ≤ 1 := by
        have hsqrt_le : c ≤ NNReal.sqrt ν := by
          dsimp [c]
          exact (NNReal.sqrt_le_sqrt).2 hν_nnreal
        exact (div_le_one (NNReal.sqrt_pos.2 hν_pos)).2 hsqrt_le
      simpa using hscaled.of_le hscale_le
    · have hstrict_empty : strictDom = ∅ := by
        exact Set.not_nonempty_iff_eq_empty.mp hstrict_nonempty
      refine
        { isOpen_domain := by simp [hstrict_empty]
          contDiffOn := by simp [hstrict_empty]
          convexOn := by
            refine ⟨by simpa [hstrict_empty] using (convex_empty : Convex ℝ (∅ : Set E)), ?_⟩
            intro x hx
            exact (hstrict_empty ▸ hx).elim
          third_deriv_bound := ?_ }
      intro x hx u
      exact (hstrict_empty ▸ hx).elim
  refine
    { toIsStandardSelfConcordantOn := hstd
      barrier_parameter_bound := ?_ }
  intro x hx u
  exact hbarrier_bound hx u

/-! ### Definition_5_3_5_1 (from Chap05) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-
Definition 5.3.5.1 lies in the Chapter 5 self-concordant Newton-iteration domain.

Sampled owner declarations:
* `IsStandardSelfConcordantOn` in `Definition_5_1_1`, the chapter owner for the standard
  self-concordant regime `M_f = 1`;
* `DampedNewton.Method.IsSelfConcordant` in `Definition_5_2_1`, the Chapter 5 refinement of the
  recursive intermediate Newton iterates;
* `NewtonDecrement.ofDetNeZero` in `Definition_5_0_24`, the canonical Chapter 5 owner for the
  Newton decrement at a domain point with nondegenerate Hessian;
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the barrier-specific downstream bridge
  showing how the analytic-center application supplies the standard self-concordant owner used
  here.

Best owner abstraction:
* `source-facing`: a stopped intermediate self-concordant Newton method, namely the recursive
  Newton owner together with the first-stop certificate for the tolerance `β`;
* `core/canonical`: `DampedNewton.Method.IsSelfConcordant dom 1 intermediate` together with its
  owner-level decrement API;
* `bridge/view`: the passage from a `ν`-self-concordant barrier to
  `IsStandardSelfConcordantOn dom F`, and the derived method-level decrement API.

Primitive data:
* the underlying Chapter 1 damped Newton method;
* its Chapter 5 intermediate self-concordant refinement;
* the stopping index and the first-stop inequalities.

Derived API:
* the iterate sequence, domain membership, Hessian nondegeneracy, and update rule, inherited
  from `DampedNewton.Method` and its Chapter 5 refinement;
* the Newton decrement at step `k`, derived canonically from
  `DampedNewton.Method.IsSelfConcordant.decrement`.

This file therefore keeps the source-facing stopped method at the Chapter 5 Newton level: it
extends the Chapter 1 damped Newton owner directly, records the Chapter 5 intermediate
self-concordant property as a separate field, and leaves the analytic-center/barrier hypotheses to
the downstream bridge files where they actually enter. -/

/-- Definition 5.3.5.1: a stopped intermediate self-concordant Newton method on a standard
self-concordant function `F` on `dom`, started at `y₀ ∈ dom` with stopping threshold `β`,
consists of the underlying intermediate self-concordant Newton iteration
`yₖ₊₁ = yₖ - [∇²F(yₖ)]⁻¹ ∇F(yₖ) / (1 + ξₖ)` with
`ξₖ = λₖ^2 / (1 + λₖ)` and `λₖ = ‖∇ F(yₖ)‖*_(yₖ)`, together with a stopping index where the
Newton decrement first drops below the tolerance `β`. In the analytic-center application, the
extra barrier data belongs in downstream assumptions rather than in this owner. -/
structure StoppedIntermediateSelfConcordantNewtonMethod
    {dom : Set E} (F : E → ℝ) [IsStandardSelfConcordantOn dom F] (y0 : dom) (β : ℝ)
    extends DampedNewton.Method F (y0 : E) where
  /-- The underlying Chapter 1 method is the intermediate self-concordant Newton method. -/
  isSelfConcordant :
    toMethod.IsSelfConcordant dom 1 SelfConcordantNewtonVariant.intermediate
  /-- The stopping index at which the Newton decrement meets the tolerance `β`. -/
  stopIndex : ℕ
  /-- Before the stopping index, the Newton decrement remains strictly above `β`. -/
  continue_condition :
    ∀ ⦃k : ℕ⦄, k < stopIndex → β < isSelfConcordant.decrement k
  /-- At the stopping index, the Newton decrement is at most `β`. -/
  stop_condition : isSelfConcordant.decrement stopIndex ≤ β

namespace StoppedIntermediateSelfConcordantNewtonMethod

variable {dom : Set E} {F : E → ℝ} [IsStandardSelfConcordantOn dom F] {y0 : dom} {β : ℝ}

/-- The Newton decrement of the stopped intermediate method at step `k`. -/
abbrev decrement (method : StoppedIntermediateSelfConcordantNewtonMethod F y0 β) (k : ℕ) : ℝ :=
  method.isSelfConcordant.decrement k

/-- Before the stopping index, the stepwise Newton decrement stays above `β`. -/
theorem beta_lt_decrement_of_lt_stopIndex
    (method : StoppedIntermediateSelfConcordantNewtonMethod F y0 β)
    {k : ℕ} (hk : k < method.stopIndex) :
    β < method.decrement k :=
  method.continue_condition hk

/-- At the stopping index, the stepwise Newton decrement is at most `β`. -/
theorem decrement_stopIndex_le
    (method : StoppedIntermediateSelfConcordantNewtonMethod F y0 β) :
    method.decrement method.stopIndex ≤ β :=
  method.stop_condition

end StoppedIntermediateSelfConcordantNewtonMethod

/-! ### Definition_5_3_5_2 (from Chap05) -/
open scoped Gradient

noncomputable section

universe u

/- Definition 5.3.5.2 is a source-facing specialization in the chapter's central-path /
barrier-penalty domain.

Primary domain:
* central paths for barrier-penalized minimization in a real inner-product space.

Sampled owner-style declarations:
* `centralPathPenaltyObjective` in `Definition_5_3_6_1`, the Chapter 5 owner for the penalty
  objective `z ↦ t ⟪c, z⟫ + F z`;
* `centralPathPenaltyObjective_apply` in `Definition_5_3_6_1`, the companion evaluation theorem
  for that owner;
* `IsCentralPath` in `Definition_5_3_6_1`, the owner predicate asserting pointwise minimizers of
  the penalty objective;
* `isCentralPath_iff` in `Definition_5_3_6_1`, the canonical pointwise minimizer bridge.

Best owner abstraction:
* source-facing: the auxiliary central path based at `y₀`;
* core/canonical: `IsCentralPath dom (-∇ F (y0 : E)) F yStar`;
* bridge/view: the specialization of `centralPathPenaltyObjective` to `c = -∇ F (y0 : E)`.

Primitive data:
* a domain `dom : Set E`;
* a barrier `F : E → ℝ`;
* a base point `y0 : dom`;
* a trajectory `yStar : Set.Ici (0 : ℝ) → dom`.

Derived API:
* the specialized penalty formula
  `centralPathPenaltyObjective (-∇ F (y0 : E)) F t z =
    F z - (t : ℝ) * inner ℝ (∇ F (y0 : E)) z`;
* the pointwise minimizer expansion of `IsCentralPath dom (-∇ F (y0 : E)) F yStar`.

Source/core/bridge triage:
* source-facing: the auxiliary central path obtained by choosing the linear objective
  `c = -∇ F(y₀)`;
* core/canonical: `centralPathPenaltyObjective` and `IsCentralPath`;
* bridge/view: the specialization to `c = -∇ F(y₀)`.

The previous version restated the specialized `IsMinOn` condition directly. This file now reuses
the Chapter 5 owner `IsCentralPath` and keeps the textbook formula only as a thin specialization
bridge. -/

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {dom : Set E} (F : E → ℝ) (y0 : dom)
variable (yStar : Set.Ici (0 : ℝ) → dom)

/- Definition 5.3.5.2 specializes the central-path owner to the choice
`c = -∇ F(y₀)`. -/
#check IsCentralPath dom (-∇ F (y0 : E)) F yStar

/- The specialized penalty objective is exactly the textbook auxiliary-central-path formula. -/
#check
  (show
      ∀ t : Set.Ici (0 : ℝ), ∀ z : E,
        centralPathPenaltyObjective (-∇ F (y0 : E)) F t z =
          F z - (t : ℝ) * inner ℝ (∇ F (y0 : E)) z
    from fun t z ↦ by
      rw [centralPathPenaltyObjective_apply]
      simp [sub_eq_add_neg, add_comm])

/- Expanding the specialized owner recovers the source-facing pointwise minimizer statement. -/
#check
  (show
      IsCentralPath dom (-∇ F (y0 : E)) F yStar ↔
        ∀ t : Set.Ici (0 : ℝ),
          IsMinOn
            (fun z ↦ F z - (t : ℝ) * inner ℝ (∇ F (y0 : E)) z)
            dom
            (yStar t : E)
    from by
      have hobjective :
          ∀ t : Set.Ici (0 : ℝ),
            centralPathPenaltyObjective (-∇ F (y0 : E)) F t =
              fun z ↦ F z - (t : ℝ) * inner ℝ (∇ F (y0 : E)) z := by
        intro t
        funext z
        rw [centralPathPenaltyObjective_apply]
        simp [sub_eq_add_neg, add_comm]
      constructor
      · intro h t
        rw [← hobjective t]
        exact h t
      · intro h t
        rw [hobjective t]
        exact h t)

end

/-! ### Definition_5_3_5_3 (from Chap05) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-
Definition 5.3.5.3 lies in the Chapter 5 self-concordant-barrier / stopped intermediate-Newton
domain.

Sampled owner declarations:
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for a
  `ν`-self-concordant barrier, which canonically supplies `IsStandardSelfConcordantOn dom F`;
* `StoppedIntermediateSelfConcordantNewtonMethod` in `Definition_5_3_5_1`, the source-facing
  owner for the recursive intermediate Newton iterates together with the first-stop certificate;
* `DampedNewton.Method.IsSelfConcordant.succ_eq_nextPoint` in `Definition_5_2_1`, the canonical
  recursion theorem identifying each successor iterate with
  `selfConcordantNewtonNextPoint F 1 .intermediate ...`;
* `StoppedIntermediateSelfConcordantNewtonMethod.decrement` in `Definition_5_3_5_1`, the
  canonical owner-level Newton decrement API.

Best owner abstraction:
* source-facing: the stopped intermediate Newton method for minimizing a `ν`-self-concordant
  barrier;
* core/canonical: `StoppedIntermediateSelfConcordantNewtonMethod F y0 β`;
* bridge/view: the inferable parent instance `IsStandardSelfConcordantOn dom F` supplied by the
  barrier owner.

Primitive data:
* the stopped intermediate Newton method itself.

Derived API:
* the recursive update
  `yₖ₊₁ = selfConcordantNewtonNextPoint F 1 SelfConcordantNewtonVariant.intermediate yₖ ...`;
* the stopping index and decrement bounds.

Definition 5.3.5.3 therefore does not introduce a second owner carrying auxiliary path-following
data. It is the barrier specialization of the existing stopped intermediate Newton owner from
Definition 5.3.5.1.
-/

section

variable {dom : Set E} {F : E → ℝ} {ν : NNReal} [IsSelfConcordantBarrierOnWith dom ν F]
variable {y0 : dom} {β : ℝ}

/- Definition 5.3.5.3: for a `ν`-self-concordant barrier `F` on `dom`, the stopped intermediate
Newton method started at `y₀` with tolerance `β` is exactly the chapter owner
`StoppedIntermediateSelfConcordantNewtonMethod F y0 β`. The barrier hypothesis contributes only
the inferable standard self-concordance needed by that owner. -/
#check (StoppedIntermediateSelfConcordantNewtonMethod F y0 β)

end

end

/-! ### Theorem_5_3_5 (from Chap05) -/
noncomputable section

universe u

variable {E : Type u}

/- Theorem 5.3.5 lies in the Chapter 5 self-concordant-barrier / epigraph-lifting domain.

Sampled owner declarations in this domain:
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for barrier data;
* `sublevelLogBarrier` and `sublevelLogBarrier_isSelfConcordantOnWith` from `Theorem_5_1_4`, the
  canonical strict-sublevel logarithmic-barrier owner and theorem;
* `constrainedEpigraph` from `Chap03/Definition_3_3`, the chapter owner for the closed epigraph,
  whose naming pattern determines the strict epigraph owner in this file;
* mathlib `WithLp 2 (E × ℝ)` together with `WithLp.ofLp`, which supplies the canonical `L²`
  product owner and its bridge back to raw pairs;
* `selfConcordantBarrier_add_linear_isStandardSelfConcordantOn` from `Theorem_5_3_1`, the
  canonical self-concordance theorem for adding a linear term.

Source/core/bridge triage:
* source-facing: the textbook strict epigraph domain on raw pairs and the barrier
  `(x, t) ↦ f x - log (t - f x)`;
* core/canonical: `IsSelfConcordantBarrierOnWith` on the canonical `L²` product owner
  `WithLp 2 (E × ℝ)`;
* bridge/view: the raw-pair formulas transported to that owner through `WithLp.ofLp`.

Primitive data:
* the base domain `dom`;
* the base barrier `f`;
* the barrier parameter `ν`;
* the owner witness `h : IsSelfConcordantBarrierOnWith dom ν f`.

Derived API:
* the source-facing raw-pair strict epigraph `strictConstrainedEpigraph dom f`;
* the source-facing raw-pair barrier `epigraphLogBarrier f`.

This file keeps the strict epigraph domain and barrier as source-facing raw-pair data, but the
main numbered theorem lives on the canonical `L²` product owner `WithLp 2 (E × ℝ)`, so the
barrier statement uses the textbook formulas only through the raw-pair bridge `WithLp.ofLp`. -/

/-- The strict epigraph `{(x, t) | x ∈ dom ∧ f x < t}` on raw pairs. -/
def strictConstrainedEpigraph (dom : Set E) (f : E → ℝ) : Set (E × ℝ) :=
  {p | p.1 ∈ dom ∧ f p.1 < p.2}

/-- Membership in `strictConstrainedEpigraph dom f` is the textbook strict epigraph condition. -/
@[simp] theorem mem_strictConstrainedEpigraph_iff
    {dom : Set E} {f : E → ℝ} {p : E × ℝ} :
    p ∈ strictConstrainedEpigraph dom f ↔ p.1 ∈ dom ∧ f p.1 < p.2 :=
  Iff.rfl

/-- The textbook epigraph barrier on raw pairs `(x, t) ↦ f x - log (t - f x)`, implemented as
the sum of the base term `x ↦ f x` and the canonical strict-sublevel barrier for the epigraph
gap `f x - t`. -/
def epigraphLogBarrier (f : E → ℝ) : E × ℝ → ℝ :=
  fun p ↦ f p.1 + sublevelLogBarrier (fun q : E × ℝ ↦ f q.1 - q.2) 0 p

/-- Evaluating `epigraphLogBarrier f` recovers the textbook raw-pair formula. -/
@[simp] theorem epigraphLogBarrier_apply (f : E → ℝ) (p : E × ℝ) :
    epigraphLogBarrier f p = f p.1 - Real.log (p.2 - f p.1) :=
  by
    simp [epigraphLogBarrier, sublevelLogBarrier, sub_eq_add_neg, add_comm]

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "Z" => WithLp 2 (E × ℝ)
local notation "ofZ" => (WithLp.ofLp : Z → E × ℝ)

-- Proof sketch: regard `z ↦ f (ofZ z).1` as the pullback of the given barrier along the first
-- projection on the canonical `L²` product owner `Z = WithLp 2 (E × ℝ)`, and regard
-- `sublevelLogBarrier (fun q ↦ f q.1 - q.2) 0` as the logarithmic barrier of the strict
-- sublevel set of the epigraph gap. The pullback theorem, the logarithmic-barrier theorem, and
-- the barrier-sum theorem then give a self-concordant barrier with parameter `ν + 1` on the
-- pulled-back strict epigraph domain.
/-- Theorem 5.3.5: if `f` is a `ν`-self-concordant barrier on `dom`, then
the textbook epigraph barrier, viewed on the canonical `L²` product owner
`WithLp 2 (E × ℝ)` through `WithLp.ofLp`, is a `(\nu + 1)`-self-concordant barrier on the
strict epigraph domain. -/
theorem epigraphLogBarrier_isSelfConcordantBarrierOnWith
    {dom : Set E} {ν : NNReal} {f : E → ℝ}
    (h : IsSelfConcordantBarrierOnWith dom ν f) :
    IsSelfConcordantBarrierOnWith
      (ofZ ⁻¹' strictConstrainedEpigraph dom f)
      (ν + 1)
      (epigraphLogBarrier f ∘ ofZ) := sorry

end
