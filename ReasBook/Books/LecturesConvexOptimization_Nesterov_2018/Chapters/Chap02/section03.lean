import Mathlib
import Mathlib.Analysis.Convex.Strong
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_3 (from Chap02) -/
section

universe u v

variable {𝕜 : Type u} {E : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]

/- Definition 2.3 lies in the convex-geometry domain for subsets of finite-dimensional real vector
spaces.

Primary domain:
* convex subsets `Q ⊆ ℝⁿ`

Sampled owner-style declarations:
* mathlib `Convex`
* mathlib `convex_iff_add_mem`
* mathlib `Convex.segment_subset`
* mathlib `Convex.inter`

Best owner abstraction:
* `Convex ℝ Q`

Primitive data:
* the subset `Q : Set (EuclideanSpace ℝ (Fin n))`

Derived API:
* the textbook two-point convex-combination criterion `convex_iff_add_mem`
* segment closure via `Convex.segment_subset`
* stability under intersection via `Convex.inter`

Source/core/bridge triage:
* source-facing: a convex subset of `ℝⁿ`
* core/canonical: `Convex ℝ Q`
* bridge/view: the two-point convex-combination membership formula

This file therefore keeps no local wrapper such as `IsConvexSet`. Downstream files should use the
owner predicate `Convex ℝ Q` directly, and use `convex_iff_add_mem` only as the companion
source-style specification theorem. This file is therefore recall-only. -/

/- The core owner is the canonical type expression `Convex 𝕜 : Set E → Prop`. -/
#check (Convex 𝕜 : Set E → Prop)

/-- Helper for Definition 2.3: the canonical owner predicate `Convex 𝕜 s` is equivalent to the
textbook two-point convex-combination membership condition. -/
theorem convex_iff_two_point_combination_mem {s : Set E} :
    Convex 𝕜 s ↔
      ∀ ⦃x : E⦄, x ∈ s → ∀ ⦃y : E⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄,
        0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ s := by
  -- This is exactly the source-facing reformulation already provided by mathlib.
  simpa using
    (convex_iff_add_mem :
      Convex 𝕜 s ↔
        ∀ ⦃x : E⦄, x ∈ s → ∀ ⦃y : E⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄,
          0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ s)

/-- Definition 2.3: a set `Q ⊆ ℝⁿ` is convex exactly when it contains every two-point convex
combination `α • x + (1 - α) • y` with `α ∈ [0, 1]`. -/
theorem convex_iff_unit_interval_smul_add_mem {n : ℕ}
    {Q : Set (EuclideanSpace ℝ (Fin n))} :
    Convex ℝ Q ↔
      ∀ ⦃x : EuclideanSpace ℝ (Fin n)⦄, x ∈ Q →
        ∀ ⦃y : EuclideanSpace ℝ (Fin n)⦄, y ∈ Q →
          ∀ ⦃α : ℝ⦄, 0 ≤ α → α ≤ 1 → α • x + (1 - α) • y ∈ Q := by
  constructor
  · intro hQ x hx y hy α hα hα_le_one
    -- Use the complementary weight `1 - α`, which is nonnegative on `[0, 1]`.
    exact hQ hx hy hα (sub_nonneg.mpr hα_le_one) (by ring)
  · intro hQ x hx y hy α β hα hβ hαβ
    -- Rewrite the second weight as `1 - α` to return to the source-facing criterion.
    have hα_le_one : α ≤ 1 := by
      linarith
    have hmem : α • x + (1 - α) • y ∈ Q := hQ hx hy hα hα_le_one
    have hβ_eq : β = 1 - α := by
      linarith
    simpa [hβ_eq] using hmem

recall convex_iff_add_mem

recall Convex.segment_subset

recall Convex.inter

end

/-! ### Lemma_2_3 (from Chap02) -/
noncomputable section

open scoped SeminormDualNorm

/- Primary domain: dual norms induced by the ambient norm on a real inner-product space, with the
source-facing specialization to the Euclidean closed unit ball in `ℝⁿ`.

Sampled owner-style declarations:
* `normSeminorm`
* `Seminorm.dualNorm`
* `Seminorm.dualNorm_apply`
* `InnerProductSpace.toDual`
* `ContinuousLinearMap.sSup_unitClosedBall_eq_norm`

Source/core/bridge triage:
* source-facing: `unit_closed_ball_support_function_eq_norm`
* core/canonical: `Seminorm.dualNorm (normSeminorm ℝ E)`
* bridge/view: `Seminorm.dualNorm_normSeminorm_eq_norm`

Primitive data:
* the ambient seminorm `normSeminorm ℝ E`

Derived API:
* `Seminorm.dualNorm_apply` rewrites the owner object as a support function over `{x | ‖x‖ ≤ 1}`
* `unit_closed_ball_support_function_eq_norm` is the Euclidean closed-ball reformulation
-/

namespace Seminorm

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- On the symmetric norm closed unit ball of a real normed space, the supremum of a real
continuous linear functional is its operator norm. -/
-- Proof sketch: `ContinuousLinearMap.sSup_unitClosedBall_eq_norm` gives the supremum of the
-- absolute value. Since the unit ball is stable under negation, every absolute-value image point
-- is realized as an ordinary image point, so the two suprema agree.
private theorem ContinuousLinearMap.sSup_unitClosedBall_eq_norm_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E →L[ℝ] ℝ) :
    sSup (f '' Metric.closedBall (0 : E) 1) = ‖f‖ := by
  let S : Set ℝ := f '' Metric.closedBall (0 : E) 1
  let T : Set ℝ := (fun x : E ↦ |f x|) '' Metric.closedBall (0 : E) 1
  have hS_nonempty : S.Nonempty := ⟨0, ⟨0, by simp, by simp⟩⟩
  have hS_bound : ∀ y ∈ S, y ≤ ‖f‖ := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx_norm : ‖x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hfx : |f x| ≤ ‖f‖ * ‖x‖ := by
      simpa [Real.norm_eq_abs] using f.le_opNorm x
    calc
      f x ≤ |f x| := le_abs_self _
      _ ≤ ‖f‖ * ‖x‖ := hfx
      _ ≤ ‖f‖ * 1 := mul_le_mul_of_nonneg_left hx_norm (norm_nonneg _)
      _ = ‖f‖ := by ring
  have hS_bdd : BddAbove S := ⟨‖f‖, hS_bound⟩
  have hT_nonempty : T.Nonempty := ⟨0, ⟨0, by simp, by simp⟩⟩
  have hT_subset : T ⊆ S := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    by_cases hfx : 0 ≤ f x
    · exact ⟨x, hx, by simp [abs_of_nonneg hfx]⟩
    · refine ⟨-x, by simpa [Metric.mem_closedBall, dist_eq_norm] using hx, ?_⟩
      simp [abs_of_neg (lt_of_not_ge hfx)]
  have hT_le : ∀ y ∈ T, y ≤ sSup S := fun y hy ↦ le_csSup hS_bdd (hT_subset hy)
  have hsSup_T_le : sSup T ≤ sSup S := csSup_le hT_nonempty hT_le
  have hT_eq : sSup T = ‖f‖ := by
    simpa [T, Real.norm_eq_abs] using ContinuousLinearMap.sSup_unitClosedBall_eq_norm f
  have hsSup_S_le : sSup S ≤ ‖f‖ := csSup_le hS_nonempty hS_bound
  exact le_antisymm hsSup_S_le <| by
    rw [← hT_eq]
    exact hsSup_T_le

/-- Lemma 2.3 in owner form: on a finite-dimensional real inner-product space, the dual norm
induced by the ambient norm is the ambient norm. -/
-- Proof sketch: rewrite the dual norm through `Seminorm.dualNorm_apply`, identify the underlying
-- real functional with `InnerProductSpace.toDual ℝ E s`, and then use the operator-norm formula
-- for real functionals on the symmetric unit ball.
theorem dualNorm_normSeminorm_eq_norm [FiniteDimensional ℝ E] (s : E) :
    ‖s‖[normSeminorm ℝ E,*] = ‖s‖ := by
  rw [dualNorm_apply]
  have hball : {x : E | (normSeminorm ℝ E) x ≤ 1} = Metric.closedBall (0 : E) 1 := by
    ext x
    simp [Metric.mem_closedBall, dist_eq_norm, coe_normSeminorm]
  rw [hball]
  simpa [InnerProductSpace.toDual_apply_apply] using
    ContinuousLinearMap.sSup_unitClosedBall_eq_norm_real (InnerProductSpace.toDual ℝ E s)

end

end Seminorm

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Lemma 2.3: the support function of the Euclidean closed unit ball in `ℝ^n` at `s` equals the
Euclidean norm of `s`, i.e. `√(∑ i, (s i)^2)`. -/
-- Proof sketch: this is the Euclidean closed-ball reformulation of
-- `Seminorm.dualNorm_normSeminorm_eq_norm`.
theorem unit_closed_ball_support_function_eq_norm (s : E) :
    sSup ((fun x : E ↦ inner ℝ s x) '' Metric.closedBall (0 : E) 1) = ‖s‖ := by
  simpa [Metric.mem_closedBall, dist_eq_norm] using
    Seminorm.dualNorm_normSeminorm_eq_norm s

/-! ### Proposition_2_3 (from Chap02) -/
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace StrongConvexOn

/- Proposition 2.3 is a bridge/view theorem in the strong-convexity owner API.

Sampled owner-style declarations:
* mathlib `UniformConvexOn`
* mathlib `UniformConvexOn.add`
* mathlib `ConvexOn.uniformConvexOn_zero`
* mathlib `StrongConvexOn`

Best owner abstraction:
* `StrongConvexOn Q μ g`

Primitive data:
* a convex perturbation `ConvexOn ℝ Q f`
* a strongly convex owner hypothesis `StrongConvexOn Q μ g`

Derived API:
* the strong convexity of `f + g`, obtained by viewing `hf` as zero-modulus uniform convexity and
  then applying the canonical modulus-addition theorem

Source/core/bridge triage:
* bridge/view: this proposition derives a new `StrongConvexOn` statement from the owner theorem
  `UniformConvexOn.add`; it does not define a new strong-convexity notion
-/

variable {Q : Set E} {f g : E → ℝ} {μ : ℝ}

/-- Proposition 2.3: on a convex subset `Q` of a real normed space, adding a convex function to a
`μ`-strongly convex function yields another `μ`-strongly convex function with respect to the
ambient norm. -/
theorem add_convexOn
    (hg : StrongConvexOn Q μ g) (hf : ConvexOn ℝ Q f) :
    StrongConvexOn Q μ (f + g) := by
  -- View the convex summand as zero-modulus uniform convexity, then add moduli.
  simpa [StrongConvexOn] using hf.uniformConvexOn_zero.add hg

end StrongConvexOn

/-! ### Text_2_3 (from Chap02) -/
open scoped Gradient ProjectedGradient StrongConvexSmooth

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: whole-space estimate-sequence lower bounds in smooth strongly convex
optimization on a real Hilbert space.

Owner declarations sampled for this refinement:
* `exactStep_objective_lower_bound` in `Theorem_2_43`, the chapter owner theorem for the
  whole-space exact-step lower bound;
* `gradientMapping_objective_lower_bound` in `Theorem_2_36`, the upstream set-level owner whose
  `Q = Set.univ` specialization yields `exactStep_objective_lower_bound`;
* `whole_space_phi_star_lower_bound_intermediate` in `Remark_2_20_1`, the owner whole-space
  estimate-sequence lower bound before regrouping the inner-product terms;
* `whole_space_phi_star_lower_bound_of_strong_objective_lower_bound` in `Remark_2_20_1`, the owner
  whole-space estimate-sequence lower bound after inserting the strong objective estimate.

Best owner abstraction:
* source-facing: the unconstrained estimate-sequence inequalities written with `gradientStep` and
  `∇`;
* core/canonical: `simpleSetEstimatingValue`, `simpleSetEstimatingCenter`, and
  `exactStep_objective_lower_bound`;
* bridge/view: the specialization `Q = Set.univ` connecting the set-level projected-gradient
  owner to the whole-space exact-step owner.

Primitive data:
* the objective `f`, the initial point `x0`, the parameters `(μ, L, gamma0)`, the stage data
  `(y, α)`, and the comparison point `xk`;
* the stage objects `φ_k^*`, `φ_{k+1}^*`, `γ_k`, `γ_{k+1}`, and `v_k`.

Derived API:
* the strong lower bound on `f xk` obtained from `exactStep_objective_lower_bound` at
  `xBar = y k`, `γ = L`, and `x = xk`;
* the pre-regrouped whole-space lower bound for `φ_{k+1}^*`;
* the final regrouped whole-space lower bound from Text 2.3.

This file keeps Text 2.3 at the source-facing whole-space theorem layer and reuses the existing
owner theorems instead of introducing a parallel wrapper API. -/

section

variable
    (f : E → ℝ) (x0 : E)
    (μ : ℝ) (L : NNRealˣ) (gamma0 : ℝ)
    (y : ℕ → E) (α : ℕ → ℝ)
    (hγ : ∀ k, estimatingSequenceCurvature μ gamma0 α (k + 1) ≠ 0)
    (k : ℕ) (xk : E)

local notation "gammaK" => estimatingSequenceCurvature μ gamma0 α k
local notation "gammaKp1" => estimatingSequenceCurvature μ gamma0 α (k + 1)

local notation "phiK" =>
  simpleSetEstimatingValue
    (Set.univ : Set E) Set.univ_nonempty isClosed_univ convex_univ
    f x0 μ L gamma0 y α k

local notation "phiKp1" =>
  simpleSetEstimatingValue
    (Set.univ : Set E) Set.univ_nonempty isClosed_univ convex_univ
    f x0 μ L gamma0 y α (k + 1)

local notation "vK" =>
  simpleSetEstimatingCenter
    (Set.univ : Set E) Set.univ_nonempty isClosed_univ convex_univ
    f x0 μ L gamma0 y α k

local notation "yK" => y k

local notation "transportCoeff" =>
  α k * (1 - α k) * gammaK / gammaKp1

local notation "strongObjectiveLowerRhs" =>
  f (gradientStep f yK L) +
    inner ℝ (∇ f yK) (xk - yK) +
      (1 / (2 * (L : ℝ))) * ‖∇ f yK‖ ^ (2 : ℕ) +
        (μ / 2) * ‖xk - yK‖ ^ (2 : ℕ)

local notation "intermediateRhs" =>
  (1 - α k) * f xk +
    α k * f (gradientStep f yK L) +
      (α k / (2 * (L : ℝ)) - α k ^ (2 : ℕ) / (2 * gammaKp1)) * ‖∇ f yK‖ ^ (2 : ℕ) +
        transportCoeff * inner ℝ (∇ f yK) (vK - yK)

local notation "finalRhs" =>
  f (gradientStep f yK L) +
    (1 / (2 * (L : ℝ)) - α k ^ (2 : ℕ) / (2 * gammaKp1)) * ‖∇ f yK‖ ^ (2 : ℕ) +
      (1 - α k) * inner ℝ (∇ f yK)
        (((α k * gammaK) / gammaKp1) • (vK - yK) + (xk - yK))

/-- Text 2.3: assuming the whole-space estimate-sequence setting and `φ_k^* ≥ f(x_k)`, the lower
bound at `x = x_k`, `xBar = y_k` implies the regrouped lower bound for `φ_{k+1}^*`. -/
-- Proof sketch: first specialize `exactStep_objective_lower_bound` to `xBar = y k`, `γ = L`, and
-- `x = xk` to obtain the strong lower model at `xk`, then feed that estimate into
-- `whole_space_phi_star_lower_bound_of_strong_objective_lower_bound` and collect the
-- inner-product terms into the final displayed expression.
theorem whole_space_phi_star_lower_bound_of_phi_star_ge_objective
    (hf : f ∈ 𝓢[μ, (L : ℝ)]¹¹)
    (halpha_k : α k ≤ 1)
    (htransportCoeff : 0 ≤ transportCoeff)
    (hphi_k : f xk ≤ phiK) :
    phiKp1 ≥ finalRhs := by
  have hμ : 0 ≤ μ := (mem_S11_iff.mp hf).mu_pos.le
  have hobjective_lower :
      f xk ≥ strongObjectiveLowerRhs :=
    by
      simpa using exactStep_objective_lower_bound yK xk hf le_rfl
  simpa using
    whole_space_phi_star_lower_bound_of_strong_objective_lower_bound
      f x0 μ L gamma0 y α k xk halpha_k htransportCoeff hμ hphi_k hobjective_lower

end

/-! ### Theorem_2_3 (from Chap02) -/
noncomputable section

universe u

open AffineMap
open InnerProductSpace
open scoped ConvexC1

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 2.3 lies in Euclidean first-order convex analysis on convex sets.

Sampled owner-style declarations before refining this file:
* mathlib `ConvexOn`
* mathlib `gradientWithin` / `HasGradientWithinAt`
* `ConvexOn.lower_tangent_plane` in `Definition_2_2`, the chapter owner theorem for the
  source-facing first-order inequality
* `ConvexC1On` in `Definition_2_4`, the chapter owner packaging of the textbook `C¹` hypothesis

Best owner abstraction:
* `ConvexOn ℝ Q f`, with `gradientWithin f Q` as the canonical first-order object derived from the
  within-set differentiability owner predicate `DifferentiableOn ℝ f Q`

Primitive data:
* the feasible set `Q`
* the objective `f`
* the convexity owner predicate `ConvexOn ℝ Q f`
* the within-set differentiability owner predicate `DifferentiableOn ℝ f Q`

Derived API:
* `GradientMonotoneOn Q f`, the bridge property recording monotonicity of `gradientWithin f Q`
* `convexOn_iff_gradient_monotone`, the source-facing equivalence between convexity and gradient
  monotonicity
* `ConvexOn.gradient_monotone` and `ConvexOn.of_gradient_monotone`, the owner forward and reverse
  implications
* `convexC1On_iff_gradient_monotone`, the textbook `C¹` bridge through the chapter owner
  `ConvexC1On`

Source/core/bridge triage:
* source-facing: Theorem 2.3 as the equivalence between convexity and monotonicity of the
  within-set gradient; the textbook `C¹` hypothesis is routed through `ConvexC1On`
* core/canonical: `ConvexOn ℝ Q f`
* bridge/view: passage through the lower-tangent-plane owner API from `Definition_2_2` and the
  chapter owner `ConvexC1On`
-/

section

variable {Q : Set E} {f : E → ℝ}

local notation "gradQ" => gradientWithin f Q

/-- The within-set gradient of `f` is monotone on `Q` when its increment has nonnegative
inner-product pairing with every feasible displacement. -/
def GradientMonotoneOn (Q : Set E) (f : E → ℝ) : Prop :=
  ∀ ⦃x y : E⦄, x ∈ Q → y ∈ Q →
    0 ≤ inner ℝ (gradientWithin f Q x - gradientWithin f Q y) (x - y)

namespace ConvexOn

/-- A convex function with within-set differentiability on `Q` has monotone within-set gradient on
that set. -/
-- Proof sketch: apply the first-order convexity inequality on `Q` at `x` and at `y`, expressed
-- with `gradientWithin f Q x` and `gradientWithin f Q y`, and add the two inequalities.
theorem gradient_monotone
    (hf_conv : ConvexOn ℝ Q f)
    (hf_diff : DifferentiableOn ℝ f Q) :
    GradientMonotoneOn Q f := by
  refine fun {x} ↦ ?_
  refine fun {y} ↦ ?_
  intro hx hy
  -- Compare the two tangent-plane inequalities based at `x` and `y`.
  have hxy := hf_conv.lower_tangent_plane x hx (hf_diff x hx) y hy
  have hyx := hf_conv.lower_tangent_plane y hy (hf_diff y hy) x hx
  have hsum :
      inner ℝ (gradQ x) (y - x) + inner ℝ (gradQ y) (x - y) ≤ 0 := by
    linarith
  -- Normalize the sum into the monotonicity pairing.
  have hrewrite :
      inner ℝ (gradQ x - gradQ y) (x - y) =
        -(inner ℝ (gradQ x) (y - x) + inner ℝ (gradQ y) (x - y)) := by
    have hxswap :
        inner ℝ (gradQ x) (x - y) = -inner ℝ (gradQ x) (y - x) := by
      calc
        inner ℝ (gradQ x) (x - y) = inner ℝ (gradQ x) (-(y - x)) := by
                congr 2
                abel
        _ = -inner ℝ (gradQ x) (y - x) := by rw [inner_neg_right]
    calc
      inner ℝ (gradQ x - gradQ y) (x - y)
          = inner ℝ (gradQ x) (x - y) - inner ℝ (gradQ y) (x - y) := by
              rw [inner_sub_left]
      _ = -(inner ℝ (gradQ x) (y - x)) - inner ℝ (gradQ y) (x - y) := by
            rw [hxswap]
      _ = -(inner ℝ (gradQ x) (y - x) + inner ℝ (gradQ y) (x - y)) := by
            ring
  rw [hrewrite]
  linarith

/-- Gradient monotonicity on a convex set forces convexity of a within-set differentiable function
there. -/
-- Proof sketch: use `convexOn_iff_lower_tangent_plane` from `Definition_2_2`; the monotonicity
-- hypothesis upgrades the tangent inequality for the within-set gradient to the owner convexity
-- predicate.
theorem of_gradient_monotone
    (hQ : Convex ℝ Q)
    (hf_diff : DifferentiableOn ℝ f Q)
    (hmono : GradientMonotoneOn Q f) :
    ConvexOn ℝ Q f := by
  refine (convexOn_iff_lower_tangent_plane hQ hf_diff).2 ?_
  refine fun {x} ↦ ?_
  intro hx
  refine fun {y} ↦ ?_
  intro hy
  -- Move from the source segment to a single mean-value point on that segment.
  have hmvt :
      ∃ z ∈ segment ℝ x y, f y - f x = inner ℝ (gradQ z) (y - x) := by
    rcases domain_mvt
        (fun z hz ↦ (hf_diff z hz).hasGradientWithinAt.hasFDerivWithinAt)
        hQ hx hy with ⟨z, hz, hEq⟩
    refine ⟨z, hz, ?_⟩
    simpa [toDual_apply_apply] using hEq
  rcases hmvt with ⟨z, hzseg, hEq⟩
  rw [segment_eq_image_lineMap] at hzseg
  rcases hzseg with ⟨t, ht, rfl⟩
  have hline_mem : lineMap x y t ∈ Q := hQ.mapsTo_lineMap hx hy ht
  -- Use monotonicity between the segment point and the left endpoint to compare directional
  -- derivatives along `y - x`.
  have hinner_mono :
      0 ≤ inner ℝ (gradQ (lineMap x y t) - gradQ x) (y - x) := by
    have hseg :
        0 ≤ inner ℝ (gradQ (lineMap x y t) - gradQ x) (lineMap x y t - x) := by
      exact hmono hline_mem hx
    by_cases ht0 : t = 0
    · subst ht0
      simp
    · have htne : 0 ≠ t := by
        simpa [eq_comm] using ht0
      have htpos : 0 < t := lt_of_le_of_ne ht.1 htne
      have hline : lineMap x y t - x = t • (y - x) := by
        simpa [vsub_eq_sub] using lineMap_vsub_left x y t
      rw [hline, real_inner_smul_right] at hseg
      exact (mul_nonneg_iff_of_pos_left htpos).mp hseg
  -- Translate the mean-value identity into the lower tangent inequality at `x`.
  have hcompare :
      0 ≤ inner ℝ (gradQ (lineMap x y t)) (y - x) - inner ℝ (gradQ x) (y - x) := by
    simpa [inner_sub_left] using hinner_mono
  linarith

end ConvexOn

/-- Theorem 2.3, stated on the canonical real Hilbert-space owner layer: for a convex set `Q` and
a function `f : E → ℝ` that is differentiable on `Q`, convexity of `f` on `Q` is equivalent to
monotonicity of its within-set gradient on `Q`; the main theorem is stated with the owner
hypothesis `DifferentiableOn ℝ f Q`, and the textbook `C¹` version appears below as a companion
bridge through `ConvexC1On`. The textbook Euclidean theorem is the finite-dimensional
specialization. -/
-- Proof sketch: combine the internal forward and reverse implications between convexity and the
-- monotonicity inequality for `gradientWithin f Q`.
theorem convexOn_iff_gradient_monotone
    (hQ : Convex ℝ Q)
    (hf_diff : DifferentiableOn ℝ f Q) :
    ConvexOn ℝ Q f ↔ GradientMonotoneOn Q f :=
  ⟨fun hf_conv ↦ ConvexOn.gradient_monotone hf_conv hf_diff,
    ConvexOn.of_gradient_monotone hQ hf_diff⟩

/-- The textbook `C¹` specialization of Theorem 2.3, expressed through the Chapter 2 owner
notation `𝓕¹(Q)`; the statement is given on the canonical real Hilbert-space layer, so the
original Euclidean theorem is a direct specialization. -/
theorem convexC1On_iff_gradient_monotone
    (hQ : Convex ℝ Q) :
    f ∈ 𝓕¹(Q) ↔
      ContDiffOn ℝ 1 f Q ∧ GradientMonotoneOn Q f := by
  constructor
  · intro hf
    have hf_diff : DifferentiableOn ℝ f Q :=
      (convexC1On_contDiffOn hf).differentiableOn (by simp)
    refine ⟨convexC1On_contDiffOn hf, ?_⟩
    exact
      (convexOn_iff_gradient_monotone hQ hf_diff).mp (convexC1On_convexOn hf)
  · rintro ⟨hf_contDiff, hmono⟩
    have hf_diff : DifferentiableOn ℝ f Q := hf_contDiff.differentiableOn (by simp)
    refine ⟨hf_contDiff, ?_⟩
    exact (convexOn_iff_gradient_monotone hQ hf_diff).mpr hmono

end

end
