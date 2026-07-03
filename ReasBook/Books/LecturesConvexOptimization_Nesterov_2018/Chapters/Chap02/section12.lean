import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_12 (from Chap02) -/
open scoped CoordinateSubspace

/- Definition 2.12 is a source-facing recall in the finite-dimensional linear-algebra domain of
coordinate subspaces of `ℝⁿ`.

Primary domain:
- linear-algebraic coordinate subspaces in Euclidean space.

Sampled owner-style declarations:
- `coordinateSubspace k n`, the chapter's canonical `Submodule` owner for `ℝ^{k,n}`;
- `mem_coordinateSubspace_iff`, the coordinatewise derived membership criterion;
- the scoped notation `ℝ^{k,n}`, the source-facing surface for that owner;
- `Submodule.comap`, the canonical way to realize a subspace by pulling back a product-side
  submodule along a linear equivalence;
- `Submodule.pi`, the canonical product-side owner used to encode coordinatewise vanishing.

Best owner abstraction:
- `coordinateSubspace k n : Submodule ℝ (EuclideanSpace ℝ (Fin n))`

Primitive data:
- the cut index `k`;
- the ambient dimension `n`.

Derived API:
- `mem_coordinateSubspace_iff`, which rewrites membership in the owner submodule into the textbook
  coordinate-vanishing condition.
- the notation `ℝ^{k,n}`, which exposes the source-facing surface while keeping
  `coordinateSubspace k n` as the raw owner.

Source/core/bridge triage:
- source-facing: the textbook coordinate subspace `ℝ^{k,n} ⊆ ℝⁿ`;
- core/canonical: the owner submodule `coordinateSubspace k n`;
- bridge/view: the coordinatewise criterion `mem_coordinateSubspace_iff`.

This recall file therefore uses the upstream owner declaration directly and introduces no parallel
wrapper or duplicate local definition. It also reuses the upstream notation `ℝ^{k,n}` rather than
adding a second alias layer.
-/

recall coordinateSubspace (k n : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin n))

recall mem_coordinateSubspace_iff
    {k n : ℕ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ ℝ^{k,n} ↔ ∀ i : Fin n, k ≤ i.1 → x i = 0

/-! ### Lemma_2_12 (from Chap02) -/
/- Lemma 2.12 is a recall-only item in the epigraph convexity domain for real-valued convex
functions.

Primary domain:
- convexity of epigraphs of convex functions.

Sampled owner-style declarations:
- `ConvexOn`
- `ConvexOn.convex_epigraph`
- `convexOn_iff_convex_epigraph`
- the later Euclidean specialization in `Chap03/Theorem_3_1_2`

Best owner abstraction:
- `ConvexOn.convex_epigraph`

Primitive data:
- a function `f`
- the owner hypothesis `hf : ConvexOn 𝕜 s f`

Derived API:
- convexity of the epigraph `{p | p.1 ∈ s ∧ f p.1 ≤ p.2}`
- in the textbook whole-space specialization, simplification of `p.1 ∈ Set.univ`

Source/core/bridge triage:
- source-facing: Lemma 2.12 as the whole-space epigraph convexity consequence
- core/canonical: `ConvexOn.convex_epigraph`
- bridge/view: specialization to `s = Set.univ`

This file therefore keeps no parallel whole-space wrapper theorem and recalls the canonical owner
declaration directly. -/

recall ConvexOn.convex_epigraph

/-! ### Proposition_2_12 (from Chap02) -/
open AffineMap
open scoped Gradient StrongConvexSmooth

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: accelerated first-order dynamics for strongly convex smooth unconstrained
minimization on real Hilbert spaces.

Relevant owner-style declarations sampled before refining this file:
* `IsStrongConvexSmoothObjective` in `Definition_2_17`, which owns the objective-side
  `C¹`/strong-convexity/gradient-Lipschitz package;
* `IsMinOn` on `Set.univ`, which gives the canonical global minimizer predicate for the ambient
  unconstrained problem;
* `ConstantStepSchemeIIMomentumRecurrence` in `Algorithm_2_4`, the nearby owner abstraction for
  accelerated `(x_k, y_k)` trajectories with a momentum law;
* `ConstantStepSchemeIIRecurrence` in `Algorithm_2_4`, which adds the analytic side conditions to
  that owner trajectory.

Best owner abstractions here:
* `ConstantStepSchemeIIIMomentumRecurrence` for the intrinsic fixed-momentum trajectory data;
* `ConstantStepSchemeIII` for the exact gradient-step specialization of that trajectory;
* `IsStrongConvexSmoothObjective μ L f` for the objective-side regularity assumptions.

Primitive data:
* the shared fixed-β trajectory data `x`, `y` and its defining recurrences;
* the exact gradient-step equation of `ConstantStepSchemeIII`;
* one minimizing point `xStar`, expressed canonically by `IsMinOn`.

Derived API:
* positivity/regularity facts extracted from `IsStrongConvexSmoothObjective`;
* the textbook coefficient `β = (1 - √q_f) / (1 + √q_f)`;
* the canonical bridge to `ConstantStepSchemeIIMomentumRecurrence` with the constant scalar
  sequence `α_k = √q_f`.

Although scheme III can be embedded into the type-II owner abstraction by taking a constant
auxiliary scalar sequence `α_k = √q_f`, that scalar sequence is auxiliary implementation data,
not the intrinsic source-level object. The public owner here therefore remains the fixed-momentum
trajectory data, with `ConstantStepSchemeIII` as the source-facing exact-step specialization.
That shared fixed-momentum owner is purely algebraic: only the exact-step specialization and the
objective-gap estimates need the ambient Hilbert-space structure. -/

/-- The constant momentum coefficient `β = (1 - √q_f) / (1 + √q_f)` attached to the reciprocal
condition-number parameter `q_f` in constant step scheme III. -/
def constantStepSchemeIIIMomentumCoefficient (qf : ℝ) : ℝ :=
  (1 - Real.sqrt qf) / (1 + Real.sqrt qf)

/- Textbook surface notation for the constant scheme-III momentum coefficient. -/
scoped[StrongConvexSmooth] notation "β[" qf "]" => constantStepSchemeIIIMomentumCoefficient qf

/-- The fixed-momentum scheme-III trajectory data shared by the chapter's exact-step variants. -/
structure ConstantStepSchemeIIIMomentumRecurrence
    (E : Type u) [AddCommGroup E] [Module ℝ E]
    (X : Type*) [CoeTC X E] (qf : ℝ) (x0 : X) where
  /-- The main iterate sequence `x_k`. -/
  x : ℕ → X
  /-- The extrapolated sequence `y_k`. -/
  y : ℕ → E
  /-- The zeroth iterate is the prescribed initial point. -/
  x_zero : x 0 = x0
  /-- The extrapolated sequence starts from the same initial point. -/
  y_zero : y 0 = (x0 : E)
  /-- The extrapolated points use the fixed momentum coefficient `β[q_f]`. -/
  y_succ (k : ℕ) :
    y (k + 1) =
      (x (k + 1) : E) +
        β[qf] •
          ((x (k + 1) : E) - (x k : E))

namespace ConstantStepSchemeIIIMomentumRecurrence

variable {qf : ℝ}

private theorem constant_alpha_momentumCoefficient_eq
    (hqf : qf ∈ Set.Ioc (0 : ℝ) 1) :
    (Real.sqrt qf * (1 - Real.sqrt qf)) /
        (Real.sqrt qf ^ (2 : ℕ) + Real.sqrt qf) =
      β[qf] := by
  unfold constantStepSchemeIIIMomentumCoefficient
  have hqf_nonneg : 0 ≤ qf := hqf.1.le
  have hsqrt_ne : Real.sqrt qf ≠ 0 := Real.sqrt_ne_zero'.2 hqf.1
  field_simp [hsqrt_ne]
  nlinarith [Real.sq_sqrt hqf_nonneg]

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable {X : Type*} [CoeTC X E] {qf : ℝ} {x0 : X}

/-- A fixed-momentum scheme-III recurrence can be used as its iterate sequence `x_k`. -/
instance :
    CoeFun
      (ConstantStepSchemeIIIMomentumRecurrence E X qf x0)
      (fun _ ↦ ℕ → X) where
  coe scheme := scheme.x

end

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable {X : Type*} [CoeTC X E] {qf : ℝ} {x0 : X}

/-- Under the admissible parameter condition `q_f ∈ (0, 1]`, a fixed-momentum scheme-III
recurrence canonically induces the chapter's type-II momentum owner by adjoining the constant
scalar sequence `α_k = √q_f`. -/
def toConstantStepSchemeIIMomentumRecurrence
    (scheme : ConstantStepSchemeIIIMomentumRecurrence E X qf x0)
    (hqf : qf ∈ Set.Ioc (0 : ℝ) 1) :
    ConstantStepSchemeIIMomentumRecurrence E X qf x0 (Real.sqrt qf) where
  x := scheme.x
  y := scheme.y
  alpha := fun _ ↦ Real.sqrt qf
  x_zero := scheme.x_zero
  y_zero := scheme.y_zero
  alpha_zero := rfl
  alpha_succ_equation := by
    intro k
    have hqf_nonneg : 0 ≤ qf := hqf.1.le
    rw [Real.sq_sqrt hqf_nonneg]
    ring
  y_succ := by
    intro k
    rw [scheme.y_succ k, constant_alpha_momentumCoefficient_eq hqf]

end

end ConstantStepSchemeIIIMomentumRecurrence

/-- A constant step scheme of type III for `f : E → ℝ` with parameter `q_f` consists of
sequences `x_k` and `y_k` with constant step size `1 / L` and fixed momentum coefficient
`β[q_f] = (1 - √q_f) / (1 + √q_f)`. -/
structure ConstantStepSchemeIII (f : E → ℝ) (L qf : ℝ) (x0 : E)
    extends ConstantStepSchemeIIIMomentumRecurrence E E qf x0 where
  /-- The smoothness constant used in the step size is positive. -/
  L_pos : 0 < L
  /-- The reciprocal condition-number parameter lies in `(0, 1]`. -/
  qf_mem_Ioc : qf ∈ Set.Ioc (0 : ℝ) 1
  /-- The iterates are produced by a gradient step of size `1 / L` from `y_k`. -/
  x_succ (k : ℕ) :
    x (k + 1) = y k - (1 / L) • ∇ f (y k)

namespace ConstantStepSchemeIII

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {L qf : ℝ} {x0 : E}

/-- A scheme-III exact-step recurrence canonically induces the upstream type-II momentum owner by
forgetting only the fixed-`β` presentation and adjoining the constant scalar sequence
`α_k = √q_f`. -/
def toConstantStepSchemeIIMomentumRecurrence
    (scheme : ConstantStepSchemeIII f L qf x0) :
    ConstantStepSchemeIIMomentumRecurrence E E qf x0 (Real.sqrt qf) :=
  scheme.toConstantStepSchemeIIIMomentumRecurrence.toConstantStepSchemeIIMomentumRecurrence
    scheme.qf_mem_Ioc

/-- A constant-step scheme III can be used as its iterate sequence `x_k`. -/
instance : CoeFun (ConstantStepSchemeIII f L qf x0) (fun _ ↦ ℕ → E) where
  coe scheme := scheme.toConstantStepSchemeIIIMomentumRecurrence

end ConstantStepSchemeIII

/-
Proposition 2.12 is stated against the chapter's owner objective predicate
`IsStrongConvexSmoothObjective μ L f`, together with the canonical minimizer predicate
`IsMinOn f Set.univ xStar`. By Definition 2.22, the reciprocal condition number appearing in the
scheme-III rate is the canonical scalar `q[μ, L]`, so the scheme's exact-step data remain owned
by `ConstantStepSchemeIII f L q[μ, L] x0`, while its shared fixed-momentum trajectory lives in
`ConstantStepSchemeIIIMomentumRecurrence E E q[μ, L] x0`.
-/
section ObjectiveGapRates

variable {μ L : ℝ} {f : E → ℝ} (hf : IsStrongConvexSmoothObjective μ L f)
variable {xStar x0 : E} (hxStar : IsMinOn f Set.univ xStar)
variable (scheme : ConstantStepSchemeIII f L (q[μ, L]) x0)

local notation "qf" => q[μ, L]
local notation "a" => Real.sqrt qf
local notation "alpha" => fun _ : ℕ ↦ a
local notation "phi" =>
  strongConvexEstimatingFunction μ f
    (quadraticallyRegularizedObjective (fun _ : E ↦ f x0) μ x0)
    scheme.y
    alpha
local notation "phiStar" =>
  estimatingSequenceValue f alpha scheme.y μ (f x0) μ x0
local notation "center" =>
  estimatingSequenceCenter f alpha scheme.y μ μ x0

/-- Helper for Proposition 2.12: the constant coefficient sequence
`α_k = √q[μ, L]` gives the geometric estimating weight `(1 - √q[μ, L])^k`. -/
lemma schemeIII_estimating_weight_eq_geometric
    (k : ℕ) :
    estimatingWeight alpha k = (1 - a) ^ k := by
  -- The constant-coefficient weight recurrence is a geometric progression.
  induction k with
  | zero =>
      simp [estimatingWeight]
  | succ k ih =>
      rw [estimatingWeight, ih]
      ring

/-- Helper for Proposition 2.12: with initial curvature `γ₀ = μ` and constant
`α_k = √q[μ, L]`, the estimating-sequence curvature stays equal to `μ`. -/
lemma schemeIII_estimating_curvature_eq_mu
    (k : ℕ) :
    estimatingSequenceCurvature μ μ alpha k = μ := by
  -- The curvature recursion fixes `μ` when both the current and target curvatures equal `μ`.
  induction k with
  | zero =>
      simp [estimatingSequenceCurvature]
  | succ k ih =>
      rw [estimatingSequenceCurvature_succ]
      simp [ih]
      ring

/-- Helper for Proposition 2.12: a centered quadratic with positive curvature attains its minimum
value at its center. -/
lemma canonical_quadratic_isLeast_value
    {γ c : ℝ} {v : E}
    (hγ : 0 < γ) :
    IsLeast (Set.range (quadraticallyRegularizedObjective (fun _ : E ↦ c) γ v)) c := by
  refine ⟨?_, ?_⟩
  · -- Evaluating the quadratic at its center gives the claimed minimum value.
    refine ⟨v, ?_⟩
    simp [quadraticallyRegularizedObjective_apply]
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    -- Every other value differs from `c` by a nonnegative quadratic term.
    have hquad_nonneg : 0 ≤ (γ / 2) * ‖x - v‖ ^ (2 : ℕ) := by
      positivity
    simp [quadraticallyRegularizedObjective_apply]
    linarith

include hf
/-- Helper for Proposition 2.12: one normalized successor step converts the center recursion into
the scheme-III iterate gap update. -/
lemma schemeIII_center_succ_normalized
    {k : ℕ}
    (hcenter : center k - scheme.y k = (1 / a) • (scheme.y k - scheme k)) :
    center (k + 1) - scheme.y (k + 1) =
      ((((1 - a) / a) - β[qf]) : ℝ) • (scheme (k + 1) - scheme k) := by
  have hqf_nonneg : 0 ≤ qf := scheme.qf_mem_Ioc.1.le
  have ha_pos : 0 < a := Real.sqrt_pos.mpr scheme.qf_mem_Ioc.1
  have ha_ne : a ≠ 0 := ha_pos.ne'
  have hmu_ne : μ ≠ 0 := hf.mu_pos.ne'
  have hstep :
      scheme.y k - scheme (k + 1) = (1 / L) • ∇ f (scheme.y k) := by
    -- Rewrite the exact gradient step into the gap form used by the source algebra.
    rw [scheme.x_succ k]
    abel
  have hcenter_sub :
      center (k + 1) - scheme.y k =
        ((1 - a) / a) • (scheme.y k - scheme k) -
          (1 / a) • (scheme.y k - scheme (k + 1)) := by
    have hyk :
        (1 / μ : ℝ) • (μ • scheme.y k) = scheme.y k := by
      rw [smul_smul, one_div, inv_mul_cancel₀ hmu_ne, one_smul]
    -- Route correction: first normalize the center recursion at the common basepoint `y_k`.
    calc
      center (k + 1) - scheme.y k
          =
            (1 / μ : ℝ) •
                (((1 - a) * μ) • center k + (a * μ) • scheme.y k - a • ∇ f (scheme.y k)) -
              (1 / μ : ℝ) • (μ • scheme.y k) := by
              rw [hyk]
              simp [estimatingSequenceCenter_succ, schemeIII_estimating_curvature_eq_mu (k := k),
                schemeIII_estimating_curvature_eq_mu (k := k + 1)]
      _ =
          (1 / μ : ℝ) •
            ((((1 - a) * μ) • center k + (a * μ) • scheme.y k - a • ∇ f (scheme.y k)) -
              μ • scheme.y k) := by
            rw [← smul_sub]
      _ =
          (1 / μ : ℝ) • (((1 - a) * μ) • (center k - scheme.y k) - a • ∇ f (scheme.y k)) := by
            congr 1
            module
      _ = (1 - a) • (center k - scheme.y k) - (a / μ) • ∇ f (scheme.y k) := by
            rw [smul_sub, smul_smul, smul_smul]
            have hcoef1 : (1 / μ : ℝ) * ((1 - a) * μ) = 1 - a := by
              field_simp [hmu_ne]
            have hcoef2 : (1 / μ : ℝ) * a = a / μ := by ring
            rw [hcoef1, hcoef2]
      _ = ((1 - a) / a) • (scheme.y k - scheme k) - (a / μ) • ∇ f (scheme.y k) := by
            rw [hcenter, smul_smul]
            congr 1
            field_simp [ha_ne]
      _ =
          ((1 - a) / a) • (scheme.y k - scheme k) -
            (1 / a) • (scheme.y k - scheme (k + 1)) := by
            have hscalar : a / μ = (1 / a : ℝ) * (1 / L) := by
              have hsq : a * a = μ / L := by
                calc
                  a * a = a ^ (2 : ℕ) := by ring
                  _ = μ / L := by simpa using Real.sq_sqrt hqf_nonneg
              calc
                a / μ = (a * a) / (a * μ) := by
                  field_simp [ha_ne, hmu_ne]
                _ = (μ / L) / (a * μ) := by rw [hsq]
                _ = (1 / a : ℝ) * (1 / L) := by
                  field_simp [ha_ne, hmu_ne, scheme.L_pos.ne']
            rw [hstep, smul_smul, hscalar]
  -- Now subtract the explicit momentum update `y_{k+1} - y_k`.
  calc
    center (k + 1) - scheme.y (k + 1)
        = (center (k + 1) - scheme.y k) - (scheme.y (k + 1) - scheme.y k) := by
            abel
    _ =
        (((1 - a) / a) • (scheme.y k - scheme k) -
            (1 / a) • (scheme.y k - scheme (k + 1))) -
          (scheme.y (k + 1) - scheme.y k) := by
            rw [hcenter_sub]
    _ =
        (((1 - a) / a) •
              ((scheme.y k - scheme (k + 1)) + (scheme (k + 1) - scheme k)) -
            (1 / a) • (scheme.y k - scheme (k + 1))) -
          (-(scheme.y k - scheme (k + 1)) +
            β[qf] • (scheme (k + 1) - scheme k)) := by
            have hydecomp :
                scheme.y k - scheme k =
                  (scheme.y k - scheme (k + 1)) + (scheme (k + 1) - scheme k) := by
              abel_nf
            have hysucc :
                scheme.y (k + 1) - scheme.y k =
                  -(scheme.y k - scheme (k + 1)) +
                    β[qf] • (scheme (k + 1) - scheme k) := by
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                congrArg (fun z : E ↦ z - scheme.y k) (scheme.y_succ k)
            rw [hydecomp, hysucc]
    _ = ((((1 - a) / a) - β[qf]) : ℝ) • (scheme (k + 1) - scheme k) := by
          let u : E := scheme.y k - scheme (k + 1)
          let v : E := scheme (k + 1) - scheme k
          have hcancel : (((1 - a) / a : ℝ) - 1 / a + 1) = 0 := by
            field_simp [ha_ne]
            ring
          change (((1 - a) / a) • (u + v) - (1 / a) • u) - (-u + β[qf] • v) =
            ((((1 - a) / a) - β[qf]) : ℝ) • v
          calc
            (((1 - a) / a) • (u + v) - (1 / a) • u) - (-u + β[qf] • v)
                = ((((1 - a) / a) - 1 / a + 1) : ℝ) • u +
                    ((((1 - a) / a) - β[qf]) : ℝ) • v := by
                      module
            _ = ((((1 - a) / a) - β[qf]) : ℝ) • v := by
                  rw [hcancel, zero_smul, zero_add]

/-- Helper for Proposition 2.12: the estimating-sequence center differs from `y_k` by the
scaled iterate gap `(1 / √q[μ, L]) (y_k - x_k)`. -/
lemma schemeIII_estimating_center_sub_eq_iterate_gap
    (k : ℕ) :
    center k - scheme.y k = (1 / a) • (scheme.y k - scheme k) := by
  induction k with
  | zero =>
      -- At time zero, both the center and the extrapolated point equal the initial iterate.
      rw [show center 0 = x0 by rfl, scheme.y_zero, scheme.x_zero]
      change (x0 : E) - (x0 : E) = (1 / a) • ((x0 : E) - (x0 : E))
      simp
  | succ k ih =>
      have hbeta_gap :
          scheme.y (k + 1) - scheme (k + 1) =
            β[qf] • (scheme (k + 1) - scheme k) := by
        -- Rewrite the momentum update as the displayed iterate gap.
        rw [scheme.y_succ k]
        module
      -- Route correction: use the normalized successor identity before converting back to the
      -- public `(1 / a) • (y_k - x_k)` bridge.
      calc
        center (k + 1) - scheme.y (k + 1)
            = ((((1 - a) / a) - β[qf]) : ℝ) • (scheme (k + 1) - scheme k) := by
                exact schemeIII_center_succ_normalized (hf := hf) (scheme := scheme) ih
        _ = (β[qf] / a) • (scheme (k + 1) - scheme k) := by
              have hbeta :
                  β[qf] = (1 - a) / (1 + a) := by
                rfl
              have ha_pos : 0 < a := Real.sqrt_pos.mpr scheme.qf_mem_Ioc.1
              have ha_ne : a ≠ 0 := ha_pos.ne'
              have hdenom_ne : 1 + a ≠ 0 := by
                linarith
              rw [hbeta]
              field_simp [ha_ne, hdenom_ne]
              ring_nf
        _ = (1 / a) • (β[qf] • (scheme (k + 1) - scheme k)) := by
              rw [smul_smul]
              congr 1
              ring
        _ = (1 / a) • (scheme.y (k + 1) - scheme (k + 1)) := by
              rw [hbeta_gap]

/-- Helper for Proposition 2.12: every estimating function `φ_k` attains the minimum value
`φ_k^*`. -/
lemma schemeIII_estimating_value_isLeast
    (k : ℕ) :
    IsLeast (Set.range (phi k)) (phiStar k) := by
  have hγ :
      ∀ j, estimatingSequenceCurvature μ μ alpha (j + 1) ≠ 0 := by
    intro j
    rw [schemeIII_estimating_curvature_eq_mu (k := j + 1)]
    exact IsStrongConvexSmoothObjective.mu_pos hf |>.ne'
  -- Re-express `φ_k` as its centered quadratic normal form, then apply the generic minimum-value
  -- lemma for positive-curvature quadratics.
  rw [estimatingSequence_eq_canonicalQuadratic f (fun _ : ℕ ↦ a) scheme.y μ (f x0) μ x0 hγ k]
  rw [schemeIII_estimating_curvature_eq_mu (k := k)]
  simpa using
    canonical_quadratic_isLeast_value
      (E := E)
      (γ := μ)
      (c := estimatingSequenceValue f (fun _ : ℕ ↦ a) scheme.y μ (f x0) μ x0 k)
      (v := estimatingSequenceCenter f (fun _ : ℕ ↦ a) scheme.y μ μ x0 k)
      (IsStrongConvexSmoothObjective.mu_pos hf)

/-- Helper for Proposition 2.12: the scalar recurrence for `φ_k^*` reduces to the exact
scheme-III Lyapunov update after rewriting the center gap by the iterate gap. -/
lemma schemeIII_estimating_value_succ_normalized
    (k : ℕ) :
    phiStar (k + 1) =
      (1 - a) * phiStar k +
        a * f (scheme.y k) -
        (1 / (2 * L)) * ‖∇ f (scheme.y k)‖ ^ (2 : ℕ) +
        (1 - a) * inner ℝ (∇ f (scheme.y k)) (scheme.y k - scheme k) +
        ((1 - a) * μ / (2 * a)) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ) := by
  have hqf_nonneg : 0 ≤ qf := scheme.qf_mem_Ioc.1.le
  have ha_pos : 0 < a := Real.sqrt_pos.mpr scheme.qf_mem_Ioc.1
  have ha_ne : a ≠ 0 := ha_pos.ne'
  have hmu_ne : μ ≠ 0 := hf.mu_pos.ne'
  have hcenter := schemeIII_estimating_center_sub_eq_iterate_gap
    (hf := hf) (scheme := scheme) k
  have hycenter :
      scheme.y k - center k = (1 / a) • (scheme k - scheme.y k) := by
    -- Reverse the center-gap identity to match the quadratic norm term.
    calc
      scheme.y k - center k = -(center k - scheme.y k) := by
        abel
      _ = -((1 / a) • (scheme.y k - scheme k)) := by
        rw [hcenter]
      _ = (1 / a) • (scheme k - scheme.y k) := by
        simp [sub_eq_add_neg, add_comm]
  have hgradient :
      a ^ (2 : ℕ) / (2 * μ) = 1 / (2 * L) := by
    have hsq : a * a = μ / L := by
      calc
        a * a = a ^ (2 : ℕ) := by ring
        _ = μ / L := by simpa using Real.sq_sqrt hqf_nonneg
    calc
      a ^ (2 : ℕ) / (2 * μ) = (a * a) / (2 * μ) := by ring
      _ = (μ / L) / (2 * μ) := by rw [hsq]
      _ = 1 / (2 * L) := by
            field_simp [hmu_ne, scheme.L_pos.ne']
  have hlinear :
      a * (1 - a) * inner ℝ (∇ f (scheme.y k)) (center k - scheme.y k) =
        (1 - a) * inner ℝ (∇ f (scheme.y k)) (scheme.y k - scheme k) := by
    rw [hcenter, real_inner_smul_right]
    field_simp [ha_ne]
  have hquadratic :
      a * (1 - a) * ((μ / 2) * ‖scheme.y k - center k‖ ^ (2 : ℕ)) =
        ((1 - a) * μ / (2 * a)) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ) := by
    rw [hycenter, norm_smul, Real.norm_eq_abs]
    have habs : |(1 / a : ℝ)| = 1 / a := by
      rw [abs_of_pos (one_div_pos.mpr ha_pos)]
    rw [habs]
    field_simp [ha_ne]
  -- Rewrite the generic estimating-sequence scalar recursion at constant curvature `μ`.
  calc
    phiStar (k + 1)
        = (1 - a) * phiStar k +
            a * f (scheme.y k) -
            (a ^ (2 : ℕ) / (2 * μ)) * ‖∇ f (scheme.y k)‖ ^ (2 : ℕ) +
            a * (1 - a) *
              ((μ / 2) * ‖scheme.y k - center k‖ ^ (2 : ℕ) +
                inner ℝ (∇ f (scheme.y k)) (center k - scheme.y k)) := by
            simpa [schemeIII_estimating_curvature_eq_mu (k := k),
              schemeIII_estimating_curvature_eq_mu (k := k + 1), hmu_ne] using
              estimatingSequenceValue_succ f (fun _ : ℕ ↦ a) scheme.y μ (f x0) μ x0 k
    _ = (1 - a) * phiStar k +
          a * f (scheme.y k) -
          (1 / (2 * L)) * ‖∇ f (scheme.y k)‖ ^ (2 : ℕ) +
          (1 - a) * inner ℝ (∇ f (scheme.y k)) (scheme.y k - scheme k) +
          ((1 - a) * μ / (2 * a)) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ) := by
            rw [hgradient]
            rw [mul_add, hquadratic, hlinear]
            ring

include hf
/-- Helper for Proposition 2.12: the estimating-sequence values dominate the actual objective
values along the scheme-III trajectory. -/
lemma schemeIII_estimating_value_ge_objective
    (k : ℕ) :
    f (scheme k) ≤ phiStar k := by
  have ha_pos : 0 < a := Real.sqrt_pos.mpr scheme.qf_mem_Ioc.1
  have hqf_nonneg : 0 ≤ qf := scheme.qf_mem_Ioc.1.le
  have ha_le_one : a ≤ 1 := by
    nlinarith [scheme.qf_mem_Ioc.2, Real.sq_sqrt hqf_nonneg, Real.sqrt_nonneg qf]
  induction k with
  | zero =>
      -- The initial estimating value is exactly `f x₀`.
      simp [estimatingSequenceValue, scheme.x_zero]
  | succ k ih =>
      have hfactor_nonneg : 0 ≤ 1 - a := by
        linarith
      have hdescent_core :
          inner ℝ (∇ f (scheme.y k)) (scheme (k + 1) - scheme.y k) +
              (L / 2) * ‖scheme (k + 1) - scheme.y k‖ ^ (2 : ℕ) =
            -(1 / (2 * L)) * ‖∇ f (scheme.y k)‖ ^ (2 : ℕ) := by
        have hstep :
            scheme (k + 1) - scheme.y k = (- (1 / L : ℝ)) • ∇ f (scheme.y k) := by
          have hstep_eq :=
            congrArg (fun z : E ↦ z - scheme.y k) (scheme.x_succ k)
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, neg_smul] using hstep_eq
        -- The exact gradient step turns the smooth tangent model into the standard decrease term.
        rw [hstep, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs]
        have habs : |(-(1 / L : ℝ))| = 1 / L := by
          have hnonpos : -(1 / L : ℝ) ≤ 0 := by
            have hLinv_pos : 0 < (1 / L : ℝ) := one_div_pos.mpr scheme.L_pos
            linarith
          rw [abs_of_nonpos hnonpos]
          ring
        rw [habs]
        field_simp [scheme.L_pos.ne']
        ring
      have hdescent :
          f (scheme (k + 1)) ≤
            f (scheme.y k) - (1 / (2 * L)) * ‖∇ f (scheme.y k)‖ ^ (2 : ℕ) := by
        have hupper := hf.upper_tangent_quadratic (scheme.y k) (scheme (k + 1))
        calc
          f (scheme (k + 1))
              ≤ f (scheme.y k) +
                  inner ℝ (∇ f (scheme.y k)) (scheme (k + 1) - scheme.y k) +
                    (L / 2) * ‖scheme (k + 1) - scheme.y k‖ ^ (2 : ℕ) := by
                      simpa using hupper
          _ = f (scheme.y k) - (1 / (2 * L)) * ‖∇ f (scheme.y k)‖ ^ (2 : ℕ) := by
                linarith [hdescent_core]
      have hnorm_nonneg : 0 ≤ ‖scheme k - scheme.y k‖ ^ (2 : ℕ) := by
        positivity
      have hinside_nonneg :
          0 ≤
            phiStar k - f (scheme.y k) +
              inner ℝ (∇ f (scheme.y k)) (scheme.y k - scheme k) +
              (μ / (2 * a)) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ) := by
        have hlower := hf.lower_tangent_quadratic (scheme.y k) (scheme k)
        have hbase :
            0 ≤
              phiStar k - f (scheme.y k) +
                inner ℝ (∇ f (scheme.y k)) (scheme.y k - scheme k) -
                (μ / 2) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ) := by
          have hinner :
              -inner ℝ (∇ f (scheme.y k)) (scheme.y k - scheme k) =
                inner ℝ (∇ f (scheme.y k)) (scheme k - scheme.y k) := by
            have hvec : scheme.y k - scheme k = -(scheme k - scheme.y k) := by
              abel
            rw [hvec, inner_neg_right, neg_neg]
          have hlower' :
              f (scheme.y k) -
                  inner ℝ (∇ f (scheme.y k)) (scheme.y k - scheme k) +
                  (μ / 2) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ) ≤
                f (scheme k) := by
            calc
              f (scheme.y k) -
                    inner ℝ (∇ f (scheme.y k)) (scheme.y k - scheme k) +
                    (μ / 2) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ)
                  =
                    f (scheme.y k) +
                      inner ℝ (∇ f (scheme.y k)) (scheme k - scheme.y k) +
                      (μ / 2) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ) := by
                        rw [sub_eq_add_neg, hinner]
              _ ≤ f (scheme k) := hlower
          nlinarith [ih, hlower']
        have hextra_nonneg :
            0 ≤
              ((μ / (2 * a)) + μ / 2) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ) := by
          have hcoef_nonneg : 0 ≤ (μ / (2 * a)) + μ / 2 := by
            have hleft : 0 ≤ μ / (2 * a) := by
              have hden : 0 ≤ 2 * a := by
                nlinarith [ha_pos]
              exact div_nonneg hf.mu_pos.le hden
            have hright : 0 ≤ μ / 2 := by
              exact div_nonneg hf.mu_pos.le (by norm_num)
            linarith
          exact mul_nonneg hcoef_nonneg hnorm_nonneg
        -- Combine the inductive domination with strong convexity at the common basepoint `y_k`.
        nlinarith [hbase, hextra_nonneg]
      have hstep_model :
          f (scheme.y k) - (1 / (2 * L)) * ‖∇ f (scheme.y k)‖ ^ (2 : ℕ) ≤
            (1 - a) * phiStar k +
              a * f (scheme.y k) -
              (1 / (2 * L)) * ‖∇ f (scheme.y k)‖ ^ (2 : ℕ) +
              (1 - a) * inner ℝ (∇ f (scheme.y k)) (scheme.y k - scheme k) +
              ((1 - a) * μ / (2 * a)) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ) := by
        have hscaled :
            0 ≤
              (1 - a) *
                (phiStar k - f (scheme.y k) +
                  inner ℝ (∇ f (scheme.y k)) (scheme.y k - scheme k) +
                  (μ / (2 * a)) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ)) := by
          exact mul_nonneg hfactor_nonneg hinside_nonneg
        calc
          f (scheme.y k) - (1 / (2 * L)) * ‖∇ f (scheme.y k)‖ ^ (2 : ℕ)
              ≤ f (scheme.y k) - (1 / (2 * L)) * ‖∇ f (scheme.y k)‖ ^ (2 : ℕ) +
                  (1 - a) *
                    (phiStar k - f (scheme.y k) +
                      inner ℝ (∇ f (scheme.y k)) (scheme.y k - scheme k) +
                      (μ / (2 * a)) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ)) := by
                    nlinarith
          _ = (1 - a) * phiStar k +
                a * f (scheme.y k) -
                (1 / (2 * L)) * ‖∇ f (scheme.y k)‖ ^ (2 : ℕ) +
                (1 - a) * inner ℝ (∇ f (scheme.y k)) (scheme.y k - scheme k) +
                ((1 - a) * μ / (2 * a)) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ) := by
                  ring
      calc
        f (scheme (k + 1))
            ≤ f (scheme.y k) - (1 / (2 * L)) * ‖∇ f (scheme.y k)‖ ^ (2 : ℕ) := hdescent
        _ ≤ (1 - a) * phiStar k +
              a * f (scheme.y k) -
              (1 / (2 * L)) * ‖∇ f (scheme.y k)‖ ^ (2 : ℕ) +
              (1 - a) * inner ℝ (∇ f (scheme.y k)) (scheme.y k - scheme k) +
              ((1 - a) * μ / (2 * a)) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ) := hstep_model
        _ = phiStar (k + 1) := by
              rw [schemeIII_estimating_value_succ_normalized (hf := hf) (scheme := scheme) k]

include hf hxStar
/-- The owner geometric objective-gap estimate for constant step scheme III is controlled by the
canonical initial Lyapunov energy
`f x₀ - f x* + (μ / 2) ‖x₀ - x*‖²`, with decay factor `(1 - √q[μ, L])^k`. -/
-- Proof sketch: identify scheme III with the `γ₀ = μ` specialization of the chapter's
-- estimating-sequence owner, whose weight is exactly `(1 - √q[μ, L])^k`. Then apply the owner
-- estimating-sequence suboptimality theorem with that geometric weight and the initial quadratic
-- model at `x₀`.
theorem constantStepSchemeIII_objective_gap_le_geometric_initial_energy
    (k : ℕ) :
    f (scheme k) - f xStar ≤
      (1 - Real.sqrt (q[μ, L])) ^ k *
        (f x0 - f xStar + (μ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) := by
  have hqf_nonneg : 0 ≤ qf := scheme.qf_mem_Ioc.1.le
  have ha_le_one : a ≤ 1 := by
    nlinarith [scheme.qf_mem_Ioc.2, Real.sq_sqrt hqf_nonneg, Real.sqrt_nonneg qf]
  have hgrad :
      ∀ j, HasGradientAt f (∇ f (scheme.y j)) (scheme.y j) := by
    intro j
    exact hf.contDiff.differentiable_one (scheme.y j) |>.hasGradientAt
  have halpha_mem_Icc : ∀ j, alpha j ∈ Set.Icc (0 : ℝ) 1 := by
    intro j
    exact ⟨Real.sqrt_nonneg qf, ha_le_one⟩
  have hphiUpper :
      ∀ j, phi j ≤ lineMap f (phi 0) (estimatingWeight alpha j) := by
    intro j
    simpa using
      strongConvexEstimatingFunction_upper_bound
        (φ₀ := quadraticallyRegularizedObjective (fun _ : E ↦ f x0) μ x0)
        (y := scheme.y) (α := fun _ : ℕ ↦ a)
        hf.strongConvexOn hgrad halpha_mem_Icc j
  have hgap :
      f (scheme k) - f xStar ∈
        Set.Icc 0 (estimatingWeight alpha k * (phi 0 xStar - f xStar)) := by
    exact estimatingSequence_gap_mem_Icc xStar phiStar scheme hxStar hphiUpper
      (schemeIII_estimating_value_isLeast (hf := hf) (scheme := scheme))
      (schemeIII_estimating_value_ge_objective (hf := hf) (scheme := scheme))
      k
  have hInitial :
      phi 0 xStar - f xStar =
        f x0 - f xStar + (μ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
    -- Evaluate the initial quadratic model at the minimizer.
    calc
      phi 0 xStar - f xStar
          = quadraticallyRegularizedObjective (fun _ : E ↦ f x0) μ x0 xStar - f xStar := by
              rfl
      _ = (f x0 + (μ / 2) * ‖xStar - x0‖ ^ (2 : ℕ)) - f xStar := by
            rw [quadraticallyRegularizedObjective_apply]
      _ = f x0 - f xStar + (μ / 2) * ‖xStar - x0‖ ^ (2 : ℕ) := by
            ring
      _ = f x0 - f xStar + (μ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
            rw [norm_sub_rev]
  -- Extract the interval upper endpoint and rewrite the owner weight as the geometric factor.
  calc
    f (scheme k) - f xStar
        ≤ estimatingWeight alpha k * (phi 0 xStar - f xStar) := hgap.2
    _ = (1 - a) ^ k * (f x0 - f xStar + (μ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) := by
          rw [schemeIII_estimating_weight_eq_geometric (k := k), hInitial]
omit hf hxStar

include hf hxStar
/-- Proposition 2.12: if `f : E → ℝ` belongs to the strongly convex smooth class with
parameters `μ` and `L`, `xStar` is a minimizer of `f`, and `x_k` is generated by constant step
scheme III with reciprocal condition number `q_f = q[μ, L]` and momentum coefficient
`β[q[μ, L]] = (1 - √q[μ, L]) / (1 + √q[μ, L])`, then
`f(x_k) - f(xStar) ≤ ((L + μ) / 2) ‖x₀ - xStar‖² exp(-k √q[μ, L])` for every `k ≥ 0`. -/
-- Proof sketch: use the standard Lyapunov function for constant step scheme III, whose one-step
-- decay factor is `1 - √q[μ, L]`. Iterating the decay gives
-- `E_k ≤ (1 - √q[μ, L])^k E_0`, while the energy controls the objective gap and
-- satisfies the initial bound `E_0 ≤ ((L + μ) / 2) ‖x₀ - xStar‖²`. Finally apply
-- `(1 - √q[μ, L])^k ≤ exp (-k √q[μ, L])`.
theorem constantStepSchemeIII_objective_gap_le_exponential_rate
    (k : ℕ) :
    f (scheme k) - f xStar ≤
      ((L + μ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) *
        Real.exp (-(k : ℝ) * Real.sqrt (q[μ, L])) := by
  have hqf_nonneg : 0 ≤ qf := scheme.qf_mem_Ioc.1.le
  have ha_le_one : a ≤ 1 := by
    nlinarith [scheme.qf_mem_Ioc.2, Real.sq_sqrt hqf_nonneg, Real.sqrt_nonneg qf]
  have hweight_nonneg : 0 ≤ (1 - a) ^ k := by
    exact pow_nonneg (sub_nonneg.mpr ha_le_one) k
  have hinitial_gap :
      f x0 - f xStar ≤ (L / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
    have hgrad_zero : ∇ f xStar = 0 := hf.gradient_eq_zero_of_isMinOn hxStar
    have hupper :
        f x0 ≤ f xStar + (L / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
      simpa [hgrad_zero] using hf.upper_tangent_quadratic xStar x0
    linarith
  have hinitial_energy :
      f x0 - f xStar + (μ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) ≤
        ((L + μ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
    linarith
  have hgeom_exp :
      (1 - a) ^ k ≤ Real.exp (-(k : ℝ) * a) := by
    -- Compare the geometric weight with its exponential majorant.
    cases k with
    | zero =>
        simp
    | succ k =>
        have haux : a * ((k + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
          nlinarith
        have hbase :=
          Real.one_sub_div_pow_le_exp_neg (n := k + 1)
            (t := a * ((k + 1 : ℕ) : ℝ)) haux
        have hdiv :
            a * ((k + 1 : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ)) = a := by
          field_simp
        calc
          (1 - a) ^ (k + 1)
              = (1 - a * ((k + 1 : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ))) ^ (k + 1) := by
                  rw [hdiv]
          _ ≤ Real.exp (-(a * ((k + 1 : ℕ) : ℝ))) := hbase
          _ = Real.exp (-((k + 1 : ℕ) : ℝ) * a) := by
                ring_nf
  have henergy_nonneg :
      0 ≤ ((L + μ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
    have hnorm_nonneg : 0 ≤ ‖x0 - xStar‖ ^ (2 : ℕ) := by
      positivity
    nlinarith [scheme.L_pos, hf.mu_pos, hnorm_nonneg]
  calc
    f (scheme k) - f xStar
        ≤ (1 - a) ^ k *
            (f x0 - f xStar + (μ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) :=
      constantStepSchemeIII_objective_gap_le_geometric_initial_energy
        (hf := hf) (hxStar := hxStar) (scheme := scheme) k
    _ ≤ (1 - a) ^ k * (((L + μ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) := by
          gcongr
    _ ≤ Real.exp (-(k : ℝ) * a) * (((L + μ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) := by
          gcongr
    _ = ((L + μ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) * Real.exp (-(k : ℝ) * a) := by
          ring

omit hf hxStar

end ObjectiveGapRates

/-! ### Theorem_2_12 (from Chap02) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: twice continuously differentiable strong-convexity criteria on open convex
subsets of real Hilbert spaces, together with the textbook bridge from `interior Q` to `Q`.

Sampled owner-style declarations before refining this file:
* mathlib `StrongConvexOn`
* mathlib `strongConvexOn_iff_convex`
* project `StrongConvexOnWith` in `Definition_2_14`
* project `StrongConvexOnWith.lower_tangent_quadratic` in `Definition_2_14`
* project `convexOn_iff_hessian_quadratic_form_nonneg` in `Theorem_2_4`

Source/core/bridge triage:
* source-facing: the lower-tangent inequality from `x ∈ interior Q` to arbitrary `y ∈ Q`
* core/canonical: `StrongConvexOnWith p μ U f` on an open convex owner domain `U`
* bridge/view: the Hessian quadratic-form lower bound on that same open convex domain

Primitive data:
* the open convex owner domain `U`
* the source-facing convex set `Q`
* continuity of `f` on `Q`
* `C²` regularity of `f` on the open owner domain

Derived API:
* `StrongConvexOnWith.lower_tangent_quadratic` on the open owner domain
* the Euclidean `StrongConvexOn` bridge used in `Definition_2_15` after finite-dimensional
  specialization

The main public theorem stays source-facing because the textbook statement compares the interior
Hessian bound with a lower-tangent inequality that reaches all the way to `y ∈ Q`, while the
owner predicate `StrongConvexOnWith` governs the intrinsic strong-convexity data on the open
convex domain where the Hessian is evaluated. -/

section

variable (p : Seminorm ℝ E)
variable {μ : ℝ} {U Q : Set E} {f : E → ℝ}

/-- Helper for Theorem 2.12: the affine line `s ↦ x + s • d` has derivative `d`. -/
private theorem line_hasDerivAt (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate the scalar multiple and then translate by the base point.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add x

/-- Helper for Theorem 2.12: scalarizing the gradient along an affine line differentiates to the
Hessian pairing in the line direction. -/
private theorem scalarized_gradient_along_line_hasDerivAt
    {x d u : E} {t : ℝ} (hf_C2 : ContDiffAt ℝ 2 f (x + t • d)) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ f (x + s • d)) u)
      (inner ℝ (hessian f (x + t • d) d) u) t := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv : DifferentiableAt ℝ (fderiv ℝ f) (x + t • d) := by
    -- A `C²` function has a differentiable Fréchet derivative field.
    have hcont : ContDiffAt ℝ 1 (fderiv ℝ f) (x + t • d) :=
      hf_C2.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact hcont.differentiableAt one_ne_zero
  have hgrad : DifferentiableAt ℝ (∇ f) (x + t • d) := by
    -- Rewrite the gradient through the Riesz map to differentiate it.
    simpa [gradient, D] using D.differentiableAt.comp (x + t • d) hfderiv
  have hgradLine :
      HasFDerivAt (fun s : ℝ ↦ ∇ f (x + s • d))
        ((hessian f (x + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d)) t := by
    -- Compose the derivative of the gradient with the derivative of the affine line.
    simpa using (hgrad.hasFDerivAt.comp t (line_hasDerivAt x d t).hasFDerivAt)
  let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) u
  have hscalar :
      HasFDerivAt (fun s : ℝ ↦ φ (∇ f (x + s • d)))
        (φ.comp ((hessian f (x + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d))) t := by
    -- Postcompose the line-gradient map with the scalar functional `v ↦ ⟪v, u⟫`.
    simpa [φ] using ((φ.hasFDerivAt).comp t hgradLine)
  simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hscalar.hasDerivAt

/-- Helper for Theorem 2.12: differentiating the corrected line restriction gives the tangent
model of the quadratic remainder. -/
private theorem corrected_line_hasDerivAt
    (μ : ℝ) {x d : E} {t : ℝ} (hf_C2 : ContDiffAt ℝ 2 f (x + t • d)) :
    HasDerivAt
      (fun s : ℝ ↦ f (x + s • d) - ((μ / 2) * (p d) ^ (2 : ℕ)) * s ^ (2 : ℕ))
      (inner ℝ (∇ f (x + t • d)) d - μ * (p d) ^ (2 : ℕ) * t) t := by
  have hf_C1 : ContDiffAt ℝ 1 f (x + t • d) :=
    hf_C2.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hline :
      HasDerivAt (fun s : ℝ ↦ f (x + s • d)) (inner ℝ (∇ f (x + t • d)) d) t := by
    -- Compose the ambient derivative of `f` with the affine line.
    simpa using
      ((hf_C1.differentiableAt one_ne_zero).hasGradientAt.hasFDerivAt.comp t
        (line_hasDerivAt x d t).hasFDerivAt).hasDerivAt
  have hquad :
      HasDerivAt
        (fun s : ℝ ↦ ((μ / 2) * (p d) ^ (2 : ℕ)) * s ^ (2 : ℕ))
        (μ * (p d) ^ (2 : ℕ) * t) t := by
    -- The quadratic correction differentiates to the expected linear term.
    have hsq : HasDerivAt (fun s : ℝ ↦ s ^ (2 : ℕ)) (2 * t) t := by
      simpa [pow_two, two_mul] using ((hasDerivAt_id t).pow 2)
    convert hsq.const_mul (((μ / 2) * (p d) ^ (2 : ℕ))) using 1
    ring
  -- Subtract the quadratic correction from the line restriction.
  simpa using hline.sub hquad

/-- Helper for Theorem 2.12: differentiating the corrected line derivative gives the Hessian
defect `⟪∇²f(x)d, d⟫ - μ‖d‖²_p`. -/
private theorem corrected_line_deriv_hasDerivAt
    (μ : ℝ) {x d : E} {t : ℝ} (hf_C2 : ContDiffAt ℝ 2 f (x + t • d)) :
    HasDerivAt
      (fun s : ℝ ↦ inner ℝ (∇ f (x + s • d)) d - μ * (p d) ^ (2 : ℕ) * s)
      (inner ℝ (hessian f (x + t • d) d) d - μ * (p d) ^ (2 : ℕ)) t := by
  have hgrad :
      HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ f (x + s • d)) d)
        (inner ℝ (hessian f (x + t • d) d) d) t :=
    scalarized_gradient_along_line_hasDerivAt hf_C2
  have hlin :
      HasDerivAt (fun s : ℝ ↦ μ * (p d) ^ (2 : ℕ) * s)
        (μ * (p d) ^ (2 : ℕ)) t := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (hasDerivAt_id t).const_mul (μ * (p d) ^ (2 : ℕ))
  -- Differentiate the scalarized gradient and subtract the explicit linear correction.
  simpa using hgrad.sub hlin

/-- Helper for Theorem 2.12: a one-variable lower-tangent inequality forces the proposed
derivative field to be monotone on the same interval. -/
private theorem monotoneOn_of_lower_tangent
    {D : Set ℝ} {φ g : ℝ → ℝ}
    (hlower : ∀ s ∈ D, ∀ t ∈ D, φ t ≥ φ s + g s * (t - s)) :
    MonotoneOn g D := by
  intro s hs t ht hst
  rcases eq_or_lt_of_le hst with rfl | hst'
  · rfl
  have hs' := hlower s hs t ht
  have ht' := hlower t ht s hs
  have hineq : 0 ≥ (g s - g t) * (t - s) := by
    linarith
  nlinarith

/-- Helper for Theorem 2.12: under the Hessian lower bound, the corrected line restriction from an
interior base point to an arbitrary feasible point is convex on `[0,1]`. -/
private theorem corrected_segment_convexOn_of_hessian_lower_bound
    (μ : ℝ) (hQ_conv : Convex ℝ Q) (hf_cont : ContinuousOn f Q)
    (hf_C2 : ContDiffOn ℝ 2 f (interior Q))
    (hquad : ∀ x ∈ interior Q, ∀ h : E,
      μ * (p h) ^ 2 ≤ inner ℝ (hessian f x h) h)
    {x y : E} (hx : x ∈ interior Q) (hy : y ∈ Q) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun t : ℝ ↦ f (x + t • (y - x)) - ((μ / 2) * (p (y - x)) ^ (2 : ℕ)) * t ^ (2 : ℕ)) := by
  let d : E := y - x
  let φ : ℝ → ℝ := fun t ↦ f (x + t • d) - ((μ / 2) * (p d) ^ (2 : ℕ)) * t ^ (2 : ℕ)
  let I : Set ℝ := Set.Icc (0 : ℝ) 1
  have hline_mem_Q : Set.MapsTo (fun t : ℝ ↦ x + t • d) I Q := by
    intro t ht
    have hcombo : (1 - t) • x + t • y ∈ Q :=
      hQ_conv (interior_subset hx) hy (sub_nonneg.mpr ht.2) ht.1 (by linarith)
    have hline_eq : x + t • d = (1 - t) • x + t • y := by
      simp [d, sub_eq_add_neg, smul_add, add_smul, add_left_comm, add_comm]
    change x + t • d ∈ Q
    rw [hline_eq]
    exact hcombo
  have hline_mem_int : ∀ t ∈ interior I, x + t • d ∈ interior Q := by
    intro t ht
    have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa [I] using ht
    have hcombo : (1 - t) • x + t • y ∈ interior Q :=
      hQ_conv.combo_interior_self_mem_interior hx hy
        (sub_pos.mpr ht'.2) ht'.1.le (by linarith)
    have hline_eq : x + t • d = (1 - t) • x + t • y := by
      simp [d, sub_eq_add_neg, smul_add, add_smul, add_left_comm, add_comm]
    change x + t • d ∈ interior Q
    rw [hline_eq]
    exact hcombo
  have hφ_cont : ContinuousOn φ I := by
    have hcont_line : ContinuousOn (fun t : ℝ ↦ f (x + t • d)) I :=
      hf_cont.comp ((continuous_const.add (continuous_id.smul continuous_const)).continuousOn)
        hline_mem_Q
    have hcont_quad : ContinuousOn
        (fun t : ℝ ↦ ((μ / 2) * (p d) ^ (2 : ℕ)) * t ^ (2 : ℕ)) I := by
      fun_prop
    -- The corrected restriction is the difference of two continuous scalar functions.
    simpa [φ] using hcont_line.sub hcont_quad
  have hφ' :
      ∀ t ∈ interior I,
        HasDerivWithinAt φ
          (inner ℝ (∇ f (x + t • d)) d - μ * (p d) ^ (2 : ℕ) * t)
          (interior I) t := by
    intro t ht
    have htC2 : ContDiffAt ℝ 2 f (x + t • d) := by
      exact hf_C2.contDiffAt (isOpen_interior.mem_nhds (hline_mem_int t ht))
    -- On the open interval `(0,1)`, the ambient derivative is also the within-interval derivative.
    exact (corrected_line_hasDerivAt (p := p) (x := x) (d := d) (t := t) μ htC2).hasDerivWithinAt
  have hφ'' :
      ∀ t ∈ interior I,
        HasDerivWithinAt
          (fun s : ℝ ↦ inner ℝ (∇ f (x + s • d)) d - μ * (p d) ^ (2 : ℕ) * s)
          (inner ℝ (hessian f (x + t • d) d) d - μ * (p d) ^ (2 : ℕ))
          (interior I) t := by
    intro t ht
    have htC2 : ContDiffAt ℝ 2 f (x + t • d) := by
      exact hf_C2.contDiffAt (isOpen_interior.mem_nhds (hline_mem_int t ht))
    have hderivAt :=
      corrected_line_deriv_hasDerivAt (p := p) (x := x) (d := d) (t := t) μ htC2
    -- Differentiate the corrected one-dimensional derivative.
    exact hderivAt.hasDerivWithinAt
  have hφ''_nonneg :
      ∀ t ∈ interior I,
        0 ≤ inner ℝ (hessian f (x + t • d) d) d - μ * (p d) ^ (2 : ℕ) := by
    intro t ht
    have htdom : x + t • d ∈ interior Q := hline_mem_int t ht
    -- The Hessian lower bound says exactly that the corrected second derivative is nonnegative.
    linarith [hquad (x + t • d) htdom d]
  -- The corrected line restriction is convex because its second derivative is nonnegative.
  simpa [I, φ] using
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc (0 : ℝ) 1) hφ_cont hφ' hφ'' hφ''_nonneg

/-- Helper for Theorem 2.12: the source-facing lower-tangent inequality on a convex set is
equivalent to the Hessian quadratic-form lower bound on the interior. -/
private theorem interior_lower_tangent_quadratic_iff_hessian_quadratic_form_lower_bound_aux
    (μ : ℝ) (hQ_conv : Convex ℝ Q) (hf_cont : ContinuousOn f Q)
    (hf_C2 : ContDiffOn ℝ 2 f (interior Q)) :
    (∀ x : E, x ∈ interior Q → ∀ y : E, y ∈ Q →
      f y ≥ f x + inner ℝ (∇ f x) (y - x) + (μ / 2) * (p (y - x)) ^ 2) ↔
      ∀ x ∈ interior Q, ∀ h : E,
        μ * (p h) ^ 2 ≤ inner ℝ (hessian f x h) h := by
  constructor
  · intro hlower x hx h
    by_cases hh : h = 0
    · -- The zero direction is immediate.
      simp [hh]
    rcases Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hx) with ⟨r, hr_pos, hr_ball⟩
    let δ : ℝ := r / (2 * ‖h‖)
    let I : Set ℝ := Set.Icc (-δ) δ
    have hnorm_pos : 0 < ‖h‖ := norm_pos_iff.mpr hh
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      positivity
    have hzero_mem : (0 : ℝ) ∈ I := by
      dsimp [I]
      constructor <;> linarith
    have hline_mem : Set.MapsTo (fun t : ℝ ↦ x + t • h) I (interior Q) := by
      intro t ht
      apply hr_ball
      rw [Metric.mem_ball, dist_eq_norm]
      have habs : |t| ≤ δ := by
        exact abs_le.mpr ⟨ht.1, ht.2⟩
      have hnorm :
          ‖x + t • h - x‖ = |t| * ‖h‖ := by
        calc
          ‖x + t • h - x‖ = ‖t • h‖ := by
            congr
            abel_nf
          _ = |t| * ‖h‖ := by
            simpa [Real.norm_eq_abs] using norm_smul t h
      have hhalf : δ * ‖h‖ = r / 2 := by
        dsimp [δ]
        field_simp [hnorm_pos.ne']
      have hbound : ‖x + t • h - x‖ < r := by
        rw [hnorm]
        have hle : |t| * ‖h‖ ≤ r / 2 := by
          calc
            |t| * ‖h‖ ≤ δ * ‖h‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg _)
            _ = r / 2 := hhalf
        linarith
      simpa using hbound
    let φ : ℝ → ℝ := fun t ↦ f (x + t • h) - ((μ / 2) * (p h) ^ (2 : ℕ)) * t ^ (2 : ℕ)
    let g : ℝ → ℝ := fun t ↦ inner ℝ (∇ f (x + t • h)) h - μ * (p h) ^ (2 : ℕ) * t
    have hline_lower :
        ∀ s ∈ I, ∀ t ∈ I, φ t ≥ φ s + g s * (t - s) := by
      intro s hs t ht
      have hs_int : x + s • h ∈ interior Q := hline_mem hs
      have ht_int : x + t • h ∈ interior Q := hline_mem ht
      have hbase := hlower (x + s • h) hs_int (x + t • h) (interior_subset ht_int)
      have hsub : x + t • h - (x + s • h) = (t - s) • h := by
        calc
          x + t • h - (x + s • h) = t • h - s • h := by
            abel_nf
          _ = (t - s) • h := by
            rw [sub_smul]
      have hp :
          (p ((t - s) • h)) ^ (2 : ℕ) =
            (t - s) ^ (2 : ℕ) * (p h) ^ (2 : ℕ) := by
        rw [map_smul_eq_mul]
        rw [Real.norm_eq_abs, mul_pow, sq_abs]
      have hbase' :
          f (x + t • h) ≥
            f (x + s • h) + (t - s) * inner ℝ (∇ f (x + s • h)) h +
              ((μ / 2) * (p h) ^ (2 : ℕ)) * (t - s) ^ (2 : ℕ) := by
        rw [hsub, real_inner_smul_right] at hbase
        rw [hp] at hbase
        simpa [mul_assoc, mul_left_comm, mul_comm] using hbase
      -- Repackage the tangent inequality as a one-variable lower support condition.
      dsimp [φ, g]
      linarith
    have hg_mono : MonotoneOn g I :=
      monotoneOn_of_lower_tangent hline_lower
    have hxC2 : ContDiffAt ℝ 2 f x := hf_C2.contDiffAt (isOpen_interior.mem_nhds hx)
    have hderiv :
        HasDerivWithinAt g
          (inner ℝ (hessian f x h) h - μ * (p h) ^ (2 : ℕ))
          I 0 := by
      simpa [g] using
        (corrected_line_deriv_hasDerivAt (p := p) (x := x) (d := h) (t := 0) μ
          (by simpa using hxC2)).hasDerivWithinAt
    have hnonneg : 0 ≤ derivWithin g I 0 := by
      simpa using (hg_mono.derivWithin_nonneg : 0 ≤ derivWithin g I 0)
    have hderiv_eq :
        derivWithin g I 0 = inner ℝ (hessian f x h) h - μ * (p h) ^ (2 : ℕ) := by
      exact hderiv.derivWithin ((uniqueDiffOn_Icc (show -δ < δ by linarith)).uniqueDiffWithinAt
        hzero_mem)
    rw [hderiv_eq] at hnonneg
    linarith
  · intro hquad x hx y hy
    let d : E := y - x
    let φ : ℝ → ℝ := fun t ↦ f (x + t • d) - ((μ / 2) * (p d) ^ (2 : ℕ)) * t ^ (2 : ℕ)
    have hφ_conv :
        ConvexOn ℝ (Set.Icc (0 : ℝ) 1) φ := by
      simpa [φ, d] using
        corrected_segment_convexOn_of_hessian_lower_bound
          (p := p) (Q := Q) (f := f) μ hQ_conv hf_cont hf_C2 hquad hx hy
    have hxC2 : ContDiffAt ℝ 2 f x := hf_C2.contDiffAt (isOpen_interior.mem_nhds hx)
    have hderiv0 :
        HasDerivWithinAt φ (inner ℝ (∇ f x) d) (Set.Icc (0 : ℝ) 1) 0 := by
      -- The quadratic correction has zero derivative at the left endpoint.
      simpa [φ, d] using
        (corrected_line_hasDerivAt (p := p) (x := x) (d := d) (t := 0) μ
          (by simpa using hxC2)).hasDerivWithinAt
    have hslope :=
      hφ_conv.le_slope_of_hasDerivWithinAt (by simp) (by simp) zero_lt_one hderiv0
    have hslope' :
        inner ℝ (∇ f x) d ≤ f (x + 1 • d) - ((μ / 2) * (p d) ^ (2 : ℕ)) - f x := by
      simpa [φ, d, slope] using hslope
    have hslope'' :
        inner ℝ (∇ f x) d ≤ f y - ((μ / 2) * (p d) ^ (2 : ℕ)) - f x := by
      simpa [d] using hslope'
    have hresult :
        f y ≥ f x + inner ℝ (∇ f x) (y - x) + (μ / 2) * (p (y - x)) ^ 2 := by
      linarith [hslope'']
    simpa using hresult

namespace StrongConvexOnWith

/-- On an open convex owner domain, positive-parameter strong convexity with respect to an
arbitrary seminorm is equivalent to the pointwise Hessian quadratic-form lower bound. The
source-facing theorem below specializes this intrinsic owner statement to `U = interior Q` and
then extends the lower-tangent inequality from `x ∈ interior Q` to arbitrary `y ∈ Q`. -/
theorem iff_hessian_quadratic_form_lower_bound
    (hμ : 0 < μ) (hU_open : IsOpen U) (hU_conv : Convex ℝ U) (hf_C2 : ContDiffOn ℝ 2 f U) :
    StrongConvexOnWith p μ U f ↔
      ∀ x ∈ U, ∀ h : E,
        μ * (p h) ^ 2 ≤ inner ℝ (hessian f x h) h := by
  constructor
  · intro hf
    have hf_cont : ContinuousOn f U := hf_C2.continuousOn
    have hlower :
        ∀ x : E, x ∈ interior U → ∀ y : E, y ∈ U →
          f y ≥ f x + inner ℝ (∇ f x) (y - x) + (μ / 2) * (p (y - x)) ^ 2 := by
      intro x hx y hy
      have hxU : x ∈ U := by simpa [hU_open.interior_eq] using hx
      have hxC2 : ContDiffAt ℝ 2 f x := hf_C2.contDiffAt (hU_open.mem_nhds hxU)
      have hdiffx : DifferentiableAt ℝ f x :=
        (hxC2.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiableAt one_ne_zero
      have hgradx : HasGradientAt f (∇ f x) x := hdiffx.hasGradientAt
      -- Strong convexity gives the corrected lower tangent inequality on the owner domain.
      exact hf.lower_tangent_quadratic hxU hy hgradx
    -- Specialize the source-facing equivalence to the open owner domain `U = interior U`.
    simpa [hU_open.interior_eq] using
      (interior_lower_tangent_quadratic_iff_hessian_quadratic_form_lower_bound_aux
        (p := p) (Q := U) (f := f) μ hU_conv hf_cont
        (by simpa [hU_open.interior_eq] using hf_C2)).1 hlower
  · intro hquad
    refine ⟨hU_conv, hμ, ?_⟩
    intro x hx y hy a b ha hb hab
    let d : E := y - x
    let c : ℝ := (μ / 2) * (p d) ^ (2 : ℕ)
    let φ : ℝ → ℝ := fun t ↦ f (x + t • d) - ((μ / 2) * (p d) ^ (2 : ℕ)) * t ^ (2 : ℕ)
    have hx_int : x ∈ interior U := by simpa [hU_open.interior_eq] using hx
    have hφ_conv :
        ConvexOn ℝ (Set.Icc (0 : ℝ) 1) φ := by
      simpa [φ, d, hU_open.interior_eq] using
        corrected_segment_convexOn_of_hessian_lower_bound
          (p := p) (Q := U) (f := f) μ hU_conv hf_C2.continuousOn
          (by simpa [hU_open.interior_eq] using hf_C2)
          (by simpa [hU_open.interior_eq] using hquad) hx_int hy
    have hsegment :
        φ (a • (0 : ℝ) + b • (1 : ℝ)) ≤ a • φ 0 + b • φ 1 := by
      exact hφ_conv.2 (by simp) (by simp) ha hb hab
    have hab' : a = 1 - b := by
      linarith
    have hline_eq : x + b • d = a • x + b • y := by
      calc
        x + b • d = (1 - b) • x + b • y := by
          simp [d, sub_eq_add_neg, smul_add, add_smul, add_left_comm, add_comm]
        _ = a • x + b • y := by
          rw [hab']
    have hp_sym : p d = p (x - y) := by
      simpa [d, sub_eq_add_neg] using (map_neg_eq_map p (x - y))
    have hsegment' :
        f (a • x + b • y) - c * b ^ (2 : ℕ) ≤ a * f x + b * (f y - c) := by
      simpa [φ, c, hline_eq, d, smul_eq_mul] using hsegment
    -- Evaluate convexity of the corrected line restriction at the endpoint weights `a, b`.
    have hresult :
        f (a • x + b • y) ≤
          a • f x + b • f y - a * b * ((μ / 2) * (p (x - y)) ^ (2 : ℕ)) := by
      dsimp [c] at hsegment'
      rw [hp_sym] at hsegment'
      have hab'' : a * b = b - b ^ (2 : ℕ) := by
        nlinarith [hab]
      have hresult' :
          f (a • x + b • y) ≤
            a * f x + b * f y - (b - b ^ (2 : ℕ)) * ((μ / 2) * (p (x - y)) ^ (2 : ℕ)) := by
        linarith [hsegment']
      rw [smul_eq_mul, smul_eq_mul, hab'']
      exact hresult'
    simpa [smul_eq_mul] using hresult

end StrongConvexOnWith

/-- Theorem 2.12 on the canonical owner layer: for a convex set in a real Hilbert space, a
function that is continuous on `Q` and `C²` on `interior Q` satisfies the strong-convexity tangent
inequality with parameter `μ` if and only if its Hessian quadratic form is bounded below by
`μ ‖h‖²_p` at every interior point. The theorem stays at the arbitrary-seminorm owner layer of
`Definition_2_14`; the textbook `ℝⁿ` statement is the finite-dimensional specialization. -/
-- Proof sketch: for the forward implication, restrict `f` to each line `α ↦ x + α • h`,
-- apply the defining lower tangent inequality with `y = x + α • h`, divide by `α ^ 2`, and let
-- `α → 0` to identify the limit with `⟪hessian f x h, h⟫`. For `0 < μ`, the intrinsic owner layer
-- is `StrongConvexOnWith p μ (interior Q) f`, identified above with the same Hessian lower bound
-- on the open convex owner domain `interior Q`.
-- For the displayed source-facing statement, fix `x ∈ interior Q` and `y ∈ Q`, study
-- `t ↦ f (x + t • (y - x))` on `[0,1]`, use convexity of `Q` to keep the segment inside
-- `interior Q` for `t < 1`, integrate the lower bound on the second derivative, and recover the
-- quadratic lower tangent inequality at `t = 1`. No explicit nonempty-interior hypothesis is
-- needed in Lean because both sides quantify only over `x ∈ interior Q`.
theorem interior_lower_tangent_quadratic_iff_hessian_quadratic_form_lower_bound
    (μ : ℝ) (hQ_conv : Convex ℝ Q) (hf_cont : ContinuousOn f Q)
    (hf_C2 : ContDiffOn ℝ 2 f (interior Q)) :
    (∀ x : E, x ∈ interior Q → ∀ y : E, y ∈ Q →
      f y ≥ f x + inner ℝ (∇ f x) (y - x) + (μ / 2) * (p (y - x)) ^ 2) ↔
      ∀ x ∈ interior Q, ∀ h : E,
        μ * (p h) ^ 2 ≤ inner ℝ (hessian f x h) h := by
  -- The source-facing theorem is exactly the private helper proved above.
  simpa using
    interior_lower_tangent_quadratic_iff_hessian_quadratic_form_lower_bound_aux
      (p := p) (Q := Q) (f := f) μ hQ_conv hf_cont hf_C2

end
