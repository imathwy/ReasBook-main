import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_23 (from Chap02) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: finite-window best-gradient quantities along first-order iterate sequences on a
real Hilbert space.

Owner-style declarations sampled before refining this file:
* `Finset.inf'`, the mathlib owner for minima over nonempty finite sets;
* `Finset.inf'_le`, the canonical pointwise upper-bound API for that owner;
* `Finset.exists_mem_eq_inf'`, the canonical attainment API for that owner;
* `minGradientNormAlongIterates_le_sqrt` in `Chap01/Theorem_1_6_8`, the direct downstream chapter
  consumer of the source-facing quantity defined here.

Source/core/bridge triage:
* source-facing: the textbook quantity `g_{k,T}`;
* core/canonical: the nonempty finite interval `Finset.Icc k T` together with `Finset.inf'`;
* bridge/view: the interval-membership and attainment consequences specialized to gradient norms.

Primitive data:
* the objective `f`;
* the iterate sequence `x`;
* the window endpoints `k ≤ T`.

Derived API:
* the pointwise bound `minGradientNormAlongIterates.le`;
* the attainment statement `minGradientNormAlongIterates.exists_eq`.

No earlier project owner packages this finite-window minimum pattern, so the correct owner
abstraction here is the direct `Finset.inf'` specialization rather than a new wrapper structure.
This file therefore keeps the source-facing owner `minGradientNormAlongIterates` and exposes only
the two canonical derived consequences directly from that owner. -/

/-- Definition 2.23: for iterates `xᵢ` of a differentiable function `f : E → ℝ` on a real Hilbert
space and indices `k ≤ T`, `g[f; x; k, T | h]` is the minimum of `‖∇ f (xᵢ)‖` over all `i` with
`k ≤ i ≤ T`. -/
def minGradientNormAlongIterates (f : E → ℝ) (x : ℕ → E)
    (k T : ℕ) (h : k ≤ T) : ℝ :=
  (Finset.Icc k T).inf' (Finset.nonempty_Icc.2 h) (fun i ↦ ‖∇ f (x i)‖)

/-
Source-facing notation for Definition 2.23: `g[f; x; k, T | h]` is the textbook quantity
`g_{k,T}` attached to the objective `f`, iterate sequence `x`, and window proof `h : k ≤ T`.
-/
namespace MinGradientNormAlongIterates

scoped notation:max "g[" f ";" x ";" k "," T "|" h "]" =>
  minGradientNormAlongIterates f x k T h

end MinGradientNormAlongIterates

open scoped MinGradientNormAlongIterates

/-- Unfolding `g[f; x; k, T | h]` gives the canonical finite-interval infimum formula from
Definition 2.23. -/
@[simp] theorem minGradientNormAlongIterates_def (f : E → ℝ) (x : ℕ → E) (k T : ℕ)
    (h : k ≤ T) :
    g[f; x; k, T | h] =
      (Finset.Icc k T).inf' (Finset.nonempty_Icc.2 h) (fun i ↦ ‖∇ f (x i)‖) := rfl

namespace minGradientNormAlongIterates

/-- The window minimum `g[f; x; k, T | h]` is bounded above by each sampled gradient norm in the
same window. -/
theorem le (f : E → ℝ) (x : ℕ → E)
    {k T i : ℕ} (h : k ≤ T) (hki : k ≤ i) (hiT : i ≤ T) :
    g[f; x; k, T | h] ≤ ‖∇ f (x i)‖ := by
  rw [minGradientNormAlongIterates_def]
  exact Finset.inf'_le (fun j ↦ ‖∇ f (x j)‖) (Finset.mem_Icc.mpr ⟨hki, hiT⟩)

/-- Some index in the window `k ≤ i ≤ T` attains the minimum gradient norm
`g[f; x; k, T | h]`. -/
theorem exists_eq (f : E → ℝ) (x : ℕ → E)
    {k T : ℕ} (h : k ≤ T) :
    ∃ i, k ≤ i ∧ i ≤ T ∧
      g[f; x; k, T | h] = ‖∇ f (x i)‖ := by
  rcases (Finset.Icc k T).exists_mem_eq_inf' (Finset.nonempty_Icc.2 h)
      (fun i ↦ ‖∇ f (x i)‖) with ⟨i, hi, hmin⟩
  rcases Finset.mem_Icc.mp hi with ⟨hki, hiT⟩
  exact ⟨i, hki, hiT, hmin⟩

end minGradientNormAlongIterates

/-! ### Lemma_2_23 (from Chap02) -/
noncomputable section

universe u

namespace LagrangianProblem

variable {E : Type u} {m : ℕ}

/- Primary domain: the auxiliary max-violation value function attached to an inequality-constrained
optimization problem.

Owner abstractions sampled before refining:
- `LagrangianProblem` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_10_2.lean`, which owns the primitive
  objective-plus-constraints data;
- `LagrangianProblem.constrainedAuxiliaryObjective` in `LecturesConvexOptimization_Nesterov_2018/Chap02/Lemma_2_21.lean`,
  the canonical auxiliary objective `x ↦ max {f₀(x) - t, f₁(x), …, fₘ(x)}`;
- `LagrangianProblem.constrainedAuxiliaryOptimalValue` in
  `LecturesConvexOptimization_Nesterov_2018/Chap02/Lemma_2_21.lean`, the derived extended-real infimum value of that owner
  objective;
- `LagrangianProblem.constrainedAuxiliaryOptimalValue_eq_of_isMinOn` in
  `LecturesConvexOptimization_Nesterov_2018/Chap02/Lemma_2_21.lean`, the owner attained-value bridge used to replace chosen
  minimizer evaluations by the canonical value function.

The primitive owner here is `LagrangianProblem E m`. For the displayed one-variable inequality, the
owner abstractions are the product-space convexity of
`problem.constrainedAuxiliaryObjective` and the attained-minimum bridge
`constrainedAuxiliaryOptimalValue_eq_of_isMinOn`: this file follows the source proof directly by
proving the convex-combination inequality for attained values and then rearranging the resulting
scalar algebra. Accordingly, the auxiliary objective and its optimal value stay derived owner
declarations, and attainment is kept as intrinsic `IsMinOn` data rather than as a chosen public
optimizer family.

Source/core/bridge triage:
- source-facing: Lemma 2.23's secant estimate for the auxiliary optimal-value function;
- core/canonical: `problem.constrainedAuxiliaryObjective t`,
  `problem.constrainedAuxiliaryOptimalValue t`, mathlib's `IsMinOn`, and product-space
  `ConvexOn`;
- bridge/view: the attained-minimum identity
  `constrainedAuxiliaryOptimalValue_eq_of_isMinOn`, which turns the extended-real owner value into
  the attained real value needed for the one-variable secant comparison; that bridge is already
  owned by `Lemma_2_22`.
-/

section SecantLowerBound

variable [AddCommMonoid E] [Module ℝ E]
variable (problem : LagrangianProblem E m)

/-- If the objective and each constraint are convex on the ambient module, then the auxiliary
objective is jointly convex in the scalar parameter and primal variable on `ℝ × E`. This is the
canonical bridge from the owner data `problem`, `problem.constraints`, and
`problem.constrainedAuxiliaryObjective` to the product-space `ConvexOn` API used downstream by
Lemma 2.23. -/
theorem constrainedAuxiliaryObjective_jointConvexOn
    (hobjective : ConvexOn ℝ Set.univ problem)
    (hconstraints : ∀ i, ConvexOn ℝ Set.univ (problem.constraints i)) :
    ConvexOn ℝ Set.univ
      (fun p : ℝ × E ↦ problem.constrainedAuxiliaryObjective p.1 p.2) := by
  have hcomponents :
      ∀ j : Fin (m + 1),
        ConvexOn ℝ Set.univ
          (fun p : ℝ × E ↦ problem.constrainedAuxiliaryComponents p.1 j p.2) := by
    intro j
    refine Fin.cases ?_ ?_ j
    · refine ⟨convex_univ, ?_⟩
      rintro ⟨s, x⟩ hs ⟨t, y⟩ ht a b ha hb hab
      simpa [constrainedAuxiliaryComponents, sub_eq_add_neg, mul_add, add_mul, add_assoc,
        add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm, smul_add] using
        hobjective.2 (by simp) (by simp) ha hb hab
    · intro i
      refine ⟨convex_univ, ?_⟩
      rintro ⟨s, x⟩ hs ⟨t, y⟩ ht a b ha hb hab
      simpa [constrainedAuxiliaryComponents] using
        (hconstraints i).2 (by simp) (by simp) ha hb hab
  simpa [constrainedAuxiliaryObjective] using
    maxTypeObjective_convexOn Set.univ
      (fun j : Fin (m + 1) ↦ fun p : ℝ × E ↦ problem.constrainedAuxiliaryComponents p.1 j p.2)
      hcomponents

omit [AddCommMonoid E] [Module ℝ E] in
/-- Helper for Lemma 2.23: any chosen attained minimizer realizes the canonical auxiliary optimal
value. -/
lemma attained_auxiliary_value_eq_optimal_value
    (xMin : ℝ → E)
    (hxMin : ∀ t : ℝ, IsMinOn (problem.constrainedAuxiliaryObjective t) Set.univ (xMin t)) :
    ∀ t : ℝ,
      problem.constrainedAuxiliaryOptimalValue t =
        ((problem.constrainedAuxiliaryObjective t (xMin t)) : EReal) := by
  intro t
  -- The owner attained-value bridge identifies the infimum with the chosen minimum value.
  simpa using problem.constrainedAuxiliaryOptimalValue_eq_of_isMinOn (hxMin t)

/-- Helper for Lemma 2.23: the attained auxiliary values satisfy the source convex-combination
inequality obtained from the joint convexity of the auxiliary objective. -/
lemma attained_auxiliary_value_convex_combination
    (hobjective : ConvexOn ℝ Set.univ problem)
    (hconstraints : ∀ i, ConvexOn ℝ Set.univ (problem.constraints i))
    (xMin : ℝ → E)
    (hxMin : ∀ t : ℝ, IsMinOn (problem.constrainedAuxiliaryObjective t) Set.univ (xMin t))
    {t0 t1 t2 α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hmid : t1 = (1 - α) * t0 + α * t2) :
    problem.constrainedAuxiliaryObjective t1 (xMin t1) ≤
      (1 - α) * problem.constrainedAuxiliaryObjective t0 (xMin t0) +
        α * problem.constrainedAuxiliaryObjective t2 (xMin t2) := by
  have haux_convex :
      ConvexOn ℝ Set.univ
        (fun p : ℝ × E ↦ problem.constrainedAuxiliaryObjective p.1 p.2) :=
    problem.constrainedAuxiliaryObjective_jointConvexOn hobjective hconstraints
  let xAlpha : E := (1 - α) • xMin t0 + α • xMin t2
  have hmin_t1 :
      problem.constrainedAuxiliaryObjective t1 (xMin t1) ≤
        problem.constrainedAuxiliaryObjective t1 xAlpha := by
    -- Minimality at `t1` is evaluated at the interpolated primal point `xAlpha`.
    exact (isMinOn_univ_iff.mp (hxMin t1)) xAlpha
  have hconv :
      problem.constrainedAuxiliaryObjective ((1 - α) * t0 + α * t2) xAlpha ≤
        (1 - α) * problem.constrainedAuxiliaryObjective t0 (xMin t0) +
          α * problem.constrainedAuxiliaryObjective t2 (xMin t2) := by
    -- Joint convexity supplies the Jensen estimate for the pair `(t, x)`.
    have hconv' :=
      haux_convex.2 (by simp : (t0, xMin t0) ∈ Set.univ) (by simp : (t2, xMin t2) ∈ Set.univ)
        (sub_nonneg.mpr hα1) hα0 (by ring)
    change problem.constrainedAuxiliaryObjective ((1 - α) * t0 + α * t2)
        ((1 - α) • xMin t0 + α • xMin t2) ≤
      (1 - α) * problem.constrainedAuxiliaryObjective t0 (xMin t0) +
        α * problem.constrainedAuxiliaryObjective t2 (xMin t2) at hconv'
    simpa [xAlpha] using hconv'
  -- The source route is: minimality at `t1`, then convexity at the interpolated point.
  calc
    problem.constrainedAuxiliaryObjective t1 (xMin t1)
        ≤ problem.constrainedAuxiliaryObjective t1 xAlpha := hmin_t1
    _ = problem.constrainedAuxiliaryObjective ((1 - α) * t0 + α * t2) xAlpha := by rw [hmid]
    _ ≤ (1 - α) * problem.constrainedAuxiliaryObjective t0 (xMin t0) +
          α * problem.constrainedAuxiliaryObjective t2 (xMin t2) := hconv

/-- Helper for Lemma 2.23: the convex-combination inequality with the source coefficient
`Δ / (t₂ - t₁ + Δ)` rearranges to the left-shifted secant lower bound. -/
lemma left_shift_secant_of_convex_combination
    {g : ℝ → ℝ} {t1 t2 Delta : ℝ}
    (ht : t1 < t2) (hDelta : 0 ≤ Delta)
    (hcombo :
      g t1 ≤
        ((t2 - t1) / (t2 - t1 + Delta)) * g (t1 - Delta) +
          (Delta / (t2 - t1 + Delta)) * g t2) :
    g (t1 - Delta) ≥ g t1 +
      (Delta / (t2 - t1)) * (g t1 - g t2) := by
  have hc : 0 < t2 - t1 := sub_pos.mpr ht
  have hd : 0 < t2 - t1 + Delta := add_pos_of_pos_of_nonneg hc hDelta
  have hmul := mul_le_mul_of_nonneg_left hcombo hd.le
  have hmul' :
      (t2 - t1 + Delta) * g t1 ≤ (t2 - t1) * g (t1 - Delta) + Delta * g t2 := by
    have htmp := hmul
    -- Clearing the positive denominator converts the convex combination into a linear inequality.
    field_simp [hd.ne'] at htmp
    ring_nf at htmp
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add, add_mul] using htmp
  have hfinal :
      (t2 - t1) * (g t1 + (Delta / (t2 - t1)) * (g t1 - g t2)) ≤
        (t2 - t1) * g (t1 - Delta) := by
    have hrewrite :
        (t2 - t1) * (g t1 + (Delta / (t2 - t1)) * (g t1 - g t2)) =
          (t2 - t1 + Delta) * g t1 - Delta * g t2 := by
      field_simp [hc.ne']
      ring
    rw [hrewrite]
    linarith
  -- Dividing by the positive secant length recovers the desired one-sided slope estimate.
  exact le_of_mul_le_mul_left hfinal hc

/-- Lemma 2.23: if the objective and all constraint functions are convex and the auxiliary minimum
is attained for every parameter `t`, then the auxiliary optimal value function satisfies the
displayed left-shifted secant lower bound. This follows the source proof directly: choose attained
minimizers, prove the convex-combination inequality for the attained real values, and then rewrite
the result back into the canonical extended-real optimal-value notation. -/
theorem constrainedAuxiliaryOptimalValue_secant_lower_bound
    (hobjective : ConvexOn ℝ Set.univ problem)
    (hconstraints : ∀ i, ConvexOn ℝ Set.univ (problem.constraints i))
    (hattained :
      ∀ t : ℝ, ∃ x : E, IsMinOn (problem.constrainedAuxiliaryObjective t) Set.univ x)
    {t1 t2 Delta : ℝ} (ht : t1 < t2) (hDelta : 0 ≤ Delta) :
    problem.constrainedAuxiliaryOptimalValue (t1 - Delta) ≥
      problem.constrainedAuxiliaryOptimalValue t1 +
        (Delta / (t2 - t1)) *
          (problem.constrainedAuxiliaryOptimalValue t1 -
            problem.constrainedAuxiliaryOptimalValue t2) := by
  let xMin : ℝ → E := fun t ↦ Classical.choose (hattained t)
  have hxMin : ∀ t : ℝ, IsMinOn (problem.constrainedAuxiliaryObjective t) Set.univ (xMin t) := by
    intro t
    simpa [xMin] using Classical.choose_spec (hattained t)
  let V : ℝ → ℝ := fun t ↦ problem.constrainedAuxiliaryObjective t (xMin t)
  have hV : ∀ t : ℝ, problem.constrainedAuxiliaryOptimalValue t = (V t : EReal) := by
    intro t
    simpa [V] using problem.attained_auxiliary_value_eq_optimal_value xMin hxMin t
  let t0 : ℝ := t1 - Delta
  let α : ℝ := Delta / (t2 - t1 + Delta)
  have hgap : 0 < t2 - t1 := sub_pos.mpr ht
  have hdenom : 0 < t2 - t1 + Delta := add_pos_of_pos_of_nonneg hgap hDelta
  have hOneSubAlpha :
      1 - α = (t2 - t1) / (t2 - t1 + Delta) := by
    dsimp [α]
    field_simp [hdenom.ne']
    ring
  have hα0 : 0 ≤ α := by
    dsimp [α]
    exact div_nonneg hDelta hdenom.le
  have hα1 : α ≤ 1 := by
    have hOneSubAlpha_nonneg : 0 ≤ 1 - α := by
      rw [hOneSubAlpha]
      exact div_nonneg hgap.le hdenom.le
    linarith
  have hmid : t1 = (1 - α) * t0 + α * t2 := by
    dsimp [t0, α]
    field_simp [hdenom.ne']
    ring
  have hcombo :
      V t1 ≤ (1 - α) * V t0 + α * V t2 := by
    -- Route correction: prove the source convex-combination estimate directly instead of calling
    -- the later secant theorem from Proposition 2.26.
    simpa [V, t0] using
      problem.attained_auxiliary_value_convex_combination
        hobjective hconstraints xMin hxMin hα0 hα1 hmid
  have hcombo' :
      V t1 ≤
        ((t2 - t1) / (t2 - t1 + Delta)) * V (t1 - Delta) +
          (Delta / (t2 - t1 + Delta)) * V t2 := by
    -- Rewriting the convex weights prepares the scalar inequality for the secant rearrangement.
    simpa [t0, α, hOneSubAlpha] using hcombo
  have hsecant :
      V (t1 - Delta) ≥ V t1 + (Delta / (t2 - t1)) * (V t1 - V t2) :=
    left_shift_secant_of_convex_combination ht hDelta hcombo'
  have hsecantEReal :
      (V (t1 - Delta) : EReal) ≥
        ((V t1 + (Delta / (t2 - t1)) * (V t1 - V t2) : ℝ) : EReal) := by
    -- The convexity computation was carried out in `ℝ`; only the final comparison is cast back.
    exact_mod_cast hsecant
  rw [hV (t1 - Delta), hV t1, hV t2]
  simpa using hsecantEReal

end SecantLowerBound

end LagrangianProblem

/-! ### Proposition_2_23 (from Chap02) -/
open scoped Gradient StrongConvexSmooth

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Primary domain: linear convergence of gradient descent on strongly convex smooth objectives over
real Hilbert spaces.

Owner-style declarations sampled before refining this file:
* `IsStrongConvexSmoothObjective` in `Definition_2_17`
* `gradientMethod` in `Algorithm_2_1`
* `IsStrongConvexSmoothObjective.pairing_lower_bound` in `Theorem_2_13`
* `gradientMethod_sqdist_le_geometric_rate` in `Theorem_2_17`

Source/core/bridge triage:
* source-facing: Proposition 2.23, the `h = 1 / L` contraction estimate;
* core/canonical: `gradientMethod_sqdist_le_geometric_rate`;
* bridge/view: the scalar comparison `((L - μ) / (L + μ)) ≤ 1 - μ / L`, with the textbook
  Euclidean `ℝⁿ` statement recovered by specializing `E`.

Primitive data:
* `hf : f ∈ 𝓢[μ, L]¹¹`;
* `hxStar : IsMinOn f Set.univ xStar`;
* `x0 : E`;
* `k : ℕ`.

Derived API:
* `μ ≤ L`, derived from the owner hypothesis in the nontrivial ambient case via
  `IsStrongConvexSmoothObjective.mu_le_L`;
* positivity of `L`, since `0 < μ ≤ L` then follows in the nontrivial case;
* admissibility of the step size `1 / L`;
* the sharper contraction factor from `Theorem_2_17`, relaxed to the source-facing factor
  `1 - q[μ, L] = 1 - μ / L`.

Accordingly, this file keeps no parallel local owner theorem for the same contraction estimate: it
states Proposition 2.23 as a direct corollary of `gradientMethod_sqdist_le_geometric_rate` on the
intrinsic real-Hilbert-space owner layer, with the textbook `ℝⁿ` case treated only as a
specialization.
-/

section

variable {μ L : ℝ} {f : E → ℝ}

/- Proposition 2.23 is stated in the text for `ℝⁿ`; the theorem below records the same
`h = 1 / L` contraction on the ambient real Hilbert-space owner abstraction and hence
specializes back to the Euclidean case. -/
/-- Proposition 2.23: if `f : E → ℝ` lies in the strongly convex smooth class `𝓢^{1,1}_{μ,L}`,
`xStar` is a
minimizer of `f`, and gradient descent uses the constant step size `1 / L`, then the iterates
satisfy the linear squared-distance contraction
`‖x_k - xStar‖² ≤ (1 - q[μ, L])^k ‖x₀ - xStar‖²`, equivalently
`‖x_k - xStar‖² ≤ (1 - μ / L)^k ‖x₀ - xStar‖²`. The textbook `ℝⁿ` statement is the
specialization `E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: specialize the owner estimate
-- `gradientMethod_sqdist_le_geometric_rate` from `Theorem_2_17` to the constant step size
-- `h = 1 / L`, obtaining the sharper factor `((L - μ) / (L + μ))^k`. Then compare
-- `((L - μ) / (L + μ))` with `1 - q[μ, L] = 1 - μ / L` using the owner-derived inequality
-- `μ ≤ L` in the nontrivial ambient case; the subsingleton case is tautological.
theorem gradientMethod_sqdist_le_geometric_rate_step_inv_L
    (hf : f ∈ 𝓢[μ, L]¹¹)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E) (k : ℕ) :
    ‖gradientMethod (fun _ ↦ 1 / L) f x0 k - xStar‖ ^ (2 : ℕ) ≤
      (1 - q[μ, L]) ^ k * ‖x0 - xStar‖ ^ (2 : ℕ) := by
  by_cases hE : Subsingleton E
  · have hx0 : x0 = xStar := hE.elim _ _
    subst hx0
    have hxk : gradientMethod (fun _ ↦ 1 / L) f x0 k = x0 := hE.elim _ _
    calc
      ‖gradientMethod (fun _ ↦ 1 / L) f x0 k - x0‖ ^ (2 : ℕ) = 0 := by
        rw [hxk]
        simp
      _ ≤ (1 - q[μ, L]) ^ k * ‖x0 - x0‖ ^ (2 : ℕ) := by
        simp
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    have hf' : IsStrongConvexSmoothObjective μ L f := mem_S11_iff.mp hf
    have hμL : μ ≤ L := hf'.mu_le_L
    have hL : 0 < L := lt_of_lt_of_le hf'.mu_pos hμL
    have hden : 0 < μ + L := by
      nlinarith [hf'.mu_pos, hμL]
    have hh0 : 0 < 1 / L := by
      positivity
    have hh : 1 / L ≤ 2 / (μ + L) := by
      have hL_ne : L ≠ 0 := ne_of_gt hL
      have hden_ne : μ + L ≠ 0 := ne_of_gt hden
      field_simp [hL_ne, hden_ne]
      nlinarith
    have hnum : 2 * (1 / L) * μ * L = 2 * μ := by
      have hL_ne : L ≠ 0 := ne_of_gt hL
      field_simp [hL_ne]
    have hleft : 1 - (2 * μ) / (μ + L) = (L - μ) / (μ + L) := by
      have hden_ne : μ + L ≠ 0 := ne_of_gt hden
      field_simp [hden_ne]
      nlinarith
    have hsq :=
      gradientMethod_sqdist_le_geometric_rate hf hxStar (1 / L) hh0 hh x0 k
    have hfactor_nonneg : 0 ≤ 1 - (2 * (1 / L) * μ * L) / (μ + L) := by
      rw [hnum, hleft]
      exact div_nonneg (sub_nonneg.mpr hμL) hden.le
    have hcomp :
        1 - (2 * (1 / L) * μ * L) / (μ + L) ≤ 1 - q[μ, L] := by
      rw [hnum]
      have hrewrite : 1 - q[μ, L] = (L - μ) / L := by
        have hL_ne : L ≠ 0 := ne_of_gt hL
        field_simp [hL_ne]
      rw [hrewrite, hleft]
      exact div_le_div_of_nonneg_left (sub_nonneg.mpr hμL) hL (by nlinarith [hf'.mu_pos])
    have hpow :
        (1 - (2 * (1 / L) * μ * L) / (μ + L)) ^ k ≤ (1 - q[μ, L]) ^ k := by
      exact pow_le_pow_left₀ hfactor_nonneg hcomp k
    calc
      ‖gradientMethod (fun _ ↦ 1 / L) f x0 k - xStar‖ ^ (2 : ℕ) ≤
          (1 - (2 * (1 / L) * μ * L) / (μ + L)) ^ k * ‖x0 - xStar‖ ^ (2 : ℕ) :=
        hsq
      _ ≤ (1 - q[μ, L]) ^ k * ‖x0 - xStar‖ ^ (2 : ℕ) := by
        gcongr

end

/-! ### Theorem_2_23 (from Chap02) -/
open scoped BigOperators Gradient
open Matrix

noncomputable section

local notation "E" => EuclideanSpace ℝ (Fin 1)
local notation "Mat" => Matrix (Fin 1) (Fin 1) ℝ

/- Primary domain: one-dimensional quadratic counterexamples for the weighted sampled point built
from an actual optimal-method trajectory.

Sampled owner declarations before refining this file:
* `GeneralOptimalMethodScheme` in `Algorithm_2_2`, the chapter's owner for genuine Algorithm 2.2
  trajectories, including the step-`(c)` descent axiom;
* `OptimalMethodRecurrence.weightedAverage` in `Algorithm_2_2`, the canonical owner of the
  weighted sampled point attached to the underlying recurrence data;
* `constantStepSchemeIToGeneralOptimalMethodScheme` in `Algorithm_2_3`, the canonical bridge from
  the recursive exact-step trajectory to an actual optimal-method scheme;
* `quadraticObjective` and `quadraticObjective_gradient_eq` in Chapter 1, the canonical Euclidean
  quadratic owner and its gradient formula.

Source/core/bridge triage:
* source-facing: the counterexample theorem for the weighted sampled point at stage `k`;
* core/canonical: an actual `GeneralOptimalMethodScheme` witness together with the owner weighted
  sampled point inherited from its underlying recurrence;
* bridge/view: `constantStepSchemeIToGeneralOptimalMethodScheme`, used only to realize a genuine
  Algorithm 2.2 trajectory from the recursive exact-step construction.

Primitive data:
* the linear coefficient `linearCoeff` of the degenerate quadratic objective
  `quadraticObjective 0 linearCoeff 0`;
* the actual scheme witness `method`.

Derived API:
* the weighted sampled point
  `\hat y_k = (λ_k / (1 - λ_k)) ∑_{i < k} (α_i / λ_{i+1}) y_i`,
  owned by `OptimalMethodRecurrence.weightedAverage`;
* the constant-gradient evaluation
  `∇ (quadraticObjective 0 linearCoeff 0) x = linearCoeff`.
-/

/-- Theorem 2.23: for every stage `k` and threshold `M`, there is a one-dimensional quadratic
objective together with an actual optimal-method scheme whose weighted sampled point
`\hat y_k = (λ_k / (1 - λ_k)) ∑_{i < k} (α_i / λ_{i+1}) y_i`,
formed from the owner data `λ_k = method.weight k`, `α_i = method.alpha i`, and `y_i = method.y i`,
has gradient norm at least `M`. -/
-- Proof sketch: fix `k` and `M`. Use the degenerate quadratic owner
-- `quadraticObjective 0 linearCoeff 0` with `linearCoeff = M e₀`. Its gradient is constant,
-- `∇ f x = linearCoeff` for every `x`. Realize an actual Algorithm 2.2 trajectory for this
-- objective by the canonical bridge
-- `constantStepSchemeIToGeneralOptimalMethodScheme`. Since the gradient is constant, the weighted
-- sampled point `\hat y_k` can be arbitrary and still satisfies
-- `‖∇ f \hat y_k‖ = ‖linearCoeff‖ = |M| ≥ M`.
theorem exists_estimatingSequence_counterexample_with_large_gradient_norm
    (k : ℕ) (M : ℝ) :
    ∃ (linearCoeff : E)
      (method : GeneralOptimalMethodScheme (quadraticObjective 0 linearCoeff (0 : Mat))
        1 0 0 1),
      let yHat := method.weightedAverage method.y k
      M ≤ ‖∇ (quadraticObjective 0 linearCoeff (0 : Mat)) yHat‖ := by
  let linearCoeff : E :=
    EuclideanSpace.single 0 M
  let f : E → ℝ := quadraticObjective 0 linearCoeff (0 : Mat)
  have hgrad_eq : ∇ f = fun _ ↦ linearCoeff := by
    simpa [f] using quadraticObjective_gradient_eq 0 linearCoeff (0 : Mat) (by simp)
  have hDiff : Differentiable ℝ f := by
    exact
      (symmetric_quadratic_contDiff_and_gradient_lipschitz
        0 linearCoeff (0 : Mat) (by simp)).1.differentiable one_ne_zero
  have hGrad : LipschitzWith 1 (∇ f) := by
    rw [hgrad_eq]
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    simp
  let method :
      GeneralOptimalMethodScheme f 1 0 0 1 :=
    constantStepSchemeIToGeneralOptimalMethodScheme
      f 1 0 0 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hDiff hGrad
  have hmethod :
      GeneralOptimalMethodScheme (quadraticObjective 0 linearCoeff (0 : Mat))
        1 0 0 1 := by
    simpa [f] using method
  have hlinearCoeff_norm : ‖linearCoeff‖ = |M| := by
    simp [linearCoeff]
  refine ⟨linearCoeff, hmethod, ?_⟩
  change M ≤
    ‖∇ (quadraticObjective 0 linearCoeff (0 : Mat)) (hmethod.weightedAverage hmethod.y k)‖
  rw [show
      ∇ (quadraticObjective 0 linearCoeff (0 : Mat))
        (hmethod.weightedAverage hmethod.y k) = linearCoeff by
      simpa [f] using congrFun hgrad_eq (hmethod.weightedAverage hmethod.y k)]
  rw [hlinearCoeff_norm]
  exact le_abs_self M
