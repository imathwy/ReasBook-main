import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_3_3_4 (from Chap03) -/
noncomputable section

universe u v w

open scoped ConstrainedArgmin

section

variable {Index : Type u} {Param : Type v} {Decision : Type w}

/-
Lemma 3.3.4 lies in the chapter's constrained-threshold / set-constrained minimization domain.

Sampled owner-style declarations:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  feasible set together with a real-valued objective;
- `argmin[Q] f` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the chapter owner
  for feasible minimizers on a fixed feasible slice;
- `SetConstrainedMinimizationProblem.optimalValue` and
  `SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn` in
  `Chap01/Definition_1_3_7`, the canonical owner optimal-value API on the feasible slice;
- mathlib `sInf`, used only in the companion upper-bound presentation after coercing the
  source-facing real upper bounds into `EReal`.

Best owner abstraction:
- source-facing: the textbook threshold `constrainedThreshold Q hatFn checkFn k X`;
- core/canonical: the feasible-slice owner
  `(.mk (Q ∩ {x | checkFn k X x ≤ 0}) (hatFn k X) :
    SetConstrainedMinimizationProblem Decision).optimalValue`;
- bridge/view: the `EReal` infimum of the real upper-bound set attached to the same feasible
  slice.

Primitive data:
- the feasible set `Q`;
- the objective family `hatFn`;
- the constraint family `checkFn`;
- the stage/index data `k` and `X`.

Derived API:
- the source-facing threshold `constrainedThreshold Q hatFn checkFn k X`;
- the upper-bound presentation in `constrainedThreshold_def`;
- the direct attained-minimum identification of the threshold;
- the direct feasible-slice owner expression when downstream arguments genuinely need the
  Chapter 1 packaged API.

Source/core/bridge triage:
- source-facing: the textbook threshold `t_k^*(X)`;
- core/canonical: the direct feasible-slice owner optimal value;
- bridge/view: the `sInf` presentation of the corresponding real upper-bound set in `EReal`.

The threshold itself remains the source-facing owner because it is a named chapter object, but
its definition now reuses the Chapter 1 owner `optimalValue` so empty or unbounded-below feasible
slices are represented faithfully in `EReal`. The feasible-slice
`SetConstrainedMinimizationProblem` is kept only as a direct bridge expression, not as a second
public owner with wrapper lemmas.
-/

/-- The threshold value `t_k^*(X)` defined as the infimum of `hatFn k X` on the feasible slice
`Q ∩ {x | checkFn k X x ≤ 0}`, viewed in `EReal` so empty or unbounded-below slices are
represented faithfully. -/
noncomputable def constrainedThreshold
    (Q : Set Decision) (hatFn checkFn : Index → Param → Decision → ℝ) (k : Index)
    (X : Param) : EReal :=
  (SetConstrainedMinimizationProblem.mk
      (Q ∩ {x | checkFn k X x ≤ 0})
      (hatFn k X)).optimalValue

namespace ConstrainedThreshold

scoped notation:max "t*[" Q "; " hatFn "; " checkFn "](" k ", " X ")" =>
  constrainedThreshold Q hatFn checkFn k X

end ConstrainedThreshold

open scoped ConstrainedThreshold

/-- Recovering the source-facing upper-bound presentation of `constrainedThreshold`. -/
-- Proof sketch: package the feasible slice as a `SetConstrainedMinimizationProblem`, expand the
-- owner optimal value as an `EReal` infimum of the feasible objective-value image, and identify
-- that image with the coerced real upper-bound set attached to the same slice.
theorem constrainedThreshold_def
    (Q : Set Decision) (hatFn checkFn : Index → Param → Decision → ℝ) (k : Index)
    (X : Param) :
    t*[Q; hatFn; checkFn](k, X) =
      sInf (((↑) : ℝ → EReal) ''
        {t : ℝ | ∃ x ∈ Q, hatFn k X x ≤ t ∧ checkFn k X x ≤ 0}) := by
  let feasibleValues : Set EReal :=
    (fun x ↦ (hatFn k X x : EReal)) '' (Q ∩ {x | checkFn k X x ≤ 0})
  let upperBounds : Set EReal :=
    ((↑) : ℝ → EReal) '' {t : ℝ | ∃ x ∈ Q, hatFn k X x ≤ t ∧ checkFn k X x ≤ 0}
  have hthreshold :
      t*[Q; hatFn; checkFn](k, X) = sInf feasibleValues := by
    let problem : SetConstrainedMinimizationProblem Decision :=
      .mk (Q ∩ {x | checkFn k X x ≤ 0}) (hatFn k X)
    simpa [constrainedThreshold, feasibleValues, problem] using
      problem.optimalValue_eq_sInf_image
  have hfeasible_le_upper : sInf feasibleValues ≤ sInf upperBounds := by
    refine le_sInf ?_
    rintro _ ⟨t, ⟨x, hxQ, hhat, hcheck⟩, rfl⟩
    have hx : ((hatFn k X x : ℝ) : EReal) ∈ feasibleValues := by
      exact ⟨x, ⟨hxQ, hcheck⟩, rfl⟩
    have hhat' : ((hatFn k X x : ℝ) : EReal) ≤ t := by
      exact_mod_cast hhat
    exact (csInf_le ⟨⊥, fun _ _ ↦ bot_le⟩ hx).trans hhat'
  have hupper_le_feasible : sInf upperBounds ≤ sInf feasibleValues := by
    refine le_sInf ?_
    rintro _ ⟨x, hx, rfl⟩
    have hx' : ((hatFn k X x : ℝ) : EReal) ∈ upperBounds := by
      refine ⟨hatFn k X x, ?_, rfl⟩
      exact ⟨x, hx.1, le_rfl, hx.2⟩
    exact csInf_le ⟨⊥, fun _ _ ↦ bot_le⟩ hx'
  have hsInf_eq : sInf upperBounds = sInf feasibleValues := by
    exact le_antisymm hupper_le_feasible hfeasible_le_upper
  calc
    t*[Q; hatFn; checkFn](k, X) = sInf feasibleValues := hthreshold
    _ = sInf upperBounds := hsInf_eq.symm
    _ =
        sInf (((↑) : ℝ → EReal) ''
          {t : ℝ | ∃ x ∈ Q, hatFn k X x ≤ t ∧ checkFn k X x ≤ 0}) := rfl

/-- Lemma 3.3.4: if `xStar` attains the minimum of `hatFn k X` on the feasible set
`Q ∩ {x | checkFn k X x ≤ 0}`, then `t_k^*(X)` equals that constrained minimum value. -/
-- Proof sketch: package the feasible slice as a `SetConstrainedMinimizationProblem` and apply
-- the Chapter 1 owner theorem `optimalValue_eq_of_isMinOn`.
theorem constrainedThreshold_eq_minimum_of_feasible_minimizer
    (Q : Set Decision) (hatFn checkFn : Index → Param → Decision → ℝ) (k : Index)
    (X : Param) {xStar : Decision}
    (hxStar : xStar ∈ argmin[Q ∩ {x | checkFn k X x ≤ 0}] (hatFn k X)) :
    t*[Q; hatFn; checkFn](k, X) = (hatFn k X xStar : EReal) := by
  rw [mem_constrainedArgmin_iff] at hxStar
  let problem : SetConstrainedMinimizationProblem Decision :=
    .mk (Q ∩ {x | checkFn k X x ≤ 0}) (hatFn k X)
  simpa [constrainedThreshold, problem] using
    problem.optimalValue_eq_of_isMinOn hxStar.1 hxStar.2

end

/-! ### Lemma_3_3_5 (from Chap03) -/
open scoped ConvexAnalysis

section

universe u v w

variable {Index : Type u} {Param : Type v} {Decision : Type w}

/-
Lemma 3.3.5 lies in the chapter's constrained-threshold / parametric-value domain.

Relevant owner declarations sampled before refining:
- `parametricValueFunction` in `Chap03/Lemma_3_3_6`, the chapter owner for the scalar model value
  `t ↦ inf_{x ∈ Q} max (hatFn k X x - t) (checkFn k X x)`;
- `estimatedValue_strict_lt_right_and_secant_lower_bound_of_nonpos_right` in `Chap03/Lemma_3_37`,
  the chapter bridge specializing the scalar secant owner to a fixed real right endpoint `τ`;
- `ConvexOn.strict_lt_and_secant_lower_bound_of_nonpos_right` in `Chap02/Proposition_2_26`, the
  upstream owner bridge from convexity plus sign data to the scalar secant inequality.

Best owner abstractions:
- `parametricValueFunction Q (hatFn k X) (checkFn k X)`;
- `extendedRealRealPart (parametricValueFunction Q (hatFn k X) (checkFn k X))`.

Primitive data:
- the feasible set `Q`;
- the stage-`k` upper model `hatFn k X`;
- the stage-`k` constraint model `checkFn k X`;
- the index `k` and parameter `X`.

Derived API:
- the source-facing right-endpoint/secant conclusion obtained by specializing the existing chapter
  bridge `estimatedValue_strict_lt_right_and_secant_lower_bound_of_nonpos_right` to the finite
  real-part view of the extended-real owner value function;
- the convexity and right-endpoint nonpositivity witnesses required by that bridge.

Source/core/bridge triage:
- source-facing: Lemma 3.3.5 in the chapter's complete-data notation;
- core/canonical: `parametricValueFunction`;
- bridge/view: `extendedRealRealPart (parametricValueFunction Q (hatFn k X) (checkFn k X))` and
  the specialization of `estimatedValue_strict_lt_right_and_secant_lower_bound_of_nonpos_right`
  to that real-valued slice.

This file therefore keeps the labeled item only as the source-facing specialization of the chapter
secant bridge to the canonical finite real-part view of `parametricValueFunction`. It does not
repackage the nearby threshold owner as extra local API, because the theorem statement itself uses
only the scalar slice and the right-endpoint sign data.
-/

section

variable (Q : Set Decision) (hatFn checkFn : Index → Param → Decision → ℝ)
variable (k : Index) (X : Param)

local notation "valueFn" =>
  parametricValueFunction Q (hatFn k X) (checkFn k X)
local notation "modelValue" =>
  extendedRealRealPart valueFn

/-- Lemma 3.3.5: if the finite real-part view of the complete-data owner value
`parametricValueFunction Q (hatFn k X) (checkFn k X) t₁` is positive for some
`t₀ < t₁ ≤ τ`, the owner value at `τ` is finite and nonpositive, and the scalar slice is convex
on `(-∞, τ]`, then `τ` lies strictly to the right of `t₁` and the displayed secant lower bound
holds. -/
theorem parametricValueFunction_strict_lt_right_and_secant_lower_bound
    {t0 t1 τ : ℝ}
    (ht0_lt_t1 : t0 < t1)
    (ht1_le_right : t1 ≤ τ)
    (hpos : 0 < modelValue t1)
    (hτ_dom : τ ∈ dom valueFn)
    (hright_nonpos : valueFn τ ≤ (0 : EReal))
    (hconvex : ConvexOn ℝ (Set.Iic τ) modelValue) :
    t1 < τ ∧
      modelValue t0 ≥
        modelValue t1 + ((t1 - t0) / (τ - t1)) * modelValue t1 := by
  exact
    estimatedValue_strict_lt_right_and_secant_lower_bound_of_nonpos_right
      (fun k X ↦ extendedRealRealPart (parametricValueFunction Q (hatFn k X) (checkFn k X)))
      k
      X
      ht0_lt_t1
      ht1_le_right
      hpos
      ((extendedRealRealPart_le_iff hτ_dom).2 hright_nonpos)
      hconvex

end

end

/-! ### Lemma_3_3_6 (from Chap03) -/
noncomputable section

universe u

variable {α : Type u}

/-
Lemma 3.3.6 lies in the chapter's set-constrained scalar parametric max-value-function domain.

Sampled owner declarations:
- `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the project
  owner for constrained extended-real optimal values;
- `SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image`, the canonical expansion of that
  owner as an infimum over the feasible-set image;
- `SetConstrainedMinimizationProblem.optimalValue_le_optimalValue_of_forall_le` and
  `SetConstrainedMinimizationProblem.optimalValue_sub_le_optimalValue_of_forall_sub_le`, the
  comparison owners that transport pointwise objective bounds to optimal-value bounds.

Best owner abstraction:
- source-facing: `setConstrainedParametricObjective f barf t` and
  `parametricValueFunction Q f barf t`;
- core/canonical: `(.mk Q (setConstrainedParametricObjective f barf t) :
  SetConstrainedMinimizationProblem α).optimalValue`;
- bridge/view: the source-facing `sInf` expansions and the shift bounds obtained from the Chapter
  1 comparison lemmas.

Primitive data:
- feasible set `Q`;
- objective `f`;
- constraint surrogate `barf`;
- scalar parameter `t`.

Derived API:
- the pointwise evaluation formula for `setConstrainedParametricObjective`;
- the value-function `sInf` expansions;
- the monotonicity and shift inequalities in the parameter.

This file therefore keeps the two-term max objective as the source-facing owner and routes the
value-level API through the canonical `SetConstrainedMinimizationProblem` comparison theorems
instead of reproving feasible-set infimum facts directly.
-/

/-- The pointwise max-type objective attached to `f`, `barf`, and the scalar parameter `t`,
namely `x ↦ max (f x - t) (barf x)`. This is the primitive owner object underlying the chapter's
parametric value function. -/
def setConstrainedParametricObjective
    (f barf : α → ℝ) (t : ℝ) : α → ℝ :=
  fun x ↦ max (f x - t) (barf x)

/-- Evaluating `setConstrainedParametricObjective f barf t` at `x` gives the defining pointwise
maximum `max (f x - t) (barf x)`. -/
@[simp] theorem setConstrainedParametricObjective_apply
    {f barf : α → ℝ} {t : ℝ} {x : α} :
    setConstrainedParametricObjective f barf t x = max (f x - t) (barf x) :=
  rfl

/-- The parametric value attached to the max-type model `x ↦ max (f x - t) (barf x)` is the
extended-real optimal value of the corresponding constrained problem on `Q`. -/
def parametricValueFunction
    (Q : Set α) (f barf : α → ℝ) (t : ℝ) : EReal :=
  SetConstrainedMinimizationProblem.optimalValue
    (.mk Q (setConstrainedParametricObjective f barf t) : SetConstrainedMinimizationProblem α)

/-- Unfolding `parametricValueFunction` gives the feasible-set image formula over `Q`. -/
theorem parametricValueFunction_eq_sInf_image
    (Q : Set α) (f barf : α → ℝ) (t : ℝ) :
    parametricValueFunction Q f barf t =
      sInf ((fun x ↦ (setConstrainedParametricObjective f barf t x : EReal)) '' Q) := by
  simpa [parametricValueFunction] using
    (SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image
      (.mk Q (setConstrainedParametricObjective f barf t) :
        SetConstrainedMinimizationProblem α))

/-- Unfolding `parametricValueFunction` gives the displayed `sInf` formula over `Q`. -/
theorem parametricValueFunction_def
    (Q : Set α) (f barf : α → ℝ) (t : ℝ) :
    parametricValueFunction Q f barf t =
      sInf (Set.range fun x : Q ↦ (setConstrainedParametricObjective f barf t x : EReal)) := by
  rw [parametricValueFunction_eq_sInf_image]
  refine congrArg sInf ?_
  ext y
  constructor
  · rintro ⟨x, hxQ, rfl⟩
    exact ⟨⟨x, hxQ⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, rfl⟩

/-- Increasing the parameter by a nonnegative amount can only decrease the pointwise max-type
objective. -/
theorem setConstrainedParametricObjective_shift_le
    (f barf : α → ℝ) (Δ t : ℝ) (hΔ : 0 ≤ Δ) (x : α) :
    setConstrainedParametricObjective f barf (t + Δ) x ≤
      setConstrainedParametricObjective f barf t x := by
  rw [setConstrainedParametricObjective_apply, setConstrainedParametricObjective_apply]
  refine max_le_max ?_ le_rfl
  linarith

/-- Increasing the parameter by `Δ ≥ 0` lowers the pointwise max-type objective by at most `Δ`.
-/
theorem setConstrainedParametricObjective_sub_le_shift
    (f barf : α → ℝ) (Δ t : ℝ) (hΔ : 0 ≤ Δ) (x : α) :
    setConstrainedParametricObjective f barf t x - Δ ≤
      setConstrainedParametricObjective f barf (t + Δ) x := by
  rw [setConstrainedParametricObjective_apply, setConstrainedParametricObjective_apply]
  by_cases h : barf x ≤ f x - t
  · rw [max_eq_left h]
    have hrewrite : f x - t - Δ = f x - (t + Δ) := by ring
    rw [hrewrite]
    exact le_max_left _ _
  · have h' : f x - t ≤ barf x := le_of_not_ge h
    rw [max_eq_right h']
    exact (sub_le_self _ hΔ).trans (le_max_right _ _)

/-- Lemma 3.3.6: for any model `f` and any `Δ ≥ 0`, shifting the parameter from `t` to `t + Δ`
decreases the chapter parametric value by at most `Δ`. The textbook exact value `f^*(t)` and the
approximate value `\hat f_k^*(X; t)` are the corresponding specializations of this owner theorem.
-/
theorem parametricValueFunction_sub_le_shift
    (Q : Set α) (f barf : α → ℝ) (Δ t : ℝ) (hΔ : 0 ≤ Δ) :
    parametricValueFunction Q f barf t - Δ ≤
      parametricValueFunction Q f barf (t + Δ) := by
  simpa [parametricValueFunction] using
    (SetConstrainedMinimizationProblem.optimalValue_sub_le_optimalValue_of_forall_sub_le
      (.mk Q (setConstrainedParametricObjective f barf t) :
        SetConstrainedMinimizationProblem α)
      (.mk Q (setConstrainedParametricObjective f barf (t + Δ)) :
        SetConstrainedMinimizationProblem α)
      rfl
      (fun x _ ↦ setConstrainedParametricObjective_sub_le_shift f barf Δ t hΔ x))

/-- For any model `f` and any `Δ ≥ 0`, shifting the parameter from `t` to `t + Δ` never
increases the parametric value. -/
theorem parametricValueFunction_shift_le
    (Q : Set α) (f barf : α → ℝ) (Δ t : ℝ) (hΔ : 0 ≤ Δ) :
    parametricValueFunction Q f barf (t + Δ) ≤
      parametricValueFunction Q f barf t := by
  simpa [parametricValueFunction] using
    (SetConstrainedMinimizationProblem.optimalValue_le_optimalValue_of_forall_le
      (.mk Q (setConstrainedParametricObjective f barf (t + Δ)) :
        SetConstrainedMinimizationProblem α)
      (.mk Q (setConstrainedParametricObjective f barf t) :
        SetConstrainedMinimizationProblem α)
      rfl
      (fun x _ ↦ setConstrainedParametricObjective_shift_le f barf Δ t hΔ x))

/-- The parametric value function is antitone in the scalar parameter. This is derived owner API:
increasing `t` lowers the pointwise model `x ↦ max (f x - t) (barf x)`, so the infimum over the
fixed feasible set `Q` cannot increase. -/
theorem parametricValueFunction_antitone
    (Q : Set α) (f barf : α → ℝ) :
    Antitone (parametricValueFunction Q f barf) := by
  intro t₁ t₂ ht
  have hΔ : 0 ≤ t₂ - t₁ := sub_nonneg.mpr ht
  have hshift :
      parametricValueFunction Q f barf (t₁ + (t₂ - t₁)) ≤
        parametricValueFunction Q f barf t₁ := by
    exact parametricValueFunction_shift_le Q f barf (t₂ - t₁) t₁ hΔ
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    hshift

/-! ### Lemma_3_3_7 (from Chap03) -/
/-
Primary domain: complete-data level-method scalar geometric decay.

Owner declarations sampled before refining:
* `HasGeometricRateOfConvergence`
* `HasGeometricRateOfConvergence.of_step_bound`
* `LevelMethodHistory` in `Lemma_3_3_1.lean`
* `constrainedMinimizationInternalGap_hasGeometricRateOfConvergence` in
  `Chap02/Proposition_2_30.lean`

Best owner abstraction:
* `HasGeometricRateOfConvergence` on the scalar sequence
  `k ↦ exactValue (j k) X (t k)`

Primitive data:
* the selector sequence `j` and threshold sequence `t`
* the exact and estimated value families
* the scalar comparison hypotheses and the initial gap bound

Derived API:
* the canonical owner statement `HasGeometricRateOfConvergence`
* the textbook geometric upper bound for the selected exact values

Source/core/bridge triage:
* source-facing: Lemma 3.3.7 in the `exactValue` / `estimatedValue` notation
* core/canonical: `HasGeometricRateOfConvergence`
* bridge/view: the pointwise unpacked geometric bound

Although the sampled values form the two scalar fields of a `LevelMethodHistory`, this lemma only
uses those primitive fields, so the public header stays source-facing instead of repackaging the
data through that owner. The proof core, however, is the owner-level statement
`HasGeometricRateOfConvergence`; the displayed bound is derived from that canonical abstraction.
-/

open HasGeometricRateOfConvergence

section

universe u v

variable {χ : Type u} {ι : Type v}

/-- Lemma 3.3.7 in canonical owner form: under the complete-data level-method hypotheses with
`ε < 1` and the three comparison inequalities between
`f_{j(k)}^*(X; t_k)` and `\hat f_{j(k)}^*(X; t_k)`, if the initial approximate value is bounded by
the initial gap, then the selected exact-value sequence has geometric rate with parameter
`1 - (2 * (1 - ε))⁻¹` and initial constant `(t 0 - tStar) / (1 - ε)`. The explicit threshold
recursion and step-size bounds from the source are redundant for this scalar consequence, and the
stronger contractivity side condition belongs only to later iteration-threshold consequences. -/
-- Proof sketch: the comparison assumptions imply the one-step contraction
-- `gap (k + 1) ≤ (1 / (2 * (1 - ε))) * gap k` for the selected exact-value sequence
-- `gap k = exactValue (j k) X (t k)`. Combine this with the zeroth-step bound
-- `estimatedValue (j 0) X (t 0) ≤ t 0 - tStar`, convert it to a bound on `gap 0`, and apply the
-- canonical constructor `HasGeometricRateOfConvergence.of_step_bound`.
theorem selectedExactValue_hasGeometricRateOfConvergence
    {ε tStar : ℝ} {X : χ} {t : ℕ → ℝ} {j : ℕ → ι}
    {exactValue estimatedValue : ι → χ → ℝ → ℝ}
    (hε : ε < 1)
    (hestimated_ge :
      ∀ k : ℕ,
        estimatedValue (j k) X (t k) ≥ (1 - ε) * exactValue (j k) X (t k))
    (hestimated_prev_ge_two_curr :
      ∀ k : ℕ,
        estimatedValue (j (k + 1)) X (t k) ≥
          2 * estimatedValue (j (k + 1)) X (t (k + 1)))
    (hexact_prev_ge_estimated_prev :
      ∀ k : ℕ,
        exactValue (j k) X (t k) ≥ estimatedValue (j (k + 1)) X (t k))
    (hestimated0_le_gap :
      estimatedValue (j 0) X (t 0) ≤ t 0 - tStar) :
    HasGeometricRateOfConvergence
      (fun k ↦ exactValue (j k) X (t k))
      (1 - (2 * (1 - ε))⁻¹)
      ((t 0 - tStar) / (1 - ε)) := by
  let gap : ℕ → ℝ := fun k ↦ exactValue (j k) X (t k)
  let β : ℝ := 1 / (2 * (1 - ε))
  have hone_sub_epsilon_pos : 0 < 1 - ε := sub_pos.mpr hε
  have hdouble_pos : 0 < (2 * (1 - ε) : ℝ) := by
    nlinarith
  have hβ_nonneg : 0 ≤ β := by
    dsimp [β]
    positivity
  have hstep :
      ∀ k : ℕ, gap (k + 1) ≤ β * gap k := by
    intro k
    dsimp [gap, β]
    have hscaled :
        (2 * (1 - ε)) * exactValue (j (k + 1)) X (t (k + 1)) ≤
          exactValue (j k) X (t k) := by
      calc
        (2 * (1 - ε)) * exactValue (j (k + 1)) X (t (k + 1))
            = 2 * ((1 - ε) * exactValue (j (k + 1)) X (t (k + 1))) := by ring
        _ ≤ 2 * estimatedValue (j (k + 1)) X (t (k + 1)) := by
          nlinarith [hestimated_ge (k + 1)]
        _ ≤ estimatedValue (j (k + 1)) X (t k) := by
          exact hestimated_prev_ge_two_curr k
        _ ≤ exactValue (j k) X (t k) := by
          exact hexact_prev_ge_estimated_prev k
    have hdiv :
        exactValue (j (k + 1)) X (t (k + 1)) ≤
          exactValue (j k) X (t k) / (2 * (1 - ε)) := by
      refine (le_div_iff₀ hdouble_pos).2 ?_
      simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
  have hgap0_le :
      gap 0 ≤ (t 0 - tStar) / (1 - ε) := by
    dsimp [gap]
    have hscaled :
        (1 - ε) * exactValue (j 0) X (t 0) ≤ t 0 - tStar := by
      calc
        (1 - ε) * exactValue (j 0) X (t 0) ≤ estimatedValue (j 0) X (t 0) := by
          exact hestimated_ge 0
        _ ≤ t 0 - tStar := hestimated0_le_gap
    refine (le_div_iff₀ hone_sub_epsilon_pos).2 ?_
    simpa [mul_comm] using hscaled
  have hgap_rate :
      HasGeometricRateOfConvergence gap (1 - β) ((t 0 - tStar) / (1 - ε)) := by
    have hq₁ : 1 - β ≤ 1 := by
      linarith
    refine of_step_bound hq₁ hgap0_le ?_
    intro k
    calc
      gap (k + 1) ≤ β * gap k := hstep k
      _ = (1 - (1 - β)) * gap k := by ring
  simpa [gap, β, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hgap_rate

/-- Lemma 3.3.7 in the displayed source-facing form: under the same hypotheses, the selected exact
values satisfy the textbook geometric upper bound. The stronger contractivity side condition is
only needed later when this estimate is converted to an iteration-threshold statement. -/
theorem selected_exactValue_le_initial_gap_div_one_sub_epsilon_mul_geometric_decay
    {ε tStar : ℝ} {X : χ} {t : ℕ → ℝ} {j : ℕ → ι}
    {exactValue estimatedValue : ι → χ → ℝ → ℝ}
    (hε : ε < 1)
    (hestimated_ge :
      ∀ k : ℕ,
        estimatedValue (j k) X (t k) ≥ (1 - ε) * exactValue (j k) X (t k))
    (hestimated_prev_ge_two_curr :
      ∀ k : ℕ,
        estimatedValue (j (k + 1)) X (t k) ≥
          2 * estimatedValue (j (k + 1)) X (t (k + 1)))
    (hexact_prev_ge_estimated_prev :
      ∀ k : ℕ,
        exactValue (j k) X (t k) ≥ estimatedValue (j (k + 1)) X (t k))
    (hestimated0_le_gap :
      estimatedValue (j 0) X (t 0) ≤ t 0 - tStar)
    (k : ℕ) :
    exactValue (j k) X (t k) ≤
      ((t 0 - tStar) / (1 - ε)) * ((1 / (2 * (1 - ε))) ^ k) := by
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    selectedExactValue_hasGeometricRateOfConvergence
      hε
      hestimated_ge
      hestimated_prev_ge_two_curr
      hexact_prev_ge_estimated_prev
      hestimated0_le_gap
      k

end

/-! ### Lemma_3_3_8 (from Chap03) -/
noncomputable section

universe u

variable {E : Type u} [PseudoMetricSpace E]

namespace ConstrainedLevelMethod

/-- Helper for Lemma 3.3.8: some produced internal iterate realizes the exact record value on
every sampled prefix of the internal history at master step `k`. -/
lemma exists_internalIterate_eq_optimalValue_prefix
    (method : ConstrainedLevelMethodInput E)
    (hrelative : method.RelativeStoppingExists)
    (hfinite : method.SelectedThresholdFinite hrelative)
    (k p : ℕ) :
    ∃ jStar : ℕ,
      jStar ≤ p ∧
        method.exactObjectiveAt (parameter method hrelative hfinite k)
            (internalIterate method hrelative hfinite k jStar) =
          (history method hrelative hfinite k).optimalValue p := by
  let values : ℕ → ℝ := fun j ↦
    method.exactObjectiveAt (parameter method hrelative hfinite k)
      (internalIterate method hrelative hfinite k j)
  obtain ⟨jStar, hjStar_eq⟩ := bestFunctionValueUpTo_exists_eq values p
  refine ⟨jStar, Nat.lt_succ_iff.mp jStar.2, ?_⟩
  -- Read the record value as the sampled minimum over the produced prefix.
  calc
    method.exactObjectiveAt (parameter method hrelative hfinite k)
        (internalIterate method hrelative hfinite k jStar) =
      bestFunctionValueUpTo values p := by
        simpa [values] using hjStar_eq
    _ = (history method hrelative hfinite k).optimalValue p := by
        symm
        simpa [values, completeRun, history, internalIterate, CompleteLevelMethod.history] using
          levelMethodHistoryFromApproximateValues_optimalValue_eq
            (approximateOptimalValue := (completeRun method hrelative hfinite k).approximateOptimalValue)
            (f := method.stageProblemAt (parameter method hrelative hfinite k))
            (xSeq := completeRun method hrelative hfinite k)
            p

/-- Helper for Lemma 3.3.8: an exact constrained-value bound controls the objective once the
current parameter is bounded above by `tStar`. -/
lemma exactObjectiveAt_objective_le_of_le
    (method : ConstrainedLevelMethodInput E)
    {tk tStar : ℝ} {x : E}
    (hvalue : method.exactObjectiveAt tk x ≤ method.epsilon)
    (htk : tk ≤ tStar) :
    method.objective x ≤ tStar + method.epsilon := by
  -- Expand the exact constrained slice into its pointwise maximum and read off the first branch.
  rw [ConstrainedLevelMethodInput.exactObjectiveAt, setConstrainedParametricObjective_apply] at hvalue
  rcases max_le_iff.mp hvalue with ⟨hobjective, _⟩
  linarith

/-- Helper for Lemma 3.3.8: an exact constrained-value bound also controls the constraint
component. -/
lemma exactObjectiveAt_constraint_le_of_le
    (method : ConstrainedLevelMethodInput E)
    {tk : ℝ} {x : E}
    (hvalue : method.exactObjectiveAt tk x ≤ method.epsilon) :
    method.constraint x ≤ method.epsilon := by
  -- Expand the exact constrained slice into its pointwise maximum and read off the second branch.
  rw [ConstrainedLevelMethodInput.exactObjectiveAt, setConstrainedParametricObjective_apply] at hvalue
  exact (max_le_iff.mp hvalue).2

/-- Lemma 3.3.8: once the global-stop condition holds at master step `k`, some produced internal
iterate attains the stopping record value and therefore satisfies the displayed objective and
constraint bounds. -/
theorem global_stop_exists_internal_witness_and_component_bounds
    (method : ConstrainedLevelMethodInput E)
    (hrelative : method.RelativeStoppingExists)
    (hfinite : method.SelectedThresholdFinite hrelative)
    (k : ℕ)
    (hstop : globallyStopsAt method hrelative hfinite k)
    (tStar : ℝ)
    (htk : parameter method hrelative hfinite k ≤ tStar) :
    ∃ jStar : ℕ,
      jStar ≤ globalStopIndex method hrelative hfinite k hstop ∧
        method.exactObjectiveAt (parameter method hrelative hfinite k)
            (internalIterate method hrelative hfinite k jStar) =
          (history method hrelative hfinite k).optimalValue
            (globalStopIndex method hrelative hfinite k hstop) ∧
        method.exactObjectiveAt (parameter method hrelative hfinite k)
            (internalIterate method hrelative hfinite k jStar) ≤
          method.epsilon ∧
        method.objective (internalIterate method hrelative hfinite k jStar) ≤
          tStar + method.epsilon ∧
        method.constraint (internalIterate method hrelative hfinite k jStar) ≤
          method.epsilon := by
  -- Route correction: work with the actual stage-`k` history and global-stop index.
  obtain ⟨jStar, hjStar_le, hjStar_eq⟩ :=
    exists_internalIterate_eq_optimalValue_prefix
      method
      hrelative
      hfinite
      k
      (globalStopIndex method hrelative hfinite k hstop)
  have hglobal :
      (history method hrelative hfinite k).optimalValue
          (globalStopIndex method hrelative hfinite k hstop) ≤
        method.epsilon := by
    simpa [globalStopCriterion] using
      global_stop_condition method hrelative hfinite k hstop
  have hvalue :
      method.exactObjectiveAt (parameter method hrelative hfinite k)
          (internalIterate method hrelative hfinite k jStar) ≤
        method.epsilon := by
    rw [hjStar_eq]
    exact hglobal
  refine ⟨jStar, hjStar_le, hjStar_eq, hvalue, ?_, ?_⟩
  · -- Use the exact-value estimate and the parameter bound to recover the source `f`-bound.
    exact
      exactObjectiveAt_objective_le_of_le
        method
        hvalue
        htk
  · -- The same exact-value estimate directly yields the source constraint bound.
    exact exactObjectiveAt_constraint_le_of_le method hvalue

end ConstrainedLevelMethod

end

/-! ### Lemma_3_3_9 (from Chap03) -/
noncomputable section

universe u

variable {E : Type u} [PseudoMetricSpace E]

/- Lemma 3.3.9 lies in the chapter's iteration-cap comparison domain.

Relevant owner declarations sampled before refining:
- `levelMethodIterationCap` and `exists_stopping_index_le_levelMethodIterationCap` in
  `Theorem_3_3_1`, the chapter owners for the floor-plus-one iteration cap and its stopping-index
  consequence;
- `ConstrainedLevelMethod.history`, `ConstrainedLevelMethod.stoppingIndex`, and
  `ConstrainedLevelMethod.globalStopIndex` in `Algorithm_3_11`, the canonical inner-history and
  iteration-count owners for one master step;
- `constrainedLevelMethodInternalIterationBound` in `Theorem_3_3_3`, the owner of the displayed
  uniform real-valued per-step complexity bound;
- `levelParameterObjective` and `levelParameterObjective_pos` in `Definition_3_71`, the owner of
  the positive `α`-dependent denominator factor.

Best owner abstraction:
- source-facing: the full-step and last-step internal iteration counts of a constrained level
  method;
- core/canonical: `levelMethodIterationCap`, `ConstrainedLevelMethod.stoppingIndex`,
  `ConstrainedLevelMethod.globalStopIndex`, and
  `constrainedLevelMethodInternalIterationBound`;
- bridge/view: denominator monotonicity for positive factors.

Primitive data:
- the actual inner history at one master step and its canonical stopping/global-stopping indices;
- the block estimate needed to invoke `Theorem_3_3_1`;
- the predecessor-gap lower bound `χ ε ≤ δ_{j-1}` for the terminal inner run.

Derived API:
- the uniform full-step cap
  `stoppingIndex ≤ levelMethodIterationCap M_f D (χ ε) α`;
- the uniform terminal-step cap
  `globalStopIndex ≤ constrainedLevelMethodInternalIterationBound M_f D χ ε α`.
-/

private theorem le_div_of_mul_right_denominator_le
    {lhs num scale smallFactor largeFactor : ℝ}
    (hbound : lhs ≤ num / (scale * largeFactor))
    (hnum_nonneg : 0 ≤ num)
    (hscale_pos : 0 < scale)
    (hsmallFactor_pos : 0 < smallFactor)
    (hsmallFactor_le_largeFactor : smallFactor ≤ largeFactor) :
    lhs ≤ num / (scale * smallFactor) := by
  have hden_le : scale * smallFactor ≤ scale * largeFactor :=
    mul_le_mul_of_nonneg_left hsmallFactor_le_largeFactor hscale_pos.le
  have hden_pos : 0 < scale * smallFactor := mul_pos hscale_pos hsmallFactor_pos
  exact hbound.trans <| div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_le

private theorem gap_le_kappa_mul_optimalValue_of_termination_rule
    (history : LevelMethodHistory) {κ : ℝ} (k : ℕ)
    (htermination :
      history.approximateOptimalValue k ≥ (1 - κ) * history.optimalValue k) :
    history.gap k ≤ κ * history.optimalValue k := by
  rw [history.gap_eq_sub]
  linarith

private theorem levelMethodIterationCap_antitone_tolerance
    {M_f D εLarge εSmall α : ℝ}
    (hεSmall_pos : 0 < εSmall)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hεSmall_le_εLarge : εSmall ≤ εLarge) :
    levelMethodIterationCap M_f D εLarge α ≤ levelMethodIterationCap M_f D εSmall α := by
  have hnum_nonneg : 0 ≤ M_f ^ (2 : ℕ) * D ^ (2 : ℕ) := by positivity
  have hlevel_pos : 0 < levelParameterObjective α := levelParameterObjective_pos hα
  have hεSmall_sq_le : εSmall ^ (2 : ℕ) ≤ εLarge ^ (2 : ℕ) := by
    nlinarith
  have hden_le :
      εSmall ^ (2 : ℕ) * levelParameterObjective α ≤
        εLarge ^ (2 : ℕ) * levelParameterObjective α :=
    mul_le_mul_of_nonneg_right hεSmall_sq_le hlevel_pos.le
  have hden_pos :
      0 < εSmall ^ (2 : ℕ) * levelParameterObjective α := by
    exact mul_pos (by positivity) hlevel_pos
  have hfrac :
      M_f ^ (2 : ℕ) * D ^ (2 : ℕ) /
          (εLarge ^ (2 : ℕ) * levelParameterObjective α) ≤
        M_f ^ (2 : ℕ) * D ^ (2 : ℕ) /
          (εSmall ^ (2 : ℕ) * levelParameterObjective α) :=
    div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_le
  unfold levelMethodIterationCap
  exact Nat.add_le_add_right (Nat.floor_le_floor hfrac) 1

namespace ConstrainedLevelMethod

/-- Lemma 3.3.9 (1): if master step `k` is a full step in the sense that the selected exact
record value is still at least `ε`, and if the chapter owner hypotheses of Theorem `3.3.1` hold
for the inner history `method.history k`, then the canonical full-step count
`j(k) - j(k - 1)` represented by `method.stoppingIndex k` is bounded by the chapter owner
`levelMethodIterationCap` evaluated at the uniform tolerance `χ ε`. -/
theorem full_step_increment_le_uniform_internal_iteration_bound
    (method : ConstrainedLevelMethodInput E)
    (hrelative : method.RelativeStoppingExists)
    (hfinite : method.SelectedThresholdFinite hrelative)
    (k : ℕ) (M_f D : ℝ)
    (hχ : 0 < method.chi)
    (hε : 0 < method.epsilon)
    (hα : method.levelCoefficient ∈ Set.Ioo (0 : ℝ) 1)
    (hblock :
      ∀ {i p : ℕ}, i ≤ p →
        (history method hrelative hfinite k).gap p ≥
          (1 - method.levelCoefficient) * (history method hrelative hfinite k).gap i →
        0 < (history method hrelative hfinite k).gap p →
        ((p + 1 - i : ℕ) : ℝ) ≤
          M_f ^ (2 : ℕ) * D ^ (2 : ℕ) /
            ((1 - method.levelCoefficient) ^ (2 : ℕ) *
              (history method hrelative hfinite k).gap p ^ (2 : ℕ)))
    (hfull_step :
      method.epsilon ≤
        (history method hrelative hfinite k).optimalValue
          (stoppingIndex method hrelative hfinite k)) :
    stoppingIndex method hrelative hfinite k ≤
      levelMethodIterationCap
        M_f D (method.chi * method.epsilon) method.levelCoefficient := by
  let history := history method hrelative hfinite k
  let j := stoppingIndex method hrelative hfinite k
  let τ := method.chi * history.optimalValue j
  have hτ_pos : 0 < τ := by
    have hopt_pos : 0 < history.optimalValue j := lt_of_lt_of_le hε hfull_step
    dsimp [τ]
    exact mul_pos hχ hopt_pos
  have hstopτ_j : history.shouldStop τ j := by
    rw [LevelMethodHistory.shouldStop_iff]
    have htermination :
        history.approximateOptimalValue j ≥ (1 - method.chi) * history.optimalValue j := by
      simpa [history, j, stoppingCriterion] using stopping_condition method hrelative hfinite k
    have hgap_le :
        history.gap j ≤ method.chi * history.optimalValue j :=
      gap_le_kappa_mul_optimalValue_of_termination_rule history j htermination
    simpa [τ] using hgap_le
  have hoptimal_succ : ∀ m : ℕ, history.optimalValue (m + 1) ≤ history.optimalValue m := by
    intro m
    simpa [history, ConstrainedLevelMethod.history, CompleteLevelMethod.history] using
      (show
          bestFunctionValueUpTo
              (fun i ↦
                method.stageProblemAt (parameter method hrelative hfinite k)
                  ((completeRun method hrelative hfinite k) i))
            (m + 1) ≤
            bestFunctionValueUpTo
              (fun i ↦
                method.stageProblemAt (parameter method hrelative hfinite k)
                  ((completeRun method hrelative hfinite k) i))
              m from
        bestFunctionValueUpTo_antitone_step m)
  have hoptimal_antitone : Antitone history.optimalValue :=
    antitone_nat_of_succ_le hoptimal_succ
  have hstopτ_min : ∀ {i : ℕ}, i < j → ¬ history.shouldStop τ i := by
    intro i hij
    rw [LevelMethodHistory.shouldStop_iff]
    have htermination_lt :
        history.approximateOptimalValue i <
          (1 - method.chi) * history.optimalValue i := by
      apply lt_of_not_ge
      intro htermination
      have hstop : stoppingCriterion method hrelative hfinite k i := by
        change history.approximateOptimalValue i ≥ (1 - method.chi) * history.optimalValue i
        exact htermination
      exact (stopping_condition_min method hrelative hfinite hij) hstop
    have hgap_gt : method.chi * history.optimalValue i < history.gap i := by
      rw [history.gap_eq_sub]
      nlinarith
    have hτ_le : τ ≤ method.chi * history.optimalValue i := by
      have hij' : i ≤ j := Nat.le_of_lt hij
      have hopt_mono : history.optimalValue j ≤ history.optimalValue i := hoptimal_antitone hij'
      exact mul_le_mul_of_nonneg_left hopt_mono hχ.le
    linarith
  have hstop_le_tau :
      j ≤ levelMethodIterationCap M_f D τ method.levelCoefficient := by
    obtain ⟨i, hi_bound, hi_stop⟩ :=
      exists_stopping_index_le_levelMethodIterationCap history hτ_pos hα hblock
    by_contra hji
    have hij : i < j := by
      apply lt_of_not_ge
      intro hij'
      exact hji (hij'.trans hi_bound)
    exact hstopτ_min hij hi_stop
  have huniform_pos : 0 < method.chi * method.epsilon := mul_pos hχ hε
  have hτ_ge_uniform : method.chi * method.epsilon ≤ τ := by
    dsimp [τ]
    exact mul_le_mul_of_nonneg_left hfull_step hχ.le
  exact hstop_le_tau.trans <|
    levelMethodIterationCap_antitone_tolerance huniform_pos hα hτ_ge_uniform

/-- If the canonical global-stop index at master step `k` is positive, then the preceding exact
record value is still above the global threshold `ε`. -/
theorem epsilon_le_optimalValue_pred_globalStopIndex
    (method : ConstrainedLevelMethodInput E)
    (hrelative : method.RelativeStoppingExists)
    (hfinite : method.SelectedThresholdFinite hrelative)
    {k : ℕ}
    (hstop : globallyStopsAt method hrelative hfinite k)
    (hglobal_pos : 0 < globalStopIndex method hrelative hfinite k hstop) :
    method.epsilon ≤
      (history method hrelative hfinite k).optimalValue
        (globalStopIndex method hrelative hfinite k hstop - 1) := by
  have h_prev_lt_global :
      globalStopIndex method hrelative hfinite k hstop - 1 <
        globalStopIndex method hrelative hfinite k hstop := by
    simpa using hglobal_pos
  have hprev_not_global :
      ¬ globalStopCriterion method hrelative hfinite k
          (globalStopIndex method hrelative hfinite k hstop - 1) := by
    exact global_stop_condition_min method hrelative hfinite k hstop h_prev_lt_global
  change ¬
      ((history method hrelative hfinite k).optimalValue
          (globalStopIndex method hrelative hfinite k hstop - 1) ≤
        method.epsilon)
    at hprev_not_global
  exact le_of_lt (lt_of_not_ge hprev_not_global)

/-- If the first global-stop index occurs no later than the canonical relative stopping index,
then the predecessor gap is at least `χ ε`. -/
theorem chi_mul_epsilon_le_gap_pred_globalStopIndex
    (method : ConstrainedLevelMethodInput E)
    (hrelative : method.RelativeStoppingExists)
    (hfinite : method.SelectedThresholdFinite hrelative)
    {k : ℕ}
    (hstop : globallyStopsAt method hrelative hfinite k)
    (hchi_nonneg : 0 ≤ method.chi)
    (hglobal_pos : 0 < globalStopIndex method hrelative hfinite k hstop)
    (hglobal_le_stopping :
      globalStopIndex method hrelative hfinite k hstop ≤
        stoppingIndex method hrelative hfinite k) :
    method.chi * method.epsilon ≤
      (history method hrelative hfinite k).gap
        (globalStopIndex method hrelative hfinite k hstop - 1) := by
  have h_prev_lt_stopping :
      globalStopIndex method hrelative hfinite k hstop - 1 <
        stoppingIndex method hrelative hfinite k := by
    omega
  have h_prev_ge_epsilon :
      method.epsilon ≤
        (history method hrelative hfinite k).optimalValue
          (globalStopIndex method hrelative hfinite k hstop - 1) :=
    epsilon_le_optimalValue_pred_globalStopIndex
      method hrelative hfinite hstop hglobal_pos
  have h_normal_stop_fails :
      method.chi *
          (history method hrelative hfinite k).optimalValue
            (globalStopIndex method hrelative hfinite k hstop - 1) ≤
        (history method hrelative hfinite k).gap
          (globalStopIndex method hrelative hfinite k hstop - 1) := by
    have hprev_not_stop :
        ¬ stoppingCriterion method hrelative hfinite k
            (globalStopIndex method hrelative hfinite k hstop - 1) :=
      stopping_condition_min method hrelative hfinite h_prev_lt_stopping
    change ¬
        ((history method hrelative hfinite k).approximateOptimalValue
            (globalStopIndex method hrelative hfinite k hstop - 1) ≥
          (1 - method.chi) *
            (history method hrelative hfinite k).optimalValue
              (globalStopIndex method hrelative hfinite k hstop - 1))
      at hprev_not_stop
    have hprev_lt :
        (history method hrelative hfinite k).approximateOptimalValue
            (globalStopIndex method hrelative hfinite k hstop - 1) <
          (1 - method.chi) *
            (history method hrelative hfinite k).optimalValue
              (globalStopIndex method hrelative hfinite k hstop - 1) :=
      lt_of_not_ge hprev_not_stop
    rw [(history method hrelative hfinite k).gap_eq_sub]
    nlinarith
  have hχ_mul :
      method.chi * method.epsilon ≤
        method.chi *
          (history method hrelative hfinite k).optimalValue
            (globalStopIndex method hrelative hfinite k hstop - 1) :=
    mul_le_mul_of_nonneg_left h_prev_ge_epsilon hchi_nonneg
  linarith

/-- Lemma 3.3.9 (2): if the final inner run at master step `k` globally stops at the canonical
index `globalStopIndex`, if this global-stop index occurs no later than the canonical relative
stopping index, and if the textbook predecessor-gap bound for that terminal run is available, then
the number of internal iterations executed up to that globally stopping step is bounded by the
displayed uniform chapter owner
`constrainedLevelMethodInternalIterationBound M_f D χ ε α`. -/
theorem last_step_internal_iterations_le_uniform_internal_iteration_bound
    (method : ConstrainedLevelMethodInput E)
    (hrelative : method.RelativeStoppingExists)
    (hfinite : method.SelectedThresholdFinite hrelative)
    {k : ℕ}
    (hstop : globallyStopsAt method hrelative hfinite k)
    {M_f D : ℝ}
    (hχ : 0 < method.chi)
    (hε : 0 < method.epsilon)
    (hα : method.levelCoefficient ∈ Set.Ioo (0 : ℝ) 1)
    (hglobal_pos : 0 < globalStopIndex method hrelative hfinite k hstop)
    (hglobal_le_stopping :
      globalStopIndex method hrelative hfinite k hstop ≤
        stoppingIndex method hrelative hfinite k)
    (h_last_step_cap :
      (globalStopIndex method hrelative hfinite k hstop : ℝ) ≤
        M_f ^ (2 : ℕ) * D ^ (2 : ℕ) /
          ((history method hrelative hfinite k).gap
              (globalStopIndex method hrelative hfinite k hstop - 1) ^
              (2 : ℕ) *
            levelParameterObjective method.levelCoefficient)) :
    (globalStopIndex method hrelative hfinite k hstop : ℝ) ≤
      constrainedLevelMethodInternalIterationBound
        M_f D method.chi method.epsilon method.levelCoefficient := by
  let gapPrev :=
    (history method hrelative hfinite k).gap
      (globalStopIndex method hrelative hfinite k hstop - 1)
  have hgapPrev : method.chi * method.epsilon ≤ gapPrev := by
    simpa [gapPrev] using
      chi_mul_epsilon_le_gap_pred_globalStopIndex
        method hrelative hfinite hstop hχ.le hglobal_pos hglobal_le_stopping
  have hnum_nonneg : 0 ≤ M_f ^ (2 : ℕ) * D ^ (2 : ℕ) := by positivity
  have hlevel_pos : 0 < levelParameterObjective method.levelCoefficient :=
    levelParameterObjective_pos hα
  have hprod_pos : 0 < method.chi * method.epsilon := mul_pos hχ hε
  have hsmallFactor_pos : 0 < (method.chi * method.epsilon) ^ (2 : ℕ) := by positivity
  have hsmallFactor_le_largeFactor :
      (method.chi * method.epsilon) ^ (2 : ℕ) ≤ gapPrev ^ (2 : ℕ) := by
    nlinarith [hgapPrev, hprod_pos]
  have hsource_bound :
      (globalStopIndex method hrelative hfinite k hstop : ℝ) ≤
        M_f ^ (2 : ℕ) * D ^ (2 : ℕ) /
          (levelParameterObjective method.levelCoefficient * gapPrev ^ (2 : ℕ)) := by
    simpa [gapPrev, mul_assoc, mul_left_comm, mul_comm] using h_last_step_cap
  have hbound :
      (globalStopIndex method hrelative hfinite k hstop : ℝ) ≤
        M_f ^ (2 : ℕ) * D ^ (2 : ℕ) /
          (levelParameterObjective method.levelCoefficient *
            (method.chi * method.epsilon) ^ (2 : ℕ)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      le_div_of_mul_right_denominator_le
        hsource_bound
        hnum_nonneg
        hlevel_pos
        hsmallFactor_pos
        hsmallFactor_le_largeFactor
  simpa
      [constrainedLevelMethodInternalIterationBound, mul_assoc, mul_left_comm, mul_comm, mul_pow]
    using hbound

end ConstrainedLevelMethod

end
