import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_54 (from Chap03) -/
noncomputable section

open MeasureTheory

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-
Definition 3.54 is a recall-only item in the measure-theoretic convex-geometry domain of
centroids of subsets of `ℝⁿ`.

Sampled owner-style declarations:
- `setAverage`, the core normalized-average construction on measurable sets;
- `setAverage_eq`, the canonical normalized-integral formula for that owner;
- `Convex.set_average_mem`, the downstream convex-geometry owner lemma showing centroid membership
  is derived from set averages.

Best owner abstraction:
- source-facing: the textbook centroid of a set
- core/canonical: `setAverage`
- bridge/view: `setAverage_eq` specialized to the identity map on `S`

Primitive data:
- a set `S : Set E`

Derived API:
- the centroid expression `⨍ x in S, x`, given directly by the owner `setAverage`;
- the normalized-integral formula obtained directly from `setAverage_eq`

This file is now recall-only: the previous public alias `centerOfGravity` duplicated the canonical
mathlib owner `setAverage` with no extra mathematics. The centroid surface is therefore expressed
directly by the set-average notation, and the normalized-integral formula remains owned by
`setAverage_eq`.
-/

section

variable (S : Set E)

/- Definition 3.54: the center of gravity of a set `S ⊆ ℝⁿ` is the canonical Lebesgue
set-average construction specialized to the identity map on `S`. -/
#check (⨍ x in S, x ∂volume : E)

/- The normalized-integral formula for the centroid is the identity-function specialization of the
owner theorem `setAverage_eq`. -/
#check (setAverage_eq volume (fun x : E ↦ x) S)

end

end

/-! ### Proposition_3_54 (from Chap03) -/
universe u

/- Proposition 3.54 lies in the chapter's finite sampled constrained-level stopping domain.

Relevant owner declarations sampled before refining this file:
* `setConstrainedParametricObjective` in `Proposition_3_52`, the chapter owner for the pointwise
  max-objective `x ↦ max (f x - tk) (fBar x)`;
* `parametricValueFunction` in `Lemma_3_3_6`, the set-level canonical infimum of that owner;
* `Finset.inf'`, `Finset.inf'_le`, and `Finset.exists_mem_eq_inf'`, the mathlib owners for
  nonempty finite minima and their canonical bound / attainment API;
* `minGradientNormAlongIterates` and `minGradientNormAlongIterates.exists_eq` in
  `Chap02/Definition_2_23`, the earlier project instance of the same `Finset.inf'` bridge shape.

Source/core/bridge triage:
* source-facing: the finite sampled constrained-level minimum on the search set `X`;
* core/canonical: `setConstrainedParametricObjective f fBar tk` and
  `parametricValueFunction (↑X : Set α) f fBar tk`;
* bridge/view: `constrained_level_minimum`, its finite attainment theorem, and the component
  bounds extracted from a bound on the canonical owner objective.

Primitive data:
* the nonempty finite search set `X`;
* the iteration parameter `tk`;
* the functions `f` and `fBar`.

Derived API:
* the finite minimum `constrained_level_minimum`;
* the source-facing notation `f*[X; f; fBar](tk)` for that finite minimum;
* the owner-style finite-minimum API `constrained_level_minimum.le` and
  `constrained_level_minimum.exists_eq`;
* the canonical bridge
  `parametricValueFunction_coe_eq_constrained_level_minimum`;
* the attainment theorem `global_stop_exists_minimizer`;
* the owner component bounds `setConstrainedParametricObjective.f_le_of_le` and
  `setConstrainedParametricObjective.fBar_le_of_le`.

This file therefore keeps only the finite-sample operational bridge and reuses the existing
Chapter 3 owner `setConstrainedParametricObjective` directly instead of introducing a duplicate
pointwise stopping-value owner.
-/

variable {α : Type u}

/-- The finite minimum of the constrained parametric objective over the search set `X`. -/
def constrained_level_minimum (X : Finset α) [Fact X.Nonempty] (tk : ℝ) (f fBar : α → ℝ) : ℝ :=
  X.inf' (Fact.out : X.Nonempty) (setConstrainedParametricObjective f fBar tk)

namespace ConstrainedLevelMinimum

scoped notation:max "f*[" X:arg "; " f:arg "; " fBar:arg "](" tk:arg ")" =>
  constrained_level_minimum X tk f fBar

end ConstrainedLevelMinimum

open scoped ConstrainedLevelMinimum

namespace constrained_level_minimum

/-- The finite minimum is bounded above by the constrained parametric objective at each point of
the search set. -/
-- Proof sketch: unfold `constrained_level_minimum` and apply `Finset.inf'_le` to the point `x`.
theorem le (X : Finset α) [Fact X.Nonempty] (tk : ℝ) (f fBar : α → ℝ) {x : α} (hx : x ∈ X) :
    f*[X; f; fBar](tk) ≤ setConstrainedParametricObjective f fBar tk x := by
  exact Finset.inf'_le (setConstrainedParametricObjective f fBar tk) hx

/-- Some point of the finite search set attains the constrained-level minimum. -/
-- Proof sketch: apply the canonical finite-attainment theorem `Finset.exists_mem_eq_inf'` to the
-- owner objective on `X`.
theorem exists_eq (X : Finset α) [Fact X.Nonempty] (tk : ℝ) (f fBar : α → ℝ) :
    ∃ xStar ∈ X,
      f*[X; f; fBar](tk) = setConstrainedParametricObjective f fBar tk xStar := by
  exact X.exists_mem_eq_inf' (Fact.out : X.Nonempty) (setConstrainedParametricObjective f fBar tk)

end constrained_level_minimum

/-- Evaluating the chapter owner `parametricValueFunction` on the finite feasible set `↑X`
recovers the finite constrained-level minimum. -/
-- Proof sketch: pick a minimizer of the finite minimum, show it is a genuine minimizer on the
-- coerced feasible set `↑X`, then apply the Chapter 1 owner theorem
-- `SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn`.
theorem parametricValueFunction_coe_eq_constrained_level_minimum
    (X : Finset α) [Fact X.Nonempty] (tk : ℝ) (f fBar : α → ℝ) :
    parametricValueFunction (↑X : Set α) f fBar tk =
      (f*[X; f; fBar](tk) : EReal) := by
  let problem : SetConstrainedMinimizationProblem α :=
    SetConstrainedMinimizationProblem.mk (↑X : Set α)
      (setConstrainedParametricObjective f fBar tk)
  rcases constrained_level_minimum.exists_eq X tk f fBar with ⟨xStar, hxStar, hmin⟩
  have hxStar' : xStar ∈ (↑X : Set α) := by
    simpa using hxStar
  have hminOn : IsMinOn (setConstrainedParametricObjective f fBar tk) (↑X : Set α) xStar := by
    intro y hy
    simpa [hmin] using constrained_level_minimum.le X tk f fBar hy
  simpa [problem, parametricValueFunction, hmin] using
    problem.optimalValue_eq_of_isMinOn hxStar' hminOn

/-- Proposition 3.54: if the global stop condition holds, then some point of the finite set `X`
attains the finite minimum of `x ↦ max (f x - tk) (fBar x)` and this value is at most `ε`. -/
-- Proof sketch: choose a minimizer of the owner objective on the nonempty finset `X`, identify
-- its value with `constrained_level_minimum`, and combine that equality with the global stop
-- inequality.
theorem global_stop_exists_minimizer (X : Finset α) [Fact X.Nonempty] (tk ε : ℝ)
    (f fBar : α → ℝ) (hstop : f*[X; f; fBar](tk) ≤ ε) :
    ∃ xStar ∈ X,
      setConstrainedParametricObjective f fBar tk xStar = f*[X; f; fBar](tk) ∧
        setConstrainedParametricObjective f fBar tk xStar ≤ ε := by
  rcases constrained_level_minimum.exists_eq X tk f fBar with ⟨xStar, hxStar, hmin⟩
  refine ⟨xStar, hxStar, hmin.symm, ?_⟩
  simpa [hmin] using hstop

namespace setConstrainedParametricObjective

/-- A point whose constrained parametric objective is at most `ε` also satisfies
the corresponding bound on `f`. -/
-- Proof sketch: rewrite the owner objective as `max (f x - tk) (fBar x)`, use `max_le_iff` to
-- read off `f x - tk ≤ ε`, then combine it with `tk ≤ tStar`.
theorem f_le_of_le {tk tStar ε : ℝ} {f fBar : α → ℝ} {x : α}
    (hvalue : setConstrainedParametricObjective f fBar tk x ≤ ε) (htk : tk ≤ tStar) :
    f x ≤ tStar + ε := by
  rw [setConstrainedParametricObjective_apply] at hvalue
  rcases max_le_iff.mp hvalue with ⟨hf, _⟩
  linarith

/-- A point whose constrained parametric objective is at most `ε` also satisfies
`fBar x ≤ ε`. -/
-- Proof sketch: rewrite the owner objective as a pointwise maximum and read off the second
-- component using `max_le_iff`.
theorem fBar_le_of_le {tk ε : ℝ} {f fBar : α → ℝ} {x : α}
    (hvalue : setConstrainedParametricObjective f fBar tk x ≤ ε) :
    fBar x ≤ ε := by
  rw [setConstrainedParametricObjective_apply] at hvalue
  exact (max_le_iff.mp hvalue).2

end setConstrainedParametricObjective

/-! ### Theorem_3_54 (from Chap03) -/
noncomputable section

universe u v

open MeasureTheory

variable {X : Type u} [PseudoMetricSpace X]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E]

local notation "dim" => Module.finrank ℝ E

/-
Primary domain: sampled best-value bounds relative to an attained closed-ball infimum, built as a
source-facing bridge over the chapter owner `bestFunctionValueUpTo`.

Sampled owner-style declarations in the same domain:
- `bestFunctionValueUpTo` and `bestFunctionValueUpTo_le` in `Definition_3_55`, the chapter owners
  for sampled prefix minima and their comparison with selected samples;
- mathlib `LipschitzOnWith.le_add_mul`, the owner one-sided Lipschitz estimate on a set;
- mathlib `IsMinOn.isGLB` and `IsGLB.csInf_eq`, the attained-infimum bridge for the source-side
  ball optimum.

Owner abstraction:
- source-facing: the textbook ball optimum as the direct canonical expression
  `sInf (f '' Metric.closedBall xStar R)`;
- core/canonical: `bestFunctionValueUpTo`, `bestFunctionValueUpTo_le`, `IsMinOn`, and
  `LipschitzOnWith`;
- bridge/view: the attained-infimum equality, the pointwise gap estimate, and the passage from the
  selected-point estimate to the owner-level sampled best-value estimate.

Primitive data:
- the objective `f`, center `xStar`, radius `R`, Lipschitz constant `M`, and the sampled sequence
  data;
- the radius nonnegativity needed for the attained-infimum owner theorem is derived downstream
  from closed-ball membership whenever a sampled point in `B₂(xStar, R)` is already part of the
  hypotheses.

Derived API:
- the attained-infimum identity for `sInf (f '' Metric.closedBall xStar R)`;
- the Lipschitz gap estimate relative to that direct ball infimum;
- the best-so-far feasible-value decay theorem on `bestFunctionValueUpTo`.

Source/core/bridge triage:
- source-facing: the direct closed-ball infimum `sInf (f '' Metric.closedBall xStar R)`;
- core/canonical: `bestFunctionValueUpTo`, `bestFunctionValueUpTo_le`, `IsMinOn`, and
  `LipschitzOnWith`;
- bridge/view: the attained-infimum equality, the pointwise gap estimate, and the passage from the
  source-side ball infimum to the owner-level sampled best-value estimate.

The previous version introduced a one-off local wrapper around the canonical expression
`sInf (f '' Metric.closedBall xStar R)` and then repaired its empty-ball partiality by passing an
unrelated witness point through the public API. This refinement deletes that duplicate surface,
keeps the source-facing optimum as the canonical `sInf` expression itself, records the natural
radius assumption `0 ≤ R` only for the attained minimum `f^*`, and lets later sampled-point
bounds recover that nonnegativity from closed-ball membership instead of carrying redundant public
guards that belong upstream in the selected-distance estimate.
-/

/-- If `0 ≤ R` and `xStar` minimizes `f` on `B₂(xStar, R)`, then the infimum of the objective
image over that ball equals `f xStar`. -/
-- Proof sketch: `0 ≤ R` puts `xStar` in `B₂(xStar, R)`. Then `IsMinOn.isGLB` identifies
-- `f xStar` as the greatest lower bound of `f '' B₂(xStar, R)`, and `IsGLB.csInf_eq` rewrites the
-- infimum accordingly.
theorem sInf_image_closedBall_eq_of_isMinOn
    {f : X → ℝ} {xStar : X} {R : ℝ}
    (hR : 0 ≤ R)
    (hxStar_opt : IsMinOn f (Metric.closedBall xStar R) xStar) :
    sInf (f '' Metric.closedBall xStar R) = f xStar := by
  -- The radius assumption puts the minimizer itself inside the closed ball.
  have hxStar_mem : xStar ∈ Metric.closedBall xStar R := by
    simpa [Metric.mem_closedBall] using hR
  -- The minimizing hypothesis upgrades `f xStar` to the greatest lower bound of the image set.
  have hglb : IsGLB (f '' Metric.closedBall xStar R) (f xStar) :=
    hxStar_opt.isGLB hxStar_mem
  -- The image is nonempty because it contains `f xStar`.
  have hnonempty : (f '' Metric.closedBall xStar R).Nonempty := by
    refine ⟨f xStar, xStar, hxStar_mem, rfl⟩
  -- The attained greatest lower bound is exactly the infimum.
  simpa using hglb.csInf_eq hnonempty

/-- If `xStar` minimizes `f` on `B₂(xStar, R)`, `f` is `M`-Lipschitz there, and `x ∈ B₂(xStar, R)`,
then the objective gap at `x` is at most `M` times its distance to `xStar`, measured relative to
the canonical closed-ball infimum `sInf (f '' B₂(xStar, R))`. -/
-- Proof sketch: first derive `0 ≤ R` from `x ∈ B₂(xStar, R)`. Rewrite
-- `sInf (f '' B₂(xStar, R))` as `f xStar` using the attained-infimum theorem. Then apply the
-- owner Lipschitz estimate to `x` and `xStar` inside the same closed ball and rearrange the
-- resulting bound on `f x - f xStar`.
theorem sub_sInf_image_closedBall_le_lipschitz_mul_dist_of_isMinOn
    {f : X → ℝ} {xStar x : X} {R : ℝ} {M : NNReal}
    (hf_lipschitz : LipschitzOnWith M f (Metric.closedBall xStar R))
    (hxStar_opt : IsMinOn f (Metric.closedBall xStar R) xStar)
    (hx : x ∈ Metric.closedBall xStar R) :
    f x - sInf (f '' Metric.closedBall xStar R) ≤ (M : ℝ) * dist x xStar := by
  -- Membership of `x` in the closed ball forces the radius to be nonnegative.
  have hdist_le_R : dist x xStar ≤ R := by
    simpa [Metric.mem_closedBall] using hx
  have hR : 0 ≤ R := le_trans dist_nonneg hdist_le_R
  -- The center also lies in the closed ball, so the Lipschitz estimate applies to `(x, xStar)`.
  have hxStar_mem : xStar ∈ Metric.closedBall xStar R := by
    simpa [Metric.mem_closedBall] using hR
  -- Rewrite the canonical infimum as the attained minimum value `f xStar`.
  have hsInf_eq : sInf (f '' Metric.closedBall xStar R) = f xStar :=
    sInf_image_closedBall_eq_of_isMinOn hR hxStar_opt
  -- The one-sided Lipschitz inequality gives the desired objective-gap control.
  have hLip : f x ≤ f xStar + (M : ℝ) * dist x xStar :=
    hf_lipschitz.le_add_mul hx hxStar_mem
  rw [hsInf_eq]
  rw [sub_le_iff_le_add]
  simpa [add_comm, add_left_comm, add_assoc] using hLip

set_option linter.style.longLine false
/-- Theorem 3.54: let `μ` be the comparison measure used in the selected-point decay estimate, let
`xSeq` be the feasible subsequence produced by the cutting-plane iterates,
let `i(k)` be the corresponding feasible index, and let `f_{i(k)}^*` be the best
objective value `bestFunctionValueUpTo (fun j ↦ f (xSeq j)) (i k)` among the first `i(k) + 1`
feasible points. If `f` is `M`-Lipschitz on `B₂(xStar, R)`, if `xStar` realizes the infimum `f^*`
on that ball, and if the selected feasible iterate
`xSeq (i k)` satisfies the standard cutting-plane distance estimate
`‖xSeq (i k) - xStar‖ ≤ R (1 - 1 / (dim + 1)^2)^(k / 2) (vol(B₂(x0, R)) / vol(Q))^(1 / dim)`,
where `dim = Module.finrank ℝ E` and `vol = Measure.real μ`, then the same decay estimate holds
for the objective gap `f_{i(k)}^* - f^*`. Taking `μ = volume` and specializing to
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ` statement. -/
-- Proof sketch: compare the best-so-far value with the selected value `f (xSeq (i k))` using
-- `bestFunctionValueUpTo_le`. Then apply the pointwise Lipschitz gap estimate relative to
-- `sInf (f '' B₂(xStar, R))` and substitute the assumed distance decay bound.
theorem selected_feasible_bestObjectiveValue_sub_sInf_image_closedBall_le_lipschitz_radius_mul_geometricDecay_volumeRatio
    (μ : Measure E)
    {f : E → ℝ} {xStar x0 : E} {R : ℝ} {M : NNReal} {Q : Set E}
    {xSeq : ℕ → E} {i : ℕ → ℕ}
    (k : ℕ)
    (hf_lipschitz : LipschitzOnWith M f (Metric.closedBall xStar R))
    (hxStar_opt : IsMinOn f (Metric.closedBall xStar R) xStar)
    (hselected_mem : xSeq (i k) ∈ Metric.closedBall xStar R)
    (hselected_dist :
      ‖xSeq (i k) - xStar‖ ≤
        R *
          Real.rpow (1 - 1 / (((dim : ℝ) + 1) ^ (2 : ℕ))) ((k : ℝ) / 2) *
            Real.rpow
              (Measure.real μ (Metric.closedBall x0 R) / Measure.real μ Q)
              (1 / (dim : ℝ))) :
    bestFunctionValueUpTo (fun j ↦ f (xSeq j)) (i k) -
        sInf (f '' Metric.closedBall xStar R) ≤
      (M : ℝ) * R *
        Real.rpow (1 - 1 / (((dim : ℝ) + 1) ^ (2 : ℕ))) ((k : ℝ) / 2) *
          Real.rpow
            (Measure.real μ (Metric.closedBall x0 R) / Measure.real μ Q)
            (1 / (dim : ℝ)) := by
  -- Compare the best sampled value with the selected feasible sample `xSeq (i k)`.
  have hbest_le_selected :
      bestFunctionValueUpTo (fun j ↦ f (xSeq j)) (i k) -
          sInf (f '' Metric.closedBall xStar R) ≤
        f (xSeq (i k)) - sInf (f '' Metric.closedBall xStar R) := by
    exact sub_le_sub_right (bestFunctionValueUpTo_le ⟨i k, Nat.lt_succ_self _⟩) _
  -- The selected sample lies in the closed ball, so the pointwise owner gap theorem applies.
  have hpointwise :
      f (xSeq (i k)) - sInf (f '' Metric.closedBall xStar R) ≤
        (M : ℝ) * dist (xSeq (i k)) xStar :=
    sub_sInf_image_closedBall_le_lipschitz_mul_dist_of_isMinOn
      hf_lipschitz hxStar_opt hselected_mem
  -- Convert the assumed norm estimate into the metric-distance form expected by the owner theorem.
  have hselected_dist' :
      dist (xSeq (i k)) xStar ≤
        R *
          Real.rpow (1 - 1 / (((dim : ℝ) + 1) ^ (2 : ℕ))) ((k : ℝ) / 2) *
            Real.rpow
              (Measure.real μ (Metric.closedBall x0 R) / Measure.real μ Q)
              (1 / (dim : ℝ)) := by
    simpa [dist_eq_norm] using hselected_dist
  -- Multiply the distance decay by the nonnegative Lipschitz constant.
  have hmul_dist :
      (M : ℝ) * dist (xSeq (i k)) xStar ≤
        (M : ℝ) *
          (R *
            Real.rpow (1 - 1 / (((dim : ℝ) + 1) ^ (2 : ℕ))) ((k : ℝ) / 2) *
              Real.rpow
                (Measure.real μ (Metric.closedBall x0 R) / Measure.real μ Q)
                (1 / (dim : ℝ))) := by
    exact mul_le_mul_of_nonneg_left hselected_dist' M.2
  -- Chaining the three comparisons yields the claimed sampled best-value bound.
  refine le_trans hbest_le_selected ?_
  refine le_trans hpointwise ?_
  simpa [mul_assoc] using hmul_dist

end
