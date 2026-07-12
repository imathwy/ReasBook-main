import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_3_3
import LecturesConvexOptimization_Nesterov_2018.Chap07.Lemma_7_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin RelativeScaleTransformNotation

noncomputable section

universe u

variable {X : Type u}

/- Proposition 7.36 lies in the monotone objective-transform / constrained argmin domain.

Relevant owner-style declarations sampled before refinement:
- `relativeScaleTransformedObjective` and `relativeScaleTransformedObjective_apply` in
  `Chap07/Lemma_7_20`, the existing Chapter 7 owner for the half-squared transform
  `x ↦ (1 / 2) * f(x)^2`;
- mathlib `IsMinOn` and `IsMinOn.comp_mono`, the canonical minimizer owner and monotone transport
  lemma for objective transforms;
- `argmin[Q]` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the project owner for
  constrained minimizer sets.

Best owner abstraction:
- source-facing: Proposition 7.36's equivalence between minimizing `f` on `Q` and minimizing its
  half-squared transform on `Q`;
- core/canonical: `relativeScaleTransformedObjective`, `IsMinOn`, and `argmin[Q]`;
- bridge/view: the minimizer and argmin equivalence lemmas below.

Primitive data:
- the feasible set `Q`;
- the objective `f : X → ℝ`;
- pointwise nonnegativity of `f` on `Q`.

Derived API:
- `isMinOn_relativeScaleTransformedObjective_iff`;
- `mem_argmin_relativeScaleTransformedObjective_iff`;
- `argmin_eq_argmin_relativeScaleTransformedObjective`.

The previous version introduced a second local owner `halfSquaredObjective` and encoded argmin sets
as raw set comprehensions. This refinement deletes that duplicate owner, reuses the Chapter 7
transform directly, and states the proposition on the canonical constrained-argmin surface.
-/

/- On the feasible set, minimizing `f` is equivalent to minimizing `f̂` when `f` is nonnegative
there. -/
-- Proof sketch: for `x ∈ Q`, the nonnegativity hypothesis gives `0 ≤ f x` and `0 ≤ f y` for every
-- `y ∈ Q`. On `ℝ≥0`, the scalar map `t ↦ (1 / 2) * t^2` is order-reflecting, so the inequalities
-- defining `IsMinOn` for `f` and for `f̂` are equivalent.
theorem isMinOn_relativeScaleTransformedObjective_iff
    {Q : Set X} {f : X → ℝ} {x : X}
    (hf_nonneg : ∀ y ∈ Q, 0 ≤ f y) (hx : x ∈ Q) :
    IsMinOn f̂ Q x ↔ IsMinOn f Q x := sorry

@[simp] theorem mem_argmin_relativeScaleTransformedObjective_iff
    {Q : Set X} {f : X → ℝ} {x : X}
    (hf_nonneg : ∀ x ∈ Q, 0 ≤ f x) :
    x ∈ argmin[Q] f̂ ↔ x ∈ argmin[Q] f := by
  rw [mem_constrainedArgmin_iff, mem_constrainedArgmin_iff]
  constructor
  · rintro ⟨hx, hxmin⟩
    exact ⟨hx, (isMinOn_relativeScaleTransformedObjective_iff hf_nonneg hx).mp hxmin⟩
  · rintro ⟨hx, hxmin⟩
    exact ⟨hx, (isMinOn_relativeScaleTransformedObjective_iff hf_nonneg hx).mpr hxmin⟩

/-- Proposition 7.36: if `f` is nonnegative on `Q`, then the minimizers of `f` on `Q`
coincide with the minimizers of the transformed objective `f̂`, so the two
optimization problems are equivalent. -/
-- Proof sketch: identify `argmin[Q]` membership with feasibility plus `IsMinOn`, then apply
-- `isMinOn_relativeScaleTransformedObjective_iff` pointwise on feasible minimizers.
theorem argmin_eq_argmin_relativeScaleTransformedObjective
    {Q : Set X} {f : X → ℝ}
    (hf_nonneg : ∀ x ∈ Q, 0 ≤ f x) :
    argmin[Q] f = argmin[Q] f̂ := by
  ext x
  exact (mem_argmin_relativeScaleTransformedObjective_iff hf_nonneg).symm

end
