import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_14 (from Chap03) -/
open scoped BigOperators

section

variable {m : ℕ} {α : Type*}
variable [PseudoMetricSpace α]

/- Definition 3.14 is a `source-facing` item: the public owner is the Fermat-Weber objective
itself. The ambient `core/canonical` notion underneath is the metric-space distance `dist`, so the
definition uses that owner directly and treats the Euclidean norm formula as a companion view. -/

/-- Definition 3.14: for weighted sites `a i` in a metric space, the Fermat-Weber objective is
the weighted finite sum of the distances from `x` to the sites. In the Euclidean specialization
this is the textbook formula `x ↦ ∑ i, ω i * ‖x - a i‖`. The textbook assumes positive weights;
positivity is imposed only in later results, since it does not affect the function definition
itself. -/
def fermatWeberObjective
    (ω : Fin m → ℝ) (a : Fin m → α) :
    α → ℝ :=
  fun x ↦ ∑ i, ω i * dist x (a i)

-- Proof sketch: unfold `fermatWeberObjective`; the statement is exactly its defining formula.
/-- Evaluating the Fermat-Weber objective at `x` gives the weighted sum of the distances from `x`
to the sites `a i`. -/
@[simp] theorem fermatWeberObjective_apply
    (ω : Fin m → ℝ) (a : Fin m → α) (x : α) :
    fermatWeberObjective ω a x = ∑ i, ω i * dist x (a i) :=
  rfl

section SeminormedAddCommGroup

variable {E : Type*} [SeminormedAddCommGroup E]

-- Proof sketch: evaluate the metric-space definition at `x` and rewrite each distance using
-- `dist_eq_norm`.
/-- In a seminormed additive commutative group, the Fermat-Weber objective is the weighted sum of
the norms `‖x - a i‖`. This is the Euclidean textbook formula specialized to the ambient norm. -/
@[simp] theorem fermatWeberObjective_apply_eq_sum_norm
    (ω : Fin m → ℝ) (a : Fin m → E) (x : E) :
    fermatWeberObjective ω a x = ∑ i, ω i * ‖x - a i‖ := by
  simp [fermatWeberObjective, dist_eq_norm]

end SeminormedAddCommGroup

section Real

-- Proof sketch: specialize the norm formula to `ℝ`, where `‖x - a i‖ = |x - a i|`, and simplify
-- the constant unit weights.
/-- On the real line with unit weights, the Fermat-Weber objective is the textbook absolute-
deviation sum `x ↦ ∑ i, |x - a_i|`. -/
@[simp] theorem fermatWeberObjective_one_apply_eq_sum_abs
    (a : Fin m → ℝ) (x : ℝ) :
    fermatWeberObjective (fun _ : Fin m ↦ (1 : ℝ)) a x = ∑ i, |x - a i| := by
  simpa using
    (fermatWeberObjective_apply_eq_sum_norm (fun _ : Fin m ↦ (1 : ℝ)) a x)

end Real

end

/-! ### Proposition_3_14 (from Chap03) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 3.14 is a `bridge/view` item for the chapter owner `subdifferentialAt` and the
calculus owners `DifferentiableAt` and `fderiv`. The singleton characterization is the primitive
source-facing bridge; stronger consequences such as simultaneously extracting differentiability and
identifying `fderiv` are derived API and are intentionally not kept here as parallel primitive
declarations. -/

-- Proof sketch: if `f` is differentiable at `x`, convexity gives the supporting-hyperplane
-- inequality for `fderiv ℝ f x`, and comparing directional estimates in directions `d` and `-d`
-- shows every subgradient agrees with `fderiv ℝ f x`. Conversely, if the subdifferential is a
-- singleton, then the directional derivative is forced to be linear in the direction variable, so
-- the convex function is differentiable and its derivative is that unique subgradient.
/-- Proposition 3.14: for a convex real-valued function, differentiability at a point is equivalent
to the subdifferential at that point being the singleton containing the Fréchet derivative. In the
Euclidean setting of the text, this functional is represented by the gradient. -/
theorem differentiableAt_iff_subdifferentialAt_eq_singleton_fderiv
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) {x : E} :
    DifferentiableAt ℝ f x ↔ subdifferentialAt f x = {fderiv ℝ f x} := sorry

end

/-! ### Theorem_3_14 (from Chap03) -/
universe u

open scoped Pointwise

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Theorem 3.14 is a `source-facing` theorem in the chapter convex-analysis API. Its owner
declarations are already the chapter/project primitives `effective_domain`, `is_subgradient_at`,
and `subdifferential`, so this file contributes only the positive-scaling calculus theorems. -/
recall effective_domain
recall is_subgradient_at
recall subdifferential
recall mem_subdifferential

-- Proof sketch: for `α > 0`, multiplication by `(α : EReal)` is order-preserving and sends `⊤`
-- to `⊤`, so `((α : EReal) * f x) < ⊤` holds exactly when `f x < ⊤`. Extensionality on points
-- then gives equality of the two effective domains.
private theorem effective_domain_pos_real_mul (f : E → EReal) (α : ℝ) (hα : 0 < α) :
    effective_domain (fun x ↦ (α : EReal) * f x) = effective_domain f := sorry

-- Proof sketch: rewrite both sides using `mem_subdifferential` and `is_subgradient_at`; the
-- domain clause is transported by `effective_domain_pos_real_mul`, and the supporting inequality
-- is equivalent after dividing by the positive scalar `α`.
private theorem mem_subdifferential_pos_real_mul_iff
    (f : E → EReal) (α : ℝ) (hα : 0 < α) (x : E) (g : Module.Dual ℝ E) :
    g ∈ subdifferential (fun y ↦ (α : EReal) * f y) x ↔
      α⁻¹ • g ∈ subdifferential f x := sorry

-- Proof sketch: extensionality on `g`; rewrite membership in the scaled set with the canonical
-- pointwise-scalar lemma `Set.mem_smul_set_iff_inv_smul_mem₀`, then apply the private owner-level
-- equivalence `mem_subdifferential_pos_real_mul_iff`.
/-- Theorem 3.14: multiplying an extended-real-valued function by a positive real scalar multiplies
its subdifferential by the same scalar. -/
theorem subdifferential_pos_real_mul (f : E → EReal) (α : ℝ) (hα : 0 < α) (x : E) :
    subdifferential (fun y ↦ (α : EReal) * f y) x = α • subdifferential f x := by
  ext g
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hα)]
  exact mem_subdifferential_pos_real_mul_iff f α hα x g

end
