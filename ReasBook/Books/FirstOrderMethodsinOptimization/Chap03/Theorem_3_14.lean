import FirstOrderMethodsinOptimization.Chap03.Definition_3_2

-- Declarations for this item will be appended below by the statement pipeline.

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
