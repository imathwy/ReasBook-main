import Mathlib
import Nesterov.Chap03.Definition_3_3
import Nesterov.Chap03.Definition_3_1_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped WithTopConvexAnalysis

/- Theorem 3.45 lies in the constrained strong-convexity / bounded-sublevel / minimizer-existence
domain.

Sampled owner-style declarations:
- mathlib `StrongConvexOn`
- mathlib `StrictConvexOn.eq_of_isMinOn`
- mathlib `LowerSemicontinuousOn.exists_isMinOn`
- mathlib `isCompact_of_isClosed_isBounded`
- project `constrainedSublevelSet` in `Definition_3_3`

Best owner abstraction:
- source-facing: bounded constrained sublevel sets and unique feasible minimizers for a positive
  strongly convex objective
- core/canonical: `StrongConvexOn Q μ f`
- bridge/view: the coercion of a real-valued objective `f : E → ℝ` to its canonical
  `WithTop ℝ`-valued view `((↑) : ℝ → WithTop ℝ) ∘ f` so that sublevel sets use the chapter owner
  `constrainedSublevelSet`

Primitive data:
- a feasible set `Q`, a real-valued objective `f`, and a strong-convexity modulus `μ`
- for attainment, the genuine extra data `IsClosed Q` and `LowerSemicontinuousOn f Q`
- for the source-facing bridge theorem, continuity of `f` on the closed feasible set

Derived API:
- boundedness of the constrained sublevel sets
- existence and uniqueness of a feasible minimizer
- the continuity-on-closed-set bridge to the lower-semicontinuous owner theorem

This file owns these consequences for `StrongConvexOn`. The only duplicate wheel in the previous
version was the raw set `Q ∩ {x | f x ≤ α}`, which is canonically the chapter owner
`constrainedSublevelSet Q (((↑) : ℝ → WithTop ℝ) ∘ f) α`. For attainment, the real extra input
after boundedness is only closedness of the feasible set together with lower semicontinuity of the
objective, so the main existence theorem is stated directly at that primitive layer. The textbook
continuous-on-closed-set formulation survives only as a thin bridge. -/

namespace StrongConvexOn

section BoundedSublevel

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Theorem 3.45: every constrained level set of a positive strongly convex real-valued objective
is bounded. -/
theorem isBounded_constrainedSublevelSet
    {Q : Set E} {f : E → ℝ} {μ α : ℝ}
    (hf : StrongConvexOn Q μ f) (hμ : 0 < μ) :
    Bornology.IsBounded
      (constrainedSublevelSet Q (((↑) : ℝ → WithTop ℝ) ∘ f) α) := sorry

end BoundedSublevel

section Existence

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- A positive strongly convex real-valued objective on a nonempty closed feasible set has a
unique feasible minimizer once the objective is lower semicontinuous on that feasible set. -/
theorem existsUnique_isMinOn_of_isClosed_lowerSemicontinuousOn
    {Q : Set E} {f : E → ℝ} {μ : ℝ}
    (hf : StrongConvexOn Q μ f) (hμ : 0 < μ)
    (hf_lower : LowerSemicontinuousOn f Q)
    (hQ_nonempty : Q.Nonempty) (hQ_closed : IsClosed Q) :
    ∃! x : E, x ∈ Q ∧ IsMinOn f Q x := by
  rcases hQ_nonempty with ⟨x₀, hx₀Q⟩
  let fTop : E → WithTop ℝ := ((↑) : ℝ → WithTop ℝ) ∘ f
  let S := constrainedSublevelSet Q fTop (f x₀)
  have hx₀S : x₀ ∈ S := by
    exact mem_constrainedSublevelSet_iff.2 ⟨hx₀Q, le_rfl⟩
  have hSQ : S ⊆ Q := by
    intro x hx
    exact (mem_constrainedSublevelSet_iff.mp hx).1
  have hS_closed : IsClosed S := by
    rw [show S = Q ∩ f ⁻¹' Set.Iic (f x₀) by
      ext x
      simp [S, fTop, Set.mem_Iic]]
    rw [lowerSemicontinuousOn_iff_preimage_Iic] at hf_lower
    obtain ⟨v, hv_closed, hv_eq⟩ := hf_lower (f x₀)
    rw [hv_eq]
    exact hQ_closed.inter hv_closed
  have hS_bounded : Bornology.IsBounded S := by
    simpa [S, fTop] using
      (hf.isBounded_constrainedSublevelSet hμ :
        Bornology.IsBounded
          (constrainedSublevelSet Q (((↑) : ℝ → WithTop ℝ) ∘ f) (f x₀)))
  have hS_compact : IsCompact S :=
    Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded
  obtain ⟨x, hxS, hxMinS⟩ :=
    (hf_lower.mono hSQ).exists_isMinOn ⟨x₀, hx₀S⟩ hS_compact
  have hxQ : x ∈ Q :=
    hSQ hxS
  have hx_le_x₀ : f x ≤ f x₀ :=
    hxMinS hx₀S
  have hxMinQ : IsMinOn f Q x := by
    intro y hyQ
    by_cases hyS : y ∈ S
    · exact hxMinS hyS
    · have hy_gt : f x₀ < f y := by
        refine lt_of_not_ge ?_
        intro hy_le
        apply hyS
        refine mem_constrainedSublevelSet_iff.2 ⟨hyQ, ?_⟩
        simpa [fTop] using hy_le
      exact (le_trans hx_le_x₀ hy_gt.le)
  refine ⟨x, ⟨hxQ, hxMinQ⟩, ?_⟩
  intro y hy
  exact (hf.strictConvexOn hμ).eq_of_isMinOn hy.2 hxMinQ hy.1 hxQ

/-- A positive strongly convex real-valued objective that is continuous on a nonempty closed
feasible set has a unique feasible minimizer. -/
theorem existsUnique_isMinOn_of_isClosed
    {Q : Set E} {f : E → ℝ} {μ : ℝ}
    (hf : StrongConvexOn Q μ f) (hμ : 0 < μ)
    (hf_cont : ContinuousOn f Q)
    (hQ_nonempty : Q.Nonempty) (hQ_closed : IsClosed Q) :
    ∃! x : E, x ∈ Q ∧ IsMinOn f Q x := by
  exact hf.existsUnique_isMinOn_of_isClosed_lowerSemicontinuousOn hμ
    hf_cont.lowerSemicontinuousOn hQ_nonempty hQ_closed

end Existence

section Uniqueness

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A positive strongly convex real-valued objective on a feasible set has at most one feasible
minimizer. -/
theorem eq_of_isMinOn
    {Q : Set E} {μ : ℝ} {f : E → ℝ} (hf : StrongConvexOn Q μ f) (hμ : 0 < μ)
    {xStar₁ xStar₂ : E}
    (hxStar₁ : xStar₁ ∈ Q) (hmin₁ : IsMinOn f Q xStar₁)
    (hxStar₂ : xStar₂ ∈ Q) (hmin₂ : IsMinOn f Q xStar₂) :
    xStar₁ = xStar₂ :=
  (hf.strictConvexOn hμ).eq_of_isMinOn hmin₁ hmin₂ hxStar₁ hxStar₂

end Uniqueness

end StrongConvexOn

end
