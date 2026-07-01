import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Theorem 4: on an open set `D ⊆ ℂ`, a continuous function whose differential form
`f(z) dz` is closed is holomorphic on `D`. -/
-- Proof sketch: apply
-- `Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn` to the open set `D`
-- and take the forward implication.
theorem differentiableOn_of_isConservativeOn_of_continuousOn
    {D : Set ℂ} {f : ℂ → ℂ} (hD : IsOpen D) (hf_cont : ContinuousOn f D)
    (hf_closed : Complex.IsConservativeOn f D) :
    DifferentiableOn ℂ f D :=
  (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hD).1
    ⟨hf_closed, hf_cont⟩

/-- A continuous conservative complex function on an open set is holomorphic at each point of
that set. -/
-- Proof sketch: first obtain `DifferentiableOn ℂ f D` from
-- `differentiableOn_of_isConservativeOn_of_continuousOn`, then use openness of `D` to pass
-- from `DifferentiableWithinAt` to `DifferentiableAt`.
theorem differentiableAt_of_isConservativeOn_of_continuousOn
    {D : Set ℂ} {f : ℂ → ℂ} (hD : IsOpen D) (hf_cont : ContinuousOn f D)
    (hf_closed : Complex.IsConservativeOn f D) :
    ∀ z ∈ D, DifferentiableAt ℂ f z := by
  intro z hz
  have hf_diff : DifferentiableWithinAt ℂ f D z :=
    differentiableOn_of_isConservativeOn_of_continuousOn hD hf_cont hf_closed z hz
  exact hf_diff.differentiableAt (hD.mem_nhds hz)
