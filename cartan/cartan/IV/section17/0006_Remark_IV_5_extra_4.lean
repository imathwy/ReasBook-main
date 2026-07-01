import Mathlib
import cartan.IV.section17.«0002_Theorem_IV_5_extra_2»

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: the chapter owner for the separate-holomorphy hypothesis is already the
-- explicit coordinate-slice `AnalyticAt` assumption used in
-- `IV/section17/0002_Theorem_IV_5_extra_2.lean`, while the target conclusion is the canonical
-- mathlib owner `AnalyticOnNhd ℂ`; this file is the downstream bridge where continuity becomes
-- automatic on open sets, so the analytic corollary is now direct recall of the upstream theorem.

section

variable {n : ℕ}
variable {D : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → ℂ}

/-- Remark IV.5-extra-4 (1): on an open set `D ⊆ ℂ^n`, a function whose coordinate slices are
holomorphic at every point of `D` is continuous on `D`. -/
theorem continuousOn_of_separately_holomorphic (hD : IsOpen D)
    (hsep : ∀ z ∈ D, ∀ i : Fin n, AnalyticAt ℂ (fun w : ℂ ↦ f (Function.update z i w)) (z i)) :
    ContinuousOn f D := by
  -- The separate holomorphy hypothesis first upgrades `f` to analyticity on a neighborhood of `D`.
  have hanalytic : AnalyticOnNhd ℂ f D := separately_holomorphic_analyticOnNhd hD hsep
  -- Continuity on `D` is the canonical consequence of analyticity on a neighborhood of `D`.
  simpa using hanalytic.continuousOn

/- Remark IV.5-extra-4 (2): on an open set `D ⊆ ℂ^n`, a function whose coordinate slices are
holomorphic at every point of `D` is analytic on `D`. This is already
`separately_holomorphic_analyticOnNhd`. -/
recall separately_holomorphic_analyticOnNhd

end
