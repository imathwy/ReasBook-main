import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap27.Example_27_11
import BauschkeLean.Chap27.LaxMilgramQuadraticObjective

open ERealFunction

universe u

noncomputable section

-- `IsCoercive F` is the canonical owner for the source coercivity witness
-- `∃ α > 0, ∀ x, α * ‖x‖^2 ≤ F x x`, while `F : H →L[ℝ] H →L[ℝ] ℝ` already packages the
-- source boundedness of the bilinear form.

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

section

variable [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for Example 27.12: on `Set.univ`, the Stampacchia variational inequality is exactly
the functional identity `F xbar = ℓ`. -/
lemma solvesStampacchiaVariationalInequality_univ_iff_eq_continuousLinearMap
    (F : H →L[ℝ] H →L[ℝ] ℝ) (ℓ : H →L[ℝ] ℝ) (xbar : H) :
    SolvesStampacchiaVariationalInequality F ℓ Set.univ xbar ↔ F xbar = ℓ := by
  constructor
  · intro hxbar
    -- Evaluate the full-space variational inequality at `xbar + y` and `xbar - y`.
    ext y
    have hplus : F xbar y ≥ ℓ y := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        hxbar.2 (xbar + y) (by simp)
    have hminus : F xbar (-y) ≥ ℓ (-y) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        hxbar.2 (xbar - y) (by simp)
    have hle : F xbar y ≤ ℓ y := by
      -- Rewrite the test at `xbar - y` through linearity in the second argument.
      have hminus' : -F xbar y ≥ -ℓ y := by
        simpa using hminus
      linarith
    exact le_antisymm hle hplus
  · intro hxbar
    refine ⟨by simp, ?_⟩
    intro y hy
    -- The unconstrained gap vanishes once `F xbar` and `ℓ` are the same functional.
    simp [hxbar]

/-- Example 27.12 (1): if `F` is a bounded coercive bilinear form on a real Hilbert space `H`,
then every continuous linear functional `ℓ` on `H` is represented by a unique point `xbar`
through the identity `F xbar = ℓ`. Here boundedness is already part of the ambient owner
`F : H →L[ℝ] H →L[ℝ] ℝ`, and `IsCoercive F` packages the source coercivity witness. -/
theorem existsUnique_eq_continuousLinearMap_of_bounded_coercive_bilinear
    (F : H →L[ℝ] H →L[ℝ] ℝ) (hF_coercive : IsCoercive F) (ℓ : H →L[ℝ] ℝ) :
    ∃! xbar : H, F xbar = ℓ := by
  -- Transport Example 27.11 from the unconstrained set `Set.univ`.
  rcases
      existsUnique_solution_stampacchiaVariationalInequality_of_nonempty_isClosed_convex
        (C := Set.univ) Set.univ_nonempty isClosed_univ convex_univ F hF_coercive ℓ with
    ⟨xbar, hxbar, hxbar_unique⟩
  refine ⟨xbar, ?_, ?_⟩
  · exact
      (solvesStampacchiaVariationalInequality_univ_iff_eq_continuousLinearMap F ℓ xbar).mp hxbar
  · intro x hx
    apply hxbar_unique x
    exact
      (solvesStampacchiaVariationalInequality_univ_iff_eq_continuousLinearMap F ℓ x).mpr hx

/-- Companion to Example 27.12 (1): the source pointwise equation `F(xbar, y) = ℓ(y)` for all
`y` is exactly the extensional form of the canonical functional identity `F xbar = ℓ`. -/
theorem existsUnique_forall_eq_of_bounded_coercive_bilinear
    (F : H →L[ℝ] H →L[ℝ] ℝ) (hF_coercive : IsCoercive F) (ℓ : H →L[ℝ] ℝ) :
    ∃! xbar : H, ∀ y : H, F xbar y = ℓ y := by
  rcases existsUnique_eq_continuousLinearMap_of_bounded_coercive_bilinear F hF_coercive ℓ with
    ⟨xbar, hxbar, hxbar_unique⟩
  refine ⟨xbar, fun y ↦ by simp [hxbar], ?_⟩
  intro x hx
  apply hxbar_unique x
  ext y
  exact hx y

end

/-- Example 27.12 (2): under the coercive boundedness assumptions of clause `(1)`, if `F` is
symmetric and `f(x) = (1 / 2) F(x, x) - ℓ(x)`, then `F xbar = ℓ` if and only if `xbar` is the
unique minimizer of `f`. The boundedness clause remains ambient through
`F : H →L[ℝ] H →L[ℝ] ℝ`, the symmetry clause is packaged canonically by
`F.toBilinForm.IsSymm`, and the pointwise equivalence itself does not use completeness. -/
theorem eq_continuousLinearMap_iff_argmin_eq_singleton_of_symmetric
    (F : H →L[ℝ] H →L[ℝ] ℝ) (hF_coercive : IsCoercive F)
    (hF_symm : F.toBilinForm.IsSymm) (ℓ : H →L[ℝ] ℝ) {xbar : H} :
    F xbar = ℓ ↔
      Argmin (laxMilgramQuadraticObjective F ℓ).toEReal.asEReal =
        {xbar} := by
  have hF_symm' : ∀ x y : H, F x y = F y x := fun x y ↦ by
    simpa using hF_symm.eq x y
  -- Reuse the constrained argmin characterization on `Set.univ` and rewrite the VI side.
  rw [← solvesStampacchiaVariationalInequality_univ_iff_eq_continuousLinearMap F ℓ xbar]
  simpa using
    (solves_stampacchiaVariationalInequality_iff_argminOn_eq_singleton_of_symmetric
      (C := Set.univ) convex_univ F hF_coercive ℓ hF_symm' (xbar := xbar))

/-- Companion to Example 27.12 (2): the source pointwise Euler-Lagrange equation is equivalent to
the canonical functional equality used by the main theorem, so the argmin characterization can be
read in the textbook pointwise form without invoking extensionality explicitly downstream. -/
theorem forall_eq_iff_argmin_eq_singleton_of_symmetric
    (F : H →L[ℝ] H →L[ℝ] ℝ) (hF_coercive : IsCoercive F)
    (hF_symm : F.toBilinForm.IsSymm) (ℓ : H →L[ℝ] ℝ) {xbar : H} :
    (∀ y : H, F xbar y = ℓ y) ↔
      Argmin (laxMilgramQuadraticObjective F ℓ).toEReal.asEReal = {xbar} := by
  rw [← eq_continuousLinearMap_iff_argmin_eq_singleton_of_symmetric F hF_coercive hF_symm ℓ]
  constructor
  · intro h
    ext y
    exact h y
  · intro h y
    simp [h]
