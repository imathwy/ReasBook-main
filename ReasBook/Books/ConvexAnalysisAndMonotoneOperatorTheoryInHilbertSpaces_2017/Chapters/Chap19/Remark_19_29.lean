import BauschkeLean.Chap19.Example_19_28

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Set

namespace ERealFunction

section

variable (φ : ℝ → Set.Ioi (⊥ : EReal))

/- Source/core/bridge triage:
- `source-facing`: Remark 19.29 records that Example 19.28 may still have primal and dual
  minimizers while failing both strong duality and saddle-point existence when
  `phiRangeInfimum φ < φ 0`.
- `core/canonical`: the owner declarations are the Example 19.28 formulas for the primal and dual
  argmin sets, the primal and dual infima, and the saddle-point criterion.
- `bridge/view`: this file should therefore only expose the three downstream consequences obtained
  by rewriting through those owner theorems, rather than introducing a parallel local attainment
  or duality API.

Primitive data: none.
Derived API: the primal and dual attainment facts are immediate consequences of the explicit
argmin descriptions already owned by Example 19.28, so this file keeps only a single bundled
source-facing attainment theorem together with the strict-inequality consequences.

Semantic recall: mathlib already exposes the saddle-point interface through
`isSaddlePointOn_iff` / `isSaddlePointOn_value`; this file only states the Example 19.28
specializations.
-/

-- Proof sketch: Example 19.28 (4) and (7) identify the primal and dual solution sets with
-- `Set.Ici (0 : ℝ) ×ˢ ({0} : Set ℝ)` and `Set.Ici (0 : ℝ)`, which are both nonempty.
/-- A companion consequence of Remark 19.29: the Lorentz-constraint perturbation of Example 19.28
has both primal and dual minimizers. -/
theorem argmin_perturbationObjectives_lorentzConstraintPerturbation_nonempty
    (hφ : φ ∈ Γ₀(ℝ)) (hφ0 : 0 ∈ effectiveDomain φ) :
    (Argmin
        (perturbationPrimalObjective (lorentzConstraintPerturbation φ))).Nonempty ∧
      (Argmin[Ici (0 : ℝ)]
        (perturbationDualObjective (lorentzConstraintPerturbation φ))).Nonempty := by
  -- Rewrite both argmin sets to the explicit solution sets computed in Example 19.28.
  rw [argmin_perturbationPrimalObjective_lorentzConstraintPerturbation (φ := φ) hφ hφ0]
  rw [argmin_perturbationDualObjective_lorentzConstraintPerturbation (φ := φ) hφ hφ0]
  -- The origin witnesses both the primal and dual nonemptiness claims.
  constructor
  · exact ⟨(0, 0), by simp⟩
  · exact ⟨0, by simp⟩

/-- Helper for Remark 19.29: a strict inequality `phiRangeInfimum φ < φ 0` rules out the equality
`(φ 0 : EReal) = phiRangeInfimum φ`. -/
lemma phiZero_ne_phiRangeInfimum_of_phiRangeInfimum_lt
    (hγ : phiRangeInfimum φ < (φ 0 : EReal)) :
    (φ 0 : EReal) ≠ phiRangeInfimum φ := by
  -- A strict inequality cannot persist after identifying its two endpoints.
  intro hEq
  rw [hEq] at hγ
  exact lt_irrefl _ hγ

-- Proof sketch: Example 19.28 (9) characterizes existence of a saddle point by the equality
-- `phiRangeInfimum φ = (φ 0 : EReal)`. A strict inequality between these two values therefore
-- excludes saddle points.
/-- Remark 19.29 (2): in the setting of Example 19.28, if `γ < φ(0)` then the Lagrangian of the
Lorentz-constraint perturbation has no saddle point. -/
theorem not_exists_saddlePoint_lorentzConstraintPerturbation_of_phiRangeInfimum_lt
    (hφ : φ ∈ Γ₀(ℝ)) (hφ0 : 0 ∈ effectiveDomain φ)
    (hγ : phiRangeInfimum φ < (φ 0 : EReal)) :
    ¬ ∃ ξ : ℝ × ℝ, ∃ v : ℝ,
      IsSaddlePointOn (univ : Set (ℝ × ℝ)) (univ : Set ℝ)
        (ℒ[lorentzConstraintPerturbation φ]) ξ v := by
  -- Transport saddle-point existence to the scalar criterion from Example 19.28.
  intro hsaddle
  have hEq :
      (φ 0 : EReal) = phiRangeInfimum φ :=
    (exists_saddlePoint_lorentzConstraintPerturbation_iff (φ := φ) hφ hφ0).mp hsaddle
  -- The strict inequality forbids that equality.
  exact phiZero_ne_phiRangeInfimum_of_phiRangeInfimum_lt (φ := φ) hγ hEq

-- Proof sketch: Example 19.28 (3) and (6) identify the primal and dual optimal values with
-- `(φ 0 : EReal)` and `-phiRangeInfimum φ`, so equality of the optimal values up to sign would
-- force `(φ 0 : EReal)` to equal that infimum, contradicting the strict inequality.
/-- Another consequence of Remark 19.29: a strict inequality `γ < φ(0)` forces failure of strong
duality for the Lorentz-constraint perturbation of Example 19.28. -/
theorem not_strongDuality_lorentzConstraintPerturbation_of_phiRangeInfimum_lt
    (hφ : φ ∈ Γ₀(ℝ)) (hφ0 : 0 ∈ effectiveDomain φ)
    (hγ : phiRangeInfimum φ < (φ 0 : EReal)) :
    sInf (range <| perturbationPrimalObjective (lorentzConstraintPerturbation φ)) ≠
      -sInf (range <| perturbationDualObjective (lorentzConstraintPerturbation φ)) := by
  -- Rewrite the primal and dual optimal values to the closed forms from Example 19.28.
  rw [sInf_perturbationPrimalObjective_lorentzConstraintPerturbation (φ := φ) hφ hφ0]
  rw [sInf_perturbationDualObjective_lorentzConstraintPerturbation (φ := φ) hφ hφ0]
  -- The resulting equality would again force `(φ 0 : EReal) = phiRangeInfimum φ`.
  simpa using phiZero_ne_phiRangeInfimum_of_phiRangeInfimum_lt (φ := φ) hγ

end

end ERealFunction
