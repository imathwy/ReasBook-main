import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Basic
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_12
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_11
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14

noncomputable section

universe u v

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: this file records the verified owner-level part of Corollary 6.30.4 at a fixed
  pair `(xBar, uStarBar)`: zero-duality-gap with primal/dual attainment is equivalent to
  objective-value equality, and hence to the objective inequality under weak duality.
- `core/canonical`: the chapter owners are `perturbationFunction`, `upperPerturbationFunction`,
  `objective`, and `adjoint`.
- `bridge/view`: the public surface stays on those owners and avoids introducing a parallel
  wrapper.

Note on scope:
- the previous local statement included an explicit saddle-point clause but did not provide a
  proved bridge at this abstraction layer; this version keeps the proved owner-level equivalence.
-/

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {UStar : Type*} {XStar : Type*}
variable [AddGroup 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [Zero U]
variable [Neg UStar] [Zero XStar]
variable [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]

variable (F : U → X → WithBotTop 𝕜)

local notation "p" => perturbationFunction F
local notation "fStar" => ((adjoint XStar UStar F) : XStar → UStar → WithBotTop 𝕜)
local notation "q" => upperPerturbationFunction fStar
local notation "f₀" => (F)₀
local notation "f⋆₀" => ((fStar)₀ : UStar → WithBotTop 𝕜)

omit [AddGroup 𝕜] in
private theorem perturbationFunction_zero_eq_of_isMinOn
    {xBar : X} (hmin : IsMinOn f₀ Set.univ xBar) :
    p 0 = f₀ xBar := by
  have hmin' : ∀ x : X, f₀ xBar ≤ f₀ x := (isMinOn_univ_iff.mp hmin)
  refine le_antisymm ?_ ?_
  · simpa [perturbationFunction_apply] using (iInf_le (fun x : X ↦ f₀ x) xBar)
  · simpa [perturbationFunction_apply] using (le_iInf hmin')

omit [Zero U] in
private theorem upperPerturbationFunction_zero_eq_of_isMaxOn
    {uStarBar : UStar} (hmax : IsMaxOn f⋆₀ Set.univ uStarBar) :
    q 0 = f⋆₀ uStarBar := by
  have hmax' : ∀ uStar : UStar, f⋆₀ uStar ≤ f⋆₀ uStarBar := (isMaxOn_univ_iff.mp hmax)
  refine le_antisymm ?_ ?_
  · simpa [upperPerturbationFunction_apply] using (iSup_le hmax')
  · simpa [upperPerturbationFunction_apply] using
      (le_iSup (fun uStar : UStar ↦ f⋆₀ uStar) uStarBar)

/-- Corollary 6.30.4 owner-level form: for a fixed pair `(xBar, uStarBar)`, the conjunction
`p 0 = q 0` with primal/dual optimality is equivalent to objective equality. -/
theorem zeroDualityGap_primalDualOptimality_iff_objective_eq
    (hweak : ∀ x : X, ∀ uStar : UStar, f⋆₀ uStar ≤ f₀ x)
    (xBar : X) (uStarBar : UStar) :
    (p 0 = q 0 ∧ IsMinOn f₀ Set.univ xBar ∧ IsMaxOn f⋆₀ Set.univ uStarBar) ↔
      f₀ xBar = f⋆₀ uStarBar := by
  constructor
  · rintro ⟨hgap, hmin, hmax⟩
    have hp0 : p 0 = f₀ xBar := perturbationFunction_zero_eq_of_isMinOn (F := F) hmin
    have hq0 : q 0 = f⋆₀ uStarBar := upperPerturbationFunction_zero_eq_of_isMaxOn (F := F) hmax
    calc
      f₀ xBar = p 0 := hp0.symm
      _ = q 0 := hgap
      _ = f⋆₀ uStarBar := hq0
  · intro heq
    have hmin : IsMinOn f₀ Set.univ xBar := by
      rw [isMinOn_univ_iff]
      intro x
      calc
        f₀ xBar = f⋆₀ uStarBar := heq
        _ ≤ f₀ x := hweak x uStarBar
    have hmax : IsMaxOn f⋆₀ Set.univ uStarBar := by
      rw [isMaxOn_univ_iff]
      intro uStar
      calc
        f⋆₀ uStar ≤ f₀ xBar := hweak xBar uStar
        _ = f⋆₀ uStarBar := heq
    have hp0 : p 0 = f₀ xBar := perturbationFunction_zero_eq_of_isMinOn (F := F) hmin
    have hq0 : q 0 = f⋆₀ uStarBar := upperPerturbationFunction_zero_eq_of_isMaxOn (F := F) hmax
    refine ⟨?_, hmin, hmax⟩
    calc
      p 0 = f₀ xBar := hp0
      _ = f⋆₀ uStarBar := heq
      _ = q 0 := hq0.symm

/-- Under weak duality at `(xBar, uStarBar)`, objective equality is equivalent to objective
inequality. -/
theorem objective_eq_iff_objective_le_of_weakDuality
    (hweak : ∀ x : X, ∀ uStar : UStar, f⋆₀ uStar ≤ f₀ x)
    (xBar : X) (uStarBar : UStar) :
    f₀ xBar = f⋆₀ uStarBar ↔
      f₀ xBar ≤ f⋆₀ uStarBar := by
  constructor
  · intro heq
    exact le_of_eq heq
  · intro hle
    exact le_antisymm hle (hweak xBar uStarBar)

/-- Corollary 6.30.4 owner-level form: for a fixed pair `(xBar, uStarBar)`, the conjunction
`p 0 = q 0` with primal/dual optimality, objective equality, and objective inequality are
equivalent under weak duality. -/
theorem zeroDualityGap_primalDualOptimality_objective_eq_objective_le_tfae
    (hweak : ∀ x : X, ∀ uStar : UStar, f⋆₀ uStar ≤ f₀ x)
    (xBar : X) (uStarBar : UStar) :
    List.TFAE
      [p 0 = q 0 ∧ IsMinOn f₀ Set.univ xBar ∧ IsMaxOn f⋆₀ Set.univ uStarBar,
        f₀ xBar = f⋆₀ uStarBar,
        f₀ xBar ≤ f⋆₀ uStarBar] := by
  tfae_have 1 ↔ 2 := by
    exact zeroDualityGap_primalDualOptimality_iff_objective_eq
      (F := F) hweak xBar uStarBar
  tfae_have 2 ↔ 3 := by
    exact objective_eq_iff_objective_le_of_weakDuality
      (F := F) hweak xBar uStarBar
  tfae_finish

/-- Under weak duality, objective inequality at a pair implies objective equality at that pair. -/
theorem objective_eq_of_objective_le_of_weakDuality
    (hweak : ∀ x : X, ∀ uStar : UStar, f⋆₀ uStar ≤ f₀ x)
    (xBar : X) (uStarBar : UStar)
    (hle : f₀ xBar ≤ f⋆₀ uStarBar) :
    f₀ xBar = f⋆₀ uStarBar :=
  (objective_eq_iff_objective_le_of_weakDuality (F := F) hweak xBar uStarBar).2 hle

end

end Bifunction
