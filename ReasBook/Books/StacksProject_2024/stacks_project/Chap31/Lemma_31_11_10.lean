import Mathlib
import StacksProject_2024.Chap17.Definition_17_5_1
import StacksProject_2024.Chap30.Lemma_30_9_1
import StacksProject_2024.Chap30.Definition_30_11_1
import StacksProject_2024.Chap31.Definition_31_2_1
import StacksProject_2024.Chap31.Lemma_31_2_3
import StacksProject_2024.Chap31.Definition_31_11_2
import StacksProject_2024.Chap31.Lemma_31_4_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced the canonical algebraic owners
-- `Module.IsTorsionFree` and `Module.support_of_noZeroSMulDivisors`; local Chapter 17, 30, and 31
-- precedent fixes the scheme-module translation here to `moduleSupport`, `associatedPoints`,
-- `embeddedAssociatedPoints`, `satisfiesSerreConditionS`, and `Scheme.Modules.IsTorsionFree`.

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable (ℱ : X.Modules) [ℱ.IsCoherent]

/-- Lemma 31.11.10 (1): let `X` be a locally Noetherian integral scheme with generic point `η`,
and let `ℱ` be a nonzero coherent `\mathcal O_X`-module. Then `ℱ` is torsion free if and only if
the generic point `η` is the only associated point of `ℱ`. -/
@[stacks 0AXY]
theorem isTorsionFree_iff_associatedPoints_eq_singleton_genericPoint
    (η : X) (hη : IsGenericPoint η (Set.univ : Set X)) (hℱ : ¬ IsZero ℱ) :
    IsTorsionFree ℱ ↔ associatedPoints ℱ = ({η} : Set X) := sorry

/-- On a locally Noetherian integral scheme, saying that the generic point is the only associated
point is equivalent to saying that it lies in the support and there are no embedded associated
points. -/
theorem associatedPoints_eq_singleton_genericPoint_iff_genericPoint_mem_support_and_embeddedAssociatedPoints_eq_empty
    (η : X) (hη : IsGenericPoint η (Set.univ : Set X)) :
    associatedPoints ℱ = ({η} : Set X) ↔
      η ∈ moduleSupport ℱ ∧ embeddedAssociatedPoints ℱ = (∅ : Set X) := by
  constructor
  · intro hAssoc
    refine ⟨mem_moduleSupport_of_mem_associatedPoints ℱ η ?_, ?_⟩
    · simpa [hAssoc]
    · rw [embeddedAssociatedPoints_eq_empty_iff]
      intro x hx
      rcases hx.exists_specializing_associated with ⟨y, hy, hyne, _⟩
      have hxeq : x = η := by
        simpa [hAssoc] using hx.mem_associatedPoints
      have hyeq : y = η := by
        simpa [hAssoc] using hy
      exact hyne (hyeq.trans hxeq.symm)
  · sorry

/-- Lemma 31.11.10 (2): let `X` be a locally Noetherian integral scheme with generic point `η`,
and let `ℱ` be a nonzero coherent `\mathcal O_X`-module. Then `ℱ` is torsion free if and only if
`η` lies in the support of `ℱ` and `ℱ` satisfies Serre's condition `(S_1)`. -/
@[stacks 0AXY]
theorem isTorsionFree_iff_genericPoint_mem_support_and_satisfiesSerreConditionS_one
    (η : X) (hη : IsGenericPoint η (Set.univ : Set X)) (hℱ : ¬ IsZero ℱ) :
    IsTorsionFree ℱ ↔ η ∈ moduleSupport ℱ ∧ satisfiesSerreConditionS ℱ 1 := by
  rw [isTorsionFree_iff_associatedPoints_eq_singleton_genericPoint ℱ η hη hℱ,
    associatedPoints_eq_singleton_genericPoint_iff_genericPoint_mem_support_and_embeddedAssociatedPoints_eq_empty
      ℱ η hη,
    embeddedAssociatedPoints_eq_empty_iff_satisfiesSerreConditionS_one]

/-- Lemma 31.11.10 (3): let `X` be a locally Noetherian integral scheme with generic point `η`,
and let `ℱ` be a nonzero coherent `\mathcal O_X`-module. Then `ℱ` is torsion free if and only if
`η` lies in the support of `ℱ` and `ℱ` has no embedded associated point. -/
@[stacks 0AXY]
theorem isTorsionFree_iff_genericPoint_mem_support_and_embeddedAssociatedPoints_eq_empty
    (η : X) (hη : IsGenericPoint η (Set.univ : Set X)) (hℱ : ¬ IsZero ℱ) :
    IsTorsionFree ℱ ↔ η ∈ moduleSupport ℱ ∧ embeddedAssociatedPoints ℱ = (∅ : Set X) :=
  by
    rw [isTorsionFree_iff_genericPoint_mem_support_and_satisfiesSerreConditionS_one ℱ η hη hℱ,
      embeddedAssociatedPoints_eq_empty_iff_satisfiesSerreConditionS_one]

end AlgebraicGeometry.Scheme.Modules
