import SmoothManifolds_Lee_2012.Chap02.Sec02_11.Proposition_2_25

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ContinuousMap

variable {M : Type u} [TopologicalSpace M]

/- Definition 2.11-extra-1: Proposition 2.25 expresses the bump-function conditions directly by
bounding the range in `[0, 1]`, requiring `EqOn ψ 1 A`, and requiring `tsupport ψ ⊆ U`. -/
#check Set.EqOn
#check tsupport

/-- The constant function `1` satisfies the bump-function conditions on the whole space. -/
theorem one_bumpConditions_univ :
    Set.range (1 : C(M, ℝ)) ⊆ Set.Icc (0 : ℝ) 1 ∧
      Set.EqOn (1 : C(M, ℝ)) 1 Set.univ ∧ tsupport (1 : C(M, ℝ)) ⊆ Set.univ := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    simp
  · simp
  · simp

end ContinuousMap
