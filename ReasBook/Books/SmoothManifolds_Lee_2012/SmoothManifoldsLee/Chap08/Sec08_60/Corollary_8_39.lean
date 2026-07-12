import SmoothManifolds_Lee_2012.Chap08.Sec08_60.Definition_8_60_extra_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

noncomputable section

universe u𝕜 uH uE uG

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {H : Type uH} [TopologicalSpace H]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type uG} [TopologicalSpace G] [ChartedSpace H G] [Group G]
variable [IsManifold I ∞ G]
variable [LieGroup I ∞ G]

-- Semantic search note: `lean_leansearch` was unavailable in this environment, so the statement
-- shape was checked directly against mathlib's `GroupLieAlgebra` API together with the chapter's
-- `IsLocalFrameOn ... Set.univ` owner and `vᴸ` notation for left-invariant vector fields.

namespace Module.Basis

/-- Corollary 8.39 (1): Every basis for the Lie algebra of a Lie group determines a left-invariant
smooth global frame on the group. -/
theorem isLeftInvariantFrameOn_mulInvariantVectorField {ι : Type uE}
    (b : Module.Basis ι 𝕜 (GroupLieAlgebra I G)) :
    IsLeftInvariantFrameOn (fun i ↦ (b i)ᴸ) Set.univ := by
  refine ⟨?_, ?_⟩
  · sorry
  intro i
  sorry

end Module.Basis

/-- Corollary 8.39 (2): Every Lie group is parallelizable. -/
theorem lie_group_is_parallelizable : parallelizable I G :=
  (Module.Basis.isLeftInvariantFrameOn_mulInvariantVectorField
    (Module.Basis.ofVectorSpace 𝕜 (GroupLieAlgebra I G))).parallelizable
