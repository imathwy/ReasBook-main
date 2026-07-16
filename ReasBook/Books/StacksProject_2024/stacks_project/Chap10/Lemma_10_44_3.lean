import StacksProject_2024.stacks_project.Chap10.Definition_10_42_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_158_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- Lemma 10.44.3 (Tag 030X): a separably generated field extension is separable in the sense of
Definition `10.42.1 (2)`, namely every finitely generated intermediate extension is again
separably generated. -/
@[stacks 030X]
theorem Lemma_10_44_3 (hK : IsSeparablyGenerated k K) :
    IsSeparableOver k K := by
  rcases hK with ⟨s, hs, hsep⟩
  have hs_range : Set.range ((↑) : s → K) = s := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hsep' : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range ((↑) : s → K))) K := by
    rw [hs_range]
    exact hsep
  letI : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range ((↑) : s → K))) K := hsep'
  letI : Algebra.FormallySmooth k K :=
    Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1
  exact Algebra.isSeparableOver_of_formallySmooth

/-- Low-priority fallback instance supplied by Lemma `10.44.3`. -/
@[instance low] instance [IsSeparablyGenerated k K] : IsSeparableOver k K :=
  Lemma_10_44_3 ‹_›

end

end Algebra
