import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_48_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

section

variable {X S : Scheme.{u}}

/-- Lemma 29.48.5: if `f : X ⟶ S` is finite locally free, then `S` admits a decomposition into
pairwise disjoint open and closed subschemes `S_d` indexed by `d : ℕ` whose union is all of `S`,
and such that the restricted morphism `f|_{X_d} : X_d → S_d` has degree `d`, where
`X_d = f⁻¹(S_d)` and `f|_{X_d}` is represented by `f ∣_ (S_d)`. -/
@[stacks 04MH]
theorem exists_clopen_degree_decomposition_of_isFiniteLocallyFree
    (f : X ⟶ S) [IsFiniteLocallyFree f] :
    ∃ Sdegree : ℕ → S.Opens,
      iSup Sdegree = ⊤ ∧
        Pairwise (fun d e ↦ Disjoint (Sdegree d : Set S) (Sdegree e : Set S)) ∧
        (∀ d, IsClopen (Sdegree d : Set S)) ∧
        ∀ d, IsFiniteLocallyFreeOfRank (f ∣_ (Sdegree d)) d := sorry

end

end AlgebraicGeometry
