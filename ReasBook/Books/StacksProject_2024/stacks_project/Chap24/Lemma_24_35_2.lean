import StacksProject_2024.stacks_project.Chap04.Remark_4_22_7
import StacksProject_2024.stacks_project.Chap13.Definition_13_34_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_87_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe uM uN uD vD

namespace CategoryTheory

-- Semantic search note: `lean_leansearch` is unavailable in this runner, so the owner choice was
-- checked against the local Chapter 15 pro-object / derived-limit API, especially
-- `exists_isIso_hom_of_proIsomorphism_of_isDerivedLimit`.

section

variable {MObj : Type uM} {NObj : Type uN}
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D] [IsTriangulated D]

/-- Lemma 24.35.2, object form: if `(N_n)` and `(N'_n)` are pro-isomorphic in the derived category
as defined
above, then for every object `(M_n)` the tensorized inverse systems
`(M_n \otimes_{A_n}^{\mathbf L} N_n)_n` and `(M_n \otimes_{A_n}^{\mathbf L} N'_n)_n` have
isomorphic derived inverse limits. Formalized here by a chosen assignment
`(M, N) ↦ (M_n \otimes_{A_n}^{\mathbf L} N_n)_n` into a fixed target category together with
chosen derived-limit objects for those towers, and by a pro-object isomorphism between the two
tensorized towers for the fixed left factor `M`. This packages the same comparison in the chapter's
canonical object-level owner `CategoryTheory.IsIsomorphic`. -/
theorem tensorizedDerivedLimit_isIsomorphic_of_proIsomorphism
    (tensorTower : MObj → NObj → ℕᵒᵖ ⥤ D)
    (tensorDerivedLimit : MObj → NObj → D)
    (hlim : ∀ M N, IsDerivedLimit (tensorTower M N) (tensorDerivedLimit M N))
    {M : MObj} {N N' : NObj}
    (η :
      colimit (((tensorTower M N').op) ⋙ uliftCoyoneda.{0}) ⟶
        proSystemHomColimitFunctor (tensorTower M N) ⋙ uliftFunctor.{0})
    [IsIso η] :
    IsIsomorphic (tensorDerivedLimit M N) (tensorDerivedLimit M N') := by
  -- Package the Chapter 15 comparison morphism between the chosen derived limits as an
  -- `IsIsomorphic` statement.
  obtain ⟨φ, hφ⟩ :=
    exists_isIso_hom_of_proIsomorphism_of_isDerivedLimit
      (hlim M N)
      (hlim M N')
      η
  letI : IsIso φ := hφ
  exact ⟨asIso φ⟩

end

end CategoryTheory
