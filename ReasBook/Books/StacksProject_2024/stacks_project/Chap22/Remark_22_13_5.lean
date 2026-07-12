import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

section

universe u v

variable {DGLeft : Type u} {CompR : Type v}
variable [Category DGLeft] [Category CompR]
variable {tensorWithHom : DGLeft ⥤ CompR} {homIntoComplex : CompR ⥤ DGLeft}
variable (adj : tensorWithHom ⊣ homIntoComplex)
variable {M : DGLeft} {N : CompR}
variable (evaluationPairing : tensorWithHom.obj M ⟶ N)

/-
Remark 22.13.5 is source-facing at the tensor-Hom adjunction layer. The current repository has no
checked DG owner for the left DG evaluation morphism, so the canonical core owner remains
`Adjunction.homEquiv`; this remark names the source-facing transpose of the evaluation pairing.
-/
recall Adjunction.homEquiv

/-- Remark 22.13.5: once the constructions above have produced the right differential graded
`A`-module `Hom(M, N^•)` and then the left differential graded `A`-module
`Hom(Hom(M, N^•), N^•)`, the evaluation morphism
`M ⟶ Hom(Hom(M, N^•), N^•)` in left differential graded `A`-modules is the adjunction transpose
of the evaluation pairing `Hom(M, N^•) ⊗_A M ⟶ N^•`, `(f, x) ↦ f(x)`. -/
@[stacks 0FQ7]
noncomputable abbrev dgLeftEvaluationMap :
    M ⟶ homIntoComplex.obj N :=
  adj.homEquiv M N evaluationPairing

/-- `dgLeftEvaluationMap` is exactly the specialized canonical adjunction transpose of the
evaluation pairing. -/
theorem dgLeftEvaluationMap_eq_homEquiv :
    dgLeftEvaluationMap adj evaluationPairing =
      adj.homEquiv M N evaluationPairing :=
  rfl

/-- The adjunction inverse sends `dgLeftEvaluationMap` back to the evaluation pairing
`(f, x) ↦ f(x)`. -/
theorem dgLeftEvaluationMap_symm_apply :
    (adj.homEquiv M N).symm
        (dgLeftEvaluationMap adj evaluationPairing) =
      evaluationPairing :=
  by
    simpa [dgLeftEvaluationMap_eq_homEquiv] using (adj.homEquiv M N).left_inv evaluationPairing

end
