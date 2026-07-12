import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

-- Semantic search hit: the canonical mathlib surface for an evaluation map produced from a tensor /
-- internal-Hom pairing is `Adjunction.homEquiv`; nearby Section 22.13 files use the same
-- adjunction-level fallback because the checked DG internal-Hom owner is not yet available here.

section

universe u v

variable {DGModA : Type u} {CompR : Type v}
variable [Category DGModA] [Category CompR]
variable (tensorWithHom : DGModA ⥤ CompR) (homIntoN : CompR ⥤ DGModA)
variable (adj : tensorWithHom ⊣ homIntoN)
variable (M : DGModA) (N : CompR)
variable (signedEvaluationPairing : tensorWithHom.obj M ⟶ N)

/-
Remark 22.13.6 is source-facing at the tensor-Hom adjunction layer. The current repository has no
checked DG owner for the right DG evaluation morphism, so the canonical core owner remains
`Adjunction.homEquiv`; this remark names the source-facing transpose of the signed evaluation
pairing.
-/
recall Adjunction.homEquiv

/-- Remark 22.13.6: once the differential graded internal-Hom owner
`N^• ↦ Hom(Hom(M, N^•), N^•)` and the corresponding tensor/internal-Hom adjunction are available,
the evaluation morphism
`M ⟶ Hom(Hom(M, N^•), N^•)` in right differential graded `A`-modules is the adjunction transpose
of the source signed pairing `M ⊗_A Hom(M, N^•) ⟶ N^•`, intended in the source to be
`(x, f) ↦ (-1)^(deg(x) * deg(f)) f(x)`. -/
@[stacks 0FQ8]
noncomputable abbrev dgRightEvaluationMap :
    M ⟶ homIntoN.obj N :=
  adj.homEquiv M N signedEvaluationPairing

/-- `dgRightEvaluationMap` is exactly the canonical adjunction transpose of the signed
evaluation pairing. -/
theorem dgRightEvaluationMap_eq_homEquiv :
    dgRightEvaluationMap tensorWithHom homIntoN adj M N signedEvaluationPairing =
      adj.homEquiv M N signedEvaluationPairing :=
  rfl

/-- The adjunction inverse sends `dgRightEvaluationMap` back to the signed evaluation pairing. -/
theorem dgRightEvaluationMap_symm_apply :
    (adj.homEquiv M N).symm
        (dgRightEvaluationMap tensorWithHom homIntoN adj M N signedEvaluationPairing) =
      signedEvaluationPairing := by
  simpa [dgRightEvaluationMap_eq_homEquiv] using (adj.homEquiv M N).left_inv signedEvaluationPairing

end
