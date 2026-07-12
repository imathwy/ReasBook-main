import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

section

universe u v

variable {DGModA : Type u} {CompR : Type v}
variable [Category DGModA] [Category CompR]
variable (tensorWithM : DGModA ⥤ CompR) (homFromM : CompR ⥤ DGModA)
variable (adj : tensorWithM ⊣ homFromM)
variable (M' : DGModA) (N : CompR)

/-
Lemma 22.13.2 is source-facing at the tensor-Hom adjunction layer. The current repository has no
checked DG owner for the relative tensor `M' ⊗_A M` or the internal Hom `Hom(M, N^•)`, so the
canonical core owner is `Adjunction.homEquiv`; the textbook displayed orientation is its symmetric
bridge/view.
-/
recall Adjunction.homEquiv

/--
Lemma 22.13.2: for a right differential graded `A`-module `M'`, a left differential graded
`A`-module `M`, and a complex `N^•`, once `homFromM` models `N^• ↦ Hom(M, N^•)` and `tensorWithM`
models `M' ↦ M' ⊗_A M`, the displayed identification
`Hom_{Mod_(A, d)}(M', Hom(M, N^•)) = Hom_{Comp(R)}(M' ⊗_A M, N^•)` is exactly the symmetric form
of the canonical adjunction equivalence.
-/
@[stacks 0FQ4]
noncomputable abbrev dgTensorHomEquiv :
    (M' ⟶ homFromM.obj N) ≃ (tensorWithM.obj M' ⟶ N) :=
  (adj.homEquiv M' N).symm

/-- Applying `dgTensorHomEquiv` is exactly the symmetric form of the adjunction
Hom-equivalence. -/
theorem dgTensorHomEquiv_apply (f : M' ⟶ homFromM.obj N) :
    dgTensorHomEquiv tensorWithM homFromM adj M' N f =
      (adj.homEquiv M' N).symm f :=
  rfl

/-- The inverse of `dgTensorHomEquiv` is the adjunction Hom-equivalence. -/
theorem dgTensorHomEquiv_symm_apply (f : tensorWithM.obj M' ⟶ N) :
    (dgTensorHomEquiv tensorWithM homFromM adj M' N).symm f =
      adj.homEquiv M' N f :=
  rfl

end
