import Mathlib
import stacks_project.Chap15.Definition_15_28_2
import stacks_project.Chap15.Lemma_15_28_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open ModuleCat
open Module
open scoped Matrix
open scoped KoszulComplex

section

variable {R : Type u} [CommRing R]

private theorem koszulLinearForm_matrix_transpose_toLin' {r : ℕ}
    (x : Matrix (Fin r) (Fin r) R) (f : Fin r → R) :
    koszulLinearForm (x.toLin' f) = (koszulLinearForm f).comp (xᵀ).toLin' := sorry

private theorem koszulLinearForm_matrix_transpose_toLin'_comp_inv {r : ℕ}
    (x : Matrix (Fin r) (Fin r) R) [Invertible x] (f : Fin r → R) :
    (koszulLinearForm (x.toLin' f)).comp (⅟ (xᵀ)).toLin' = koszulLinearForm f := sorry

/-- Lemma 15.28.4: an invertible linear change of generators
`g i = ∑ j, x i j * f j` induces an isomorphism between the Koszul complex on `f` and the Koszul
complex on the transformed family `g`. -/
noncomputable def koszul_complex_on_matrix_linear_combination_iso {r : ℕ}
    (x : Matrix (Fin r) (Fin r) R) [Invertible x] (f : Fin r → R) :
    K^•(f) ≅ K^•(x.toLin' f) where
  hom :=
    KoszulComplex.map (⅟ (xᵀ)).toLin' (koszulLinearForm_matrix_transpose_toLin'_comp_inv x f)
  inv :=
    KoszulComplex.map (xᵀ).toLin' (koszulLinearForm_matrix_transpose_toLin' x f).symm
  hom_inv_id := by
    sorry
  inv_hom_id := by
    sorry

/-- The degree `n` component of the forward map in
`koszul_complex_on_matrix_linear_combination_iso x f` is induced by the inverse transpose of
`x`. -/
theorem koszul_complex_on_matrix_linear_combination_iso_hom_f {r : ℕ}
    (x : Matrix (Fin r) (Fin r) R) [Invertible x] (f : Fin r → R) (n : ℕ) :
    (koszul_complex_on_matrix_linear_combination_iso x f).hom.f n =
      ModuleCat.exteriorPower.map (ofHom (⅟ (xᵀ)).toLin') n := by
  simp [koszul_complex_on_matrix_linear_combination_iso]

end
