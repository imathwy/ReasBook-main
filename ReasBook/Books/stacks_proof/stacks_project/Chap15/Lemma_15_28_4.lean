import Mathlib
import stacks_proof.stacks_project.Chap15.Definition_15_28_2
import stacks_proof.stacks_project.Chap15.Lemma_15_28_3

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

/-- Helper for Lemma 15.28.4: changing generators by a matrix `x` corresponds to precomposing the
original tuple linear form with the transpose of `x`. -/
private theorem koszulLinearForm_matrix_transpose_toLin' {r : ℕ}
    (x : Matrix (Fin r) (Fin r) R) (f : Fin r → R) :
    koszulLinearForm (x.toLin' f) = (koszulLinearForm f).comp (xᵀ).toLin' := by
  -- Evaluate both linear forms on a vector and rearrange the finite double sum.
  apply LinearMap.ext
  intro v
  calc
    koszulLinearForm (x.toLin' f) v = ∑ i : Fin r, v i * (x.toLin' f) i := by
      simp [koszulLinearForm, Module.piEquiv_apply_apply]
    _ = ∑ i : Fin r, ∑ j : Fin r, v i * (x i j * f j) := by
      simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
    _ = ∑ i : Fin r, ∑ j : Fin r, v i * x i j * f j := by
      simp [mul_assoc]
    _ = ∑ j : Fin r, ∑ i : Fin r, v i * x i j * f j := by
      exact Finset.sum_comm
    _ = ∑ j : Fin r, f j * ((xᵀ).toLin' v) j := by
      simp [Matrix.toLin'_apply, Matrix.mulVec, Matrix.transpose_apply, dotProduct,
        Finset.mul_sum, mul_left_comm, mul_comm]
    _ = ((koszulLinearForm f).comp (xᵀ).toLin') v := by
      simp [LinearMap.comp_apply, koszulLinearForm, Module.piEquiv_apply_apply, mul_comm]

/-- Helper for Lemma 15.28.4: the transpose acts as a right inverse to its inverse on the free
module `Fin r → R`. -/
private theorem transpose_toLin'_comp_inv_eq_id {r : ℕ}
    (x : Matrix (Fin r) (Fin r) R) [Invertible x] :
    ((xᵀ).toLin').comp (⅟ (xᵀ)).toLin' = LinearMap.id := by
  -- Rewrite the composite as the matrix product and use the right-inverse identity.
  calc
    ((xᵀ).toLin').comp (⅟ (xᵀ)).toLin' =
        (((xᵀ) * ⅟ (xᵀ)).toLin' : (Fin r → R) →ₗ[R] Fin r → R) := by
          rw [← Matrix.toLin'_mul]
    _ = ((1 : Matrix (Fin r) (Fin r) R).toLin' : (Fin r → R) →ₗ[R] Fin r → R) := by
          congr
          simpa using (invOf_eq_right_inv (xᵀ))
    _ = LinearMap.id := by
          simp [Matrix.toLin'_one]

/-- Helper for Lemma 15.28.4: the inverse transpose acts as a left inverse to the transpose on
the free module `Fin r → R`. -/
private theorem inv_transpose_toLin'_comp_eq_id {r : ℕ}
    (x : Matrix (Fin r) (Fin r) R) [Invertible x] :
    ((⅟ (xᵀ)).toLin').comp (xᵀ).toLin' = LinearMap.id := by
  -- Rewrite the composite as the matrix product and use the left-inverse identity.
  calc
    ((⅟ (xᵀ)).toLin').comp (xᵀ).toLin' =
        (((⅟ (xᵀ)) * xᵀ).toLin' : (Fin r → R) →ₗ[R] Fin r → R) := by
          rw [← Matrix.toLin'_mul]
    _ = ((1 : Matrix (Fin r) (Fin r) R).toLin' : (Fin r → R) →ₗ[R] Fin r → R) := by
          congr
          simpa using (invOf_eq_left_inv (xᵀ))
    _ = LinearMap.id := by
          simp [Matrix.toLin'_one]

/-- Helper for Lemma 15.28.4: after changing generators by an invertible matrix, precomposing with
the inverse transpose recovers the original tuple linear form. -/
private theorem koszulLinearForm_matrix_transpose_toLin'_comp_inv {r : ℕ}
    (x : Matrix (Fin r) (Fin r) R) [Invertible x] (f : Fin r → R) :
    (koszulLinearForm (x.toLin' f)).comp (⅟ (xᵀ)).toLin' = koszulLinearForm f := by
  -- Compose the transpose-compatibility bridge with the inverse transpose and collapse to `id`.
  apply LinearMap.ext
  intro v
  calc
    ((koszulLinearForm (x.toLin' f)).comp (⅟ (xᵀ)).toLin') v =
        koszulLinearForm f (((xᵀ).toLin') ((⅟ (xᵀ)).toLin' v)) := by
          rw [koszulLinearForm_matrix_transpose_toLin' x f]
          rfl
    _ = koszulLinearForm f v := by
          simpa using
            congrArg (fun ψ : (Fin r → R) →ₗ[R] Fin r → R => koszulLinearForm f (ψ v))
              (transpose_toLin'_comp_inv_eq_id (R := R) x)

/-- Lemma 15.28.4: an invertible linear change of generators
`g i = ∑ j, x i j * f j` induces an isomorphism between the Koszul complex on `f` and the Koszul
complex on the transformed family `g`. -/
@[stacks 0625]
noncomputable def koszul_complex_on_matrix_linear_combination_iso {r : ℕ}
    (x : Matrix (Fin r) (Fin r) R) [Invertible x] (f : Fin r → R) :
    K^•(f) ≅ K^•(x.toLin' f) where
  hom :=
    KoszulComplex.map (⅟ (xᵀ)).toLin' (koszulLinearForm_matrix_transpose_toLin'_comp_inv x f)
  inv :=
    KoszulComplex.map (xᵀ).toLin' (koszulLinearForm_matrix_transpose_toLin' x f).symm
  hom_inv_id := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    -- Check the degreewise composite on exterior-power generators.
    apply exteriorPower.linearMap_ext
    ext m
    change
      ModuleCat.exteriorPower.map (ofHom (xᵀ).toLin') n
          (ModuleCat.exteriorPower.map (ofHom (⅟ (xᵀ)).toLin') n
            (ModuleCat.exteriorPower.mk m)) =
        ModuleCat.exteriorPower.mk m
    rw [ModuleCat.exteriorPower.map_mk, ModuleCat.exteriorPower.map_mk]
    congr 1
    ext i
    simpa using
      congrArg (fun ψ : (Fin r → R) →ₗ[R] Fin r → R => ψ (m i))
        (transpose_toLin'_comp_inv_eq_id (R := R) x)
  inv_hom_id := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    -- Check the reverse composite on exterior-power generators in the same way.
    apply exteriorPower.linearMap_ext
    ext m
    change
      ModuleCat.exteriorPower.map (ofHom (⅟ (xᵀ)).toLin') n
          (ModuleCat.exteriorPower.map (ofHom (xᵀ).toLin') n
            (ModuleCat.exteriorPower.mk m)) =
        ModuleCat.exteriorPower.mk m
    rw [ModuleCat.exteriorPower.map_mk, ModuleCat.exteriorPower.map_mk]
    congr 1
    ext i
    simpa using
      congrArg (fun ψ : (Fin r → R) →ₗ[R] Fin r → R => ψ (m i))
        (inv_transpose_toLin'_comp_eq_id (R := R) x)

/-- The degree `n` component of the forward map in
`koszul_complex_on_matrix_linear_combination_iso x f` is induced by the inverse transpose of
`x`. -/
theorem koszul_complex_on_matrix_linear_combination_iso_hom_f {r : ℕ}
    (x : Matrix (Fin r) (Fin r) R) [Invertible x] (f : Fin r → R) (n : ℕ) :
    (koszul_complex_on_matrix_linear_combination_iso x f).hom.f n =
      ModuleCat.exteriorPower.map (ofHom (⅟ (xᵀ)).toLin') n := by
  simp [koszul_complex_on_matrix_linear_combination_iso]

end
