import Mathlib
import stacks_proof.stacks_project.Chap11.Lemma_11_4_4

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped TensorProduct

universe u v w

section

variable {k : Type u} [Field k]
variable {A : Type v} {A' : Type w} [Ring A] [Ring A'] [Algebra k A] [Algebra k A']
variable [IsSimpleRing A] [IsSimpleRing A']

/-- Helper for Lemma 11.4.7: centrality of a matrix algebra descends to its division-ring
coefficients. -/
lemma isCentral_of_matrix (n : ℕ) [NeZero n] (K : Type v) [DivisionRing K] [Algebra k K]
    [Algebra.IsCentral k (Matrix (Fin n) (Fin n) K)] :
    Algebra.IsCentral k K := by
  -- Pull the scalar matrix of a central element back to the corresponding diagonal entry.
  refine ⟨fun x hx ↦ ?_⟩
  have hxM : scalar (Fin n) x ∈ (Subalgebra.center k K).map (scalarAlgHom (Fin n) k) := by
    exact ⟨x, hx, rfl⟩
  rw [← subalgebraCenter_eq_scalarAlgHom_map] at hxM
  obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff k).1 hxM
  rw [Algebra.mem_bot]
  refine ⟨a, ?_⟩
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  simpa [i] using (congrArg (fun M : Matrix (Fin n) (Fin n) K ↦ M i i) ha).symm

/-- Helper for Lemma 11.4.7: the tensor product with a central division algebra is simple even
when the division algebra appears on the left. -/
lemma isSimpleRing_tensorProduct_of_isSimpleRing_right_division
    {K : Type v} [DivisionRing K] [Algebra k K] [Algebra.IsCentral k K] :
    IsSimpleRing (K ⊗[k] A') := by
  -- Commute the factors to reuse Lemma 11.4.4 in its original tensor order.
  let h : IsSimpleRing (A' ⊗[k] K) :=
    isSimpleRing_tensorProduct_of_isSimpleRing (k := k) (A := A') (K := K)
  exact IsSimpleRing.of_ringEquiv (Algebra.TensorProduct.comm k A' K).toRingEquiv h

/-- Helper for Lemma 11.4.7: the inverse formula for `fin_prod_one_equiv` recovers the original
pair. -/
lemma fin_prod_one_equiv_left_inv (n : ℕ) (ij : Fin n × Fin 1) : (ij.1, (0 : Fin 1)) = ij := by
  -- The second coordinate of `Fin 1` is forced, so the pair is determined by its first entry.
  rcases ij with ⟨i, j⟩
  have hj : j = 0 := Subsingleton.elim _ _
  simp [hj]

/-- Helper for Lemma 11.4.7: the trivial right factor `Fin 1` can be removed from matrix indices. -/
def fin_prod_one_equiv (n : ℕ) : Fin n × Fin 1 ≃ Fin n where
  toFun ij := ij.1
  invFun i := (i, 0)
  left_inv := fin_prod_one_equiv_left_inv n
  right_inv := fun _ ↦ rfl

/-- Helper for Lemma 11.4.7: tensoring a matrix presentation of `A` with `A'` yields a matrix
presentation over `K ⊗[k] A'`. -/
def tensorProduct_algEquiv_matrix_of_algEquiv_matrix
    {n : ℕ} [NeZero n] {K : Type v} [DivisionRing K] [Algebra k K]
    (e : A ≃ₐ[k] Matrix (Fin n) (Fin n) K) :
    A ⊗[k] A' ≃ₐ[k] Matrix (Fin n) (Fin n) (K ⊗[k] A') :=
  let eA' : A' ≃ₐ[k] Matrix (Fin 1) (Fin 1) A' :=
    ((reindexAlgEquiv k A' finOneEquiv).trans uniqueAlgEquiv).symm
  let eTensor :
      A ⊗[k] A' ≃ₐ[k] Matrix (Fin n) (Fin n) K ⊗[k] Matrix (Fin 1) (Fin 1) A' :=
    Algebra.TensorProduct.congr e eA'
  let eKronecker :
      Matrix (Fin n) (Fin n) K ⊗[k] Matrix (Fin 1) (Fin 1) A' ≃ₐ[k]
        Matrix (Fin n × Fin 1) (Fin n × Fin 1) (K ⊗[k] A') :=
    Matrix.kroneckerTMulAlgEquiv (Fin n) (Fin 1) k k K A'
  -- First replace both factors by matrix models, then use the Kronecker tensor equivalence.
  eTensor.trans <| eKronecker.trans <| reindexAlgEquiv k (K ⊗[k] A') (fin_prod_one_equiv n)

/-- If `A` is a finite-dimensional central simple `k`-algebra and `A'` is simple over `k`, then
`A ⊗[k] A'` is simple. -/
theorem isSimpleRing_tensorProduct_of_finite_central_left_factor
    [FiniteDimensional k A] [Algebra.IsCentral k A] :
    IsSimpleRing (A ⊗[k] A') := by
  -- Route correction: follow the source proof through a Wedderburn matrix presentation of `A`.
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨n, hn, K, hKdiv, hKalg, hKfinite, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k A
  letI : NeZero n := hn
  letI : DivisionRing K := hKdiv
  letI : Algebra k K := hKalg
  letI : Module.Finite k K := hKfinite
  letI : FiniteDimensional k K := inferInstance
  letI : Algebra.IsCentral k (Matrix (Fin n) (Fin n) K) := Algebra.IsCentral.of_algEquiv k A _ e
  letI : Algebra.IsCentral k K := isCentral_of_matrix (k := k) n K
  have hTensor : IsSimpleRing (K ⊗[k] A') :=
    isSimpleRing_tensorProduct_of_isSimpleRing_right_division (k := k) (A' := A')
  letI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  have hMatrix : IsSimpleRing (Matrix (Fin n) (Fin n) (K ⊗[k] A')) :=
    IsSimpleRing.matrix (Fin n) (K ⊗[k] A')
  -- Transport simplicity back along the canonical tensor/matrix identification.
  exact IsSimpleRing.of_ringEquiv
    (tensorProduct_algEquiv_matrix_of_algEquiv_matrix (k := k) (A := A) (A' := A') e).symm.toRingEquiv
    hMatrix

/-- Lemma 11.4.7: if `A` and `A'` are simple `k`-algebras and one of them is finite-dimensional
and central over `k`, then the tensor product `A ⊗[k] A'` is simple. -/
-- Proof sketch: argue by cases on which factor is finite and central. In the finite central case,
-- apply the Wedderburn decomposition of that factor into a matrix algebra over a central division
-- algebra, use Lemma 11.4.4 to obtain simplicity after tensoring with the division algebra, and
-- then transport simplicity across the resulting matrix-algebra identification using Lemma 11.4.5.
theorem isSimpleRing_tensorProduct_of_finite_central_factor
    (h : (FiniteDimensional k A ∧ Algebra.IsCentral k A) ∨
      (FiniteDimensional k A' ∧ Algebra.IsCentral k A')) :
    IsSimpleRing (A ⊗[k] A') := by
  rcases h with h | h
  · letI := h.1
    letI := h.2
    exact isSimpleRing_tensorProduct_of_finite_central_left_factor
  · letI := h.1
    letI := h.2
    let h' : IsSimpleRing (A' ⊗[k] A) :=
      isSimpleRing_tensorProduct_of_finite_central_left_factor
    exact IsSimpleRing.of_ringEquiv (Algebra.TensorProduct.comm k A' A).toRingEquiv h'

end
