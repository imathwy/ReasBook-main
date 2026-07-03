import Mathlib
import Mathlib.Algebra.Category.Ring.Epi
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_107_11 (from Chap10) -/
open scoped BigOperators TensorProduct
open Finsupp Submodule TensorProduct

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Domain-style sampling for this item:
-- - primary domain: commutative algebra of tensor-product equalizer criteria, expressed through
--   finite matrices over the base ring;
-- - `source-facing`: a finite matrix witness for the relation `g ⊗ 1 = 1 ⊗ g`;
-- - `core/canonical`: the tensor-product owner API from Lemma `10.107.10`, organized around
--   finitely supported generator matrices;
-- - `bridge/view`: the standard `Matrix`, `Matrix.map`, `ᵥ*`, `*ᵥ`, and `⬝ᵥ` operations rather
--   than an ad hoc `Fin`-indexed matrix encoding.

/-- A finite matrix expression for `g` whose row sums and column sums come from the image of
`R` in `S`. -/
structure IsFiniteMatrixExpression (g : S) (n : ℕ) (y z : Fin n → S)
    (P : Matrix (Fin n) (Fin n) R) : Prop where
  /-- The matrix expression evaluates to `g`. -/
  eq_repr :
    g = dotProduct (Matrix.vecMul y (P.map (algebraMap R S))) z
  /-- Each row sum lies in the image of `R` in `S`. -/
  row_mem_range :
    ∀ j : Fin n,
      Matrix.vecMul y (P.map (algebraMap R S)) j ∈ Set.range (algebraMap R S)
  /-- Each column sum lies in the image of `R` in `S`. -/
  col_mem_range :
    ∀ i : Fin n,
      Matrix.mulVec (P.map (algebraMap R S)) z i ∈ Set.range (algebraMap R S)

/-- Helper for Lemma 10.107.11: package the existential matrix witness as a reusable predicate. -/
abbrev HasFiniteMatrixExpression (g : S) : Prop :=
  ∃ n : ℕ,
    ∃ y z : Fin n → S,
      ∃ P : Matrix (Fin n) (Fin n) R,
        IsFiniteMatrixExpression g n y z P

/-- Helper for Lemma 10.107.11: duplicate the distinguished slots for `1` and `g` while still
containing every element of `S` as a generator. -/
def duplicatedGenerator (g : S) : Bool ⊕ S → S
  | Sum.inl false => 1
  | Sum.inl true => g
  | Sum.inr x => x

/-- Helper for Lemma 10.107.11: the tensor relation is encoded by the two distinguished rows in
the duplicated generating family. -/
noncomputable abbrev duplicatedRelation (g : S) : (Bool ⊕ S) →₀ S :=
  Finsupp.single (Sum.inl false) g - Finsupp.single (Sum.inl true) (1 : S)

/-- Helper for Lemma 10.107.11: the duplicated generating family still spans `S` because every
element appears on the `Sum.inr` branch. -/
lemma span_range_duplicatedGenerator (g : S) :
    span R (Set.range (duplicatedGenerator g)) = ⊤ := by
  -- Every `x : S` lies in the range as `duplicatedGenerator g (Sum.inr x)`.
  apply top_unique
  intro x hx
  exact Submodule.subset_span ⟨Sum.inr x, rfl⟩

/-- Helper for Lemma 10.107.11: the duplicated finitely supported tensor relation is exactly the
equation `g ⊗ 1 = 1 ⊗ g`. -/
lemma tensor_relation_eq_finsupp_sum_zero (g : S) :
    (duplicatedRelation g).sum
        (fun j mj ↦ mj ⊗ₜ[R] duplicatedGenerator g j) = 0 ↔
      g ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] g := by
  classical
  -- Expand the two distinguished singleton terms and rewrite the result as a subtraction.
  have hsum :
      (duplicatedRelation g).sum
          (fun j mj ↦ mj ⊗ₜ[R] duplicatedGenerator g j)
        = g ⊗ₜ[R] (1 : S) - (1 : S) ⊗ₜ[R] g := by
    simp [duplicatedRelation, duplicatedGenerator, Finsupp.sum_sub_index, sub_tmul]
  rw [hsum]
  simpa using sub_eq_zero

/-- Helper for Lemma 10.107.11: a finite matrix expression forces the tensor relation
`g ⊗ 1 = 1 ⊗ g`. -/
lemma tmul_one_eq_one_tmul_of_has_finite_matrix_expression {g : S}
    (h : HasFiniteMatrixExpression (R := R) g) :
    g ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] g := by
  classical
  rcases h with ⟨n, y, z, P, hP⟩
  let A : Matrix (Fin n) (Fin n) S := P.map (algebraMap R S)
  let rowScalar : Fin n → R := fun j ↦ Classical.choose (hP.row_mem_range j)
  let colScalar : Fin n → R := fun i ↦ Classical.choose (hP.col_mem_range i)
  have hrow : ∀ j : Fin n, Matrix.vecMul y A j = algebraMap R S (rowScalar j) := by
    intro j
    simpa [A] using (Classical.choose_spec (hP.row_mem_range j)).symm
  have hcol : ∀ i : Fin n, Matrix.mulVec A z i = algebraMap R S (colScalar i) := by
    intro i
    simpa [A] using (Classical.choose_spec (hP.col_mem_range i)).symm
  -- First rewrite `g ⊗ 1` using the column sums, so each term carries a scalar on the right.
  calc
    g ⊗ₜ[R] (1 : S) = dotProduct y (Matrix.mulVec A z) ⊗ₜ[R] (1 : S) := by
      rw [hP.eq_repr, Matrix.dotProduct_mulVec]
    _ = ∑ i : Fin n, (y i * Matrix.mulVec A z i) ⊗ₜ[R] (1 : S) := by
      rw [dotProduct, TensorProduct.sum_tmul]
    _ = ∑ i : Fin n, y i ⊗ₜ[R] Matrix.mulVec A z i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      calc
        (y i * Matrix.mulVec A z i) ⊗ₜ[R] (1 : S)
            = (algebraMap R S (colScalar i) * y i) ⊗ₜ[R] (1 : S) := by
                rw [hcol i, mul_comm]
        _ = ((colScalar i : R) • y i) ⊗ₜ[R] (1 : S) := by
              rw [Algebra.smul_def]
        _ = y i ⊗ₜ[R] ((colScalar i : R) • (1 : S)) := by
              rw [TensorProduct.smul_tmul]
        _ = y i ⊗ₜ[R] algebraMap R S (colScalar i) := by
              simp [Algebra.smul_def]
        _ = y i ⊗ₜ[R] Matrix.mulVec A z i := by
              rw [hcol i]
    _ = ∑ i : Fin n, y i ⊗ₜ[R] ∑ j : Fin n, A i j * z j := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [Matrix.mulVec, dotProduct]
    _ = ∑ i : Fin n, ∑ j : Fin n, y i ⊗ₜ[R] (A i j * z j) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [TensorProduct.tmul_sum]
    _ = ∑ j : Fin n, ∑ i : Fin n, (A i j * y i) ⊗ₜ[R] z j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro j hj
      refine Finset.sum_congr rfl ?_
      intro i hi
      calc
        y i ⊗ₜ[R] (A i j * z j) = y i ⊗ₜ[R] ((P i j : R) • z j) := by
          simp [A, Algebra.smul_def]
        _ = ((P i j : R) • y i) ⊗ₜ[R] z j := by
          rw [← TensorProduct.smul_tmul]
        _ = (A i j * y i) ⊗ₜ[R] z j := by
          simp [A, Algebra.smul_def, mul_comm]
    _ = ∑ j : Fin n, (∑ i : Fin n, A i j * y i) ⊗ₜ[R] z j := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [TensorProduct.sum_tmul]
    _ = ∑ j : Fin n, Matrix.vecMul y A j ⊗ₜ[R] z j := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      congr 1
      simp [Matrix.vecMul, dotProduct, mul_comm]
    _ = ∑ j : Fin n, algebraMap R S (rowScalar j) ⊗ₜ[R] z j := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [hrow j]
    _ = ∑ j : Fin n, (1 : S) ⊗ₜ[R] (Matrix.vecMul y A j * z j) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      calc
        algebraMap R S (rowScalar j) ⊗ₜ[R] z j
            = (((rowScalar j : R) • (1 : S)) ⊗ₜ[R] z j) := by
                simp [Algebra.smul_def]
        _ = (1 : S) ⊗ₜ[R] ((rowScalar j : R) • z j) := by
              rw [TensorProduct.smul_tmul]
        _ = (1 : S) ⊗ₜ[R] (algebraMap R S (rowScalar j) * z j) := by
              simp [Algebra.smul_def]
        _ = (1 : S) ⊗ₜ[R] (Matrix.vecMul y A j * z j) := by
              rw [← hrow j]
    _ = (1 : S) ⊗ₜ[R] ∑ j : Fin n, Matrix.vecMul y A j * z j := by
      rw [TensorProduct.tmul_sum]
    _ = (1 : S) ⊗ₜ[R] dotProduct (Matrix.vecMul y A) z := by
      simp [dotProduct]
    _ = (1 : S) ⊗ₜ[R] g := by
      rw [← hP.eq_repr]

/-- Helper for Lemma 10.107.11: any finite-index witness can be reindexed along
`Fintype.equivFin` to the `Fin n` format of `HasFiniteMatrixExpression`. -/
lemma has_finite_matrix_expression_of_finite_index {ι : Type*} [Fintype ι]
    (g : S) (y z : ι → S) (P : Matrix ι ι R)
    (hEq : g = dotProduct (Matrix.vecMul y (P.map (algebraMap R S))) z)
    (hrow : ∀ j : ι,
      Matrix.vecMul y (P.map (algebraMap R S)) j ∈ Set.range (algebraMap R S))
    (hcol : ∀ i : ι,
      Matrix.mulVec (P.map (algebraMap R S)) z i ∈ Set.range (algebraMap R S)) :
    HasFiniteMatrixExpression (R := R) g := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let y' : Fin (Fintype.card ι) → S := y ∘ e.symm
  let z' : Fin (Fintype.card ι) → S := z ∘ e.symm
  let P' : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) R := P.reindex e e
  have hEq' :
      g = dotProduct (Matrix.vecMul y' (P'.map (algebraMap R S))) z' := by
    -- Reindex the finite double sum along `e`.
    simpa [y', z', P', Matrix.vecMul, dotProduct, Matrix.reindex_apply, ← e.symm.sum_comp] using hEq
  refine ⟨Fintype.card ι, y', z', P', ?_⟩
  refine ⟨hEq', ?_, ?_⟩
  · intro j
    -- Row sums are unchanged by the `equivFin` reindexing.
    simpa [y', P', Matrix.vecMul, dotProduct, Matrix.reindex_apply, ← e.symm.sum_comp] using
      hrow (e.symm j)
  · intro i
    -- Column sums are likewise preserved under the same reindexing.
    simpa [z', P', Matrix.mulVec, dotProduct, Matrix.reindex_apply, ← e.symm.sum_comp] using
      hcol (e.symm i)

/-- Helper for Lemma 10.107.11: scalar elements of `S` coming from `R` admit a trivial
`1 × 1` matrix expression. -/
lemma has_finite_matrix_expression_algebraMap (r : R) :
    HasFiniteMatrixExpression (R := R) (algebraMap R S r) := by
  -- Use the obvious single-entry matrix witness.
  refine ⟨1, fun _ ↦ (1 : S), fun _ ↦ (1 : S), fun _ _ ↦ r, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [Matrix.vecMul, dotProduct]
  · intro j
    refine ⟨r, ?_⟩
    simp [Matrix.vecMul, dotProduct]
  · intro i
    refine ⟨r, ?_⟩
    simp [Matrix.mulVec, dotProduct]

/-- Helper for Lemma 10.107.11: finite matrix expressions are closed under subtraction. -/
lemma has_finite_matrix_expression_sub {x y : S}
    (hx : HasFiniteMatrixExpression (R := R) x)
    (hy : HasFiniteMatrixExpression (R := R) y) :
    HasFiniteMatrixExpression (R := R) (x - y) := by
  classical
  rcases hx with ⟨n, u, v, P, hP⟩
  rcases hy with ⟨m, u', v', Q, hQ⟩
  let ys : Fin n ⊕ Fin m → S := Sum.elim u u'
  let zs : Fin n ⊕ Fin m → S := Sum.elim v v'
  let M : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) R := Matrix.fromBlocks P 0 0 (-Q)
  have hEq :
      x - y = dotProduct (Matrix.vecMul ys (M.map (algebraMap R S))) zs := by
    -- Route correction: realize subtraction by a block-diagonal matrix with the second block negated.
    calc
      x - y = x + -y := by
            rw [sub_eq_add_neg]
      _ = dotProduct (Matrix.vecMul u (P.map (algebraMap R S))) v +
            dotProduct (Matrix.vecMul u' ((-Q).map (algebraMap R S))) v' := by
            rw [hP.eq_repr, hQ.eq_repr]
            simp [Matrix.vecMul, dotProduct]
      _ = dotProduct (Matrix.vecMul ys (M.map (algebraMap R S))) zs := by
            simp [ys, zs, M, Matrix.vecMul, dotProduct, Fintype.sum_sum_type,
              Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
              Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  have hrow :
      ∀ j : Fin n ⊕ Fin m,
        Matrix.vecMul ys (M.map (algebraMap R S)) j ∈ Set.range (algebraMap R S) := by
    intro j
    cases j with
    | inl j =>
        simpa [ys, zs, M, Matrix.vecMul, dotProduct, Fintype.sum_sum_type,
          Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
          Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂] using hP.row_mem_range j
    | inr j =>
        rcases hQ.row_mem_range j with ⟨r, hr⟩
        refine ⟨-r, ?_⟩
        calc
          algebraMap R S (-r) = -algebraMap R S r := by simp
          _ = -Matrix.vecMul u' (Q.map (algebraMap R S)) j := by rw [hr]
          _ = Matrix.vecMul ys (M.map (algebraMap R S)) (Sum.inr j) := by
                simp [ys, M, Matrix.vecMul, dotProduct, Fintype.sum_sum_type,
                  Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂]
  have hcol :
      ∀ i : Fin n ⊕ Fin m,
        Matrix.mulVec (M.map (algebraMap R S)) zs i ∈ Set.range (algebraMap R S) := by
    intro i
    cases i with
    | inl i =>
        simpa [ys, zs, M, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
          Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
          Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂] using hP.col_mem_range i
    | inr i =>
        rcases hQ.col_mem_range i with ⟨r, hr⟩
        refine ⟨-r, ?_⟩
        calc
          algebraMap R S (-r) = -algebraMap R S r := by simp
          _ = -(Q.map (algebraMap R S)).mulVec v' i := by rw [hr]
          _ = (M.map (algebraMap R S)).mulVec zs (Sum.inr i) := by
                simp [zs, M, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
                  Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  exact has_finite_matrix_expression_of_finite_index
    (R := R) (S := S) (g := x - y) ys zs M hEq hrow hcol

/-- Helper for Lemma 10.107.11: truncating the duplicated generator matrix yields a finite matrix
expression for a scalar shift of `g`. -/
lemma exists_scalar_sub_expression_of_generator_matrix (g : S)
    (a : (Bool ⊕ S) →₀ (Bool ⊕ S) →₀ R)
    (hm : ∀ j,
      duplicatedRelation g j =
        linearCombination R (duplicatedGenerator g) (a j))
    (ha : ∀ i,
      a.sum (fun j aij ↦ aij i • duplicatedGenerator g j) = 0) :
    ∃ r : R, HasFiniteMatrixExpression (R := R) (algebraMap R S r - g) := by
  classical
  let U : Finset (Bool ⊕ S) := a.support ∪ a.support.biUnion fun j ↦ (a j).support
  let K : Finset (Bool ⊕ S) := U.erase (Sum.inl false)
  let ι := {x // x ∈ K}
  let y : ι → S := fun i ↦ duplicatedGenerator g i.1
  let z : ι → S := fun i ↦ duplicatedGenerator g i.1
  let P : Matrix ι ι R := fun i j ↦ a j.1 i.1
  let r : R := a (Sum.inl false) (Sum.inl false)
  have hmem_ne_false (i : ι) : i.1 ≠ Sum.inl false := by
    exact (Finset.mem_erase.mp i.2).1
  have restricted_linearCombination {l : (Bool ⊕ S) →₀ R}
      (hl : ∀ x ∈ l.support, x ∈ K) :
      linearCombination R y (l.subtypeDomain (· ∈ K))
        = linearCombination R (duplicatedGenerator g) l := by
    -- Restricting a finitely supported family to the finite subtype `K` does not change its value.
    calc
      linearCombination R y (l.subtypeDomain (· ∈ K))
          = (l.subtypeDomain (· ∈ K)).sum (fun i bi ↦ bi • y i) := by
              rw [Finsupp.linearCombination_apply]
      _ = l.sum (fun i bi ↦ bi • duplicatedGenerator g i) := by
            simpa [y] using
              (Finsupp.sum_subtypeDomain_index
                (v := l) (h := fun i bi ↦ bi • duplicatedGenerator g i) hl)
      _ = linearCombination R (duplicatedGenerator g) l := by
            rw [Finsupp.linearCombination_apply]
  have row_trim_support (j : Bool ⊕ S) :
      ∀ x ∈
          (a j - Finsupp.single (Sum.inl false) (a j (Sum.inl false))).support,
        x ∈ K := by
    intro x hx
    let l : (Bool ⊕ S) →₀ R :=
      a j - Finsupp.single (Sum.inl false) (a j (Sum.inl false))
    have hxne :
        l x ≠ 0 :=
      Finsupp.mem_support_iff.mp hx
    have hxf : x ≠ Sum.inl false := by
      intro hxfalse
      subst hxfalse
      have hx0 : l (Sum.inl false) ≠ 0 := by simpa using hxne
      simpa [l] using hx0
    have hax : a j x ≠ 0 := by
      have hx0 : l x ≠ 0 := hxne
      simpa [l, hxf] using hx0
    have hj : j ∈ a.support := by
      refine Finsupp.mem_support_iff.mpr ?_
      intro hj0
      exact hax (hj0 ▸ by simp)
    have hxU : x ∈ U := by
      refine Finset.mem_union.mpr ?_
      right
      refine Finset.mem_biUnion.mpr ?_
      exact ⟨j, hj, Finsupp.mem_support_iff.mpr hax⟩
    exact Finset.mem_erase.mpr ⟨hxf, hxU⟩
  have col_trim_support (i : Bool ⊕ S) :
      ∀ x ∈
          (kernelFamilyMatrix (R := R) (I := Bool ⊕ S) (J := Bool ⊕ S) a i -
            Finsupp.single (Sum.inl false) (a (Sum.inl false) i)).support,
        x ∈ K := by
    intro x hx
    let c : (Bool ⊕ S) →₀ R :=
      kernelFamilyMatrix (R := R) (I := Bool ⊕ S) (J := Bool ⊕ S) a i -
        Finsupp.single (Sum.inl false) (a (Sum.inl false) i)
    have hxne :
        c x ≠ 0 :=
      Finsupp.mem_support_iff.mp hx
    have hxf : x ≠ Sum.inl false := by
      intro hxfalse
      subst hxfalse
      have hx0 : c (Sum.inl false) ≠ 0 := by simpa using hxne
      simpa [c, kernel_family_matrix_apply] using hx0
    have hax : a x i ≠ 0 := by
      have hx0 : c x ≠ 0 := hxne
      simpa [c, hxf, kernel_family_matrix_apply] using hx0
    have hxU : x ∈ U := by
      refine Finset.mem_union.mpr ?_
      left
      exact Finsupp.mem_support_iff.mpr (by
        intro hx0
        exact hax (hx0 ▸ by simp))
    exact Finset.mem_erase.mpr ⟨hxf, hxU⟩
  have row_exact (j : ι) :
      Matrix.vecMul y (P.map (algebraMap R S)) j
        = duplicatedRelation g j.1 - algebraMap R S (a j.1 (Sum.inl false)) := by
    let l : (Bool ⊕ S) →₀ R :=
      a j.1 - Finsupp.single (Sum.inl false) (a j.1 (Sum.inl false))
    have hl : ∀ x ∈ l.support, x ∈ K := by
      intro x hx
      simpa [l] using row_trim_support j.1 x hx
    have hmatrix :
        Matrix.vecMul y (P.map (algebraMap R S)) j
          = linearCombination R y (l.subtypeDomain (· ∈ K)) := by
      rw [Finsupp.linearCombination_apply]
      rw [Finsupp.sum_fintype (l.subtypeDomain (· ∈ K)) (fun i bi ↦ bi • y i) (by intro i; simp)]
      rw [Matrix.vecMul, dotProduct]
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [y, P, l, Finsupp.subtypeDomain_apply, hmem_ne_false, Algebra.smul_def, mul_comm]
    calc
      Matrix.vecMul y (P.map (algebraMap R S)) j
          = linearCombination R y (l.subtypeDomain (· ∈ K)) := hmatrix
      _ = linearCombination R (duplicatedGenerator g) l := restricted_linearCombination hl
      _ = linearCombination R (duplicatedGenerator g) (a j.1) -
            linearCombination R (duplicatedGenerator g)
              (Finsupp.single (Sum.inl false) (a j.1 (Sum.inl false))) := by
              simp [l, map_sub]
      _ = duplicatedRelation g j.1 - algebraMap R S (a j.1 (Sum.inl false)) := by
            rw [hm j.1]
            simp [duplicatedGenerator, Algebra.smul_def]
  have col_exact (i : ι) :
      Matrix.mulVec (P.map (algebraMap R S)) z i
        = -algebraMap R S (a (Sum.inl false) i.1) := by
    let c : (Bool ⊕ S) →₀ R :=
      kernelFamilyMatrix (R := R) (I := Bool ⊕ S) (J := Bool ⊕ S) a i.1 -
        Finsupp.single (Sum.inl false) (a (Sum.inl false) i.1)
    have hc : ∀ x ∈ c.support, x ∈ K := by
      intro x hx
      simpa [c] using col_trim_support i.1 x hx
    have hmatrix :
        Matrix.mulVec (P.map (algebraMap R S)) z i
          = linearCombination R z (c.subtypeDomain (· ∈ K)) := by
      rw [Finsupp.linearCombination_apply]
      rw [Finsupp.sum_fintype (c.subtypeDomain (· ∈ K)) (fun j bj ↦ bj • z j) (by intro j; simp)]
      rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl ?_
      intro j hj
      simp [z, P, c, Finsupp.subtypeDomain_apply, hmem_ne_false,
        kernel_family_matrix_apply, Algebra.smul_def]
    have hcol_total :
        linearCombination R (duplicatedGenerator g)
            (kernelFamilyMatrix (R := R) (I := Bool ⊕ S) (J := Bool ⊕ S) a i.1)
          = 0 := by
      calc
        linearCombination R (duplicatedGenerator g)
            (kernelFamilyMatrix (R := R) (I := Bool ⊕ S) (J := Bool ⊕ S) a i.1)
            = a.sum (fun j aij ↦ aij i.1 • duplicatedGenerator g j) := by
                simpa using
                  (row_linearCombination_of_kernel_family_matrix
                    (R := R) (M := S) (I := Bool ⊕ S) (J := Bool ⊕ S)
                    (duplicatedGenerator g) a i.1)
        _ = 0 := ha i.1
    calc
      Matrix.mulVec (P.map (algebraMap R S)) z i
          = linearCombination R z (c.subtypeDomain (· ∈ K)) := hmatrix
      _ = linearCombination R (duplicatedGenerator g) c := restricted_linearCombination hc
      _ = linearCombination R (duplicatedGenerator g)
            (kernelFamilyMatrix (R := R) (I := Bool ⊕ S) (J := Bool ⊕ S) a i.1) -
            linearCombination R (duplicatedGenerator g)
              (Finsupp.single (Sum.inl false) (a (Sum.inl false) i.1)) := by
              simp [c, map_sub]
      _ = -algebraMap R S (a (Sum.inl false) i.1) := by
            rw [hcol_total]
            simp [duplicatedGenerator, Algebra.smul_def]
  have row_false_exact :
      linearCombination R y
          ((a (Sum.inl false) -
              Finsupp.single (Sum.inl false) (a (Sum.inl false) (Sum.inl false))).subtypeDomain
            (· ∈ K))
        = g - algebraMap R S r := by
    let l : (Bool ⊕ S) →₀ R :=
      a (Sum.inl false) - Finsupp.single (Sum.inl false) r
    have hl : ∀ x ∈ l.support, x ∈ K := by
      intro x hx
      simpa [l, r] using row_trim_support (Sum.inl false) x hx
    calc
      linearCombination R y (l.subtypeDomain (· ∈ K))
          = linearCombination R (duplicatedGenerator g) l := restricted_linearCombination hl
      _ = linearCombination R (duplicatedGenerator g) (a (Sum.inl false)) -
            linearCombination R (duplicatedGenerator g) (Finsupp.single (Sum.inl false) r) := by
              simp [l, map_sub]
      _ = g - algebraMap R S r := by
            rw [← hm (Sum.inl false)]
            simp [duplicatedRelation, duplicatedGenerator, r, Algebra.smul_def]
  have hEq :
      algebraMap R S r - g
        = dotProduct (Matrix.vecMul y (P.map (algebraMap R S))) z := by
    -- Evaluate the double sum through the column relations, then identify the remaining row.
    calc
      algebraMap R S r - g
          = -linearCombination R y
              ((a (Sum.inl false) -
                  Finsupp.single (Sum.inl false) (a (Sum.inl false) (Sum.inl false))).subtypeDomain
                (· ∈ K)) := by
                rw [row_false_exact]
                ring
      _ = -∑ i : ι,
            ((a (Sum.inl false) -
                Finsupp.single (Sum.inl false) (a (Sum.inl false) (Sum.inl false))).subtypeDomain
              (· ∈ K)) i • y i := by
              rw [Finsupp.linearCombination_apply]
              congr 1
              exact Finsupp.sum_fintype
                ((a (Sum.inl false) -
                    Finsupp.single (Sum.inl false) (a (Sum.inl false) (Sum.inl false))).subtypeDomain
                  (· ∈ K))
                (fun i bi ↦ bi • y i)
                (by intro i; simp)
      _ = ∑ i : ι, y i * (-algebraMap R S (a (Sum.inl false) i.1)) := by
            simp [Finsupp.subtypeDomain_apply, hmem_ne_false, Algebra.smul_def, mul_comm]
      _ = ∑ i : ι, y i * Matrix.mulVec (P.map (algebraMap R S)) z i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [col_exact i]
      _ = dotProduct y (Matrix.mulVec (P.map (algebraMap R S)) z) := by
            rw [dotProduct]
      _ = dotProduct (Matrix.vecMul y (P.map (algebraMap R S))) z := by
            rw [← Matrix.dotProduct_mulVec]
  have hrow :
      ∀ j : ι, Matrix.vecMul y (P.map (algebraMap R S)) j ∈ Set.range (algebraMap R S) := by
    intro j
    cases hjs : j.1 with
    | inl b =>
        cases b with
        | false =>
            exact (hmem_ne_false j hjs).elim
        | true =>
            refine ⟨-1 - a (Sum.inl true) (Sum.inl false), ?_⟩
            simpa [hjs, duplicatedRelation] using (row_exact j).symm
    | inr s =>
        refine ⟨-a (Sum.inr s) (Sum.inl false), ?_⟩
        simpa [hjs, duplicatedRelation] using (row_exact j).symm
  have hcol :
      ∀ i : ι, Matrix.mulVec (P.map (algebraMap R S)) z i ∈ Set.range (algebraMap R S) := by
    intro i
    refine ⟨-a (Sum.inl false) i.1, ?_⟩
    simpa using (col_exact i).symm
  refine ⟨r, ?_⟩
  exact has_finite_matrix_expression_of_finite_index
    (R := R) (S := S) (g := algebraMap R S r - g) y z P hEq hrow hcol

/-- Helper for Lemma 10.107.11: the generator matrix produced by Lemma `10.107.10` for the
duplicated tensor relation can be truncated to a finite matrix expression for `g`. -/
lemma has_finite_matrix_expression_of_generator_matrix (g : S)
    (a : (Bool ⊕ S) →₀ (Bool ⊕ S) →₀ R)
    (hm : ∀ j,
      duplicatedRelation g j =
        linearCombination R (duplicatedGenerator g) (a j))
    (ha : ∀ i,
      a.sum (fun j aij ↦ aij i • duplicatedGenerator g j) = 0) :
    HasFiniteMatrixExpression (R := R) g := by
  -- First truncate the duplicated generator matrix to obtain a witness for `algebraMap r - g`.
  rcases
      exists_scalar_sub_expression_of_generator_matrix
        (R := R) (S := S) g a hm ha with
    ⟨r, hr⟩
  -- Then subtract that witness from the obvious scalar expression to recover `g`.
  have hs : HasFiniteMatrixExpression (R := R) (algebraMap R S r) :=
    has_finite_matrix_expression_algebraMap (R := R) (S := S) r
  have hsub :
      HasFiniteMatrixExpression (R := R)
        (algebraMap R S r - (algebraMap R S r - g)) :=
    has_finite_matrix_expression_sub (R := R) (S := S) hs hr
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub

-- Proof sketch: for the forward implication, choose an `R`-module generating family of `S`
-- containing `1` and `g`, apply Lemma `10.107.10` to the tensor relation
-- `g ⊗ₜ[R] 1 - 1 ⊗ₜ[R] g = 0`, and rewrite the resulting coefficient data into the stated matrix
-- form. For the reverse implication, expand the displayed sum in `S ⊗[R] S` and use the
-- assumptions that each row sum and column sum lies in the image of `algebraMap R S` to move the
-- scalar coefficients across the tensor factors.
/-- Lemma 10.107.11: for an element `g : S`, the tensor relation `g ⊗ 1 = 1 ⊗ g` in `S ⊗[R] S`
is equivalent to the existence of a finite matrix expression
`g = ∑ i, ∑ j, φ(x i j) y i z j` whose row sums and column sums lie in the image of `R` in `S`. -/
theorem tmul_one_eq_one_tmul_iff_exists_finite_matrix_expression (g : S) :
    g ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] g ↔
      ∃ n : ℕ,
        ∃ y z : Fin n → S,
          ∃ P : Matrix (Fin n) (Fin n) R,
            IsFiniteMatrixExpression g n y z P := by
  change g ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] g ↔
    HasFiniteMatrixExpression (R := R) g
  constructor
  · intro hg
    classical
    -- Apply Lemma `10.107.10` to the duplicated generating family with separate slots for `1`
    -- and `g`.
    have hzero :
        (duplicatedRelation g).sum
            (fun j mj ↦ mj ⊗ₜ[R] duplicatedGenerator g j) = 0 :=
      (tensor_relation_eq_finsupp_sum_zero (R := R) (S := S) g).2 hg
    rcases
        (finsupp_sum_tmul_eq_zero_iff_exists_generator_matrix
          (R := R) (M := S) (N := S)
          (x := duplicatedGenerator g)
          (y := duplicatedGenerator g)
          (m := duplicatedRelation g)
          (span_range_duplicatedGenerator (R := R) (S := S) g)
          (span_range_duplicatedGenerator (R := R) (S := S) g)).1 hzero with
      ⟨a, hm, ha⟩
    -- The remaining source-faithful step is the finite-support truncation of this generator
    -- matrix to the advertised square matrix witness.
    exact has_finite_matrix_expression_of_generator_matrix
      (R := R) (S := S) g a hm ha
  · intro h
    -- The reverse implication is the direct tensor expansion of the finite matrix witness.
    exact tmul_one_eq_one_tmul_of_has_finite_matrix_expression (R := R) (S := S) h

end

/-! ### Remark_10_107_12 (from Chap10) -/
open scoped TensorProduct
open Matrix

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Domain-style sampling for this item:
-- - primary domain: commutative algebra of tensor-product equalizer criteria, expressed through
--   finite matrix witnesses over the base ring;
-- - sampled owner API: `tmul_one_eq_one_tmul_iff_exists_finite_matrix_expression`,
--   `replicateRow`, `replicateCol`, and the canonical vector/matrix operations `ᵥ*`, `*ᵥ`, `⬝ᵥ`;
-- - `source-facing`: the associated matrix triple `(P, U, V)` from the remark;
-- - `core/canonical`: Lemma `10.107.11`, which packages the same tensor relation by a finite
--   matrix expression;
-- - `bridge/view`: row and column vectors realized canonically as `replicateRow` and
--   `replicateCol`.

/-- Remark 10.107.12: an `n`-triple `(P, U, V)` is associated to `g` if there are a row vector
`Y` and a column vector `Z` over `S` such that `g = Y P Z`, `U = Y P`, and `V = P Z`, with `P`
defined over `R` and `U`, `V` landing in the image of `R`. -/
def is_associated_matrix_triple (g : S) (n : ℕ) (P : Matrix (Fin n) (Fin n) R)
    (U : Matrix (Fin 1) (Fin n) R) (V : Matrix (Fin n) (Fin 1) R) : Prop :=
  ∃ y z : Fin n → S,
    g = y ᵥ* P.map (algebraMap R S) ⬝ᵥ z ∧
      U.map (algebraMap R S) = replicateRow (Fin 1) (y ᵥ* P.map (algebraMap R S)) ∧
      V.map (algebraMap R S) = replicateCol (Fin 1) (P.map (algebraMap R S) *ᵥ z)

/-- If `g` lies in the epicenter, then some finite matrix triple is associated to `g`. -/
-- Proof sketch: apply
-- `tmul_one_eq_one_tmul_iff_exists_finite_matrix_expression` to obtain coefficient data
-- `x`, `y`, `z`. Package `x` as the matrix `P`, package `y` and `z` as matrices `Y` and `Z`,
-- and choose `U` and `V` from the row-sum and column-sum image conditions.
theorem exists_associated_matrix_triple_of_tmul_one_eq_one_tmul (g : S)
    (hg : g ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] g) :
    ∃ n : ℕ,
      ∃ P : Matrix (Fin n) (Fin n) R,
        ∃ U : Matrix (Fin 1) (Fin n) R,
          ∃ V : Matrix (Fin n) (Fin 1) R,
            is_associated_matrix_triple g n P U V := by
  classical
  rcases (tmul_one_eq_one_tmul_iff_exists_finite_matrix_expression g).1 hg with
    ⟨n, y, z, P, hgP, hy, hz⟩
  let u : Fin n → R := fun j ↦ Classical.choose (hy j)
  let v : Fin n → R := fun i ↦ Classical.choose (hz i)
  refine ⟨n, P, replicateRow (Fin 1) u, replicateCol (Fin 1) v, ?_⟩
  refine ⟨y, z, hgP, ?_, ?_⟩
  · ext i j
    simp [u, Classical.choose_spec (hy j)]
  · ext i j
    simp [v, Classical.choose_spec (hz i)]

end

/-! ### Lemma_10_107_13 (from Chap10) -/
universe u v

noncomputable section

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

open Matrix
open scoped TensorProduct

/-- Helper for Lemma 10.107.13: `AssocTriple R` is the type of finite matrix triples over `R`
used in Remark 10.107.12. -/
abbrev AssocTriple (R : Type u) [CommRing R] :=
  Σ n : ℕ, Matrix (Fin n) (Fin n) R × Matrix (Fin 1) (Fin n) R × Matrix (Fin n) (Fin 1) R

/-- Helper for Lemma 10.107.13: an associated matrix triple determines the source element
uniquely. -/
lemma associated_matrix_triple_eq {g g' : S} {n : ℕ}
    {P : Matrix (Fin n) (Fin n) R} {U : Matrix (Fin 1) (Fin n) R}
    {V : Matrix (Fin n) (Fin 1) R}
    (hg : is_associated_matrix_triple (R := R) g n P U V)
    (hg' : is_associated_matrix_triple (R := R) g' n P U V) :
    g = g' := by
  rcases hg with ⟨y, z, rfl, hU, hV⟩
  rcases hg' with ⟨y', z', hg', hU', hV'⟩
  let P' := P.map (algebraMap R S)
  have hrow : y ᵥ* P' = y' ᵥ* P' := by
    -- The common row matrix `U` forces the two row-vector products to coincide.
    apply Matrix.replicateRow_injective (ι := Fin 1)
    calc
      Matrix.replicateRow (Fin 1) (y ᵥ* P') = U.map (algebraMap R S) := hU.symm
      _ = Matrix.replicateRow (Fin 1) (y' ᵥ* P') := hU'
  have hcol : P' *ᵥ z = P' *ᵥ z' := by
    -- The common column matrix `V` forces the two column-vector products to coincide.
    apply Matrix.replicateCol_injective (ι := Fin 1)
    calc
      Matrix.replicateCol (Fin 1) (P' *ᵥ z) = V.map (algebraMap R S) := hV.symm
      _ = Matrix.replicateCol (Fin 1) (P' *ᵥ z') := hV'
  -- Route correction: the source proof compares the common row and column data first, then
  -- rewrites the scalar expression for `g` through the shared matrix product.
  calc
    y ᵥ* P' ⬝ᵥ z = y' ᵥ* P' ⬝ᵥ z := by rw [hrow]
    _ = y' ⬝ᵥ (P' *ᵥ z) := by rw [← Matrix.dotProduct_mulVec]
    _ = y' ⬝ᵥ (P' *ᵥ z') := by rw [hcol]
    _ = y' ᵥ* P' ⬝ᵥ z' := by rw [Matrix.dotProduct_mulVec]
    _ = g' := hg'.symm

/-- Helper for Lemma 10.107.13: an epic algebra embeds into the space of associated matrix
triples. -/
lemma associated_matrix_triple_embedding [Algebra.IsEpi R S] :
    Nonempty (S ↪ AssocTriple R) := by
  classical
  have htmul : ∀ g : S, g ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] g :=
    fun g ↦ ((Algebra.isEpi_iff_forall_one_tmul_eq R S).mp inferInstance g).symm
  choose n P U V htriple using
    fun g : S =>
      exists_associated_matrix_triple_of_tmul_one_eq_one_tmul (R := R) (S := S) g (htmul g)
  let τ : S → AssocTriple R := fun g ↦ ⟨n g, (P g, U g, V g)⟩
  refine ⟨
    { toFun := τ
      inj' := ?_ }⟩
  intro g g' hEq
  -- Equality of the chosen triples reduces directly to the uniqueness lemma above.
  have hgTriple :
      is_associated_matrix_triple (R := R) g (τ g).1 (τ g).2.1 (τ g).2.2.1 (τ g).2.2.2 := by
    simpa [τ] using htriple g
  have hg'Triple :
      is_associated_matrix_triple (R := R) g' (τ g).1 (τ g).2.1 (τ g).2.2.1 (τ g).2.2.2 :=
    Eq.ndrec
      (motive := fun t : AssocTriple R =>
        is_associated_matrix_triple (R := R) g' t.1 t.2.1 t.2.2.1 t.2.2.2)
      (by simpa [τ] using htriple g')
      hEq.symm
  exact associated_matrix_triple_eq (R := R) (g := g) (g' := g') hgTriple hg'Triple

/-- Helper for Lemma 10.107.13: encode an associated triple by its size and the lists of matrix,
row, and column entries. -/
def assocTripleToLists : AssocTriple R → ℕ × List R × List R × List R
  | ⟨n, (P, U, V)⟩ =>
      ( n
      , List.ofFn fun ij : Fin (n * n) => Matrix.vec P (finProdFinEquiv.symm ij)
      , List.ofFn fun j : Fin n => U 0 j
      , List.ofFn fun i : Fin n => V i 0 )

/-- Helper for Lemma 10.107.13: the list encoding of associated triples is injective. -/
lemma assocTripleToLists_injective :
    Function.Injective (assocTripleToLists (R := R)) := by
  intro x y hxy
  rcases x with ⟨n, P, U, V⟩
  rcases y with ⟨n', P', U', V'⟩
  have hn : n = n' := by
    simpa [assocTripleToLists] using congrArg Prod.fst hxy
  subst hn
  have hPList :
      List.ofFn (fun ij : Fin (n * n) => Matrix.vec P (finProdFinEquiv.symm ij)) =
        List.ofFn (fun ij : Fin (n * n) => Matrix.vec P' (finProdFinEquiv.symm ij)) := by
    simpa [assocTripleToLists] using congrArg (fun t ↦ t.2.1) hxy
  have hUList :
      List.ofFn (fun j : Fin n => U 0 j) = List.ofFn (fun j : Fin n => U' 0 j) := by
    simpa [assocTripleToLists] using congrArg (fun t ↦ t.2.2.1) hxy
  have hVList :
      List.ofFn (fun i : Fin n => V i 0) = List.ofFn (fun i : Fin n => V' i 0) := by
    simpa [assocTripleToLists] using congrArg (fun t ↦ t.2.2.2) hxy
  have hP : P = P' := by
    -- The flattened matrix entry list recovers every entry of `P`.
    ext i j
    have hEntries := List.ofFn_inj.mp hPList
    simpa using congrFun hEntries (finProdFinEquiv (j, i))
  have hU : U = U' := by
    -- The single-row list recovers every entry of `U`.
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    cases hi
    exact congrFun (List.ofFn_inj.mp hUList) j
  have hV : V = V' := by
    -- The single-column list recovers every entry of `V`.
    ext i j
    have hj : j = 0 := Subsingleton.elim _ _
    cases hj
    exact congrFun (List.ofFn_inj.mp hVList) i
  subst hP
  subst hU
  subst hV
  rfl

/-- Helper for Lemma 10.107.13: over an infinite base ring, associated triples have cardinality at
most the cardinality of the base ring. -/
lemma associated_triple_cardinal_le_of_infinite [Infinite R] :
    Cardinal.lift.{v} (Cardinal.mk (AssocTriple R)) ≤ Cardinal.lift.{v} (Cardinal.mk R) := by
  have hencode0 :
      Cardinal.lift (Cardinal.mk (AssocTriple R)) ≤
        Cardinal.lift (Cardinal.mk (ℕ × List R × List R × List R)) :=
    Cardinal.lift_mk_le_lift_mk_of_injective (assocTripleToLists_injective (R := R))
  have hencode :
      Cardinal.lift.{v} (Cardinal.mk (AssocTriple R)) ≤
        Cardinal.lift.{v} (Cardinal.mk (ℕ × List R × List R × List R)) :=
    by simpa [Cardinal.lift_id] using Cardinal.lift_monotone hencode0
  have hlist : Cardinal.mk (List R) = Cardinal.mk R :=
    Cardinal.mk_list_eq_mk R
  have hR : Cardinal.aleph0 ≤ Cardinal.mk R :=
    Cardinal.aleph0_le_mk R
  have hcodomain : Cardinal.mk (ℕ × List R × List R × List R) = Cardinal.mk R := by
    calc
      Cardinal.mk (ℕ × List R × List R × List R)
          = Cardinal.aleph0 * Cardinal.mk R * Cardinal.mk R * Cardinal.mk R := by
              simp [Cardinal.mk_prod, hlist]
      _ = Cardinal.mk R := by
            rw [Cardinal.aleph0_mul_eq hR, Cardinal.mul_eq_self hR, Cardinal.mul_eq_self hR]
  calc
    Cardinal.lift.{v} (Cardinal.mk (AssocTriple R))
        ≤ Cardinal.lift.{v} (Cardinal.mk (ℕ × List R × List R × List R)) := hencode
    _ = Cardinal.lift.{v} (Cardinal.mk R) := by rw [hcodomain]

/-- Helper for Lemma 10.107.13: an epic algebra admits at most one algebra map to any target. -/
lemma algHom_eq_of_isEpi [Algebra.IsEpi R S] {T : Type*} [CommRing T] [Algebra R T]
    (f g : S →ₐ[R] T) :
    f = g := by
  ext s
  simpa using
    congr(Algebra.TensorProduct.lift f g (fun _ _ ↦ .all _ _)
      $((Algebra.isEpi_iff_forall_one_tmul_eq R S).mp inferInstance s)).symm

/-- Helper for Lemma 10.107.13: base change of an epic algebra remains epic without a
same-universe restriction on the target algebra. -/
lemma algebra_isEpi_tensorProduct_of_isEpi_univ {R' : Type u} [CommRing R'] [Algebra R R']
    [Algebra.IsEpi R S] :
    Algebra.IsEpi R' (R' ⊗[R] S) := by
  -- The tensor product is initial among `R'`-algebras equipped with an `R`-algebra map from `S`.
  refine (algebra_isEpi_iff_includeLeft_eq_includeRight (R := R') (S := R' ⊗[R] S)).mpr ?_
  apply Algebra.TensorProduct.ext
  · -- Both maps are `R'`-algebra morphisms, so they agree on the left tensor factor.
    apply AlgHom.ext
    intro x
    simpa using
      (Algebra.TensorProduct.tmul_one_eq_one_tmul
        (R := R') (A := R' ⊗[R] S) (B := R' ⊗[R] S) x)
  · -- On the right tensor factor, equality reduces to the original epimorphism `R → S`.
    exact algHom_eq_of_isEpi (R := R) (S := S)
      ((Algebra.TensorProduct.includeLeft :
          R' ⊗[R] S →ₐ[R'] (R' ⊗[R] S) ⊗[R'] (R' ⊗[R] S))
        |>.restrictScalars R |>.comp Algebra.TensorProduct.includeRight)
      ((Algebra.TensorProduct.includeRight :
          R' ⊗[R] S →ₐ[R'] (R' ⊗[R] S) ⊗[R'] (R' ⊗[R] S))
        |>.restrictScalars R |>.comp Algebra.TensorProduct.includeRight)

/-- Helper for Lemma 10.107.13: the fibers over residue fields of an epic algebra are finite as
modules over the residue field. -/
lemma fiber_moduleFinite_of_isEpi [Algebra.IsEpi R S] (P : Ideal R) [P.IsPrime] :
    Module.Finite P.ResidueField (P.Fiber S) := by
  let _ : Algebra.IsEpi P.ResidueField (P.Fiber S) :=
    algebra_isEpi_tensorProduct_of_isEpi_univ (R := R) (S := S) (R' := P.ResidueField)
  rcases epi_field_subsingleton_or_alg_equiv (k := P.ResidueField) (S := P.Fiber S) with hsub | he
  · let _ : Subsingleton (P.Fiber S) := hsub
    let _ : Module.FinitePresentation P.ResidueField (P.Fiber S) := inferInstance
    infer_instance
  · let e := he.some
    exact Module.Finite.of_surjective e.toLinearEquiv.toLinearMap e.surjective

/-- Helper for Lemma 10.107.13: an epic algebra is quasi-finite in the fiberwise sense. -/
lemma quasiFinite_of_isEpi [Algebra.IsEpi R S] :
    Algebra.QuasiFinite R S := by
  exact ⟨fun P _ ↦ fiber_moduleFinite_of_isEpi (R := R) (S := S) P⟩

/-- Helper for Lemma 10.107.13: a finite commutative ring is Artinian. -/
lemma isArtinianRing_of_finite [Finite R] :
    IsArtinianRing R := by
  let _ : IsNoetherianRing R := inferInstance
  let _ : Ring.KrullDimLE 0 R := Ring.KrullDimLE.mk₀ fun I hI ↦ by
    let _ : Finite (R ⧸ I) :=
      Finite.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    exact Ideal.Quotient.maximal_of_isField I (Finite.isField_of_domain (R ⧸ I))
  exact (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero).2 ⟨inferInstance, inferInstance⟩

-- Domain-style sampling for this item:
-- - primary domain: commutative algebra of ring epimorphisms, controlled via the tensor-product
--   criterion and finite matrix witnesses over the base ring;
-- - sampled owner API: `Algebra.isEpi_iff_forall_one_tmul_eq`,
--   `tmul_one_eq_one_tmul_iff_exists_finite_matrix_expression`, and the source-facing bridge
--   `exists_associated_matrix_triple_of_tmul_one_eq_one_tmul`;
-- - `source-facing`: the cardinality comparison `|S| ≤ |R|`;
-- - `core/canonical`: Lemma `10.107.11`, which organizes the epicity relation `g ⊗ 1 = 1 ⊗ g`
--   by finite matrix data over `R`;
-- - `bridge/view`: Remark `10.107.12`, which repackages those matrix witnesses as an associated
--   triple `(P, U, V)` with row and column data landing in the image of `R`.
--
-- Proof sketch: by `Algebra.isEpi_iff_forall_one_tmul_eq`, epimorphy gives
-- `g ⊗ₜ[R] 1 = 1 ⊗ₜ[R] g` for every `g : S`. The owner theorem
-- `tmul_one_eq_one_tmul_iff_exists_finite_matrix_expression` supplies finite matrix witness data
-- over `R`, and Remark `10.107.12` compresses that data to an associated triple `(P, U, V)`. The
-- source uniqueness argument shows that one triple cannot be associated to two different elements
-- of `S`, so `S` injects into the set of finite triples over `R`. That set has cardinality at
-- most `|R|`; in the finite-ring case the source reduces to surjectivity of an epimorphism from an
-- Artinian ring.
/-- Lemma 10.107.13: if `R → S` is an epimorphism of commutative rings, then the cardinality of
`S` is at most the cardinality of `R`. -/
theorem cardinalMk_le_of_isEpi [Algebra.IsEpi R S] :
    Cardinal.lift.{u} (Cardinal.mk S) ≤ Cardinal.lift.{v} (Cardinal.mk R) := by
  rcases finite_or_infinite R with hR | hR
  · let _ : Finite R := hR
    let _ : IsArtinianRing R := isArtinianRing_of_finite (R := R)
    let _ : Algebra.QuasiFinite R S := quasiFinite_of_isEpi (R := R) (S := S)
    let _ : Module.Finite R S := Module.Finite.of_quasiFinite
    have hsurj : Function.Surjective (algebraMap R S) :=
      (Algebra.isEpi_iff_surjective_algebraMap_of_finite (R := R) (A := S)).mp inferInstance
    -- In the finite-source branch, quasi-finiteness upgrades to module-finiteness, so the
    -- epicity criterion collapses to surjectivity.
    exact Cardinal.lift_mk_le_lift_mk_of_surjective hsurj
  · let _ : Infinite R := hR
    obtain ⟨e⟩ := associated_matrix_triple_embedding (R := R) (S := S)
    have hembed :
        Cardinal.lift.{u} (Cardinal.mk S) ≤ Cardinal.lift.{v} (Cardinal.mk (AssocTriple R)) :=
      Cardinal.lift_mk_le_lift_mk_of_injective e.injective
    -- In the infinite-source branch, the source-faithful triple-counting argument closes the
    -- cardinal estimate.
    exact hembed.trans (associated_triple_cardinal_le_of_infinite (R := R))

end

/-! ### Lemma_10_107_14 (from Chap10) -/
open CategoryTheory
open scoped TensorProduct ModuleCat
open Algebra.TensorProduct

universe u

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Helper for Lemma 10.107.14: over an epic algebra map, the tensors `1 ⊗ (s • x)` and
`s ⊗ x` have the same image under the canonical tensor-collapse equivalence, hence coincide. -/
lemma one_tmul_smul_eq_tmul_of_algebra_isEpi
    (h : Algebra.IsEpi R S) {M : ModuleCat S} [Module R M] [IsScalarTower R S M]
    (s : S) (x : M) :
    (1 : S) ⊗ₜ[R] (s • x) = s ⊗ₜ[R] x := by
  letI : Algebra.IsEpi R S := h
  -- Collapse both tensors to the same element of `M` via `TensorProduct.lid'`.
  apply (TensorProduct.lid' R S M).injective
  simp

/-- Helper for Lemma 10.107.14: if `R → S` is an epimorphism, then every `R`-linear map between
`S`-modules already commutes with the `S`-action. -/
lemma restrictScalars_map_smul_of_algebra_isEpi
    (h : Algebra.IsEpi R S) {M N : ModuleCat S}
    (φ : (ModuleCat.restrictScalars (algebraMap R S)).obj M ⟶
      (ModuleCat.restrictScalars (algebraMap R S)).obj N)
    (s : S) (x : M) :
    φ (s • x) = s • φ x := by
  letI : Algebra.IsEpi R S := h
  let _ : Module R M := Module.compHom M (algebraMap R S)
  let _ : Module R N := Module.compHom N (algebraMap R S)
  letI : IsScalarTower R S M :=
    { smul_assoc := fun r s x => by
        simpa [Algebra.smul_def] using (mul_smul (algebraMap R S r) s x) }
  letI : IsScalarTower R S N :=
    { smul_assoc := fun r s y => by
        simpa [Algebra.smul_def] using (mul_smul (algebraMap R S r) s y) }
  -- Route correction: replace the raw tensor evaluation map by base change followed by `lid'`.
  have h_tensor :
      φ.hom.baseChange S ((1 : S) ⊗ₜ[R] (s • x)) =
        φ.hom.baseChange S (s ⊗ₜ[R] x) := by
    exact congrArg (φ.hom.baseChange S)
      (one_tmul_smul_eq_tmul_of_algebra_isEpi (R := R) (S := S) (M := M) h s x)
  -- Injectivity of `TensorProduct.lid'` converts the tensor equality back to the desired formula.
  apply (TensorProduct.lid' R S N).symm.injective
  rw [TensorProduct.lid'_symm_apply, TensorProduct.lid'_symm_apply]
  calc
    (1 : S) ⊗ₜ[R] φ (s • x)
        = φ.hom.baseChange S ((1 : S) ⊗ₜ[R] (s • x)) := by
            rw [LinearMap.baseChange_tmul]
    _ = φ.hom.baseChange S (s ⊗ₜ[R] x) := h_tensor
    _ = s ⊗ₜ[R] φ x := by rw [LinearMap.baseChange_tmul]
    _ = (1 : S) ⊗ₜ[R] (s • φ x) := by
          symm
          exact one_tmul_smul_eq_tmul_of_algebra_isEpi (R := R) (S := S) (M := N) h s (φ x)

/-- Helper for Lemma 10.107.14: an epimorphic algebra map makes restriction of scalars full on
module categories. -/
lemma restrictScalars_full_of_algebra_isEpi
    (h : Algebra.IsEpi R S) :
    (ModuleCat.restrictScalars (algebraMap R S)).Full := by
  refine ⟨?_⟩
  intro M N φ
  -- Rebuild the unique `S`-linear map from the underlying `R`-linear map.
  let φS : M →ₗ[S] N :=
    { toFun := φ
      map_add' := φ.hom.map_add
      map_smul' := fun s x => restrictScalars_map_smul_of_algebra_isEpi h φ s x }
  refine ⟨ModuleCat.ofHom φS, ?_⟩
  ext x
  rfl

/-- Helper for Lemma 10.107.14: the identity map from a restricted object to the chosen
`R`-module structure is linear because both actions agree via the scalar tower. -/
lemma restrictScalars_objIso_identity_linear
    {A B M : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    (a : A) (x : (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B M)) :
    (AddEquiv.refl M).toFun (a • x) = a • (AddEquiv.refl M).toFun x := by
  -- Rewrite the restricted action through `A → B` and then use the scalar-tower compatibility.
  rw [ModuleCat.restrictScalars.smul_def]
  simpa [one_smul, mul_one] using (IsScalarTower.smul_assoc a (1 : B) (x : M)).symm

/-- Helper for Lemma 10.107.14: the restricted object on an `S`-module with a compatible
`R`-module structure is canonically the same underlying `R`-module. -/
noncomputable def restrictScalars_objIso
    {A B M : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M] :
    (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B M) ≅ ModuleCat.of A M :=
  (show ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B M)) ≃ₗ[A] M from
    { __ := AddEquiv.refl M
      map_smul' := restrictScalars_objIso_identity_linear (A := A) (B := B) (M := M) }).toModuleIso

/-- Helper for Lemma 10.107.14: the object-identity bridge on restricted scalars acts by the
identity on elements. -/
@[simp] lemma restrictScalars_objIso_hom_apply
    {A B M : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    (x : (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B M)) :
    (restrictScalars_objIso (A := A) (B := B) (M := M)).hom x = x :=
  rfl

/-- Helper for Lemma 10.107.14: the inverse object-identity bridge on restricted scalars also
acts by the identity on elements. -/
@[simp] lemma restrictScalars_objIso_inv_apply
    {A B M : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    (x : M) :
    (restrictScalars_objIso (A := A) (B := B) (M := M)).inv x = x :=
  rfl

/-- Helper for Lemma 10.107.14: this is the restricted-scalars version of the canonical map
`s ↦ 1 ⊗ s` from `S` to `S ⊗[R] S`. -/
noncomputable def restrictScalars_includeRight_hom :
    ((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) ⟶
      ((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S (S ⊗[R] S))) :=
  -- Route correction: conjugate the concrete `includeRight` linear map through identity-carrier
  -- isomorphisms so the reverse implication works on stable `ModuleCat.of R` objects.
  (restrictScalars_objIso (A := R) (B := S) (M := S)).hom ≫
    ModuleCat.ofHom
      ((Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S).toLinearMap) ≫
    (restrictScalars_objIso (A := R) (B := S) (M := S ⊗[R] S)).inv

/-- Helper for Lemma 10.107.14: the restricted `includeRight` morphism sends `s` to `1 ⊗ s`. -/
@[simp] lemma restrictScalars_includeRight_hom_apply (s : S) :
    restrictScalars_includeRight_hom (R := R) (S := S) s = (1 : S) ⊗ₜ[R] s :=
by
  -- Unfold the transported adapter and collapse the identity-carrier isomorphisms pointwise.
  simp [restrictScalars_includeRight_hom, restrictScalars_objIso]

/-- Helper for Lemma 10.107.14: full faithfulness of restriction of scalars forces the two
canonical maps `S → S ⊗[R] S` to coincide. -/
lemma includeLeft_eq_includeRight_of_restrictScalars_fullyFaithful
    (hff : (ModuleCat.restrictScalars.{u, u, u} (algebraMap R S)).FullyFaithful) :
    (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S) =
      (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S) := by
  let X : ModuleCat.{u} S := ModuleCat.of.{u} S S
  let Y : ModuleCat.{u} S := ModuleCat.of.{u} S (S ⊗[R] S)
  let hRight :
      ((ModuleCat.restrictScalars (algebraMap R S)).obj X) ⟶
        ((ModuleCat.restrictScalars (algebraMap R S)).obj Y) := by
    simpa [X, Y] using (restrictScalars_includeRight_hom (R := R) (S := S))
  let g : ModuleCat.of.{u} S S ⟶ ModuleCat.of.{u} S (S ⊗[R] S) :=
    hff.homEquiv.symm hRight
  have hg_map :
      (ModuleCat.restrictScalars (algebraMap R S)).map g =
        hRight := by
    simpa [g] using hff.homEquiv.apply_symm_apply hRight
  have hg_right (s : S) : g s = (1 : S) ⊗ₜ[R] s := by
    -- The fully faithful preimage has the same underlying `R`-linear map after restriction.
    have hs :
        ((ModuleCat.restrictScalars (algebraMap R S)).map g) s =
          hRight s := by
      exact congrArg
        (fun f : ((ModuleCat.restrictScalars (algebraMap R S)).obj X) ⟶
            ((ModuleCat.restrictScalars (algebraMap R S)).obj Y) ↦ f s)
        hg_map
    simpa [hRight, X, Y, restrictScalars_includeRight_hom_apply] using hs
  have hg_left (s : S) : g s = s ⊗ₜ[R] (1 : S) := by
    -- The preimage `g` is `S`-linear for the left `S`-action on the tensor product.
    calc
      g s = g (s • (1 : S)) := by simp
      _ = s • g 1 := by simpa using g.hom.map_smul s (1 : S)
      _ = s • ((1 : S) ⊗ₜ[R] (1 : S)) := by rw [hg_right 1]
      _ = s ⊗ₜ[R] (1 : S) := by
            simpa using (TensorProduct.smul_tmul' s (1 : S) (1 : S))
  -- Compare both canonical tensor-factor maps with the same `S`-linear preimage `g`.
  ext s
  calc
    (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S) s = g s := by
      simpa using (hg_left s).symm
    _ = (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S) s := by
      simpa using hg_right s

/-- The canonical `core/canonical` bridge for Lemma 10.107.14: for a commutative `R`-algebra `S`,
the algebra map is epic exactly when restriction of scalars on module categories is fully
faithful. This refines the source-text equality
`Hom_S(N₁, N₂) = Hom_R(N₁, N₂)` to the owner abstraction `Algebra.IsEpi R S`. -/
-- Proof sketch: if `R → S` is epic, `TensorProduct.lid'` upgrades every `R`-linear map of
-- `S`-modules canonically to an `S`-linear map, so restriction of scalars is fully faithful.
-- Conversely, full faithfulness forces the `R`-linear map `s ↦ 1 ⊗ s : S → S ⊗[R] S` to come
-- from an `S`-linear map for the left `S`-module structure, hence `1 ⊗ s = s ⊗ 1` for all `s`,
-- which is exactly `Algebra.IsEpi R S`.
theorem algebra_isEpi_iff_restrictScalars_fullyFaithful
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.IsEpi R S ↔
      Nonempty ((ModuleCat.restrictScalars.{u, u, u} (algebraMap R S)).FullyFaithful) := by
  constructor
  · intro h
    -- The forward direction is the source argument: tensor-collapse upgrades every underlying
    -- `R`-linear map to an `S`-linear one, so restriction of scalars is fully faithful.
    letI : (ModuleCat.restrictScalars (algebraMap R S)).Full :=
      restrictScalars_full_of_algebra_isEpi h
    exact ⟨Functor.FullyFaithful.ofFullyFaithful _⟩
  · rintro ⟨hff : (ModuleCat.restrictScalars.{u, u, u} (algebraMap R S)).FullyFaithful⟩
    -- The reverse direction recovers `1 ⊗ s = s ⊗ 1` from the fully faithful preimage of
    -- `includeRight`, then invokes the epimorphism criterion from Lemma 10.107.1.
    exact (algebra_isEpi_iff_includeLeft_eq_includeRight).mpr
      (includeLeft_eq_includeRight_of_restrictScalars_fullyFaithful hff)

end

/-- Lemma 10.107.14: a ring homomorphism `f : R →+* S` is an epimorphism of commutative rings if
and only if the restriction-of-scalars functor `ModuleCat.restrictScalars f : ModuleCat S ⥤
ModuleCat R` is fully faithful. This is the canonical category-theoretic form of the equivalence
between ring epimorphisms, equality of `S`-linear and `R`-linear maps between `S`-modules, and
full faithfulness of restriction of scalars. -/
-- Proof sketch: equip `S` with the `R`-algebra structure induced by `f`. The core bridge above
-- gives `Algebra.IsEpi R S ↔` full faithfulness of `ModuleCat.restrictScalars f`, and
-- `CommRingCat.epi_iff_epi` identifies `Algebra.IsEpi R S` with `Epi (CommRingCat.ofHom f)`.
theorem ringHom_epi_iff_restrictScalars_fullyFaithful
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    Epi (CommRingCat.ofHom f) ↔ Nonempty ((ModuleCat.restrictScalars.{u, u, u} f).FullyFaithful) := by
  letI : Algebra R S := f.toAlgebra
  have hf : Epi (CommRingCat.ofHom f) ↔ Algebra.IsEpi R S := by
    simpa [RingHom.algebraMap_toAlgebra] using CommRingCat.epi_iff_epi
  exact hf.trans <| by
    simpa [RingHom.algebraMap_toAlgebra] using
      (algebra_isEpi_iff_restrictScalars_fullyFaithful (R := R) (S := S))

/-- Restriction of scalars along an epimorphism of commutative rings is fully faithful. This is
the canonical instance-level companion to `ringHom_epi_iff_restrictScalars_fullyFaithful`. -/
noncomputable instance restrictScalars_fullyFaithful_of_epi
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) [Epi (CommRingCat.ofHom f)] :
    (ModuleCat.restrictScalars.{u, u, u} f).FullyFaithful :=
  ((ringHom_epi_iff_restrictScalars_fullyFaithful f).mp inferInstance).some
