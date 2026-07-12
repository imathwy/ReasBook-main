import Mathlib
import StacksProject_2024.Chap10.Lemma_10_107_10

-- Declarations for this item will be appended below by the statement pipeline.

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
@[stacks 04VY]
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
