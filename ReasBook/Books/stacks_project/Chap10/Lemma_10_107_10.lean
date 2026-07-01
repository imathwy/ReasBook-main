import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Finsupp Submodule TensorProduct

universe u v w x y

section

variable {R : Type u} {M : Type v} {N : Type w} {I : Type x} {J : Type y}
variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

-- Proof sketch: lift the displayed tensor relation through the surjection
-- `Finsupp.linearCombination R y : (J →₀ R) →ₗ[R] N`, use right exactness of tensor product to land
-- in `LinearMap.ker (linearCombination R y) ⊗ M`, then use the generators `x` to write that lift as
-- a finitely supported family of kernel elements. Reading off the coordinates of those kernel
-- elements yields the desired coefficient matrix.
/- Layering for this item:
- `source-facing`: the finitely supported tensor relation `m.sum (fun j mj ↦ mj ⊗ₜ[R] y j) = 0`
  expressed in terms of the generating families `x` and `y`;
- `core/canonical`: right exactness of tensor product together with the free-module identifications
  `TensorProduct.finsuppScalarLeft` and `TensorProduct.finsuppScalarRight`;
- `bridge/view`: the surjective linear-combination maps attached to `x` and `y`, plus the explicit
  formulas that read a kernel family back into row and column identities.
-/
/-- Helper for Lemma 10.107.10: expand a finitely supported family into the canonical tensor on the
free module with basis indexed by the same set. -/
lemma finsuppScalarLeft_symm_apply_sum [DecidableEq J]
    (m : J →₀ M) :
    ((TensorProduct.finsuppScalarLeft R M J).symm m)
      = m.sum (fun j mj ↦ Finsupp.single j (1 : R) ⊗ₜ[R] mj) := by
  -- Reduce the statement to the single-support case and extend by linearity.
  refine Finsupp.induction_linear m ?_ ?_ ?_
  · simp
  · intro m1 m2 hm1 hm2
    calc
      ((TensorProduct.finsuppScalarLeft R M J).symm (m1 + m2))
          = ((TensorProduct.finsuppScalarLeft R M J).symm m1) +
              ((TensorProduct.finsuppScalarLeft R M J).symm m2) := by
                simp
      _ = m1.sum (fun j mj ↦ Finsupp.single j (1 : R) ⊗ₜ[R] mj) +
            m2.sum (fun j mj ↦ Finsupp.single j (1 : R) ⊗ₜ[R] mj) := by
              rw [hm1, hm2]
      _ = (m1 + m2).sum (fun j mj ↦ Finsupp.single j (1 : R) ⊗ₜ[R] mj) := by
            symm
            rw [Finsupp.sum_add_index]
            · intro j _
              simp
            · intro j _ mj1 mj2
              simp [TensorProduct.tmul_add]
  · intro j mj
    simp [TensorProduct.finsuppScalarLeft_symm_apply_single]

/-- Helper for Lemma 10.107.10: convert a finitely supported family of coefficients into the
corresponding tensor against the free module on `I`. -/
lemma finsuppScalarRight_symm_apply_sum [DecidableEq I]
    (b : I →₀ M) :
    ((TensorProduct.finsuppScalarRight R R M I).symm b)
      = b.sum (fun i bi ↦ bi ⊗ₜ[R] Finsupp.single i (1 : R)) := by
  -- As above, the linear equivalence is determined by its behavior on single-support families.
  refine Finsupp.induction_linear b ?_ ?_ ?_
  · simp
  · intro b1 b2 hb1 hb2
    calc
      ((TensorProduct.finsuppScalarRight R R M I).symm (b1 + b2))
          = ((TensorProduct.finsuppScalarRight R R M I).symm b1) +
              ((TensorProduct.finsuppScalarRight R R M I).symm b2) := by
                simp
      _ = b1.sum (fun i bi ↦ bi ⊗ₜ[R] Finsupp.single i (1 : R)) +
            b2.sum (fun i bi ↦ bi ⊗ₜ[R] Finsupp.single i (1 : R)) := by
              rw [hb1, hb2]
      _ = (b1 + b2).sum (fun i bi ↦ bi ⊗ₜ[R] Finsupp.single i (1 : R)) := by
            symm
            rw [Finsupp.sum_add_index]
            · intro i _
              simp
            · intro i _ bi1 bi2
              simp [add_tmul]
  · intro i bi
    simp [TensorProduct.finsuppScalarRight_symm_apply_single]

/-- Helper for Lemma 10.107.10: commuting the tensor lift through the free module on `J`
recovers the displayed finite tensor sum. -/
lemma comm_rTensor_finsuppScalarLeft_symm [DecidableEq J]
    (y : J → N) (m : J →₀ M) :
    TensorProduct.comm R N M
        (((Finsupp.linearCombination R y).rTensor M)
          ((TensorProduct.finsuppScalarLeft R M J).symm m))
      = m.sum (fun j mj ↦ mj ⊗ₜ[R] y j) := by
  -- The free-module lift is a sum of basis vectors, so the commuted tensor map is termwise.
  refine Finsupp.induction_linear m ?_ ?_ ?_
  · simp
  · intro m1 m2 hm1 hm2
    calc
      TensorProduct.comm R N M
          (((Finsupp.linearCombination R y).rTensor M)
            ((TensorProduct.finsuppScalarLeft R M J).symm (m1 + m2)))
          = TensorProduct.comm R N M
              (((Finsupp.linearCombination R y).rTensor M)
                ((TensorProduct.finsuppScalarLeft R M J).symm m1) +
                  ((Finsupp.linearCombination R y).rTensor M)
                    ((TensorProduct.finsuppScalarLeft R M J).symm m2)) := by
                  simp
      _ = TensorProduct.comm R N M
            (((Finsupp.linearCombination R y).rTensor M)
              ((TensorProduct.finsuppScalarLeft R M J).symm m1)) +
          TensorProduct.comm R N M
            (((Finsupp.linearCombination R y).rTensor M)
              ((TensorProduct.finsuppScalarLeft R M J).symm m2)) := by
                simp
      _ = m1.sum (fun j mj ↦ mj ⊗ₜ[R] y j) + m2.sum (fun j mj ↦ mj ⊗ₜ[R] y j) := by
            rw [hm1, hm2]
      _ = (m1 + m2).sum (fun j mj ↦ mj ⊗ₜ[R] y j) := by
            symm
            rw [Finsupp.sum_add_index]
            · intro j _
              simp
            · intro j _ mj1 mj2
              exact add_tmul mj1 mj2 (y j)
  · intro j mj
    simp [TensorProduct.finsuppScalarLeft_symm_apply_single, LinearMap.rTensor_tmul]

/-- Helper for Lemma 10.107.10: a finitely supported family of kernel vectors records the row
expansions needed for the coefficient matrix. -/
lemma kernel_family_rows_raw [DecidableEq I] [DecidableEq J]
    (x : I → M) {π : (J →₀ R) →ₗ[R] N} (b : I →₀ LinearMap.ker π) :
    TensorProduct.finsuppScalarLeft R M J
        (((LinearMap.ker π).subtype.rTensor M)
          (((Finsupp.linearCombination R x).lTensor (LinearMap.ker π))
            ((TensorProduct.finsuppScalarRight R R (LinearMap.ker π) I).symm b)))
      = b.sum (fun i bi ↦ (bi : J →₀ R).sum (fun j rij ↦ Finsupp.single j (rij • x i))) := by
  -- Expand the tensor via `finsuppScalarRight`, then evaluate each pure tensor explicitly.
  ext j
  rw [finsuppScalarRight_symm_apply_sum]
  simp [Finsupp.sum, LinearMap.lTensor_tmul, Finsupp.linearCombination_apply,
    LinearMap.rTensor_tmul, TensorProduct.finsuppScalarLeft_apply_tmul]
  refine Finset.sum_congr rfl ?_
  intro i hi
  refine Finset.sum_congr rfl ?_
  intro c hc
  by_cases h : c = j
  · have hs' : Finsupp.linearCombination R x (Finsupp.single i (1 : R)) = x i := by
      exact (Finsupp.linearCombination_single (R := R) (v := x) (c := (1 : R)) (a := i)).trans
        (one_smul R (x i))
    have hs : ∑ x_1 ∈ (fun₀ | i => (1 : R)).support, (fun₀ | i => (1 : R)) x_1 • x x_1 = x i := by
      change Finsupp.linearCombination R x (Finsupp.single i (1 : R)) = x i
      exact hs'
    simp [h, hs]
  · simp [h]

/-- Helper for Lemma 10.107.10: the finitely supported family of kernel vectors defines a direct
coefficient matrix by recording the `(i,j)` coefficient as the `j`th coordinate of the `i`th
kernel vector. -/
noncomputable def kernelFamilyMatrix [DecidableEq I] [DecidableEq J] (c : I →₀ J →₀ R) :
    J →₀ I →₀ R :=
  c.sum (fun i ci ↦ ci.sum (fun j rij ↦ Finsupp.single j (Finsupp.single i rij)))

/-- Helper for Lemma 10.107.10: the `j`th row of `kernelFamilyMatrix c` is the finitely supported
family of coefficients `i ↦ c i j`. -/
lemma kernel_family_matrix_row [DecidableEq I] [DecidableEq J]
    (c : I →₀ J →₀ R) (j : J) :
    kernelFamilyMatrix c j = c.sum (fun i ci ↦ Finsupp.single i (ci j)) := by
  -- Route correction: normalize the whole row before reading individual coefficients.
  ext i
  calc
    kernelFamilyMatrix c j i = c i j := by
      rw [kernelFamilyMatrix, Finsupp.sum, Finset.sum_apply', Finset.sum_apply']
      rw [Finset.sum_eq_single i]
      · rw [Finsupp.sum, Finset.sum_apply', Finset.sum_apply']
        rw [Finset.sum_eq_single j]
        · simp
        · intro j' hj' hne
          simp [hne]
        · simp
      · intro i' hi' hne
        rw [Finsupp.sum, Finset.sum_apply', Finset.sum_apply']
        refine Finset.sum_eq_zero ?_
        intro j' hj'
        by_cases hjj : j' = j
        · subst hjj
          simp [hne]
        · simp [hjj]
      · intro hzero
        have hci : c i = 0 := by
          exact notMem_support_iff.mp hzero
        simp [hci]
    _ = (c.sum (fun i' ci ↦ Finsupp.single i' (ci j))) i := by
      rw [Finsupp.sum, Finset.sum_apply']
      rw [Finset.sum_eq_single i]
      · simp
      · intro i' hi' hne
        simp [hne]
      · intro hzero
        have hci : c i = 0 := by
          exact notMem_support_iff.mp hzero
        simp [hci]

/-- Helper for Lemma 10.107.10: the direct matrix records exactly the original coefficient
`c i j` in row `j` and column `i`. -/
lemma kernel_family_matrix_apply [DecidableEq I] [DecidableEq J]
    (c : I →₀ J →₀ R) (j : J) (i : I) :
    kernelFamilyMatrix c j i = c i j := by
  -- Read the coefficient from the normalized row description.
  calc
    kernelFamilyMatrix c j i = (c.sum (fun i' ci ↦ Finsupp.single i' (ci j))) i := by
      simpa using
        congrArg (fun z ↦ z i) (kernel_family_matrix_row (R := R) (I := I) (J := J) c j)
    _ = c i j := by
      rw [Finsupp.sum, Finset.sum_apply']
      rw [Finset.sum_eq_single i]
      · simp
      · intro i' hi' hne
        simp [hne]
      · intro hzero
        have hci : c i = 0 := by
          exact notMem_support_iff.mp hzero
        simp [hci]

/-- Helper for Lemma 10.107.10: forgetting the subtype on a kernel family does not change the
row sum obtained by evaluating at a fixed `j`. -/
lemma row_sum_mapRange_subtype
    (x : I → M) {π : (J →₀ R) →ₗ[R] N} (b : I →₀ LinearMap.ker π) (j : J) :
    ((Finsupp.mapRange.linearMap ((LinearMap.ker π).subtype : LinearMap.ker π →ₗ[R] J →₀ R) b).sum
      (fun i ci ↦ ci j • x i))
      = b.sum (fun i bi ↦ (bi : J →₀ R) j • x i) := by
  -- Passing from `b` to the mapped family `c` only removes the subtype wrapper on coefficients.
  simpa [Finsupp.sum_mapRange_index]

/-- Helper for Lemma 10.107.10: each row of the direct matrix gives the corresponding linear
combination of the generators `x`. -/
lemma row_linearCombination_of_kernel_family_matrix [DecidableEq I] [DecidableEq J]
    (x : I → M) (c : I →₀ J →₀ R) (j : J) :
    linearCombination R x (kernelFamilyMatrix c j) = c.sum (fun i ci ↦ ci j • x i) := by
  -- First rewrite the row in canonical `Finsupp.single` form, then evaluate `linearCombination`.
  calc
    linearCombination R x (kernelFamilyMatrix c j)
      = linearCombination R x (c.sum (fun i ci ↦ Finsupp.single i (ci j))) := by
          rw [kernel_family_matrix_row]
    _ = c.sum (fun i ci ↦ linearCombination R x (Finsupp.single i (ci j))) := by
          rw [map_finsuppSum]
    _ = c.sum (fun i ci ↦ ci j • x i) := by
          simp [Finsupp.linearCombination_single]

/-- Helper for Lemma 10.107.10: transposing twice returns the original finitely supported matrix. -/
lemma kernel_family_matrix_involutive [DecidableEq I] [DecidableEq J]
    (c : I →₀ J →₀ R) :
    kernelFamilyMatrix (R := R) (I := J) (J := I) (kernelFamilyMatrix c) = c := by
  -- Each entry survives exactly once under the second transpose.
  ext i j
  simp [kernel_family_matrix_apply]

/-- Helper for Lemma 10.107.10: the `i`th column sum of the direct matrix is the linear
combination of the family `y` with coefficients `c i`. -/
lemma column_sum_eq_linearCombination_of_kernel_family_matrix [DecidableEq I] [DecidableEq J]
    (y : J → N) (c : I →₀ J →₀ R) (i : I) :
    (kernelFamilyMatrix c).sum (fun j aij ↦ aij i • y j) = linearCombination R y (c i) := by
  -- View the `i`th column as the `i`th row of the transposed matrix, then transpose back.
  calc
    (kernelFamilyMatrix c).sum (fun j aij ↦ aij i • y j)
      = linearCombination R y
          (kernelFamilyMatrix (R := R) (I := J) (J := I) (kernelFamilyMatrix c) i) := by
            symm
            simpa using
              row_linearCombination_of_kernel_family_matrix
                (R := R) (M := N) (I := J) (J := I) y (kernelFamilyMatrix c) i
    _ = linearCombination R y (c i) := by
          rw [kernel_family_matrix_involutive]

/-- Helper for Lemma 10.107.10: rewriting the row formulas `hm` as a single finitely supported
family removes the support mismatch before taking the tensor sum. -/
lemma generator_matrix_rows_as_finsupp
    (x : I → M) (m : J →₀ M) (a : J →₀ I →₀ R)
    (hm : ∀ j, m j = linearCombination R x (a j)) :
    m = a.sum (fun j aij ↦ Finsupp.single j (linearCombination R x aij)) := by
  classical
  -- Evaluate both finitely supported families at a fixed index `j`.
  ext j
  -- Only the singleton row at `j` survives when reading the `j`th coordinate.
  rw [Finsupp.sum_apply, Finsupp.sum_eq_single j]
  · simpa using hm j
  · intro j' _ hne
    rw [Finsupp.single_apply]
    simp [hne]
  · simp

/-- Helper for Lemma 10.107.10: after rewriting `m` as a sum of singleton rows, the outer
`Finsupp.sum` collapses to the row-indexed tensor sum. -/
lemma generator_matrix_sum_single_rows
    (x : I → M) (y : J → N) (a : J →₀ I →₀ R) :
    (a.sum (fun j aij ↦ Finsupp.single j (linearCombination R x aij))).sum
        (fun j mj ↦ mj ⊗ₜ[R] y j)
      = a.sum (fun j aij ↦ linearCombination R x aij ⊗ₜ[R] y j) := by
  classical
  -- Flatten the outer `Finsupp.sum` and then collapse each singleton row.
  calc
    (a.sum (fun j aij ↦ Finsupp.single j (linearCombination R x aij))).sum
        (fun j mj ↦ mj ⊗ₜ[R] y j)
      = a.sum (fun j aij ↦
          (Finsupp.single j (linearCombination R x aij)).sum
            (fun j' mj ↦ mj ⊗ₜ[R] y j')) := by
            rw [Finsupp.sum_sum_index]
            · intro j
              simp
            · intro j mj₁ mj₂
              exact add_tmul mj₁ mj₂ (y j)
    _ = a.sum (fun j aij ↦ linearCombination R x aij ⊗ₜ[R] y j) := by
          refine Finsupp.sum_congr ?_
          intro j hj
          simpa using
            (Finsupp.sum_single_index
              (m := j) (r := linearCombination R x (a j))
              (h := fun j' mj ↦ mj ⊗ₜ[R] y j')
              (by simp))

/-- Helper for Lemma 10.107.10: transposing the finitely supported coefficient matrix commutes the
finite double tensor sum. -/
lemma generator_matrix_tensor_transpose [DecidableEq I] [DecidableEq J]
    (x : I → M) (y : J → N) (a : J →₀ I →₀ R) :
    a.sum (fun j aij ↦ linearCombination R x aij ⊗ₜ[R] y j)
      = (kernelFamilyMatrix (R := R) (I := J) (J := I) a).sum
          (fun i col ↦ x i ⊗ₜ[R] linearCombination R y col) := by
  classical
  -- Expand each row tensor into a finite double sum over the matrix coefficients.
  calc
    a.sum (fun j aij ↦ linearCombination R x aij ⊗ₜ[R] y j)
      = a.sum (fun j aij ↦ aij.sum (fun i rij ↦ x i ⊗ₜ[R] (rij • y j))) := by
          refine Finsupp.sum_congr ?_
          intro j hj
          calc
            linearCombination R x (a j) ⊗ₜ[R] y j
              = (a j).sum (fun i rij ↦ (rij • x i) ⊗ₜ[R] y j) := by
                  rw [Finsupp.linearCombination_apply]
                  simpa [Finsupp.sum] using
                    (TensorProduct.sum_tmul (R := R) (s := (a j).support)
                      (m := fun i ↦ (a j) i • x i) (n := y j))
            _ = (a j).sum (fun i rij ↦ x i ⊗ₜ[R] (rij • y j)) := by
                  refine Finsupp.sum_congr ?_
                  intro i hi
                  rw [TensorProduct.smul_tmul]
    _ = a.sum (fun j aij ↦ aij.sum (fun i rij ↦
          (Finsupp.single i (Finsupp.single j rij)).sum
            (fun i' col ↦ x i' ⊗ₜ[R] linearCombination R y col))) := by
          refine Finsupp.sum_congr ?_
          intro j hj
          refine Finsupp.sum_congr ?_
          intro i hi
          calc
            x i ⊗ₜ[R] (a j i • y j)
              = x i ⊗ₜ[R] linearCombination R y (Finsupp.single j (a j i)) := by
                  simp [Finsupp.linearCombination_single, TensorProduct.tmul_smul]
            _ = (Finsupp.single i (Finsupp.single j (a j i))).sum
                  (fun i' col ↦ x i' ⊗ₜ[R] linearCombination R y col) := by
                  symm
                  simpa using
                    (Finsupp.sum_single_index
                      (m := i) (r := Finsupp.single j (a j i))
                      (h := fun i' col ↦ x i' ⊗ₜ[R] linearCombination R y col)
                      (by simp))
    _ = a.sum (fun j aij ↦
          (aij.sum (fun i rij ↦ Finsupp.single i (Finsupp.single j rij))).sum
            (fun i' col ↦ x i' ⊗ₜ[R] linearCombination R y col)) := by
          refine Finsupp.sum_congr ?_
          intro j hj
          -- Commute the inner finite sum so that each row becomes a finitely supported family on `I`.
          symm
          rw [Finsupp.sum_sum_index]
          · intro i'
            simp
          · intro i' col₁ col₂
            simp [TensorProduct.tmul_add, map_add]
    _ = (a.sum (fun j aij ↦ aij.sum (fun i rij ↦ Finsupp.single i (Finsupp.single j rij)))).sum
          (fun i col ↦ x i ⊗ₜ[R] linearCombination R y col) := by
          -- Commute the outer finite sum once to package the transposed matrix.
          symm
          rw [Finsupp.sum_sum_index]
          · intro i
            simp
          · intro i col₁ col₂
            simp [TensorProduct.tmul_add, map_add]
    _ = (kernelFamilyMatrix (R := R) (I := J) (J := I) a).sum
          (fun i col ↦ x i ⊗ₜ[R] linearCombination R y col) := by
          simp [kernelFamilyMatrix]

/-- Helper for Lemma 10.107.10: a coefficient matrix whose rows express the `m j` in the
generators `x` and whose columns are relations among the `y j` yields a vanishing tensor sum. -/
lemma generator_matrix_sum_tmul_eq_zero
    (x : I → M) (y : J → N) (m : J →₀ M) (a : J →₀ I →₀ R)
    (hm : ∀ j, m j = linearCombination R x (a j))
    (ha : ∀ i, a.sum (fun j aij ↦ aij i • y j) = 0) :
    m.sum (fun j mj ↦ mj ⊗ₜ[R] y j) = (0 : M ⊗[R] N) := by
  classical
  -- Route correction: rewrite the entire family `m` first, so later steps never compare
  -- `m.support` with `a.support`.
  calc
    m.sum (fun j mj ↦ mj ⊗ₜ[R] y j)
      = (a.sum (fun j aij ↦ Finsupp.single j (linearCombination R x aij))).sum
          (fun j mj ↦ mj ⊗ₜ[R] y j) := by
            rw [generator_matrix_rows_as_finsupp (R := R) (M := M) (I := I) (J := J) x m a hm]
    _ = a.sum (fun j aij ↦ linearCombination R x aij ⊗ₜ[R] y j) := by
          simpa using
            generator_matrix_sum_single_rows (R := R) (M := M) (N := N) (I := I) (J := J) x y a
    _ = (kernelFamilyMatrix (R := R) (I := J) (J := I) a).sum
          (fun i col ↦ x i ⊗ₜ[R] linearCombination R y col) := by
            simpa using
              generator_matrix_tensor_transpose
                (R := R) (M := M) (N := N) (I := I) (J := J) x y a
    _ = (kernelFamilyMatrix (R := R) (I := J) (J := I) a).sum
          (fun i col ↦ x i ⊗ₜ[R] (a.sum (fun j aij ↦ aij i • y j))) := by
            refine Finsupp.sum_congr ?_
            intro i hi
            rw [row_linearCombination_of_kernel_family_matrix
              (R := R) (M := N) (I := J) (J := I) y a i]
    _ = (kernelFamilyMatrix (R := R) (I := J) (J := I) a).sum
          (fun i col ↦ x i ⊗ₜ[R] 0) := by
            refine Finsupp.sum_congr ?_
            intro i hi
            rw [ha i]
    _ = 0 := by
          simp

/-- Lemma 10.107.10: let `x : I → M` and `y : J → N` be generating families of the `R`-modules
`M` and `N`. For a finitely supported family `m : J →₀ M`, the tensor relation
`∑ j, m j ⊗ y j = 0` is equivalent to the existence of a finitely supported coefficient matrix
whose rows express the `m j` in terms of the generators `x i` and whose columns give relations
among the generators `y j`. -/
theorem finsupp_sum_tmul_eq_zero_iff_exists_generator_matrix
    (x : I → M) (y : J → N) (m : J →₀ M)
    (hx : span R (Set.range x) = ⊤)
    (hy : span R (Set.range y) = ⊤) :
    (m.sum (fun j mj ↦ mj ⊗ₜ[R] y j) = (0 : M ⊗[R] N)) ↔
      ∃ a : J →₀ I →₀ R,
        (∀ j, m j = linearCombination R x (a j)) ∧
          ∀ i, a.sum (fun j aij ↦ aij i • y j) = 0 := by
  classical
  constructor
  · intro hmzero
    let π : (J →₀ R) →ₗ[R] N := Finsupp.linearCombination R y
    let σ : (I →₀ R) →ₗ[R] M := Finsupp.linearCombination R x
    -- Turn the generating hypotheses into surjectivity of the canonical linear-combination maps.
    have hπ_surj : Function.Surjective π :=
      (_root_.span_range_eq_top_iff_surjective_finsuppLinearCombination (R := R) (v := y)).1 hy
    have hσ_surj : Function.Surjective σ :=
      (_root_.span_range_eq_top_iff_surjective_finsuppLinearCombination (R := R) (v := x)).1 hx
    let u : (J →₀ R) ⊗[R] M := (TensorProduct.finsuppScalarLeft R M J).symm m
    -- The given tensor relation says exactly that the lifted element `u` is killed by `π.rTensor M`.
    have hu_mem_ker : u ∈ LinearMap.ker (π.rTensor M) := by
      rw [LinearMap.mem_ker]
      apply (TensorProduct.comm R N M).injective
      rw [comm_rTensor_finsuppScalarLeft_symm (R := R) (M := M) (N := N) (J := J) y m]
      exact hmzero
    -- Exactness lifts `u` to the tensor product with `ker π`.
    have hu_range : u ∈ LinearMap.range ((LinearMap.ker π).subtype.rTensor M) := by
      rw [← Function.Exact.linearMap_ker_eq (rTensor_exact M (LinearMap.exact_subtype_ker_map π) hπ_surj)]
      exact hu_mem_ker
    obtain ⟨v, hv⟩ := hu_range
    -- Surjectivity of `σ` lets us write that lift using the generators `x`.
    obtain ⟨w, hw⟩ := LinearMap.lTensor_surjective (LinearMap.ker π) hσ_surj v
    let b : I →₀ LinearMap.ker π := TensorProduct.finsuppScalarRight R R (LinearMap.ker π) I w
    let c : I →₀ J →₀ R :=
      Finsupp.mapRange.linearMap ((LinearMap.ker π).subtype : LinearMap.ker π →ₗ[R] J →₀ R) b
    let a : J →₀ I →₀ R := kernelFamilyMatrix c
    have hw' :
        ((TensorProduct.finsuppScalarRight R R (LinearMap.ker π) I).symm b) = w := by
      simp [b]
    have hu_eq :
        ((LinearMap.ker π).subtype.rTensor M)
            ((σ.lTensor (LinearMap.ker π))
              ((TensorProduct.finsuppScalarRight R R (LinearMap.ker π) I).symm b))
          = u := by
      rw [hw', hw, hv]
    -- Applying `finsuppScalarLeft` turns the lifted tensor equality into a row-wise identity.
    have hm_rows :
        m = b.sum (fun i bi ↦ (bi : J →₀ R).sum (fun j rij ↦ Finsupp.single j (rij • x i))) := by
      have hm_rows' := congrArg (TensorProduct.finsuppScalarLeft R M J) hu_eq
      calc
        m = TensorProduct.finsuppScalarLeft R M J
              (((LinearMap.ker π).subtype.rTensor M)
                ((σ.lTensor (LinearMap.ker π))
                  ((TensorProduct.finsuppScalarRight R R (LinearMap.ker π) I).symm b))) := by
                simpa [u] using hm_rows'.symm
        _ = b.sum (fun i bi ↦ (bi : J →₀ R).sum (fun j rij ↦ Finsupp.single j (rij • x i))) := by
              simpa [σ] using
                kernel_family_rows_raw (R := R) (M := M) (N := N) (I := I) (J := J) x (π := π) b
    refine ⟨a, ?_, ?_⟩
    · intro j
      -- Evaluate the row identity at `j`, then rewrite the resulting coefficient sum as the
      -- linear combination attached to the `j`th row of the direct matrix.
      have hmj := congrArg (fun z ↦ z j) hm_rows
      -- Evaluate the row-wise identity at the fixed index `j`.
      calc
        m j = b.sum (fun i bi ↦ ((bi : J →₀ R).sum
            (fun j' rij ↦ Finsupp.single j' (rij • x i))) j) := by
          simpa using hmj
        _ = b.sum (fun i bi ↦ (bi : J →₀ R) j • x i) := by
          refine Finsupp.sum_congr ?_
          intro i hi
          simpa [Finsupp.linearCombination_apply, Pi.single_apply, Finsupp.single_apply] using
            (Finsupp.linearCombination_single_index (R := R) (M := M) (c := x i) (a := j)
              (f := ((b i : LinearMap.ker π) : J →₀ R)))
        _ = c.sum (fun i ci ↦ ci j • x i) := by
          symm
          simpa [c] using row_sum_mapRange_subtype (R := R) (M := M) (I := I) (J := J) x b j
        _ = linearCombination R x (a j) := by
          simpa [a] using
            (row_linearCombination_of_kernel_family_matrix
              (R := R) (M := M) (I := I) (J := J) x c j).symm
    · intro i
      -- Read the `i`th column of the direct matrix and use that `b i` lies in `ker π`.
      have hci : linearCombination R y (c i) = 0 := by
        -- Membership of `b i` in `ker π` is exactly the vanishing column relation.
        simpa [c, π] using (b i).2
      -- Replace the explicit column sum by the corresponding linear combination in `N`.
      rw [column_sum_eq_linearCombination_of_kernel_family_matrix (R := R) (N := N) (I := I)
        (J := J) y c i]
      exact hci
  · intro h
    rcases h with ⟨a, hm, ha⟩
    -- Collapse the tensor relation by rewriting the rows, transposing the finite matrix sum once,
    -- and then applying the column relations.
    simpa using
      generator_matrix_sum_tmul_eq_zero
        (R := R) (M := M) (N := N) (I := I) (J := J) x y m a hm ha

end
