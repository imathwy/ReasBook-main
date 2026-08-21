/-
  Copyright (c) 2026 Zichen Wang. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Zichen Wang, Wanli Ma, Yi Yuan, Zaiwen Wen
-/

import Mathlib

section Chap06
section Section01

/-- Definition 6.1 (Row vectors): for a natural number `n`, an `n`-dimensional row
vector over `ℝ` is represented as a `1 × n` matrix; vector addition,
scalar multiplication, the zero vector, and additive inverses are the inherited
pointwise operations. -/
abbrev RowVector (n : ℕ) : Type := Matrix (Fin 1) (Fin n) ℝ

/-- Helper for Lemma 6.1: additive-group identities for vectors `Fin n → ℝ`. -/
lemma helperForLemma_6_1_additiveGroupIdentities (n : ℕ) :
    ∀ x y z : Fin n → ℝ,
      x + y = y + x ∧
        (x + y) + z = x + (y + z) ∧
          x + 0 = x ∧
            0 + x = x ∧
              x + (-x) = 0 ∧
                (-x) + x = 0 := by
  intro x y z
  constructor
  · simpa using add_comm x y
  constructor
  · simpa using add_assoc x y z
  constructor
  · simpa using add_zero x
  constructor
  · simpa using zero_add x
  constructor
  · simpa using add_neg_cancel x
  · simpa using neg_add_cancel x

/-- Helper for Lemma 6.1: scalar associativity and scalar unit on `Fin n → ℝ`. -/
lemma helperForLemma_6_1_scalarAssociativityUnit (n : ℕ) :
    ∀ x : Fin n → ℝ, ∀ c d : ℝ,
      (c * d) • x = c • (d • x) ∧
        (1 : ℝ) • x = x := by
  intro x c d
  constructor
  · simpa using mul_smul c d x
  · simpa using one_smul ℝ x

/-- Helper for Lemma 6.1: scalar distributivity identities on `Fin n → ℝ`. -/
lemma helperForLemma_6_1_scalarDistributivity (n : ℕ) :
    ∀ x y : Fin n → ℝ, ∀ c d : ℝ,
      c • (x + y) = c • x + c • y ∧
        (c + d) • x = c • x + d • x := by
  intro x y c d
  constructor
  · simpa using smul_add c x y
  · simpa using add_smul c d x

/-- Lemma 6.1: `ℝ^n` is a vector space over `ℝ`; for all `x y z : Fin n → ℝ` and
`c d : ℝ`, vector addition is commutative and associative, `0` is an additive
identity, `-x` is an additive inverse, scalar multiplication is associative,
distributes over vector and scalar addition, and `1` acts as the identity
scalar. -/
lemma rowVector_real_vector_space_identities (n : ℕ) :
    ∀ x y z : Fin n → ℝ, ∀ c d : ℝ,
      x + y = y + x ∧
        (x + y) + z = x + (y + z) ∧
          x + 0 = x ∧
            0 + x = x ∧
              x + (-x) = 0 ∧
                (-x) + x = 0 ∧
                  (c * d) • x = c • (d • x) ∧
                    c • (x + y) = c • x + c • y ∧
                      (c + d) • x = c • x + d • x ∧
                        (1 : ℝ) • x = x := by
  intro x y z c d
  have hAdd := helperForLemma_6_1_additiveGroupIdentities n x y z
  have hAssocUnit := helperForLemma_6_1_scalarAssociativityUnit n x c d
  have hDistrib := helperForLemma_6_1_scalarDistributivity n x y c d
  rcases hAdd with ⟨hxy, hxyz, hx0, h0x, hxneg, hnegx⟩
  rcases hAssocUnit with ⟨hsmulAssoc, hsmulOne⟩
  rcases hDistrib with ⟨hsmulAdd, haddSmul⟩
  constructor
  · exact hxy
  constructor
  · exact hxyz
  constructor
  · exact hx0
  constructor
  · exact h0x
  constructor
  · exact hxneg
  constructor
  · exact hnegx
  constructor
  · exact hsmulAssoc
  constructor
  · exact hsmulAdd
  constructor
  · exact haddSmul
  · exact hsmulOne

/-- An `n`-dimensional column vector over `ℝ`, represented as an `n × 1` matrix. -/
abbrev ColumnVector (n : ℕ) : Type := Matrix (Fin n) (Fin 1) ℝ

/-- Definition 6.2 (Transpose): for `n : ℕ` and a row vector
`x = (x₁, …, xₙ) : RowVector n`, its transpose `xᵀ` is the `n × 1` column vector
with the same coordinates. Equivalently, an `n`-dimensional column vector is a
vector of the form `xᵀ` for some row vector `x`. -/
def rowVectorTranspose {n : ℕ} (x : RowVector n) : ColumnVector n := Matrix.transpose x

/-- Every `n`-dimensional column vector is the transpose of a row vector. -/
lemma columnVector_exists_as_transpose (n : ℕ) (y : ColumnVector n) :
    ∃ x : RowVector n, rowVectorTranspose x = y := by
  refine ⟨Matrix.transpose y, ?_⟩
  simpa [rowVectorTranspose] using Matrix.transpose_transpose y

/-- Definition 6.3 (Standard basis vectors of `ℝ^n`): for `j : Fin n`, the
standard basis row vector `e_j` has entries `(e_j)_i = 1` if `i = j` and
`(e_j)_i = 0` otherwise. -/
def standardBasisRowVector (n : ℕ) (j : Fin n) : RowVector n :=
  fun _ i => if i = j then 1 else 0

/-- Every row vector in `ℝ^n` is the sum of its coordinates times the standard
basis row vectors. -/
theorem rowVector_eq_sum_standardBasisRowVector (n : ℕ) (x : RowVector n) :
    x = ∑ j : Fin n, (x 0 j) • standardBasisRowVector n j := by
  ext r i
  fin_cases r
  simp [Matrix.sum_apply, standardBasisRowVector]

/-- The transpose of a row vector is the corresponding linear combination of
the transposed standard basis vectors. -/
theorem rowVectorTranspose_eq_sum_standardBasisTranspose (n : ℕ) (x : RowVector n) :
    rowVectorTranspose x =
      ∑ j : Fin n, (x 0 j) • rowVectorTranspose (standardBasisRowVector n j) := by
  simpa [rowVectorTranspose, Matrix.transpose_sum] using
    congrArg Matrix.transpose (rowVector_eq_sum_standardBasisRowVector n x)

/-- Definition 6.4 (Linear transformation): a function `T : ℝ^n → ℝ^m` is linear
iff for all `x y : ℝ^n` and `c : ℝ`, (i) `T (x + y) = T x + T y`
and (ii) `T (c • x) = c • T x`. -/
def IsLinearTransformation {n m : ℕ} (T : (Fin n → ℝ) → (Fin m → ℝ)) : Prop :=
  (∀ x y : Fin n → ℝ, T (x + y) = T x + T y) ∧
    ∀ (c : ℝ) (x : Fin n → ℝ), T (c • x) = c • T x

/-- Definition 6.5 (Matrices): for positive natural numbers `m, n`, an `m × n`
matrix over a set `S` is a family `A = (a i j)` of elements of `S` indexed by
`i : Fin m` and `j : Fin n`. A `1 × n` matrix is an `n`-dimensional row vector,
and an `n × 1` matrix is an `n`-dimensional column vector. -/
abbrev MatrixOver (S : Type*) (m n : ℕ+) := Matrix (Fin m) (Fin n) S

/-- Definition 6.6 (Matrix product): for `m n p : ℕ`, if `A` is an `m × n`
matrix and `B` is an `n × p` matrix (over `ℝ`), then `matrixProduct A B` is the
`m × p` matrix with entries `(matrixProduct A B) i k = ∑ j : Fin n, A i j * B j k`.
In particular, when `p = 1`, this gives matrix-column-vector multiplication
`(A xᵀ) i = ∑ j : Fin n, A i j * xᵀ j 0`. -/
abbrev matrixProduct {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin p) ℝ) :
    Matrix (Fin m) (Fin p) ℝ :=
  A * B

/-- Helper for Lemma 6.2: convert `IsLinearTransformation` to a mathlib `LinearMap`. -/
def helperForLemma_6_2_linearMapFromIsLinearTransformation {n m : ℕ}
    (T : (Fin n → ℝ) → (Fin m → ℝ)) (hT : IsLinearTransformation T) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
  {
    toFun := T
    map_add' := hT.1
    map_smul' := hT.2
  }

/-- Helper for Lemma 6.2: the matrix from `LinearMap.toMatrix'` represents `T`. -/
lemma helperForLemma_6_2_matrixCandidateRepresentsT {n m : ℕ}
    (T : (Fin n → ℝ) → (Fin m → ℝ)) (hT : IsLinearTransformation T) :
    ∀ x : Fin n → ℝ,
      T x =
        Matrix.mulVec
          (LinearMap.toMatrix'
            (helperForLemma_6_2_linearMapFromIsLinearTransformation T hT)) x := by
  intro x
  have hMulVec :
      Matrix.mulVec
          (LinearMap.toMatrix'
            (helperForLemma_6_2_linearMapFromIsLinearTransformation T hT)) x =
        helperForLemma_6_2_linearMapFromIsLinearTransformation T hT x := by
    simpa using
      (LinearMap.toMatrix'_mulVec
        (helperForLemma_6_2_linearMapFromIsLinearTransformation T hT) x)
  calc
    T x = helperForLemma_6_2_linearMapFromIsLinearTransformation T hT x := rfl
    _ =
        Matrix.mulVec
          (LinearMap.toMatrix'
            (helperForLemma_6_2_linearMapFromIsLinearTransformation T hT)) x := by
          simpa using hMulVec.symm

/-- Helper for Lemma 6.2: a representing matrix yields the corresponding
`Matrix.toLin'` equality. -/
lemma helperForLemma_6_2_toLin_eq_of_representsT {n m : ℕ}
    (T : (Fin n → ℝ) → (Fin m → ℝ)) (hT : IsLinearTransformation T)
    (B : Matrix (Fin m) (Fin n) ℝ)
    (hB : ∀ x : Fin n → ℝ, T x = Matrix.mulVec B x) :
    Matrix.toLin' B =
      helperForLemma_6_2_linearMapFromIsLinearTransformation T hT := by
  apply LinearMap.ext
  intro x
  calc
    (Matrix.toLin' B) x = Matrix.mulVec B x := by
      simp [Matrix.toLin'_apply]
    _ = T x := by
      exact (hB x).symm
    _ = helperForLemma_6_2_linearMapFromIsLinearTransformation T hT x := rfl

/-- Helper for Lemma 6.2: matrix representation of `T` is unique. -/
lemma helperForLemma_6_2_representation_unique {n m : ℕ}
    (T : (Fin n → ℝ) → (Fin m → ℝ)) (hT : IsLinearTransformation T)
    (B : Matrix (Fin m) (Fin n) ℝ)
    (hB : ∀ x : Fin n → ℝ, T x = Matrix.mulVec B x) :
    B =
      LinearMap.toMatrix'
        (helperForLemma_6_2_linearMapFromIsLinearTransformation T hT) := by
  have hToLinB :
      Matrix.toLin' B =
        helperForLemma_6_2_linearMapFromIsLinearTransformation T hT :=
    helperForLemma_6_2_toLin_eq_of_representsT T hT B hB
  have hToLinA :
      Matrix.toLin'
          (LinearMap.toMatrix'
            (helperForLemma_6_2_linearMapFromIsLinearTransformation T hT)) =
        helperForLemma_6_2_linearMapFromIsLinearTransformation T hT := by
    simpa using
      (Matrix.toLin'_toMatrix'
        (helperForLemma_6_2_linearMapFromIsLinearTransformation T hT))
  have hEqToLin :
      Matrix.toLin' B =
        Matrix.toLin'
          (LinearMap.toMatrix'
            (helperForLemma_6_2_linearMapFromIsLinearTransformation T hT)) := by
    calc
      Matrix.toLin' B =
          helperForLemma_6_2_linearMapFromIsLinearTransformation T hT :=
        hToLinB
      _ =
          Matrix.toLin'
            (LinearMap.toMatrix'
              (helperForLemma_6_2_linearMapFromIsLinearTransformation T hT)) := by
          exact hToLinA.symm
  exact (Matrix.toLin').injective hEqToLin

/-- Lemma 6.2: if `T : ℝ^n → ℝ^m` is a linear transformation, then there exists a
unique matrix `A : ℝ^{m × n}` such that `T x = A x` for every `x : ℝ^n`. -/
theorem linearTransformation_existsUnique_matrixRepresentation {n m : ℕ}
    (T : (Fin n → ℝ) → (Fin m → ℝ)) (hT : IsLinearTransformation T) :
    ∃! A : Matrix (Fin m) (Fin n) ℝ, ∀ x : Fin n → ℝ, T x = Matrix.mulVec A x := by
  refine ⟨
    LinearMap.toMatrix' (helperForLemma_6_2_linearMapFromIsLinearTransformation T hT),
    ?_,
    ?_
  ⟩
  · exact helperForLemma_6_2_matrixCandidateRepresentsT T hT
  · intro B hB
    exact helperForLemma_6_2_representation_unique T hT B hB

/-- Lemma 6.3: for matrices `A` and `B` over the same field, if `L_M` denotes
left-multiplication by `M` on compatible column vectors, then
`L_A ∘ L_B = L_{AB}` as linear maps `𝔽^p → 𝔽^m`. -/
theorem leftMultiplication_comp_eq_leftMultiplication_mul {𝔽 : Type*} [Field 𝔽]
    {m n p : ℕ} (A : Matrix (Fin m) (Fin n) 𝔽) (B : Matrix (Fin n) (Fin p) 𝔽) :
    (Matrix.mulVecLin A).comp (Matrix.mulVecLin B) = Matrix.mulVecLin (A * B) := by
  simpa using (Matrix.mulVecLin_mul A B).symm

/-- Helper for Proposition 6.1: scaling by a fixed scalar preserves addition on
`Fin n → ℝ`. -/
lemma helperForProposition_6_1_fixedScalar_add (n : ℕ) (a : ℝ)
    (x y : Fin n → ℝ) :
    a • (x + y) = a • x + a • y := by
  simpa using smul_add a x y

/-- Helper for Proposition 6.1: scaling by a fixed scalar commutes with an
external scalar multiplication on `Fin n → ℝ`. -/
lemma helperForProposition_6_1_fixedScalar_smul (n : ℕ) (a c : ℝ)
    (x : Fin n → ℝ) :
    a • (c • x) = c • (a • x) := by
  calc
    a • (c • x) = (a * c) • x := by simpa [smul_smul]
    _ = (c * a) • x := by rw [mul_comm]
    _ = c • (a • x) := by simpa [smul_smul]

/-- Helper for Proposition 6.1: for any dimension `n` and scalar `a`, the map
`x ↦ a • x` is linear. -/
lemma helperForProposition_6_1_fixedScalar_isLinear (n : ℕ) (a : ℝ) :
    IsLinearTransformation (fun x : Fin n → ℝ => a • x) := by
  constructor
  · intro x y
    exact helperForProposition_6_1_fixedScalar_add n a x y
  · intro c x
    exact helperForProposition_6_1_fixedScalar_smul n a c x

/-- Proposition 6.1: the map `T₁ : ℝ^3 → ℝ^3` defined by `T₁ x = 5x` is a linear
transformation. -/
theorem t1_isLinearTransformation :
    IsLinearTransformation (fun x : Fin 3 → ℝ => (5 : ℝ) • x) := by
  simpa using helperForProposition_6_1_fixedScalar_isLinear 3 (5 : ℝ)

/-- Helper for Proposition 6.2: the rotation map `x ↦ (-x₂, x₁)` preserves
vector addition on `ℝ²`. -/
lemma helperForProposition_6_2_rotate_add (x y : Fin 2 → ℝ) :
    (fun z : Fin 2 → ℝ => ![-z 1, z 0]) (x + y) =
      (fun z : Fin 2 → ℝ => ![-z 1, z 0]) x +
        (fun z : Fin 2 → ℝ => ![-z 1, z 0]) y := by
  ext i
  fin_cases i <;> simp [add_comm, add_left_comm, add_assoc]

/-- Helper for Proposition 6.2: the rotation map `x ↦ (-x₂, x₁)` commutes with
scalar multiplication on `ℝ²`. -/
lemma helperForProposition_6_2_rotate_smul (c : ℝ) (x : Fin 2 → ℝ) :
    (fun z : Fin 2 → ℝ => ![-z 1, z 0]) (c • x) =
      c • (fun z : Fin 2 → ℝ => ![-z 1, z 0]) x := by
  ext i
  fin_cases i <;> simp

/-- Proposition 6.2: let `T₂ : ℝ² → ℝ²` be the map that rotates each vector
about the origin by angle `π/2` counterclockwise, i.e. `T₂(x₁, x₂) = (-x₂, x₁)`.
Then `T₂` is a linear transformation. -/
theorem t2_rotatePiOverTwo_isLinearTransformation :
    IsLinearTransformation (fun x : Fin 2 → ℝ => ![-x 1, x 0]) := by
  constructor
  · intro x y
    exact helperForProposition_6_2_rotate_add x y
  · intro c x
    exact helperForProposition_6_2_rotate_smul c x

/-- Helper for Proposition 6.3: dropping the third coordinate preserves
vector addition on `ℝ³`. -/
lemma helperForProposition_6_3_dropThird_add (x y : Fin 3 → ℝ) :
    (fun z : Fin 3 → ℝ => ![z 0, z 1]) (x + y) =
      (fun z : Fin 3 → ℝ => ![z 0, z 1]) x +
        (fun z : Fin 3 → ℝ => ![z 0, z 1]) y := by
  ext i
  fin_cases i <;> simp

/-- Helper for Proposition 6.3: dropping the third coordinate commutes with
scalar multiplication on `ℝ³`. -/
lemma helperForProposition_6_3_dropThird_smul (c : ℝ) (x : Fin 3 → ℝ) :
    (fun z : Fin 3 → ℝ => ![z 0, z 1]) (c • x) =
      c • (fun z : Fin 3 → ℝ => ![z 0, z 1]) x := by
  ext i
  fin_cases i <;> simp

/-- Proposition 6.3: define `T₃ : ℝ³ → ℝ²` by `T₃(x, y, z) = (x, y)`.
Then `T₃` is a linear transformation, i.e. for all `u v : ℝ³` and `c : ℝ`,
`T₃ (u + v) = T₃ u + T₃ v` and `T₃ (c • u) = c • T₃ u`. -/
theorem t3_dropThirdCoordinate_isLinearTransformation :
    IsLinearTransformation (fun x : Fin 3 → ℝ => ![x 0, x 1]) := by
  constructor
  · intro x y
    exact helperForProposition_6_3_dropThird_add x y
  · intro c x
    exact helperForProposition_6_3_dropThird_smul c x

/-- Helper for Proposition 6.4: the embedding map `x ↦ (x₁, x₂, 0)` preserves
vector addition on `ℝ²`. -/
lemma helperForProposition_6_4_embed_add (x y : Fin 2 → ℝ) :
    (fun z : Fin 2 → ℝ => ![z 0, z 1, 0]) (x + y) =
      (fun z : Fin 2 → ℝ => ![z 0, z 1, 0]) x +
        (fun z : Fin 2 → ℝ => ![z 0, z 1, 0]) y := by
  ext i
  fin_cases i <;> simp

/-- Helper for Proposition 6.4: the embedding map `x ↦ (x₁, x₂, 0)` commutes
with scalar multiplication on `ℝ²`. -/
lemma helperForProposition_6_4_embed_smul (c : ℝ) (x : Fin 2 → ℝ) :
    (fun z : Fin 2 → ℝ => ![z 0, z 1, 0]) (c • x) =
      c • (fun z : Fin 2 → ℝ => ![z 0, z 1, 0]) x := by
  ext i
  fin_cases i <;> simp

/-- Helper for Proposition 6.4: the embedding map `x ↦ (x₁, x₂, 0)` is linear. -/
lemma helperForProposition_6_4_embed_isLinear :
    IsLinearTransformation (fun x : Fin 2 → ℝ => ![x 0, x 1, 0]) := by
  constructor
  · intro x y
    exact helperForProposition_6_4_embed_add x y
  · intro c x
    exact helperForProposition_6_4_embed_smul c x

/-- Proposition 6.4: define `T₄ : ℝ² → ℝ³` by `T₄(x, y) = (x, y, 0)`.
Then `T₄` is a linear transformation, i.e. for all `u v : ℝ²` and `c : ℝ`,
`T₄ (u + v) = T₄ u + T₄ v` and `T₄ (c • u) = c • T₄ u`. -/
theorem t4_embedInThreeSpace_isLinearTransformation :
    IsLinearTransformation (fun x : Fin 2 → ℝ => ![x 0, x 1, 0]) := by
  simpa using helperForProposition_6_4_embed_isLinear

/-- Helper for Proposition 6.5: the identity map on `Fin n → ℝ` preserves
addition. -/
lemma helperForProposition_6_5_identity_add (n : ℕ) (x y : Fin n → ℝ) :
    (fun z : Fin n → ℝ => z) (x + y) =
      (fun z : Fin n → ℝ => z) x + (fun z : Fin n → ℝ => z) y := by
  rfl

/-- Helper for Proposition 6.5: the identity map on `Fin n → ℝ` commutes with
scalar multiplication. -/
lemma helperForProposition_6_5_identity_smul (n : ℕ) (c : ℝ) (x : Fin n → ℝ) :
    (fun z : Fin n → ℝ => z) (c • x) =
      c • (fun z : Fin n → ℝ => z) x := by
  rfl

/-- Helper for Proposition 6.5: for each `n`, the identity map on `Fin n → ℝ`
is linear. -/
lemma helperForProposition_6_5_identity_isLinear (n : ℕ) :
    IsLinearTransformation (fun x : Fin n → ℝ => x) := by
  constructor
  · intro x y
    exact helperForProposition_6_5_identity_add n x y
  · intro c x
    exact helperForProposition_6_5_identity_smul n c x

/-- Proposition 6.5: for each `n : ℕ`, the map `I_n : ℝ^n → ℝ^n` defined by
`I_n x = x` for all `x` is a linear transformation. -/
theorem identityMap_isLinearTransformation (n : ℕ) :
    IsLinearTransformation (fun x : Fin n → ℝ => x) := by
  simpa using helperForProposition_6_5_identity_isLinear n

/-- Proposition 6.6: if `T : ℝ^n → ℝ^m` and `S : ℝ^p → ℝ^n` are linear
transformations, then their composition `TS`, defined by `(TS) x = T (S x)` for
all `x : ℝ^p`, is also a linear transformation. -/
theorem composition_isLinearTransformation {p n m : ℕ}
    (T : (Fin n → ℝ) → (Fin m → ℝ)) (S : (Fin p → ℝ) → (Fin n → ℝ))
    (hT : IsLinearTransformation T) (hS : IsLinearTransformation S) :
    IsLinearTransformation (fun x : Fin p → ℝ => T (S x)) := by
  constructor
  · intro x y
    calc
      T (S (x + y)) = T (S x + S y) := by rw [hS.1 x y]
      _ = T (S x) + T (S y) := by rw [hT.1 (S x) (S y)]
  · intro c x
    calc
      T (S (c • x)) = T (c • S x) := by rw [hS.2 c x]
      _ = c • T (S x) := by rw [hT.2 c (S x)]

/-- Helper for Proposition 6.7: the operator norm of `T` bounds `‖T x‖` by
`‖LinearMap.toContinuousLinearMap T‖ * ‖x‖`. -/
lemma helperForProposition_6_7_bound_by_opNorm {n m : ℕ}
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖T x‖ ≤ ‖LinearMap.toContinuousLinearMap T‖ * ‖x‖ := by
  simpa using (LinearMap.toContinuousLinearMap T).le_opNorm x

/-- Helper for Proposition 6.7: replacing the operator norm by
`‖LinearMap.toContinuousLinearMap T‖ + 1` preserves the bound. -/
lemma helperForProposition_6_7_bound_by_opNormPlusOne {n m : ℕ}
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖T x‖ ≤ (‖LinearMap.toContinuousLinearMap T‖ + 1) * ‖x‖ := by
  have hBound : ‖T x‖ ≤ ‖LinearMap.toContinuousLinearMap T‖ * ‖x‖ :=
    helperForProposition_6_7_bound_by_opNorm T x
  have hCoeff : ‖LinearMap.toContinuousLinearMap T‖ ≤
      ‖LinearMap.toContinuousLinearMap T‖ + 1 := by
    exact le_add_of_nonneg_right zero_le_one
  have hNormNonneg : 0 ≤ ‖x‖ := norm_nonneg x
  have hMul : ‖LinearMap.toContinuousLinearMap T‖ * ‖x‖ ≤
      (‖LinearMap.toContinuousLinearMap T‖ + 1) * ‖x‖ := by
    exact mul_le_mul_of_nonneg_right hCoeff hNormNonneg
  exact le_trans hBound hMul

/-- Helper for Proposition 6.7: the constant
`‖LinearMap.toContinuousLinearMap T‖ + 1` is strictly positive. -/
lemma helperForProposition_6_7_positive_constant {n m : ℕ}
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    0 < ‖LinearMap.toContinuousLinearMap T‖ + 1 := by
  exact add_pos_of_nonneg_of_pos (norm_nonneg (LinearMap.toContinuousLinearMap T))
    zero_lt_one

/-- Helper for Proposition 6.7: every linear map between these finite-dimensional
Euclidean spaces is continuous. -/
lemma helperForProposition_6_7_continuous_apply {n m : ℕ}
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    Continuous (fun x : EuclideanSpace ℝ (Fin n) => T x) := by
  simpa using T.continuous_of_finiteDimensional

/-- Proposition 6.7: if `T : ℝ^n → ℝ^m` is a linear transformation, then there
exists a constant `M > 0` such that `‖T x‖ ≤ M * ‖x‖` for all `x : ℝ^n`.
Consequently, `T` is continuous on `ℝ^n`. -/
theorem linearTransformation_exists_pos_bound_and_continuous {n m : ℕ}
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    ∃ M > 0,
      (∀ x : EuclideanSpace ℝ (Fin n), ‖T x‖ ≤ M * ‖x‖) ∧
        Continuous (fun x : EuclideanSpace ℝ (Fin n) => T x) := by
  refine ⟨‖LinearMap.toContinuousLinearMap T‖ + 1,
    helperForProposition_6_7_positive_constant T, ?_⟩
  constructor
  · intro x
    exact helperForProposition_6_7_bound_by_opNormPlusOne T x
  · exact helperForProposition_6_7_continuous_apply T

end Section01
end Chap06
