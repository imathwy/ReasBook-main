import Mathlib
import LinearRepresentations_Serre_1977.Chap12.Corollary_12_12_2_2
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_5.QuaternionicSchurModel

noncomputable section

open scoped MonoidAlgebra Quaternion TensorProduct

universe u v w

namespace Representation

local notation "Q8" => QuaternionGroup 2

section

variable (K : Type) [Field K] [Algebra ℚ K]

/-- Helper for Exercise 12-12.2-5: the quaternionic `Q8` character viewed over an arbitrary
`ℚ`-algebra `K`. -/
def quaternionGroupTwoQuaternionCharacterOver : Q8 → K
  | QuaternionGroup.a i => if i = 0 then 2 else if i = 2 then -2 else 0
  | QuaternionGroup.xa _ => 0

/-- Helper for Exercise 12-12.2-5: the `K`-valued quaternionic character takes the value `2` at
`1`, the value `-2` at the central involution `-1 = a 2`, and vanishes on every other element of
`Q8`. -/
theorem quaternionGroupTwoQuaternionCharacterOver_apply (s : Q8) :
    quaternionGroupTwoQuaternionCharacterOver (K := K) s =
      if s = 1 then 2 else if s = QuaternionGroup.a (2 : ZMod 4) then -2 else 0 := by
  -- Reuse the same explicit normal-form split as for the complex character table.
  cases s with
  | a i =>
      -- On the `a i` branch the character only distinguishes `i = 0` and `i = 2`.
      by_cases h0 : i = 0
      · subst h0
        simp [quaternionGroupTwoQuaternionCharacterOver]
      · by_cases h2 : i = 2
        · subst h2
          have h_ne_one : (QuaternionGroup.a (2 : ZMod 4) : Q8) ≠ 1 := by
              intro h
              rw [← QuaternionGroup.a_zero] at h
              injection h with h'
              exact h0 h'
          calc
            quaternionGroupTwoQuaternionCharacterOver (K := K) (QuaternionGroup.a (2 : ZMod 4)) =
                -2 := by
                  simp [quaternionGroupTwoQuaternionCharacterOver, h0]
            _ = if (QuaternionGroup.a (2 : ZMod 4) : Q8) = 1 then 2
                  else if (QuaternionGroup.a (2 : ZMod 4) : Q8) =
                      QuaternionGroup.a (2 : ZMod 4) then -2 else 0 := by
                    simp [h_ne_one]
        · have h_ne_one : QuaternionGroup.a i ≠ (1 : Q8) := by
            intro h
            rw [← QuaternionGroup.a_zero] at h
            injection h with h'
            exact h0 h'
          calc
            quaternionGroupTwoQuaternionCharacterOver (K := K) (QuaternionGroup.a i) = 0 := by
              simp [quaternionGroupTwoQuaternionCharacterOver, h0, h2]
            _ = if (QuaternionGroup.a i : Q8) = 1 then 2
                  else if (QuaternionGroup.a i : Q8) = QuaternionGroup.a (2 : ZMod 4)
                    then -2 else 0 := by
                      simp [h_ne_one, h2]
  | xa i =>
      -- On the `xa i` branch the character vanishes and these elements are never `1`.
      have h_ne_one : QuaternionGroup.xa i ≠ (1 : Q8) := by
        intro h
        rw [← QuaternionGroup.a_zero] at h
        cases h
      calc
        quaternionGroupTwoQuaternionCharacterOver (K := K) (QuaternionGroup.xa i) = 0 := by
          simp [quaternionGroupTwoQuaternionCharacterOver]
        _ = if (QuaternionGroup.xa i : Q8) = 1 then 2
              else if (QuaternionGroup.xa i : Q8) = QuaternionGroup.a (2 : ZMod 4) then -2 else 0 := by
                simp [h_ne_one]

/-- Helper for Exercise 12-12.2-5: if the `K`-valued quaternionic character is realized by a
finite-dimensional `K`-representation of `Q8`, then `-1` is a sum of two squares in `K`. -/
theorem quaternionGroupTwoQuaternionCharacterOver_realizable_implies_neg_one_sum_two_squares
    (τ : Rep.{w} K Q8) [FiniteDimensional K τ]
    (hτchar : τ.ρ.character = quaternionGroupTwoQuaternionCharacterOver (K := K)) :
    ∃ a b : K, -(1 : K) = a ^ 2 + b ^ 2 := by
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  let A : τ →ₗ[K] τ := τ.ρ (QuaternionGroup.a (1 : ZMod 4))
  let B : τ →ₗ[K] τ := τ.ρ (QuaternionGroup.xa (0 : ZMod 4))
  have hchar_one : τ.ρ.character (1 : Q8) = (2 : K) := by
    -- The quaternionic character has degree `2`.
    simpa [quaternionGroupTwoQuaternionCharacterOver] using congrFun hτchar (1 : Q8)
  have hdim : Module.finrank K τ = 2 := by
    -- The value of the character at the identity is the dimension of the representation.
    have hdimK : (Module.finrank K τ : K) = 2 := by
      simpa [Representation.char_one] using hchar_one
    exact Nat.cast_injective hdimK
  have hchar_a_one : τ.ρ.character (QuaternionGroup.a (1 : ZMod 4)) = (0 : K) := by
    -- The quaternionic character vanishes away from `±1`.
    have h10 : (1 : ZMod 4) ≠ 0 := by decide
    have h12 : (1 : ZMod 4) ≠ 2 := by decide
    simpa [quaternionGroupTwoQuaternionCharacterOver, h10, h12] using
      congrFun hτchar (QuaternionGroup.a (1 : ZMod 4))
  have hchar_xa_zero : τ.ρ.character (QuaternionGroup.xa (0 : ZMod 4)) = (0 : K) := by
    -- The same vanishing holds for the `j`-generator.
    simpa [quaternionGroupTwoQuaternionCharacterOver] using
      congrFun hτchar (QuaternionGroup.xa (0 : ZMod 4))
  have hchar_a_two : τ.ρ.character (QuaternionGroup.a (2 : ZMod 4)) = (-2 : K) := by
    -- The central involution has character value `-2`.
    have h20 : (2 : ZMod 4) ≠ 0 := by decide
    simpa [quaternionGroupTwoQuaternionCharacterOver, h20] using
      congrFun hτchar (QuaternionGroup.a (2 : ZMod 4))
  have ha_sq :
      (QuaternionGroup.a (1 : ZMod 4) : Q8) * QuaternionGroup.a (1 : ZMod 4) =
        QuaternionGroup.a (2 : ZMod 4) := by
    native_decide
  have hxa_sq :
      (QuaternionGroup.xa (0 : ZMod 4) : Q8) * QuaternionGroup.xa (0 : ZMod 4) =
        QuaternionGroup.a (2 : ZMod 4) := by
    native_decide
  have hanticomm_group :
      (QuaternionGroup.xa (0 : ZMod 4) : Q8) * QuaternionGroup.a (1 : ZMod 4) =
        QuaternionGroup.a (2 : ZMod 4) *
          (QuaternionGroup.a (1 : ZMod 4) * QuaternionGroup.xa (0 : ZMod 4)) := by
    native_decide
  have hA_sq_trace : LinearMap.trace K τ (A * A) = (-2 : K) := by
    -- Squaring `a 1` gives the central involution `a 2`.
    calc
      LinearMap.trace K τ (A * A) =
          τ.ρ.character
            ((QuaternionGroup.a (1 : ZMod 4) : Q8) * QuaternionGroup.a (1 : ZMod 4)) := by
              change LinearMap.trace K τ (τ.ρ (QuaternionGroup.a (1 : ZMod 4)) *
                τ.ρ (QuaternionGroup.a (1 : ZMod 4))) =
                LinearMap.trace K τ (τ.ρ
                  ((QuaternionGroup.a (1 : ZMod 4) : Q8) * QuaternionGroup.a (1 : ZMod 4)))
              rw [(τ.ρ.map_mul _ _).symm]
      _ = τ.ρ.character (QuaternionGroup.a (2 : ZMod 4)) := by rw [ha_sq]
      _ = (-2 : K) := hchar_a_two
  have hB_sq_trace : LinearMap.trace K τ (B * B) = (-2 : K) := by
    -- Squaring `xa 0` gives the same central involution.
    calc
      LinearMap.trace K τ (B * B) =
          τ.ρ.character
            ((QuaternionGroup.xa (0 : ZMod 4) : Q8) * QuaternionGroup.xa (0 : ZMod 4)) := by
              change LinearMap.trace K τ (τ.ρ (QuaternionGroup.xa (0 : ZMod 4)) *
                τ.ρ (QuaternionGroup.xa (0 : ZMod 4))) =
                LinearMap.trace K τ (τ.ρ
                  ((QuaternionGroup.xa (0 : ZMod 4) : Q8) * QuaternionGroup.xa (0 : ZMod 4)))
              rw [(τ.ρ.map_mul _ _).symm]
      _ = τ.ρ.character (QuaternionGroup.a (2 : ZMod 4)) := by rw [hxa_sq]
      _ = (-2 : K) := hchar_a_two
  have hA2 : A * A = (-1 : K) • LinearMap.id := by
    -- The trace-zero square lemma upgrades the character data to the exact relation `A² = -1`.
    exact square_eq_neg_one_of_trace_zero_of_square_trace_neg_two
      (K := K) (V := τ) hdim A hchar_a_one hA_sq_trace
  have hB2 : B * B = (-1 : K) • LinearMap.id := by
    -- The same argument applies to `B = τ(xa 0)`.
    exact square_eq_neg_one_of_trace_zero_of_square_trace_neg_two
      (K := K) (V := τ) hdim B hchar_xa_zero hB_sq_trace
  have hcentral : τ.ρ (QuaternionGroup.a (2 : ZMod 4)) = (-1 : K) • LinearMap.id := by
    -- The central involution acts by `-1` because it is the square of `a 1`.
    calc
      τ.ρ (QuaternionGroup.a (2 : ZMod 4)) =
          τ.ρ ((QuaternionGroup.a (1 : ZMod 4) : Q8) * QuaternionGroup.a (1 : ZMod 4)) := by
            rw [ha_sq]
      _ = A * A := by
            simpa [A] using (τ.ρ.map_mul (QuaternionGroup.a (1 : ZMod 4))
              (QuaternionGroup.a (1 : ZMod 4)))
      _ = (-1 : K) • LinearMap.id := hA2
  have hBA : B * A = -(A * B) := by
    -- Route correction: use the source relation `ji = (-1) (ij)` and identify the central
    -- involution with `-1` through the already established square relation.
    calc
      B * A =
          τ.ρ
            ((QuaternionGroup.xa (0 : ZMod 4) : Q8) * QuaternionGroup.a (1 : ZMod 4)) := by
              simpa [A, B] using (τ.ρ.map_mul (QuaternionGroup.xa (0 : ZMod 4))
                (QuaternionGroup.a (1 : ZMod 4))).symm
      _ =
          τ.ρ
            (QuaternionGroup.a (2 : ZMod 4) *
              (QuaternionGroup.a (1 : ZMod 4) * QuaternionGroup.xa (0 : ZMod 4))) := by
                rw [hanticomm_group]
      _ = τ.ρ (QuaternionGroup.a (2 : ZMod 4)) * (A * B) := by
            rw [τ.ρ.map_mul, τ.ρ.map_mul]
      _ = ((-1 : K) • LinearMap.id) * (A * B) := by rw [hcentral]
      _ = (-1 : K) • (A * B) := by
            ext x
            rfl
      _ = -(A * B) := by simp
  -- The existing `2`-dimensional anticommuting-matrix criterion now applies verbatim.
  exact neg_one_sum_two_squares_of_anticommuting_square_neg_one
    (hdim := hdim) (A := A) (B := B) hA2 hB2 hBA

/-- Helper for Exercise 12-12.2-5: the standard matrix playing the role of the quaternionic unit
`i` in a split Hamilton model over `K`. -/
def quaternion_split_matrix_i :
    Matrix (Fin 2) (Fin 2) K :=
  !![0, -1; 1, 0]

/-- Helper for Exercise 12-12.2-5: the matrix playing the role of the quaternionic unit `j`
once `-1 = a² + b²`. -/
def quaternion_split_matrix_j (a b : K) :
    Matrix (Fin 2) (Fin 2) K :=
  !![a, b; b, -a]

/-- Helper for Exercise 12-12.2-5: the corresponding matrix image of `k = ij`. -/
def quaternion_split_matrix_k (a b : K) :
    Matrix (Fin 2) (Fin 2) K :=
  !![-b, a; a, b]

/-- Helper for Exercise 12-12.2-5: the split-model matrix `I` satisfies `I² = -1`. -/
theorem quaternion_split_matrix_i_sq :
    quaternion_split_matrix_i (K := K) * quaternion_split_matrix_i (K := K) =
      (-1 : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  -- Compare the four matrix entries of `I²` with those of `-1`.
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quaternion_split_matrix_i]

/-- Helper for Exercise 12-12.2-5: if `-1 = a² + b²`, then the split-model matrix `J` also
satisfies `J² = -1`. -/
theorem quaternion_split_matrix_j_sq
    (a b : K) (h : -(1 : K) = a ^ 2 + b ^ 2) :
    quaternion_split_matrix_j (K := K) a b * quaternion_split_matrix_j (K := K) a b =
      (-1 : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  -- The defining relation is an entrywise calculation using the witness `a² + b² = -1`.
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quaternion_split_matrix_j, h] <;> ring

/-- Helper for Exercise 12-12.2-5: the split-model matrices satisfy `IJ = K`. -/
theorem quaternion_split_matrix_i_mul_j
    (a b : K) :
    quaternion_split_matrix_i (K := K) * quaternion_split_matrix_j (K := K) a b =
      quaternion_split_matrix_k (K := K) a b := by
  -- This is the entrywise verification of the Hamilton relation `ij = k`.
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternion_split_matrix_i, quaternion_split_matrix_j, quaternion_split_matrix_k]

/-- Helper for Exercise 12-12.2-5: the split-model matrices satisfy `JI = -K`. -/
theorem quaternion_split_matrix_j_mul_i
    (a b : K) :
    quaternion_split_matrix_j (K := K) a b * quaternion_split_matrix_i (K := K) =
      -quaternion_split_matrix_k (K := K) a b := by
  -- This is the entrywise verification of the Hamilton relation `ji = -k`.
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternion_split_matrix_i, quaternion_split_matrix_j, quaternion_split_matrix_k]

/-- Helper for Exercise 12-12.2-5: the matrices `I`, `J`, and `K` define a split Hamilton basis
on `Matrix₂(K)` once `-1` is represented by `a² + b²`. -/
def quaternion_split_matrix_basis
    (a b : K) (h : -(1 : K) = a ^ 2 + b ^ 2) :
    QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) K) (-1 : K) 0 (-1 : K) where
  i := quaternion_split_matrix_i (K := K)
  j := quaternion_split_matrix_j (K := K) a b
  k := quaternion_split_matrix_k (K := K) a b
  i_mul_i := by
    -- The `i`-matrix already has the correct square relation.
    simpa [zero_smul] using quaternion_split_matrix_i_sq (K := K)
  j_mul_j := by
    -- The witness `a² + b² = -1` gives the second square relation.
    simpa using quaternion_split_matrix_j_sq (K := K) a b h
  i_mul_j := quaternion_split_matrix_i_mul_j (K := K) a b
  j_mul_i := by
    -- Rewrite `ji = -k` in the basis-fielded form required by `QuaternionAlgebra.Basis`.
    simpa [zero_smul, sub_eq_add_neg] using quaternion_split_matrix_j_mul_i (K := K) a b

/-- Helper for Exercise 12-12.2-5: the split Hamilton basis yields the canonical algebra map
`ℍ[K] → M₂(K)`. -/
def quaternion_split_algHom
    (a b : K) (h : -(1 : K) = a ^ 2 + b ^ 2) :
    ℍ[K] →ₐ[K] Matrix (Fin 2) (Fin 2) K :=
  (quaternion_split_matrix_basis (K := K) a b h).liftHom

/-- Helper for Exercise 12-12.2-5: in the split Hamilton model, the quaternion basis element
`i` is sent to the standard complex-structure matrix `I`. -/
theorem quaternion_split_algHom_basis_i
    (a b : K) (h : -(1 : K) = a ^ 2 + b ^ 2) :
    quaternion_split_algHom (K := K) a b h ((QuaternionAlgebra.Basis.self K).i) =
      quaternion_split_matrix_i (K := K) := by
  -- Compare the four matrix entries after expanding the universal quaternion map on the basis
  -- element `i`.
  ext i j
  fin_cases i <;> fin_cases j
  · change
      ((quaternion_split_matrix_basis (K := K) a b h).liftHom
        (QuaternionAlgebra.Basis.self K).i) 0 0 =
        quaternion_split_matrix_i (K := K) 0 0
    rw [QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift]
    simp [quaternion_split_matrix_basis, quaternion_split_matrix_i,
      quaternion_split_matrix_j, quaternion_split_matrix_k]
  · change
      ((quaternion_split_matrix_basis (K := K) a b h).liftHom
        (QuaternionAlgebra.Basis.self K).i) 0 1 =
        quaternion_split_matrix_i (K := K) 0 1
    rw [QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift]
    simp [quaternion_split_matrix_basis, quaternion_split_matrix_i,
      quaternion_split_matrix_j, quaternion_split_matrix_k]
  · change
      ((quaternion_split_matrix_basis (K := K) a b h).liftHom
        (QuaternionAlgebra.Basis.self K).i) 1 0 =
        quaternion_split_matrix_i (K := K) 1 0
    rw [QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift]
    simp [quaternion_split_matrix_basis, quaternion_split_matrix_i,
      quaternion_split_matrix_j, quaternion_split_matrix_k]
  · change
      ((quaternion_split_matrix_basis (K := K) a b h).liftHom
        (QuaternionAlgebra.Basis.self K).i) 1 1 =
        quaternion_split_matrix_i (K := K) 1 1
    rw [QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift]
    simp [quaternion_split_matrix_basis, quaternion_split_matrix_i,
      quaternion_split_matrix_j, quaternion_split_matrix_k]

/-- Helper for Exercise 12-12.2-5: in the split Hamilton model, the quaternion basis element
`j` is sent to the witness-dependent matrix `J(a,b)`. -/
theorem quaternion_split_algHom_basis_j
    (a b : K) (h : -(1 : K) = a ^ 2 + b ^ 2) :
    quaternion_split_algHom (K := K) a b h ((QuaternionAlgebra.Basis.self K).j) =
      quaternion_split_matrix_j (K := K) a b := by
  -- Compare the four matrix entries after expanding the universal quaternion map on the basis
  -- element `j`.
  ext i j
  fin_cases i <;> fin_cases j
  · change
      ((quaternion_split_matrix_basis (K := K) a b h).liftHom
        (QuaternionAlgebra.Basis.self K).j) 0 0 =
        quaternion_split_matrix_j (K := K) a b 0 0
    rw [QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift]
    simp [quaternion_split_matrix_basis, quaternion_split_matrix_i,
      quaternion_split_matrix_j, quaternion_split_matrix_k]
  · change
      ((quaternion_split_matrix_basis (K := K) a b h).liftHom
        (QuaternionAlgebra.Basis.self K).j) 0 1 =
        quaternion_split_matrix_j (K := K) a b 0 1
    rw [QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift]
    simp [quaternion_split_matrix_basis, quaternion_split_matrix_i,
      quaternion_split_matrix_j, quaternion_split_matrix_k]
  · change
      ((quaternion_split_matrix_basis (K := K) a b h).liftHom
        (QuaternionAlgebra.Basis.self K).j) 1 0 =
        quaternion_split_matrix_j (K := K) a b 1 0
    rw [QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift]
    simp [quaternion_split_matrix_basis, quaternion_split_matrix_i,
      quaternion_split_matrix_j, quaternion_split_matrix_k]
  · change
      ((quaternion_split_matrix_basis (K := K) a b h).liftHom
        (QuaternionAlgebra.Basis.self K).j) 1 1 =
        quaternion_split_matrix_j (K := K) a b 1 1
    rw [QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift]
    simp [quaternion_split_matrix_basis, quaternion_split_matrix_i,
      quaternion_split_matrix_j, quaternion_split_matrix_k]

/-- Helper for Exercise 12-12.2-5: in the split Hamilton model, the quaternion basis element
`k = ij` is sent to the matrix product `K(a,b) = I J(a,b)`. -/
theorem quaternion_split_algHom_basis_k
    (a b : K) (h : -(1 : K) = a ^ 2 + b ^ 2) :
    quaternion_split_algHom (K := K) a b h ((QuaternionAlgebra.Basis.self K).k) =
      quaternion_split_matrix_k (K := K) a b := by
  -- Rewrite `k` as `ij` in the source basis and transport that identity through the split-model
  -- algebra map.
  calc
    quaternion_split_algHom (K := K) a b h ((QuaternionAlgebra.Basis.self K).k) =
        quaternion_split_algHom (K := K) a b h
          ((QuaternionAlgebra.Basis.self K).i * (QuaternionAlgebra.Basis.self K).j) := by
            exact congrArg (quaternion_split_algHom (K := K) a b h)
              (QuaternionAlgebra.Basis.self K).i_mul_j.symm
    _ =
        quaternion_split_algHom (K := K) a b h ((QuaternionAlgebra.Basis.self K).i) *
          quaternion_split_algHom (K := K) a b h ((QuaternionAlgebra.Basis.self K).j) := by
            exact
              (quaternion_split_algHom (K := K) a b h).map_mul
                (QuaternionAlgebra.Basis.self K).i (QuaternionAlgebra.Basis.self K).j
    _ = quaternion_split_matrix_i (K := K) * quaternion_split_matrix_j (K := K) a b := by
          rw [quaternion_split_algHom_basis_i, quaternion_split_algHom_basis_j]
    _ = quaternion_split_matrix_k (K := K) a b := by
          exact quaternion_split_matrix_i_mul_j (K := K) a b

/-- Helper for Exercise 12-12.2-5: the `(0,0)`-entry of the explicit split map records the real
part together with the `j`- and `k`-coordinates. -/
theorem quaternion_split_algHom_entry₀₀
    (a b : K) (h : -(1 : K) = a ^ 2 + b ^ 2) (q : ℍ[K]) :
    quaternion_split_algHom (K := K) a b h q 0 0 =
      q.re + q.imJ * a - q.imK * b := by
  -- Expand the universal quaternion lift and read the `(0,0)`-entry of the resulting matrix.
  change (quaternion_split_matrix_basis (K := K) a b h).lift q 0 0 = _
  simp [sub_eq_add_neg, QuaternionAlgebra.Basis.lift, quaternion_split_matrix_basis,
    quaternion_split_matrix_i, quaternion_split_matrix_j, quaternion_split_matrix_k,
    Algebra.algebraMap_eq_smul_one]

/-- Helper for Exercise 12-12.2-5: the `(0,1)`-entry of the explicit split map records the
`i`-, `j`-, and `k`-coordinates in the standard split model. -/
theorem quaternion_split_algHom_entry₀₁
    (a b : K) (h : -(1 : K) = a ^ 2 + b ^ 2) (q : ℍ[K]) :
    quaternion_split_algHom (K := K) a b h q 0 1 =
      -q.imI + q.imJ * b + q.imK * a := by
  -- Expand the universal quaternion lift and read the `(0,1)`-entry of the resulting matrix.
  change (quaternion_split_matrix_basis (K := K) a b h).lift q 0 1 = _
  simp [QuaternionAlgebra.Basis.lift, quaternion_split_matrix_basis, quaternion_split_matrix_i,
    quaternion_split_matrix_j, quaternion_split_matrix_k, Algebra.algebraMap_eq_smul_one]

/-- Helper for Exercise 12-12.2-5: the `(1,0)`-entry of the explicit split map records the
`i`-, `j`-, and `k`-coordinates in the standard split model. -/
theorem quaternion_split_algHom_entry₁₀
    (a b : K) (h : -(1 : K) = a ^ 2 + b ^ 2) (q : ℍ[K]) :
    quaternion_split_algHom (K := K) a b h q 1 0 =
      q.imI + q.imJ * b + q.imK * a := by
  -- Expand the universal quaternion lift and read the `(1,0)`-entry of the resulting matrix.
  change (quaternion_split_matrix_basis (K := K) a b h).lift q 1 0 = _
  simp [QuaternionAlgebra.Basis.lift, quaternion_split_matrix_basis, quaternion_split_matrix_i,
    quaternion_split_matrix_j, quaternion_split_matrix_k, Algebra.algebraMap_eq_smul_one]

/-- Helper for Exercise 12-12.2-5: the `(1,1)`-entry of the explicit split map records the real
part together with the `j`- and `k`-coordinates. -/
theorem quaternion_split_algHom_entry₁₁
    (a b : K) (h : -(1 : K) = a ^ 2 + b ^ 2) (q : ℍ[K]) :
    quaternion_split_algHom (K := K) a b h q 1 1 =
      q.re - q.imJ * a + q.imK * b := by
  -- Expand the universal quaternion lift and read the `(1,1)`-entry of the resulting matrix.
  change (quaternion_split_matrix_basis (K := K) a b h).lift q 1 1 = _
  simp [sub_eq_add_neg, QuaternionAlgebra.Basis.lift, quaternion_split_matrix_basis,
    quaternion_split_matrix_i, quaternion_split_matrix_j, quaternion_split_matrix_k,
    Algebra.algebraMap_eq_smul_one]

/-- Helper for Exercise 12-12.2-5: the explicit split-model algebra map is injective. -/
theorem quaternion_split_algHom_injective
    (a b : K) (h : -(1 : K) = a ^ 2 + b ^ 2) :
    Function.Injective (quaternion_split_algHom (K := K) a b h) := by
  intro q r hqr
  have h00 := congrArg (fun M ↦ M 0 0) hqr
  have h01 := congrArg (fun M ↦ M 0 1) hqr
  have h10 := congrArg (fun M ↦ M 1 0) hqr
  have h11 := congrArg (fun M ↦ M 1 1) hqr
  simp [quaternion_split_algHom_entry₀₀, quaternion_split_algHom_entry₀₁,
    quaternion_split_algHom_entry₁₀, quaternion_split_algHom_entry₁₁] at h00 h01 h10 h11
  have hre : q.re = r.re := by
    -- Adding the two diagonal-entry equations isolates the real coordinate.
    have hsum := congrArg₂ (fun x y : K ↦ x + y) h00 h11
    ring_nf at hsum
    have htwo : (2 : K) ≠ 0 := by
      intro htwo
      have htwoQ : algebraMap ℚ K 2 = algebraMap ℚ K 0 := by simpa using htwo
      have : (2 : ℚ) = 0 := (FaithfulSMul.algebraMap_injective ℚ K) htwoQ
      norm_num at this
    exact mul_right_cancel₀ htwo hsum
  have himI : q.imI = r.imI := by
    -- Subtracting the off-diagonal equations isolates the `i`-coordinate.
    have hdiff := congrArg₂ (fun x y : K ↦ x - y) h10 h01
    ring_nf at hdiff
    have htwo : (2 : K) ≠ 0 := by
      intro htwo
      have htwoQ : algebraMap ℚ K 2 = algebraMap ℚ K 0 := by simpa using htwo
      have : (2 : ℚ) = 0 := (FaithfulSMul.algebraMap_injective ℚ K) htwoQ
      norm_num at this
    exact mul_right_cancel₀ htwo hdiff
  have hJ : (q.imJ - r.imJ) * a - (q.imK - r.imK) * b = 0 := by
    -- After fixing the real part, one diagonal equation records the `j`/`k` linear relation.
    rw [hre] at h00
    have h0 : r.re + (q.imJ * a - q.imK * b) = r.re + (r.imJ * a - r.imK * b) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_comm, mul_left_comm,
        mul_assoc] using h00
    have h1 : q.imJ * a - q.imK * b = r.imJ * a - r.imK * b := add_left_cancel h0
    have h2 :
        (q.imJ - r.imJ) * a - (q.imK - r.imK) * b =
          (q.imJ * a - q.imK * b) - (r.imJ * a - r.imK * b) := by
      ring
    rw [h2, h1]
    ring
  have hK : (q.imJ - r.imJ) * b + (q.imK - r.imK) * a = 0 := by
    -- After fixing the `i`-part, one off-diagonal equation records the companion relation.
    rw [himI] at h10
    have h0 : r.imI + (q.imJ * b + q.imK * a) = r.imI + (r.imJ * b + r.imK * a) := by
      simpa [add_assoc, add_left_comm, add_comm, mul_comm, mul_left_comm, mul_assoc] using h10
    have h1 : q.imJ * b + q.imK * a = r.imJ * b + r.imK * a := add_left_cancel h0
    have h2 :
        (q.imJ - r.imJ) * b + (q.imK - r.imK) * a =
          (q.imJ * b + q.imK * a) - (r.imJ * b + r.imK * a) := by
      ring
    rw [h2, h1]
    ring
  have himJ : q.imJ = r.imJ := by
    -- Combine the two `j`/`k` relations with `a² + b² = -1` to force the `j`-difference to
    -- vanish.
    have hcombo : (q.imJ - r.imJ) * (a ^ 2 + b ^ 2) = 0 := by
      calc
        (q.imJ - r.imJ) * (a ^ 2 + b ^ 2) =
            a * ((q.imJ - r.imJ) * a - (q.imK - r.imK) * b) +
              b * ((q.imJ - r.imJ) * b + (q.imK - r.imK) * a) := by
                ring
        _ = 0 := by
              simp [hJ, hK]
    have hneg : -(q.imJ - r.imJ) = 0 := by
      calc
        -(q.imJ - r.imJ) = (q.imJ - r.imJ) * (-(1 : K)) := by
          ring
        _ = (q.imJ - r.imJ) * (a ^ 2 + b ^ 2) := by
              simp [h]
        _ = 0 := hcombo
    exact sub_eq_zero.mp (neg_eq_zero.mp hneg)
  have himK : q.imK = r.imK := by
    -- The same norm-form calculation forces the `k`-difference to vanish.
    have hcombo : (q.imK - r.imK) * (a ^ 2 + b ^ 2) = 0 := by
      calc
        (q.imK - r.imK) * (a ^ 2 + b ^ 2) =
            (-b) * ((q.imJ - r.imJ) * a - (q.imK - r.imK) * b) +
              a * ((q.imJ - r.imJ) * b + (q.imK - r.imK) * a) := by
                ring
        _ = 0 := by
              simp [hJ, hK]
    have hneg : -(q.imK - r.imK) = 0 := by
      calc
        -(q.imK - r.imK) = (q.imK - r.imK) * (-(1 : K)) := by
          ring
        _ = (q.imK - r.imK) * (a ^ 2 + b ^ 2) := by
              simp [h]
        _ = 0 := hcombo
    exact sub_eq_zero.mp (neg_eq_zero.mp hneg)
  exact QuaternionAlgebra.ext hre himI himJ himK

/-- Helper for Exercise 12-12.2-5: the explicit split-model algebra map is surjective because it
is an injective linear map between two `4`-dimensional `K`-vector spaces. -/
theorem quaternion_split_algHom_surjective
    (a b : K) (h : -(1 : K) = a ^ 2 + b ^ 2) :
    Function.Surjective (quaternion_split_algHom (K := K) a b h) := by
  have hinj :
      Function.Injective (quaternion_split_algHom (K := K) a b h).toLinearMap :=
    quaternion_split_algHom_injective (K := K) a b h
  have hdim :
      Module.finrank K ℍ[K] = Module.finrank K (Matrix (Fin 2) (Fin 2) K) := by
    rw [Quaternion.finrank_eq_four, Module.finrank_matrix]
    norm_num
  -- Equal finite dimension upgrades injectivity of the underlying linear map to surjectivity.
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := _ ) hdim).mp hinj

/-- Helper for Exercise 12-12.2-5: a witness `-1 = a² + b²` produces an explicit split model of
the Hamilton quaternion algebra over `K`. -/
theorem quaternion_split_of_neg_one_sum_two_squares
    (hsum : ∃ a b : K, -(1 : K) = a ^ 2 + b ^ 2) :
    Nonempty (ℍ[K] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) := by
  rcases hsum with ⟨a, b, h⟩
  have hinj : Function.Injective (quaternion_split_algHom (K := K) a b h) :=
    quaternion_split_algHom_injective (K := K) a b h
  have hsurj : Function.Surjective (quaternion_split_algHom (K := K) a b h) :=
    quaternion_split_algHom_surjective (K := K) a b h
  -- Route correction: use the dimension-theoretic bijectivity route instead of solving for
  -- explicit matrix units.
  exact ⟨AlgEquiv.ofBijective (quaternion_split_algHom (K := K) a b h) ⟨hinj, hsurj⟩⟩

/-- Helper for Exercise 12-12.2-5: the rational Hamilton basis also defines the scalar-extended
Hamilton basis on `ℍ[K]`. -/
def scalarExtendedRationalQuaternionBasis :
    QuaternionAlgebra.Basis ℍ[K] (-1 : ℚ) 0 (-1 : ℚ) where
  i := (QuaternionAlgebra.Basis.self K).i
  j := (QuaternionAlgebra.Basis.self K).j
  k := (QuaternionAlgebra.Basis.self K).k
  i_mul_i := by
    -- The Hamilton relation is unchanged after restricting scalars from `K` to `ℚ`.
    ext <;> simp
  j_mul_j := by
    -- The second square relation is likewise coefficientwise unchanged.
    ext <;> simp
  i_mul_j := by
    -- The product `ij = k` is literal in the scalar-extended model.
    ext <;> simp
  j_mul_i := by
    -- And the anticommutation relation `ji = -k` survives scalar restriction.
    ext <;> simp

/-- Helper for Exercise 12-12.2-5: the canonical `ℚ`-algebra map from the rational Hamilton
algebra to the scalar-extended Hamilton algebra over `K`. -/
def rationalQuaternionToScalarExtension :
    ℍ[ℚ] →ₐ[ℚ] ℍ[K] :=
  (scalarExtendedRationalQuaternionBasis (K := K)).liftHom

/-- Helper for Exercise 12-12.2-5: the canonical scalar-extension map sends `1` to `1`. -/
theorem rationalQuaternionToScalarExtension_one :
    rationalQuaternionToScalarExtension (K := K) 1 = (1 : ℍ[K]) := by
  -- Unfold the lift on the scalar basis vector.
  change (scalarExtendedRationalQuaternionBasis (K := K)).lift 1 = (1 : ℍ[K])
  rw [QuaternionAlgebra.Basis.lift]
  simp [scalarExtendedRationalQuaternionBasis]

/-- Helper for Exercise 12-12.2-5: the canonical scalar-extension map sends the rational
Hamilton basis element `i` to the scalar-extended basis element `i`. -/
theorem rationalQuaternionToScalarExtension_i :
    rationalQuaternionToScalarExtension (K := K) (QuaternionAlgebra.Basis.self ℚ).i =
      (QuaternionAlgebra.Basis.self K).i := by
  -- Expand the lift on the rational basis vector `i`.
  change (scalarExtendedRationalQuaternionBasis (K := K)).lift
      ((QuaternionAlgebra.Basis.self ℚ).i : ℍ[ℚ]) = (QuaternionAlgebra.Basis.self K).i
  rw [QuaternionAlgebra.Basis.lift]
  ext <;> simp [scalarExtendedRationalQuaternionBasis]

/-- Helper for Exercise 12-12.2-5: the canonical scalar-extension map sends the rational
Hamilton basis element `j` to the scalar-extended basis element `j`. -/
theorem rationalQuaternionToScalarExtension_j :
    rationalQuaternionToScalarExtension (K := K) (QuaternionAlgebra.Basis.self ℚ).j =
      (QuaternionAlgebra.Basis.self K).j := by
  -- Expand the lift on the rational basis vector `j`.
  change (scalarExtendedRationalQuaternionBasis (K := K)).lift
      ((QuaternionAlgebra.Basis.self ℚ).j : ℍ[ℚ]) = (QuaternionAlgebra.Basis.self K).j
  rw [QuaternionAlgebra.Basis.lift]
  ext <;> simp [scalarExtendedRationalQuaternionBasis]

/-- Helper for Exercise 12-12.2-5: the canonical scalar-extension map sends the rational
Hamilton basis element `k` to the scalar-extended basis element `k`. -/
theorem rationalQuaternionToScalarExtension_k :
    rationalQuaternionToScalarExtension (K := K) (QuaternionAlgebra.Basis.self ℚ).k =
      (QuaternionAlgebra.Basis.self K).k := by
  -- Expand the lift on the rational basis vector `k`.
  change (scalarExtendedRationalQuaternionBasis (K := K)).lift
      ((QuaternionAlgebra.Basis.self ℚ).k : ℍ[ℚ]) = (QuaternionAlgebra.Basis.self K).k
  rw [QuaternionAlgebra.Basis.lift]
  ext <;> simp [scalarExtendedRationalQuaternionBasis]

/-- Helper for Exercise 12-12.2-5: scalar coefficients commute with the image of the rational
Hamilton algebra inside the scalar-extended Hamilton algebra. -/
theorem scalar_commutes_with_rationalQuaternion_image
    (x : K) (y : ℍ[ℚ]) :
    Commute (algebraMap K ℍ[K] x) (rationalQuaternionToScalarExtension (K := K) y) := by
  -- The image of a scalar in a `K`-algebra is central.
  simpa [Commute] using
    (Algebra.commutes x (rationalQuaternionToScalarExtension (K := K) y))

/-- Helper for Exercise 12-12.2-5: tensoring the rational Hamilton algebra from `ℚ` to `K`
produces the plain Hamilton algebra `ℍ[K]`. -/
theorem quaternion_tensor_base_change_equiv :
    Nonempty (K ⊗[ℚ] ℍ[ℚ] ≃ₐ[K] ℍ[K]) := by
  let Φ : K ⊗[ℚ] ℍ[ℚ] →ₐ[K] ℍ[K] :=
    Algebra.TensorProduct.lift
      (Algebra.ofId K ℍ[K])
      (rationalQuaternionToScalarExtension (K := K))
      (scalar_commutes_with_rationalQuaternion_image (K := K))
  have hsurj : Function.Surjective Φ := by
    intro q
    let iQ : ℍ[ℚ] := rationalQuaternionBasis.i
    let jQ : ℍ[ℚ] := rationalQuaternionBasis.j
    let kQ : ℍ[ℚ] := rationalQuaternionBasis.k
    let iK : ℍ[K] := (scalarExtendedRationalQuaternionBasis (K := K)).i
    let jK : ℍ[K] := (scalarExtendedRationalQuaternionBasis (K := K)).j
    let kK : ℍ[K] := (scalarExtendedRationalQuaternionBasis (K := K)).k
    let x : K ⊗[ℚ] ℍ[ℚ] :=
      q.re ⊗ₜ[ℚ] (1 : ℍ[ℚ]) +
        q.imI ⊗ₜ[ℚ] iQ +
        q.imJ ⊗ₜ[ℚ] jQ +
        q.imK ⊗ₜ[ℚ] kQ
    have hiMap : rationalQuaternionToScalarExtension (K := K) iQ = iK := by
      -- The tensor bridge sends the rational basis vector `i` to its scalar-extended copy.
      simpa [iQ, iK, rationalQuaternionBasis, scalarExtendedRationalQuaternionBasis] using
        rationalQuaternionToScalarExtension_i (K := K)
    have hjMap : rationalQuaternionToScalarExtension (K := K) jQ = jK := by
      -- The same identification holds for the rational basis vector `j`.
      simpa [jQ, jK, rationalQuaternionBasis, scalarExtendedRationalQuaternionBasis] using
        rationalQuaternionToScalarExtension_j (K := K)
    have hkMap : rationalQuaternionToScalarExtension (K := K) kQ = kK := by
      -- And likewise for the rational basis vector `k`.
      simpa [kQ, kK, rationalQuaternionBasis, scalarExtendedRationalQuaternionBasis] using
        rationalQuaternionToScalarExtension_k (K := K)
    have hΦone : Φ (q.re ⊗ₜ[ℚ] (1 : ℍ[ℚ])) = q.re • (1 : ℍ[K]) := by
      -- On pure tensors with the scalar basis vector, the comparison map is the scalar action.
      dsimp [Φ]
      rw [rationalQuaternionToScalarExtension_one]
      ext <;> simp [Algebra.algebraMap_eq_smul_one]
    have hΦi :
        Φ (q.imI ⊗ₜ[ℚ] iQ) = q.imI • iK := by
      -- The rational basis vector `i` maps to the scalar-extended basis vector `i`.
      dsimp [Φ]
      rw [hiMap]
      ext <;> simp [iK, scalarExtendedRationalQuaternionBasis, Algebra.algebraMap_eq_smul_one]
    have hΦj :
        Φ (q.imJ ⊗ₜ[ℚ] jQ) = q.imJ • jK := by
      -- The same tensor comparison sends `j` to the scalar-extended basis vector `j`.
      dsimp [Φ]
      rw [hjMap]
      ext <;> simp [jK, scalarExtendedRationalQuaternionBasis, Algebra.algebraMap_eq_smul_one]
    have hΦk :
        Φ (q.imK ⊗ₜ[ℚ] kQ) = q.imK • kK := by
      -- And likewise for the rational basis vector `k`.
      dsimp [Φ]
      rw [hkMap]
      ext <;> simp [kK, scalarExtendedRationalQuaternionBasis, Algebra.algebraMap_eq_smul_one]
    refine ⟨x, ?_⟩
    -- Sum the four basis-vector images and compare quaternion coordinates.
    calc
      Φ x = q.re • (1 : ℍ[K]) +
          q.imI • iK +
          q.imJ • jK +
          q.imK • kK := by
            simp [x, hΦone, hΦi, hΦj, hΦk]
      _ = q := by
            ext <;> simp [iK, jK, kK, scalarExtendedRationalQuaternionBasis]
  have hdim :
      Module.finrank K (K ⊗[ℚ] ℍ[ℚ]) = Module.finrank K ℍ[K] := by
    -- Both the tensor product and the scalar-extended Hamilton algebra are `4`-dimensional over
    -- `K`, so surjectivity upgrades to bijectivity.
    calc
      Module.finrank K (K ⊗[ℚ] ℍ[ℚ]) = Module.finrank K K * Module.finrank ℚ ℍ[ℚ] := by
        rw [Module.finrank_tensorProduct]
      _ = 4 := by
        rw [Module.finrank_self, Quaternion.finrank_eq_four]
      _ = Module.finrank K ℍ[K] := by
        simpa using (Quaternion.finrank_eq_four (R := K)).symm
  have hinjLinear : Function.Injective Φ.toLinearMap := by
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := Φ.toLinearMap) hdim).2 hsurj
  exact ⟨AlgEquiv.ofBijective Φ ⟨hinjLinear, hsurj⟩⟩

/-- Helper for Exercise 12-12.2-5: if the Hamilton quaternion algebra over `K` splits, then the
images of `i` and `j` in `M₂(K)` force `-1` to be a sum of two squares in `K`. -/
theorem neg_one_sum_two_squares_of_quaternion_split
    (hsplit : Nonempty (ℍ[K] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K)) :
    ∃ a b : K, -(1 : K) = a ^ 2 + b ^ 2 := by
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  rcases hsplit with ⟨e⟩
  let qi : ℍ[K] := ⟨0, 1, 0, 0⟩
  let qj : ℍ[K] := ⟨0, 0, 1, 0⟩
  let A : (Fin 2 → K) →ₗ[K] (Fin 2 → K) := (e qi).mulVecLin
  let B : (Fin 2 → K) →ₗ[K] (Fin 2 → K) := (e qj).mulVecLin
  have hdim : Module.finrank K (Fin 2 → K) = 2 := by
    -- The ambient vector space for `2 × 2` matrices is the standard `K²`.
    simpa using (Module.finrank_pi K (ι := Fin 2))
  have hqi_sq : qi * qi = (-1 : ℍ[K]) := by
    -- The explicit quaternion generator `i` still satisfies `i² = -1`.
    ext <;> simp [qi]
  have hqj_sq : qj * qj = (-1 : ℍ[K]) := by
    -- The explicit quaternion generator `j` satisfies the same square relation.
    ext <;> simp [qj]
  have hji : qj * qi = -(qi * qj) := by
    -- The explicit generators anticommute in the Hamilton algebra.
    ext <;> simp [qi, qj]
  have hA2 : A * A = (-1 : K) • LinearMap.id := by
    have hsquare : e qi * e qi = (-1 : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      -- Transport the Hamilton relation `i² = -1` through the chosen split equivalence.
      calc
        e qi * e qi = e (qi * qi) := by
          simpa using (e.map_mul qi qi).symm
        _ = e (-(1 : ℍ[K])) := by
          rw [hqi_sq]
        _ = (-1 : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
          simp
    have hlin :
        (e qi).mulVecLin * (e qi).mulVecLin = -LinearMap.id := by
      change (e qi).mulVecLin * (e qi).mulVecLin = -LinearMap.id
      rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul]
      simpa [A, Matrix.mulVecLin_one] using congrArg Matrix.mulVecLin hsquare
    have hnegId : (-1 : K) • (LinearMap.id : (Fin 2 → K) →ₗ[K] (Fin 2 → K)) = -LinearMap.id := by
      ext x i
      simp
    rw [hnegId]
    exact hlin
  have hB2 : B * B = (-1 : K) • LinearMap.id := by
    have hsquare : e qj * e qj = (-1 : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      -- The same transport sends `j² = -1` to the matrix model.
      calc
        e qj * e qj = e (qj * qj) := by
          simpa using (e.map_mul qj qj).symm
        _ = e (-(1 : ℍ[K])) := by
          rw [hqj_sq]
        _ = (-1 : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
          simp
    have hlin :
        (e qj).mulVecLin * (e qj).mulVecLin = -LinearMap.id := by
      change (e qj).mulVecLin * (e qj).mulVecLin = -LinearMap.id
      rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul]
      simpa [B, Matrix.mulVecLin_one] using congrArg Matrix.mulVecLin hsquare
    have hnegId : (-1 : K) • (LinearMap.id : (Fin 2 → K) →ₗ[K] (Fin 2 → K)) = -LinearMap.id := by
      ext x i
      simp
    rw [hnegId]
    exact hlin
  have hBA : B * A = -(A * B) := by
    have hanticomm : e qj * e qi = -(e qi * e qj) := by
      -- Transport the Hamilton relation `ji = -(ij)` to the split model.
      calc
        e qj * e qi = e (qj * qi) := by
          simpa using (e.map_mul qj qi).symm
        _ = e (-(qi * qj)) := by
          rw [hji]
        _ = -(e qi * e qj) := by
          calc
            e (-(qi * qj)) = -(e (qi * qj)) := by
              rw [map_neg]
            _ = -(e qi * e qj) := by
              simpa using congrArg Neg.neg (e.map_mul qi qj)
    change (e qj).mulVecLin * (e qi).mulVecLin = -((e qi).mulVecLin * (e qj).mulVecLin)
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      ← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul]
    simpa [A, B] using congrArg Matrix.mulVecLin hanticomm
  -- Apply the existing `2`-dimensional anticommuting-matrix criterion.
  exact neg_one_sum_two_squares_of_anticommuting_square_neg_one
    (hdim := hdim) (A := A) (B := B) hA2 hB2 hBA

/-- Helper for Exercise 12-12.2-5: if the tensor extension `K ⊗[ℚ] ℍ[ℚ]` splits, then the
quaternion norm form already represents `-1` over `K`. -/
theorem neg_one_sum_two_squares_of_tensorQuaternion_split
    (hsplit : Nonempty (K ⊗[ℚ] ℍ[ℚ] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K)) :
    ∃ a b : K, -(1 : K) = a ^ 2 + b ^ 2 := by
  rcases quaternion_tensor_base_change_equiv (K := K) with ⟨eTensor⟩
  have hsplit' : Nonempty (ℍ[K] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) := by
    -- Transport the split model from the tensor product to the plain Hamilton algebra.
    rcases hsplit with ⟨e⟩
    exact ⟨eTensor.symm.trans e⟩
  -- The base-changed Hamilton algebra is now in the scope of the existing matrix criterion.
  exact neg_one_sum_two_squares_of_quaternion_split (K := K) hsplit'

/-- Helper for Exercise 12-12.2-5: any solution of `-1 = a² + b²` yields a split model of the
tensor extension `K ⊗[ℚ] ℍ[ℚ]`. -/
theorem tensorQuaternion_split_of_neg_one_sum_two_squares
    (hsum : ∃ a b : K, -(1 : K) = a ^ 2 + b ^ 2) :
    Nonempty (K ⊗[ℚ] ℍ[ℚ] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) := by
  rcases quaternion_tensor_base_change_equiv (K := K) with ⟨eTensor⟩
  rcases quaternion_split_of_neg_one_sum_two_squares (K := K) hsum with ⟨eSplit⟩
  -- Compose the canonical base-change equivalence with the explicit split model of `ℍ[K]`.
  exact ⟨eTensor.trans eSplit⟩

end

end Representation
