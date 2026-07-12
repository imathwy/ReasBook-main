import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic Lean search was unavailable in this session; the statement below uses the canonical
-- mathlib owners `MvPolynomial.restrictTotalDegree` for `P_d^n` and
-- `LinearMap.GeneralLinearGroup` for `GL(P_d^n)`.

open scoped BigOperators Matrix

noncomputable section

open MvPolynomial

/-- The polynomial space `P_d^n`, realized as the subspace of real multivariate polynomials in `n`
variables of total degree at most `d`. -/
abbrev polynomialSpace (n : ℕ) (d : ℕ+) :=
  MvPolynomial.restrictTotalDegree (Fin n) ℝ (d : ℕ)

/-- The image of the coordinate function `X i` under the linear change of variables determined by
`A⁻¹`. -/
def polynomialCoordinateChange {n : ℕ} (A : GL (Fin n) ℝ) (i : Fin n) :
    MvPolynomial (Fin n) ℝ :=
  ∑ j : Fin n,
    MvPolynomial.C ((↑(A⁻¹) : Matrix (Fin n) (Fin n) ℝ) i j) * MvPolynomial.X j

/-- Helper for Problem 7-24: the coordinate substitution attached to the identity matrix fixes each
coordinate polynomial. -/
theorem polynomialCoordinateChange_one {n : ℕ} (i : Fin n) :
    polynomialCoordinateChange (1 : GL (Fin n) ℝ) i = MvPolynomial.X i := by
  classical
  -- Only the `j = i` summand survives for the identity matrix.
  rw [polynomialCoordinateChange, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]

/-- Helper for Problem 7-24: the coefficient of `X j` in the transformed coordinate polynomial is
the `(i, j)` entry of `A⁻¹`. -/
theorem coeff_polynomialCoordinateChange {n : ℕ} (A : GL (Fin n) ℝ) (i j : Fin n) :
    MvPolynomial.coeff (Finsupp.single j 1) (polynomialCoordinateChange A i) =
      ((↑(A⁻¹) : Matrix (Fin n) (Fin n) ℝ) i j) := by
  classical
  -- Only the `j`-summand contributes to the coefficient of `X j`.
  rw [polynomialCoordinateChange, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k hk hkj
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X']
    simp [hkj]

/-- Helper for Problem 7-24: each transformed coordinate polynomial is homogeneous of degree `1`.
-/
theorem polynomialCoordinateChange_isHomogeneous {n : ℕ} (A : GL (Fin n) ℝ) (i : Fin n) :
    (polynomialCoordinateChange A i).IsHomogeneous 1 := by
  classical
  -- Every summand is a scalar multiple of a coordinate function, hence homogeneous of degree `1`.
  rw [polynomialCoordinateChange]
  refine MvPolynomial.IsHomogeneous.sum Finset.univ
    (fun j ↦ MvPolynomial.C ((↑(A⁻¹) : Matrix (Fin n) (Fin n) ℝ) i j) * MvPolynomial.X j) 1 ?_
  intro j hj
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

/-- Helper for Problem 7-24: substituting the linear form for `B` into the substitution for `A`
produces the linear form for `A * B`. -/
theorem coeff_polynomialPrecompose_coordinateChange {n : ℕ} (A B : GL (Fin n) ℝ)
    (i j : Fin n) :
    MvPolynomial.coeff (Finsupp.single j 1)
        (MvPolynomial.aeval (polynomialCoordinateChange A) (polynomialCoordinateChange B i)) =
      ((↑((A * B)⁻¹) : Matrix (Fin n) (Fin n) ℝ) i j) := by
  -- The coefficient of `X j` is computed by the matrix product formula for `(A * B)⁻¹`.
  calc
    MvPolynomial.coeff (Finsupp.single j 1)
        (MvPolynomial.aeval (polynomialCoordinateChange A) (polynomialCoordinateChange B i)) =
        ∑ k : Fin n,
          ((↑(B⁻¹) : Matrix (Fin n) (Fin n) ℝ) i k) *
            ((↑(A⁻¹) : Matrix (Fin n) (Fin n) ℝ) k j) := by
          simp [polynomialCoordinateChange, coeff_polynomialCoordinateChange]
    _ = ((↑((A * B)⁻¹) : Matrix (Fin n) (Fin n) ℝ) i j) := by
          simp [Matrix.mul_apply]

/-- Helper for Problem 7-24: substituting one linear change of coordinates into another still
produces a homogeneous polynomial of degree `1`. -/
theorem polynomialPrecompose_coordinateChange_isHomogeneous {n : ℕ} (A B : GL (Fin n) ℝ)
    (i : Fin n) :
    (MvPolynomial.aeval (polynomialCoordinateChange A) (polynomialCoordinateChange B i)).IsHomogeneous
      1 := by
  -- Substituting degree-`1` coordinate polynomials into a degree-`1` polynomial preserves degree.
  simpa using MvPolynomial.IsHomogeneous.aeval
    (polynomialCoordinateChange_isHomogeneous B i)
    (polynomialCoordinateChange A)
    (fun j ↦ polynomialCoordinateChange_isHomogeneous A j)

/-- Helper for Problem 7-24: substituting the linear form for `B` into the substitution for `A`
produces the linear form for `A * B`. -/
theorem polynomialPrecompose_coordinateChange {n : ℕ} (A B : GL (Fin n) ℝ) (i : Fin n) :
    MvPolynomial.aeval (polynomialCoordinateChange A) (polynomialCoordinateChange B i) =
      polynomialCoordinateChange (A * B) i := by
  sorry

/-- The substitution attached to `A` really is inverse to the one attached to `A⁻¹`. -/
theorem polynomialPrecompose_left_inv {n : ℕ} (A : GL (Fin n) ℝ) :
    Function.LeftInverse
      (MvPolynomial.aeval (polynomialCoordinateChange A⁻¹))
      (MvPolynomial.aeval (polynomialCoordinateChange A)) := by
  intro p
  -- Route correction: the coordinate-change helper uses the rows of `A⁻¹`, so composition
  -- matches matrix multiplication in the stated order.
  have hcomp :
      (MvPolynomial.aeval (polynomialCoordinateChange A⁻¹)).comp
        (MvPolynomial.aeval (polynomialCoordinateChange A)) =
        AlgHom.id ℝ (MvPolynomial (Fin n) ℝ) := by
    apply (MvPolynomial.algHom_ext_iff).2
    intro i
    -- It is enough to compute the composite on the generators `X i`.
    rw [MvPolynomial.comp_aeval, MvPolynomial.aeval_X]
    rw [polynomialPrecompose_coordinateChange]
    simpa using polynomialCoordinateChange_one i
  simpa using AlgHom.congr_fun hcomp p

/-- The substitution attached to `A⁻¹` is also a right inverse. -/
theorem polynomialPrecompose_right_inv {n : ℕ} (A : GL (Fin n) ℝ) :
    Function.RightInverse
      (MvPolynomial.aeval (polynomialCoordinateChange A⁻¹))
      (MvPolynomial.aeval (polynomialCoordinateChange A)) := by
  -- The left-inverse statement for `A⁻¹` is exactly the right-inverse statement for `A`.
  simpa using polynomialPrecompose_left_inv (A := A⁻¹)

/-- The polynomial substitution induced by `A ∈ GL(n, ℝ)`, acting by precomposition with the
inverse linear map on coordinates. -/
noncomputable def polynomialPrecompose {n : ℕ} (A : GL (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ ≃ₐ[ℝ] MvPolynomial (Fin n) ℝ where
  toFun := MvPolynomial.aeval (polynomialCoordinateChange A)
  invFun := MvPolynomial.aeval (polynomialCoordinateChange A⁻¹)
  left_inv := polynomialPrecompose_left_inv A
  right_inv := polynomialPrecompose_right_inv A
  map_mul' := (MvPolynomial.aeval (polynomialCoordinateChange A)).map_mul
  map_add' := (MvPolynomial.aeval (polynomialCoordinateChange A)).map_add
  commutes' := (MvPolynomial.aeval (polynomialCoordinateChange A)).commutes

/-- On coordinate polynomials, `polynomialPrecompose A` is the explicit linear substitution coming
from the inverse matrix of `A`. -/
theorem polynomialPrecompose_X {n : ℕ} (A : GL (Fin n) ℝ) (i : Fin n) :
    polynomialPrecompose A (MvPolynomial.X i) = polynomialCoordinateChange A i := by
  -- This is the defining computation rule for the substitution equivalence.
  simp [polynomialPrecompose, polynomialCoordinateChange]

/-- Helper for Problem 7-24: the identity substitution acts trivially on the polynomial ring. -/
theorem polynomialPrecompose_one_apply {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    polynomialPrecompose (1 : GL (Fin n) ℝ) p = p := by
  -- The ambient algebra equivalence is determined by its values on the generators `X i`.
  have hId :
      (polynomialPrecompose (1 : GL (Fin n) ℝ)).toAlgHom =
        AlgHom.id ℝ (MvPolynomial (Fin n) ℝ) := by
    apply (MvPolynomial.algHom_ext_iff).2
    intro i
    simpa [polynomialPrecompose] using polynomialCoordinateChange_one i
  exact congrArg (fun f : MvPolynomial (Fin n) ℝ →ₐ[ℝ] MvPolynomial (Fin n) ℝ => f p) hId

/-- Helper for Problem 7-24: composing the substitutions for `A` and `B` gives the substitution
for `A * B`. -/
theorem polynomialPrecompose_mul_apply {n : ℕ} (A B : GL (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) :
    polynomialPrecompose A (polynomialPrecompose B p) = polynomialPrecompose (A * B) p := by
  -- The two ambient algebra homomorphisms agree because they agree on every generator `X i`.
  have hComp :
      (polynomialPrecompose A).toAlgHom.comp (polynomialPrecompose B).toAlgHom =
        (polynomialPrecompose (A * B)).toAlgHom := by
    apply (MvPolynomial.algHom_ext_iff).2
    intro i
    rw [AlgHom.comp_apply, polynomialPrecompose_X, polynomialPrecompose_X,
      polynomialPrecompose_coordinateChange]
  exact congrArg (fun f : MvPolynomial (Fin n) ℝ →ₐ[ℝ] MvPolynomial (Fin n) ℝ => f p) hComp

/-- Helper for Problem 7-24: the polynomial substitution induced by `A` preserves the bounded
total-degree subspace `P_d^n`. -/
theorem polynomialPrecompose_homogeneousComponent_isHomogeneous {n : ℕ}
    (A : GL (Fin n) ℝ) (k : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    (polynomialPrecompose A ((MvPolynomial.homogeneousComponent k) p)).IsHomogeneous k := by
  -- Each homogeneous component keeps its degree because every coordinate change is degree `1`.
  simpa [polynomialPrecompose, one_mul] using MvPolynomial.IsHomogeneous.aeval
    (MvPolynomial.homogeneousComponent_isHomogeneous k p)
    (polynomialCoordinateChange A)
    (fun i ↦ polynomialCoordinateChange_isHomogeneous A i)

/-- Helper for Problem 7-24: the polynomial substitution induced by `A` preserves the bounded
total-degree subspace `P_d^n`. -/
theorem polynomialPrecompose_mem_polynomialSpace {n : ℕ} (d : ℕ+) (A : GL (Fin n) ℝ)
    {p : MvPolynomial (Fin n) ℝ} (hp : p ∈ polynomialSpace n d) :
    polynomialPrecompose A p ∈ polynomialSpace n d := by
  sorry

/-- The polynomial substitution induced by `A` preserves the subspace `P_d^n`. -/
theorem polynomialPrecompose_map_polynomialSpace {n : ℕ} (d : ℕ+) (A : GL (Fin n) ℝ) :
    (polynomialSpace n d).map (polynomialPrecompose A).toLinearEquiv.toLinearMap =
      polynomialSpace n d := by
  -- Compare membership on both sides, using the inverse substitution for the reverse inclusion.
  ext q
  constructor
  · intro hq
    rw [Submodule.mem_map] at hq
    rcases hq with ⟨p, hp, rfl⟩
    exact polynomialPrecompose_mem_polynomialSpace d A hp
  · intro hq
    rw [Submodule.mem_map]
    refine ⟨polynomialPrecompose A⁻¹ q, polynomialPrecompose_mem_polynomialSpace d A⁻¹ hq, ?_⟩
    exact polynomialPrecompose_right_inv A q

/-- The linear automorphism of `P_d^n` induced by the change of variables associated to
`A ∈ GL(n, ℝ)`. -/
noncomputable def tau_d_n_linearEquiv (n : ℕ) (d : ℕ+) (A : GL (Fin n) ℝ) :
    polynomialSpace n d ≃ₗ[ℝ] polynomialSpace n d :=
  ((polynomialPrecompose A).toLinearEquiv).ofSubmodules
    (polynomialSpace n d) (polynomialSpace n d)
    (polynomialPrecompose_map_polynomialSpace d A)

/-- The identity matrix acts trivially on `P_d^n`. -/
theorem tau_d_n_linearEquiv_one (n : ℕ) (d : ℕ+) :
    tau_d_n_linearEquiv n d (1 : GL (Fin n) ℝ) =
      LinearEquiv.refl ℝ (polynomialSpace n d) := by
  apply LinearEquiv.ext
  intro p
  apply Subtype.ext
  -- The induced map is just the ambient identity substitution restricted to `P_d^n`.
  rw [tau_d_n_linearEquiv, LinearEquiv.ofSubmodules_apply]
  exact polynomialPrecompose_one_apply ↑p

/-- Matrix multiplication corresponds to composition of the induced automorphisms of `P_d^n`. -/
theorem tau_d_n_linearEquiv_mul (n : ℕ) (d : ℕ+) (A B : GL (Fin n) ℝ) :
    tau_d_n_linearEquiv n d (A * B) =
      tau_d_n_linearEquiv n d A * tau_d_n_linearEquiv n d B := by
  apply LinearEquiv.ext
  intro p
  apply Subtype.ext
  -- Both subtype automorphisms are restrictions of the same ambient composition law.
  rw [LinearEquiv.mul_apply, tau_d_n_linearEquiv, LinearEquiv.ofSubmodules_apply,
    tau_d_n_linearEquiv, LinearEquiv.ofSubmodules_apply, tau_d_n_linearEquiv,
    LinearEquiv.ofSubmodules_apply]
  symm
  exact polynomialPrecompose_mul_apply A B ↑p

/-- The value of `τ_d^n` at the identity is the identity automorphism of `P_d^n`. -/
theorem tau_d_n_toGeneralLinearGroup_one (n : ℕ) (d : ℕ+) :
    LinearMap.GeneralLinearGroup.ofLinearEquiv
      (tau_d_n_linearEquiv n d (1 : GL (Fin n) ℝ)) = 1 := by
  -- The `GL(P_d^n)` element is the identity once the underlying linear equivalence is.
  rw [tau_d_n_linearEquiv_one]
  rfl

/-- The value of `τ_d^n` at a product is the product of the induced automorphisms of `P_d^n`. -/
theorem tau_d_n_toGeneralLinearGroup_mul (n : ℕ) (d : ℕ+) :
    ∀ A B : GL (Fin n) ℝ,
      LinearMap.GeneralLinearGroup.ofLinearEquiv (tau_d_n_linearEquiv n d (A * B)) =
        LinearMap.GeneralLinearGroup.ofLinearEquiv (tau_d_n_linearEquiv n d A) *
          LinearMap.GeneralLinearGroup.ofLinearEquiv (tau_d_n_linearEquiv n d B) := by
  intro A B
  -- The group law on `GL(P_d^n)` is induced from multiplication of linear equivalences.
  rw [tau_d_n_linearEquiv_mul, LinearMap.GeneralLinearGroup.ofLinearEquiv_mul]

/-- The map `τ_d^n : GL(n, ℝ) → GL(P_d^n)` attached to the degree-`d` polynomial action. -/
noncomputable def tau_d_n (n : ℕ) (d : ℕ+) :
    GL (Fin n) ℝ →* LinearMap.GeneralLinearGroup ℝ (polynomialSpace n d) where
  toFun := fun A ↦ LinearMap.GeneralLinearGroup.ofLinearEquiv (tau_d_n_linearEquiv n d A)
  map_one' := tau_d_n_toGeneralLinearGroup_one n d
  map_mul' := tau_d_n_toGeneralLinearGroup_mul n d

/-- The `τ_d^n` representation sends the identity of `GL(n, ℝ)` to the identity of
`GL(P_d^n)`. -/
theorem tau_d_n_one (n : ℕ) (d : ℕ+) :
    tau_d_n n d (1 : GL (Fin n) ℝ) = 1 := by
  -- This is the `map_one` axiom of the monoid homomorphism `tau_d_n`.
  simpa using (tau_d_n n d).map_one

/-- The `τ_d^n` action is multiplicative as a homomorphism into `GL(P_d^n)`. -/
theorem tau_d_n_mul (n : ℕ) (d : ℕ+) :
    ∀ A B : GL (Fin n) ℝ, tau_d_n n d (A * B) = tau_d_n n d A * tau_d_n n d B := by
  intro A B
  -- This is the `map_mul` axiom of the monoid homomorphism `tau_d_n`.
  simpa using (tau_d_n n d).map_mul A B

/-- Helper for Problem 7-24: the coordinate polynomial `X i` lies in `P_d^n` whenever `d > 0`. -/
theorem mem_polynomialSpace_X (n : ℕ) (d : ℕ+) (i : Fin n) :
    MvPolynomial.X i ∈ polynomialSpace n d := by
  -- The total degree of `X i` is `1`, and every positive natural number is at least `1`.
  rw [polynomialSpace, MvPolynomial.mem_restrictTotalDegree]
  simpa [MvPolynomial.totalDegree_X] using Nat.succ_le_of_lt d.pos

/-- Helper for Problem 7-24: the induced linear equivalence sends the subtype point represented by
`X i` to the corresponding transformed coordinate polynomial. -/
theorem tau_d_n_linearEquiv_apply_X (n : ℕ) (d : ℕ+) (A : GL (Fin n) ℝ) (i : Fin n)
    (hx : MvPolynomial.X i ∈ polynomialSpace n d) :
    ↑(tau_d_n_linearEquiv n d A ⟨MvPolynomial.X i, hx⟩) = polynomialCoordinateChange A i := by
  -- The `ofSubmodules` interface lets us compute on the ambient polynomial ring.
  rw [tau_d_n_linearEquiv, LinearEquiv.ofSubmodules_apply]
  exact polynomialPrecompose_X A i

/-- Problem 7-24: for every positive degree bound `d`, the polynomial action
`τ_d^n : GL(n, ℝ) → GL(P_d^n)` is a faithful representation of `GL(n, ℝ)`. -/
theorem tau_d_n_injective (n : ℕ) (d : ℕ+) :
    Function.Injective (tau_d_n n d) := by
  intro A B hAB
  have hLinear :
      tau_d_n_linearEquiv n d A = tau_d_n_linearEquiv n d B := by
    -- Equality in `GL(P_d^n)` is equality of the underlying linear equivalences.
    simpa [tau_d_n] using congrArg
      (fun g : LinearMap.GeneralLinearGroup ℝ (polynomialSpace n d) =>
        LinearMap.GeneralLinearGroup.toLinearEquiv g)
      hAB
  apply inv_injective
  ext i j
  change ((↑(A⁻¹) : Matrix (Fin n) (Fin n) ℝ) i j) =
    ((↑(B⁻¹) : Matrix (Fin n) (Fin n) ℝ) i j)
  have hx : MvPolynomial.X i ∈ polynomialSpace n d := mem_polynomialSpace_X n d i
  have hCoordinate :
      polynomialCoordinateChange A i = polynomialCoordinateChange B i := by
    -- Evaluate the equality of linear equivalences on the degree-`1` coordinate polynomial.
    have hEval := congrArg
      (fun e : polynomialSpace n d ≃ₗ[ℝ] polynomialSpace n d =>
        ((e ⟨MvPolynomial.X i, hx⟩ : polynomialSpace n d) : MvPolynomial (Fin n) ℝ))
      hLinear
    simpa [tau_d_n_linearEquiv_apply_X, hx] using hEval
  -- Comparing the `X j`-coefficients recovers the entries of the inverse matrices.
  have hCoeff :=
    congrArg (MvPolynomial.coeff (Finsupp.single j 1)) hCoordinate
  simpa [coeff_polynomialCoordinateChange] using hCoeff
