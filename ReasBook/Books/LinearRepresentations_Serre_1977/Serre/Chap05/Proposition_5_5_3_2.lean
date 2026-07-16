import LinearRepresentations_Serre_1977.Serre.Chap01.Definition_1_1_2_1
import LinearRepresentations_Serre_1977.Serre.Chap05.Definition_5_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open AddChar
open Matrix

/- The source-facing owners in this proposition are the two-dimensional family `ρ^h` and the
associated dihedral characters `χ_h`, `ψ₁`, and `ψ₂`. The `core/canonical` owner for the
one-dimensional pieces is still `DihedralGroup n →* ℂˣ`, and later exercises should build on this
file rather than re-owning these declarations. The proposition then adds the explicit matrix
formulas, the exceptional reducible and irreducible cases, and the even-`n` characters `ψ₃`,
`ψ₄`. -/

/-- The linear action maps used to define Serre's two-dimensional representation `ρ^h`. -/
private def dihedralTwoDimensionalLinear (n : ℕ) [NeZero n] (h : ZMod n) :
    DihedralGroup n → (Fin 2 → ℂ) →ₗ[ℂ] Fin 2 → ℂ
  | DihedralGroup.r k =>
      Matrix.toLin' !![zmodAddEquiv h k, 0; 0, zmodAddEquiv (-h) k]
  | DihedralGroup.sr k =>
      Matrix.toLin' !![0, zmodAddEquiv (-h) k; zmodAddEquiv h k, 0]

/-- Helper for Proposition 5-5.3-2: negating the parameter in the canonical cyclic character
inverts its value. -/
private theorem zmodAddEquiv_neg_parameter (n : ℕ) [NeZero n] (h k : ZMod n) :
    zmodAddEquiv (-h) k = (zmodAddEquiv h k)⁻¹ := by
  -- The Pontryagin-duality parameterization is additive in `h`, so negation on the parameter
  -- becomes inversion on character values.
  calc
    zmodAddEquiv (-h) k = (-zmodAddEquiv h) k := by
      rw [← AddEquiv.map_neg]
    _ = (zmodAddEquiv h k)⁻¹ := AddChar.neg_apply' (zmodAddEquiv h) k

/-- Helper for Proposition 5-5.3-2: evaluating the cyclic character at `-k` negates the
parameter instead. -/
private theorem zmodAddEquiv_apply_neg (n : ℕ) [NeZero n] (h k : ZMod n) :
    zmodAddEquiv h (-k) = zmodAddEquiv (-h) k := by
  -- Moving the minus sign from the input to the parameter is exactly the inversion identity
  -- viewed from the argument side.
  calc
    zmodAddEquiv h (-k) = (zmodAddEquiv h k)⁻¹ := AddChar.map_neg_eq_inv _ _
    _ = zmodAddEquiv (-h) k := (zmodAddEquiv_neg_parameter n h k).symm

/-- Helper for Proposition 5-5.3-2: simultaneous negation of parameter and input leaves the
cyclic character unchanged. -/
private theorem zmodAddEquiv_neg_neg (n : ℕ) [NeZero n] (h k : ZMod n) :
    zmodAddEquiv (-h) (-k) = zmodAddEquiv h k := by
  -- Apply the previous transport identity once and then cancel the double negation.
  rw [zmodAddEquiv_apply_neg, neg_neg]

/-- The auxiliary linear action defining `ρ^h` sends the identity to the identity map. -/
private theorem dihedralTwoDimensionalLinear_map_one (n : ℕ) [NeZero n] (h : ZMod n) :
    dihedralTwoDimensionalLinear n h 1 = 1 := by
  -- The identity element is the zero rotation, so the defining matrix is the identity matrix.
  rw [show (1 : DihedralGroup n) = DihedralGroup.r 0 by simp]
  apply LinearMap.toMatrix'.injective
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dihedralTwoDimensionalLinear]

/-- Helper for Proposition 5-5.3-2: multiplying the explicit rotation matrix by the explicit
reflection matrix produces the expected reflection matrix. -/
private theorem dihedral_rotation_reflection_matrix_mul (n : ℕ) [NeZero n] (h : ZMod n)
    (i j : ZMod n) :
    !![zmodAddEquiv h i, 0; 0, zmodAddEquiv (-h) i] *
        !![0, zmodAddEquiv (-h) j; zmodAddEquiv h j, 0] =
      !![0, zmodAddEquiv (-h) (j - i); zmodAddEquiv h (j - i), 0] := by
  -- The diagonal/off-diagonal shape leaves only two scalar identities, both coming from
  -- additivity of the canonical cyclic character together with the `-` transport lemmas.
  ext a b
  fin_cases a <;> fin_cases b
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hnegneg :
        (circleEquivComplex (zmod n (-h))) (-i) = (circleEquivComplex (zmod n h)) i := by
      simpa using zmodAddEquiv_neg_neg n h i
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul, hnegneg, mul_comm]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hneg :
        (circleEquivComplex (zmod n h)) (-i) = (circleEquivComplex (zmod n (-h))) i := by
      simpa using zmodAddEquiv_apply_neg n h i
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul, hneg, mul_comm]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Helper for Proposition 5-5.3-2: multiplying two explicit reflection matrices gives the
expected rotation matrix. -/
private theorem dihedral_reflection_reflection_matrix_mul (n : ℕ) [NeZero n] (h : ZMod n)
    (i j : ZMod n) :
    !![0, zmodAddEquiv (-h) i; zmodAddEquiv h i, 0] *
        !![0, zmodAddEquiv (-h) j; zmodAddEquiv h j, 0] =
      !![zmodAddEquiv h (j - i), 0; 0, zmodAddEquiv (-h) (j - i)] := by
  -- Again the only nonzero entries are the diagonal ones, and they match the dihedral product
  -- formula `sr i * sr j = r (j - i)`.
  ext a b
  fin_cases a <;> fin_cases b
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hneg :
        (circleEquivComplex (zmod n h)) (-i) = (circleEquivComplex (zmod n (-h))) i := by
      simpa using zmodAddEquiv_apply_neg n h i
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul, hneg, mul_comm]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hnegneg :
        (circleEquivComplex (zmod n (-h))) (-i) = (circleEquivComplex (zmod n h)) i := by
      simpa using zmodAddEquiv_neg_neg n h i
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul, hnegneg, mul_comm]

/-- The auxiliary linear action defining `ρ^h` is multiplicative on `DihedralGroup n`. -/
private theorem dihedralTwoDimensionalLinear_map_mul (n : ℕ) [NeZero n] (h : ZMod n)
    (x y : DihedralGroup n) :
    dihedralTwoDimensionalLinear n h (x * y) =
      dihedralTwoDimensionalLinear n h x * dihedralTwoDimensionalLinear n h y := by
  -- Route correction: the stable proof layer here is the explicit `2 x 2` matrix algebra, with
  -- `LinearMap.toMatrix'` translates the endomorphism identity into a direct `2 x 2` matrix
  -- identity, which is exactly the source calculation.
  cases x with
  | r i =>
      cases y with
      | r j =>
          apply LinearMap.toMatrix'.injective
          rw [Module.End.mul_eq_comp, LinearMap.toMatrix'_comp]
          ext a b
          fin_cases a <;> fin_cases b <;> simp [dihedralTwoDimensionalLinear,
            AddChar.map_add_eq_mul]
      | sr j =>
          apply LinearMap.toMatrix'.injective
          rw [Module.End.mul_eq_comp, LinearMap.toMatrix'_comp]
          simpa [dihedralTwoDimensionalLinear] using
            (dihedral_rotation_reflection_matrix_mul n h i j).symm
  | sr i =>
      cases y with
      | r j =>
          apply LinearMap.toMatrix'.injective
          rw [Module.End.mul_eq_comp, LinearMap.toMatrix'_comp]
          ext a b
          fin_cases a <;> fin_cases b <;> simp [dihedralTwoDimensionalLinear,
            AddChar.map_add_eq_mul]
      | sr j =>
          apply LinearMap.toMatrix'.injective
          rw [Module.End.mul_eq_comp, LinearMap.toMatrix'_comp]
          simpa [dihedralTwoDimensionalLinear] using
            (dihedral_reflection_reflection_matrix_mul n h i j).symm

/-- The two-dimensional complex representation `ρ^h` of `DihedralGroup n` given by Serre's
rotation and reflection matrices. -/
def dihedralTwoDimensionalRepresentation (n : ℕ) [NeZero n] (h : ZMod n) :
    Representation ℂ (DihedralGroup n) (Fin 2 → ℂ) where
  toFun := dihedralTwoDimensionalLinear n h
  map_one' := dihedralTwoDimensionalLinear_map_one n h
  map_mul' := dihedralTwoDimensionalLinear_map_mul n h

notation:max "ρ[" n "]" " ^ " h => dihedralTwoDimensionalRepresentation n h

/- The source-facing dihedral characters `χ_h`, `ψ₁`, and `ψ₂` are exported in the
`DihedralCharacter` scope. -/
scoped[DihedralCharacter] notation:max "χ_" h:max =>
  Representation.character (dihedralTwoDimensionalRepresentation _ h)

scoped[DihedralCharacter] notation:max "ψ₁[" n "]" =>
  Representation.character (Representation.trivial ℂ (DihedralGroup n) ℂ)

/-- The degree-1 dihedral character affording Serre's reflection-sign character `ψ₂`. -/
private theorem dihedralReflectionSignDegreeOneCharacter_map_one (n : ℕ) :
    (match (1 : DihedralGroup n) with
      | DihedralGroup.r _ => (1 : ℂˣ)
      | DihedralGroup.sr _ => (-1 : ℂˣ)) = 1 := by
  -- The identity is the zero rotation, so the sign character is trivial there.
  rw [show (1 : DihedralGroup n) = DihedralGroup.r 0 by simp]

/-- Helper for Proposition 5-5.3-2: the reflection-sign function is multiplicative on
`DihedralGroup n`. -/
private theorem dihedralReflectionSignDegreeOneCharacter_map_mul (n : ℕ)
    (x y : DihedralGroup n) :
    (match x * y with
      | DihedralGroup.r _ => (1 : ℂˣ)
      | DihedralGroup.sr _ => (-1 : ℂˣ)) =
      (match x with
        | DihedralGroup.r _ => (1 : ℂˣ)
        | DihedralGroup.sr _ => (-1 : ℂˣ)) *
        (match y with
          | DihedralGroup.r _ => (1 : ℂˣ)
          | DihedralGroup.sr _ => (-1 : ℂˣ)) := by
  -- Exhaust the four dihedral normal-form products; the sign bookkeeping is then immediate.
  cases x <;> cases y <;> simp

/-- The degree-1 dihedral character affording Serre's reflection-sign character `ψ₂`. -/
def dihedralReflectionSignDegreeOneCharacter (n : ℕ) : DihedralGroup n →* ℂˣ where
  toFun
    | DihedralGroup.r _ => 1
    | DihedralGroup.sr _ => -1
  map_one' := dihedralReflectionSignDegreeOneCharacter_map_one n
  map_mul' := dihedralReflectionSignDegreeOneCharacter_map_mul n

/-- The source's character `ψ₂`, given by `1` on rotations and `-1` on reflections. -/
scoped[DihedralCharacter] notation:max "ψ₂[" n "]" =>
  Representation.character (MonoidHom.toRepresentation (dihedralReflectionSignDegreeOneCharacter n))

open scoped DihedralCharacter

private def dihedralParityUnit {n : ℕ} (k : ZMod n) : ℂˣ :=
  (-1 : ℂˣ) ^ k.val

section

variable (n : ℕ) [NeZero n]

/-- On a rotation `r^k`, the character `χ_h` is the sum of the two canonical cyclic characters
indexed by `h` and `-h`. -/
theorem dihedralTwoDimensionalCharacter_apply_r (h k : ZMod n) :
    χ_ h (DihedralGroup.r k) =
      zmodAddEquiv h k + zmodAddEquiv (-h) k := by
  -- The trace of the diagonal rotation matrix is the sum of its diagonal entries.
  simp [Representation.character, dihedralTwoDimensionalRepresentation, dihedralTwoDimensionalLinear,
    Matrix.trace_fin_two]

/-- On a reflection `sr^k`, the character `χ_h` vanishes. -/
theorem dihedralTwoDimensionalCharacter_apply_sr (h k : ZMod n) :
    χ_ h (DihedralGroup.sr k) = 0 := by
  -- The defining reflection matrix is off-diagonal, so its trace is zero.
  simp [Representation.character, dihedralTwoDimensionalRepresentation, dihedralTwoDimensionalLinear,
    Matrix.trace_fin_two]

/-- The trivial dihedral character takes the value `1` on every element. -/
theorem dihedralTrivialCharacter_apply (g : DihedralGroup n) :
    ψ₁[n] g = 1 := by
  -- The trivial representation acts by the identity on the one-dimensional space `ℂ`.
  simp [Representation.character]

/-- The reflection-sign character takes the value `1` on every rotation. -/
theorem dihedralReflectionSignCharacter_apply_r (k : ZMod n) :
    ψ₂[n] (DihedralGroup.r k) = 1 := by
  -- This is the degree-one character formula specialized to a rotation.
  simpa [dihedralReflectionSignDegreeOneCharacter] using
    (MonoidHom.toRepresentation_character_apply
      (dihedralReflectionSignDegreeOneCharacter n) (DihedralGroup.r k))

/-- The reflection-sign character takes the value `-1` on every reflection. -/
theorem dihedralReflectionSignCharacter_apply_sr (k : ZMod n) :
    ψ₂[n] (DihedralGroup.sr k) = -1 := by
  -- The same degree-one character sends each reflection to the sign `-1`.
  simpa [dihedralReflectionSignDegreeOneCharacter] using
    (MonoidHom.toRepresentation_character_apply
      (dihedralReflectionSignDegreeOneCharacter n) (DihedralGroup.sr k))

/-- On a rotation `r^k`, the representation `ρ^h` is the diagonal matrix with entries
`w^(hk)` and `w^(-hk)`. -/
theorem dihedralTwoDimensionalRepresentation_apply_r (h k : ZMod n) :
    (ρ[n] ^ h) (DihedralGroup.r k) =
      Matrix.toLin' !![zmodAddEquiv h k, 0; 0, zmodAddEquiv (-h) k] :=
  rfl

/-- On a reflection `sr^k`, the representation `ρ^h` is the off-diagonal matrix from the text. -/
theorem dihedralTwoDimensionalRepresentation_apply_sr (h k : ZMod n) :
    (ρ[n] ^ h) (DihedralGroup.sr k) =
      Matrix.toLin' !![0, zmodAddEquiv (-h) k; zmodAddEquiv h k, 0] :=
  rfl

/-- The coordinate-swap linear equivalence on `Fin 2 → ℂ`. -/
private def dihedralCoordinateSwap : (Fin 2 → ℂ) ≃ₗ[ℂ] Fin 2 → ℂ :=
  LinearEquiv.funCongrLeft ℂ ℂ (Equiv.swap (0 : Fin 2) 1)

/-- Helper for Proposition 5-5.3-2: the coordinate swap sends the first output coordinate to the
original second coordinate. -/
private theorem dihedralCoordinateSwap_apply_zero (v : Fin 2 → ℂ) :
    dihedralCoordinateSwap v 0 = v 1 := by
  simp [dihedralCoordinateSwap, LinearEquiv.funCongrLeft]

/-- Helper for Proposition 5-5.3-2: the coordinate swap sends the second output coordinate to the
original first coordinate. -/
private theorem dihedralCoordinateSwap_apply_one (v : Fin 2 → ℂ) :
    dihedralCoordinateSwap v 1 = v 0 := by
  simp [dihedralCoordinateSwap, LinearEquiv.funCongrLeft]

-- Proof sketch: check the intertwining identity separately on rotations and reflections; swapping
-- the two coordinates exchanges the parameters `h` and `-h` in the explicit matrices.
/-- Swapping the two coordinates intertwines `ρ^h` with `ρ^{-h}`. -/
private theorem dihedralCoordinateSwap_intertwines_neg (h : ZMod n) (g : DihedralGroup n) :
    dihedralCoordinateSwap.toLinearMap ∘ₗ (ρ[n] ^ h) g =
      (ρ[n] ^ (-h)) g ∘ₗ dihedralCoordinateSwap.toLinearMap :=
  by
  -- Swapping the two coordinates exchanges the two diagonal characters and preserves the
  -- off-diagonal reflection shape, which is exactly the passage `h ↦ -h`.
  cases g with
  | r k =>
      apply LinearMap.ext
      intro v
      ext i
      fin_cases i
      · change ((ρ[n] ^ h) (DihedralGroup.r k) v) 1 =
            ((ρ[n] ^ (-h)) (DihedralGroup.r k) (dihedralCoordinateSwap v)) 0
        rw [dihedralTwoDimensionalRepresentation_apply_r, dihedralTwoDimensionalRepresentation_apply_r]
        simp [Matrix.toLin'_apply, dihedralCoordinateSwap_apply_zero, vecHead, vecTail]
      · change ((ρ[n] ^ h) (DihedralGroup.r k) v) 0 =
            ((ρ[n] ^ (-h)) (DihedralGroup.r k) (dihedralCoordinateSwap v)) 1
        rw [dihedralTwoDimensionalRepresentation_apply_r, dihedralTwoDimensionalRepresentation_apply_r]
        simp [Matrix.toLin'_apply, dihedralCoordinateSwap_apply_one, vecHead, vecTail]
  | sr k =>
      apply LinearMap.ext
      intro v
      ext i
      fin_cases i
      · change ((ρ[n] ^ h) (DihedralGroup.sr k) v) 1 =
            ((ρ[n] ^ (-h)) (DihedralGroup.sr k) (dihedralCoordinateSwap v)) 0
        rw [dihedralTwoDimensionalRepresentation_apply_sr, dihedralTwoDimensionalRepresentation_apply_sr]
        simp [Matrix.toLin'_apply, dihedralCoordinateSwap_apply_one, vecHead, vecTail]
      · change ((ρ[n] ^ h) (DihedralGroup.sr k) v) 0 =
            ((ρ[n] ^ (-h)) (DihedralGroup.sr k) (dihedralCoordinateSwap v)) 1
        rw [dihedralTwoDimensionalRepresentation_apply_sr, dihedralTwoDimensionalRepresentation_apply_sr]
        simp [Matrix.toLin'_apply, dihedralCoordinateSwap_apply_zero, vecHead, vecTail]

/-- Helper for Proposition 5-5.3-2: the diagonal vector fixed by the coordinate swap. -/
private def dihedralDiagonalVector : Fin 2 → ℂ :=
  Pi.basisFun ℂ (Fin 2) 0 + Pi.basisFun ℂ (Fin 2) 1

/-- Helper for Proposition 5-5.3-2: in the self-opposite case, every group element sends the
diagonal vector to a scalar multiple of itself. -/
private theorem dihedralSelfOpposite_apply_diagonal_vector
    (h : ZMod n) (hfix : h = -h) (g : DihedralGroup n) :
    ∃ c : ℂ, (ρ[n] ^ h) g dihedralDiagonalVector = c • dihedralDiagonalVector := by
  -- Route correction: the stable line is the diagonal line `ℂ · (e₀ + e₁)`, not a coordinate
  -- axis. The remaining step is the explicit scalar-action computation on that generator.
  cases g with
  | r k =>
      have hh : (circleEquivComplex (zmod n (-h))) k = (circleEquivComplex (zmod n h)) k := by
        have hh' : zmodAddEquiv (-h) k = zmodAddEquiv h k := by
          simpa using (congrArg (fun x : ZMod n => zmodAddEquiv x k) hfix).symm
        simpa using hh'
      refine ⟨zmodAddEquiv h k, ?_⟩
      -- When `h = -h`, both diagonal entries coincide, so the diagonal vector is an eigenvector.
      ext i
      fin_cases i
      · simp [dihedralDiagonalVector, dihedralTwoDimensionalRepresentation_apply_r,
          Matrix.toLin'_apply, hh]
      · simp [dihedralDiagonalVector, dihedralTwoDimensionalRepresentation_apply_r,
          Matrix.toLin'_apply, hh]
  | sr k =>
      have hh : (circleEquivComplex (zmod n (-h))) k = (circleEquivComplex (zmod n h)) k := by
        have hh' : zmodAddEquiv (-h) k = zmodAddEquiv h k := by
          simpa using (congrArg (fun x : ZMod n => zmodAddEquiv x k) hfix).symm
        simpa using hh'
      refine ⟨zmodAddEquiv h k, ?_⟩
      -- The reflection matrix has the same scalar on both off-diagonal entries in the
      -- self-opposite case, so it preserves the same diagonal line.
      ext i
      fin_cases i
      · simp [dihedralDiagonalVector, dihedralTwoDimensionalRepresentation_apply_sr,
          Matrix.toLin'_apply, hh]
      · simp [dihedralDiagonalVector, dihedralTwoDimensionalRepresentation_apply_sr,
          Matrix.toLin'_apply, hh]

/-- Helper for Proposition 5-5.3-2: the diagonal line is stable when `h = -h`. -/
private theorem dihedralSelfOpposite_diagonal_line_apply_mem
    (h : ZMod n) (hfix : h = -h) (g : DihedralGroup n)
    {v : Fin 2 → ℂ}
    (hv : v ∈ Submodule.span ℂ ({dihedralDiagonalVector} : Set (Fin 2 → ℂ))) :
    (ρ[n] ^ h) g v ∈ Submodule.span ℂ ({dihedralDiagonalVector} : Set (Fin 2 → ℂ)) := by
  rcases Submodule.mem_span_singleton.mp hv with ⟨c, rfl⟩
  rcases dihedralSelfOpposite_apply_diagonal_vector n h hfix g with ⟨d, hd⟩
  -- Once the generator is an eigenvector, every vector on its span stays on that same span.
  rw [LinearMap.map_smul, hd, smul_smul]
  exact Submodule.mem_span_singleton.mpr ⟨c * d, rfl⟩

/-- Helper for Proposition 5-5.3-2: the diagonal vector is nonzero. -/
private theorem dihedralDiagonalVector_ne_zero :
    dihedralDiagonalVector ≠ 0 := by
  -- The first coordinate of `e₀ + e₁` is `1`, so the vector cannot vanish.
  intro hzero
  have hcoord : dihedralDiagonalVector 0 = 0 := by
    simpa using congrFun hzero 0
  simp [dihedralDiagonalVector] at hcoord

/-- Helper for Proposition 5-5.3-2: the first coordinate basis vector does not lie on the
diagonal line. -/
private theorem dihedralCoordinateBasis_zero_not_mem_diagonal_span :
    Pi.basisFun ℂ (Fin 2) 0 ∉
      Submodule.span ℂ ({dihedralDiagonalVector} : Set (Fin 2 → ℂ)) := by
  -- A vector on the diagonal line has equal coordinates, whereas `e₀` does not.
  intro hmem
  rcases Submodule.mem_span_singleton.mp hmem with ⟨c, hc⟩
  have hcoord0 : c = 1 := by
    simpa [dihedralDiagonalVector] using congrFun hc 0
  have hcoord1 : c = 0 := by
    simpa [dihedralDiagonalVector] using congrFun hc 1
  exact one_ne_zero (hcoord0.symm.trans hcoord1)

/-- The canonical equivalence between `ρ^h` and `ρ^{-h}`. -/
def dihedralTwoDimensionalRepresentationNegEquiv (h : ZMod n) :
    (ρ[n] ^ h).Equiv (ρ[n] ^ (-h)) :=
  Representation.Equiv.mk dihedralCoordinateSwap
    (dihedralCoordinateSwap_intertwines_neg n h)

-- Proof sketch: when `h = -h`, the two diagonal characters on rotations coincide, so one of the
-- coordinate lines is stable under the whole action and yields a proper subrepresentation.
/-- If `h = -h`, then the representation `ρ^h` is reducible. -/
theorem dihedralTwoDimensionalRepresentation_not_isIrreducible_of_eq_neg
    (h : ZMod n) (hfix : h = -h) :
    ¬ (ρ[n] ^ h).IsIrreducible := by
  let U : Subrepresentation (ρ[n] ^ h) :=
    { toSubmodule := Submodule.span ℂ ({dihedralDiagonalVector} : Set (Fin 2 → ℂ))
      apply_mem_toSubmodule := by
        intro g v hv
        exact dihedralSelfOpposite_diagonal_line_apply_mem n h hfix g hv }
  have hUbot : U ≠ ⊥ := by
    intro hU
    -- The diagonal vector generates `U`, so `U` cannot be zero.
    have hmem : dihedralDiagonalVector ∈ U.toSubmodule := Submodule.mem_span_singleton_self _
    rw [hU] at hmem
    exact dihedralDiagonalVector_ne_zero (by simpa using hmem)
  have hUtop : U ≠ ⊤ := by
    intro hU
    -- The first coordinate axis is not the diagonal line, so `U` cannot be all of `ℂ²`.
    have hmem : Pi.basisFun ℂ (Fin 2) 0 ∈ (⊤ : Subrepresentation (ρ[n] ^ h)).toSubmodule := by
      change Pi.basisFun ℂ (Fin 2) 0 ∈ (⊤ : Submodule ℂ (Fin 2 → ℂ))
      simp
    rw [← hU] at hmem
    exact dihedralCoordinateBasis_zero_not_mem_diagonal_span hmem
  intro hirr
  exact hUtop ((hirr.eq_bot_or_eq_top U).resolve_left hUbot)

/-- Helper for Proposition 5-5.3-2: distinct parameters `h` and `-h` yield distinct cyclic
characters on some rotation. -/
private theorem exists_rotation_with_distinct_character_values
    (h : ZMod n) (hneg : h ≠ -h) :
    ∃ k : ZMod n, zmodAddEquiv h k ≠ zmodAddEquiv (-h) k := by
  -- The textbook inequality `w^h ≠ w^{-h}` means the two characters differ as functions,
  -- so they must differ at some input.
  by_contra hdistinct
  have hdistinct' : ∀ k : ZMod n, zmodAddEquiv h k = zmodAddEquiv (-h) k := by
    intro k
    by_contra hk
    exact hdistinct ⟨k, hk⟩
  apply hneg
  exact zmodAddEquiv.injective <| by
    ext k
    exact hdistinct' k

/-- Helper for Proposition 5-5.3-2: two distinct cyclic parameters differ on some rotation. -/
private theorem exists_rotation_separating_parameters
    {a b : ZMod n} (hne : a ≠ b) :
    ∃ k : ZMod n, zmodAddEquiv a k ≠ zmodAddEquiv b k := by
  -- Injectivity of the canonical `ZMod n` character parametrization turns functional equality
  -- of characters back into equality of parameters.
  by_contra hsame
  apply hne
  exact zmodAddEquiv.injective <| by
    ext k
    by_contra hk
    exact hsame ⟨k, hk⟩

/-- Helper for Proposition 5-5.3-2: the reflection `sr^0` swaps the two coordinate basis vectors
of `Fin 2 → ℂ`. -/
private theorem reflection_zero_swaps_coordinate_basis (h : ZMod n) :
    (ρ[n] ^ h) (DihedralGroup.sr 0) (Pi.basisFun ℂ (Fin 2) 0) = Pi.basisFun ℂ (Fin 2) 1 ∧
      (ρ[n] ^ h) (DihedralGroup.sr 0) (Pi.basisFun ℂ (Fin 2) 1) = Pi.basisFun ℂ (Fin 2) 0 := by
  constructor
  · -- At `sr 0`, the off-diagonal matrix sends the first basis vector to the second one.
    ext i
    fin_cases i <;> simp [dihedralTwoDimensionalRepresentation_apply_sr, Matrix.toLin'_apply]
  · -- The same specialized reflection sends the second basis vector back to the first one.
    ext i
    fin_cases i <;> simp [dihedralTwoDimensionalRepresentation_apply_sr, Matrix.toLin'_apply]

/-- Helper for Proposition 5-5.3-2: the reflection `sr^0` swaps the two coordinates of every
vector in `Fin 2 → ℂ`. -/
private theorem reflection_zero_apply_swap (h : ZMod n) (v : Fin 2 → ℂ) :
    (ρ[n] ^ h) (DihedralGroup.sr 0) v 0 = v 1 ∧
      (ρ[n] ^ h) (DihedralGroup.sr 0) v 1 = v 0 := by
  constructor <;> simp [dihedralTwoDimensionalRepresentation_apply_sr, Matrix.toLin'_apply,
    vecHead, vecTail]

/-- Helper for Proposition 5-5.3-2: a submodule containing both coordinate basis vectors is all of
`Fin 2 → ℂ`. -/
private theorem submodule_eq_top_of_coordinate_basis_mem
    {U : Submodule ℂ (Fin 2 → ℂ)}
    (h0 : Pi.basisFun ℂ (Fin 2) 0 ∈ U)
    (h1 : Pi.basisFun ℂ (Fin 2) 1 ∈ U) :
    U = ⊤ := by
  -- Every vector is the sum of its two coordinate components, so membership of both basis
  -- vectors forces membership of every vector.
  refine Submodule.eq_top_iff'.2 ?_
  intro v
  have hv0 : v 0 • Pi.basisFun ℂ (Fin 2) 0 ∈ U := U.smul_mem (v 0) h0
  have hv1 : v 1 • Pi.basisFun ℂ (Fin 2) 1 ∈ U := U.smul_mem (v 1) h1
  have hsum : v 0 • Pi.basisFun ℂ (Fin 2) 0 + v 1 • Pi.basisFun ℂ (Fin 2) 1 ∈ U :=
    U.add_mem hv0 hv1
  have hdecomp :
      v 0 • Pi.basisFun ℂ (Fin 2) 0 + v 1 • Pi.basisFun ℂ (Fin 2) 1 = v := by
    ext i
    fin_cases i <;> simp
  rw [← hdecomp]
  exact hsum

-- Proof sketch: the matrix of `ρ^h(r)` has distinct eigenvalues when `h ≠ -h`, so
-- any stable line must be a coordinate axis; the reflection matrices exchange the axes, so no
-- nontrivial proper stable line exists.
/-- Proposition 5-5.3-2: in the canonical `ZMod n` parametrization of Serre's family `ρ^h`, the
non-self-opposite cases `h ≠ -h` are irreducible. This is the `ZMod n` reformulation of the
text's condition `0 < h < n / 2`. -/
theorem dihedralTwoDimensionalRepresentation_isIrreducible
    (h : ZMod n) (hneg : h ≠ -h) :
    (ρ[n] ^ h).IsIrreducible := by
  letI : Nontrivial (Subrepresentation (ρ[n] ^ h)) :=
    ⟨⊥, ⊤, fun hU ↦
      bot_ne_top <| by simpa using congrArg Subrepresentation.toSubmodule hU⟩
  refine IsSimpleOrder.of_forall_eq_top fun U hU ↦ ?_
  let e0 : Fin 2 → ℂ := Pi.basisFun ℂ (Fin 2) 0
  let e1 : Fin 2 → ℂ := Pi.basisFun ℂ (Fin 2) 1
  obtain ⟨k, hk⟩ := exists_rotation_with_distinct_character_values n h hneg
  have hswap := reflection_zero_swaps_coordinate_basis n h
  have hUsub : U.toSubmodule ≠ ⊥ := by
    intro hUbot
    apply hU
    exact Subrepresentation.toSubmodule_injective hUbot
  rcases U.toSubmodule.ne_bot_iff.mp hUsub with ⟨v, hvU, hv0⟩
  -- Start from a nonzero vector in the stable subrepresentation. If it is already on one axis,
  -- the reflection `sr 0` produces the other axis; otherwise a separating rotation isolates both.
  by_cases h0 : v 0 = 0
  · have hv1 : v 1 ≠ 0 := by
      intro hv1
      apply hv0
      ext i
      fin_cases i <;> simp [h0, hv1]
    have hv_eq : v = v 1 • e1 := by
      ext i
      fin_cases i <;> simp [e1, h0]
    have he1_mem : e1 ∈ U.toSubmodule := by
      -- Rescaling a nonzero vector on the second axis recovers the second basis vector.
      have hscaled : (v 1)⁻¹ • v ∈ U.toSubmodule := U.toSubmodule.smul_mem (v 1)⁻¹ hvU
      rw [hv_eq, smul_smul] at hscaled
      simpa [e1, hv1] using hscaled
    have he0_mem : e0 ∈ U.toSubmodule := by
      -- The reflection `sr 0` swaps the axes, so stability transports `e₁` to `e₀`.
      have hsr_mem : (ρ[n] ^ h) (DihedralGroup.sr 0) e1 ∈ U.toSubmodule :=
        U.apply_mem_toSubmodule (DihedralGroup.sr 0) he1_mem
      rw [hswap.2] at hsr_mem
      exact hsr_mem
    exact Subrepresentation.toSubmodule_injective <|
      submodule_eq_top_of_coordinate_basis_mem he0_mem he1_mem
  · by_cases h1 : v 1 = 0
    · have hv_eq : v = v 0 • e0 := by
        ext i
        fin_cases i <;> simp [e0, h1]
      have he0_mem : e0 ∈ U.toSubmodule := by
        -- Rescaling a nonzero vector on the first axis recovers the first basis vector.
        have hscaled : (v 0)⁻¹ • v ∈ U.toSubmodule := U.toSubmodule.smul_mem (v 0)⁻¹ hvU
        rw [hv_eq, smul_smul] at hscaled
        simpa [e0, h0] using hscaled
      have he1_mem : e1 ∈ U.toSubmodule := by
        -- The same specialized reflection sends `e₀` to `e₁`.
        have hsr_mem : (ρ[n] ^ h) (DihedralGroup.sr 0) e0 ∈ U.toSubmodule :=
          U.apply_mem_toSubmodule (DihedralGroup.sr 0) he0_mem
        rw [hswap.1] at hsr_mem
        exact hsr_mem
      exact Subrepresentation.toSubmodule_injective <|
        submodule_eq_top_of_coordinate_basis_mem he0_mem he1_mem
    · let a : ℂ := zmodAddEquiv h k
      let b : ℂ := zmodAddEquiv (-h) k
      have hrv_mem : (ρ[n] ^ h) (DihedralGroup.r k) v ∈ U.toSubmodule :=
        U.apply_mem_toSubmodule (DihedralGroup.r k) hvU
      have hfirst_eq :
          (ρ[n] ^ h) (DihedralGroup.r k) v - b • v = ((a - b) * v 0) • e0 := by
        ext i
        fin_cases i
        · simp [a, b, e0, dihedralTwoDimensionalRepresentation_apply_r, Matrix.toLin'_apply,
            vecHead, vecTail]
          ring
        · simp [a, b, e0, dihedralTwoDimensionalRepresentation_apply_r, Matrix.toLin'_apply,
            vecHead, vecTail]
      have hsecond_eq :
          (ρ[n] ^ h) (DihedralGroup.r k) v - a • v = ((b - a) * v 1) • e1 := by
        ext i
        fin_cases i
        · simp [a, b, e1, dihedralTwoDimensionalRepresentation_apply_r, Matrix.toLin'_apply,
            vecHead, vecTail]
        · simp [a, b, e1, dihedralTwoDimensionalRepresentation_apply_r, Matrix.toLin'_apply,
            vecHead, vecTail]
          ring
      have hc0 : ((a - b) * v 0) ≠ 0 := by
        refine mul_ne_zero ?_ h0
        exact sub_ne_zero.mpr hk
      have hc1 : ((b - a) * v 1) ≠ 0 := by
        refine mul_ne_zero ?_ h1
        exact sub_ne_zero.mpr hk.symm
      have he0_mem : e0 ∈ U.toSubmodule := by
        -- Subtracting the second eigenspace component isolates the first basis vector.
        have hfirst_mem : (ρ[n] ^ h) (DihedralGroup.r k) v - b • v ∈ U.toSubmodule :=
          U.toSubmodule.sub_mem hrv_mem (U.toSubmodule.smul_mem b hvU)
        rw [hfirst_eq] at hfirst_mem
        have hscaled : ((a - b) * v 0)⁻¹ • (((a - b) * v 0) • e0) ∈ U.toSubmodule :=
          U.toSubmodule.smul_mem (((a - b) * v 0)⁻¹) hfirst_mem
        rw [smul_smul, inv_mul_cancel₀ hc0, one_smul] at hscaled
        exact hscaled
      have he1_mem : e1 ∈ U.toSubmodule := by
        -- Subtracting the first eigenspace component isolates the second basis vector.
        have hsecond_mem : (ρ[n] ^ h) (DihedralGroup.r k) v - a • v ∈ U.toSubmodule :=
          U.toSubmodule.sub_mem hrv_mem (U.toSubmodule.smul_mem a hvU)
        rw [hsecond_eq] at hsecond_mem
        have hscaled : ((b - a) * v 1)⁻¹ • (((b - a) * v 1) • e1) ∈ U.toSubmodule :=
          U.toSubmodule.smul_mem (((b - a) * v 1)⁻¹) hsecond_mem
        rw [smul_smul, inv_mul_cancel₀ hc1, one_smul] at hscaled
        exact hscaled
      exact Subrepresentation.toSubmodule_injective <|
        submodule_eq_top_of_coordinate_basis_mem he0_mem he1_mem

-- Proof sketch: compare the eigenvalues of `ρ^h(r)` and `ρ^{h'}(r)`; if `h'` is neither `h` nor
-- `-h`, the multisets of rotation eigenvalues differ, so no intertwining equivalence can exist.
/-- Distinct parameters not related by `h' = h` or `h' = -h` give nonisomorphic
two-dimensional dihedral representations. -/
theorem dihedralTwoDimensionalRepresentation_not_isomorphic
    {h h' : ZMod n} (hne : h' ≠ h) (hneg : h' ≠ -h) :
    ¬ Nonempty ((ρ[n] ^ h).Equiv (ρ[n] ^ h')) := by
  rintro ⟨e⟩
  let eI : Representation.IntertwiningMap (ρ[n] ^ h) (ρ[n] ^ h') := e.toIntertwiningMap
  let e0 : Fin 2 → ℂ := Pi.basisFun ℂ (Fin 2) 0
  let e1 : Fin 2 → ℂ := Pi.basisFun ℂ (Fin 2) 1
  let a : ℂ := e e0 0
  let b : ℂ := e e0 1
  obtain ⟨k, hk⟩ := exists_rotation_separating_parameters n (show h ≠ h' by simpa [eq_comm] using hne)
  obtain ⟨l, hl⟩ := exists_rotation_separating_parameters n (show h ≠ -h' by
    intro hh
    exact hneg (by simpa [hh]))
  have hswap_h := reflection_zero_swaps_coordinate_basis n h
  have hsr_e0 := reflection_zero_apply_swap n h' (e e0)
  have he1_zero : e e1 0 = b := by
    -- Intertwining `sr 0` forces the second basis vector to map to the swapped coordinates of
    -- the image of the first basis vector.
    have hsr := Representation.IntertwiningMap.isIntertwining
      (ρ := ρ[n] ^ h) (σ := ρ[n] ^ h') eI (DihedralGroup.sr 0) e0
    rw [hswap_h.1] at hsr
    exact (congrFun hsr 0).trans hsr_e0.1
  have he1_one : e e1 1 = a := by
    -- The other coordinate gives the symmetric matrix shape `[[a,b],[b,a]]`.
    have hsr := Representation.IntertwiningMap.isIntertwining
      (ρ := ρ[n] ^ h) (σ := ρ[n] ^ h') eI (DihedralGroup.sr 0) e0
    rw [hswap_h.1] at hsr
    exact (congrFun hsr 1).trans hsr_e0.2
  have hrot_e0_zero :
      zmodAddEquiv h k * a = zmodAddEquiv h' k * a := by
    -- The rotation relation on the first basis vector compares the first diagonal entries.
    have hrot := Representation.IntertwiningMap.isIntertwining
      (ρ := ρ[n] ^ h) (σ := ρ[n] ^ h') eI (DihedralGroup.r k) e0
    have he0_rot :
        (ρ[n] ^ h) (DihedralGroup.r k) e0 = zmodAddEquiv h k • e0 := by
      ext i
      fin_cases i <;> simp [e0, dihedralTwoDimensionalRepresentation_apply_r, Matrix.toLin'_apply,
        vecHead, vecTail]
    rw [he0_rot] at hrot
    have hcoord := congrFun hrot 0
    simpa [a, e0, dihedralTwoDimensionalRepresentation_apply_r, Matrix.toLin'_apply,
      vecHead, vecTail] using hcoord
  have hrot_e0_one :
      zmodAddEquiv h l * b = zmodAddEquiv (-h') l * b := by
    -- The same relation on the second coordinate compares against the opposite parameter.
    have hrot := Representation.IntertwiningMap.isIntertwining
      (ρ := ρ[n] ^ h) (σ := ρ[n] ^ h') eI (DihedralGroup.r l) e0
    have he0_rot :
        (ρ[n] ^ h) (DihedralGroup.r l) e0 = zmodAddEquiv h l • e0 := by
      ext i
      fin_cases i <;> simp [e0, dihedralTwoDimensionalRepresentation_apply_r, Matrix.toLin'_apply,
        vecHead, vecTail]
    rw [he0_rot] at hrot
    have hcoord := congrFun hrot 1
    simpa [b, e0, dihedralTwoDimensionalRepresentation_apply_r, Matrix.toLin'_apply,
      vecHead, vecTail] using hcoord
  have ha : a = 0 := by
    -- If `a` were nonzero, right-cancellation would force the forbidden equality `h = h'`.
    by_contra ha0
    exact hk (mul_right_cancel₀ ha0 hrot_e0_zero)
  have hb : b = 0 := by
    -- If `b` were nonzero, the same argument would force the forbidden equality `h = -h'`.
    by_contra hb0
    exact hl (mul_right_cancel₀ hb0 hrot_e0_one)
  have he0_zero : e e0 = 0 := by
    -- Both coordinates of `e e₀` vanish, so the vector itself vanishes.
    ext i
    fin_cases i <;> simp [a, b, ha, hb]
  have he0_ne_zero : e0 ≠ 0 := by
    intro he0
    have hcoord : e0 0 = 0 := by simpa using congrFun he0 0
    simp [e0] at hcoord
  exact he0_ne_zero <| e.toLinearEquiv.injective <| by simpa [e0] using he0_zero

end

section

variable (n : ℕ) [NeZero n]

/-- Helper for Proposition 5-5.3-2: the parity unit at `0` is trivial. -/
private theorem dihedralParityUnit_zero [Fact (Even n)] :
    dihedralParityUnit (0 : ZMod n) = 1 := by
  -- The exponent is `0`, so the parity sign is trivial.
  simp [dihedralParityUnit]

/-- Helper for Proposition 5-5.3-2: the parity unit only depends on the residue class modulo `2`,
so it is multiplicative on `ZMod n` when `n` is even. -/
private theorem dihedralParityUnit_add [NeZero n] [Fact (Even n)] (a b : ZMod n) :
    dihedralParityUnit (a + b) = dihedralParityUnit a * dihedralParityUnit b := by
  apply Units.ext
  have h2 : 2 ∣ n := even_iff_two_dvd.mp (Fact.out : Even n)
  -- Compare the underlying complex numbers and reduce both exponents modulo `2`.
  rw [dihedralParityUnit, dihedralParityUnit, dihedralParityUnit, Units.val_mul]
  rw [show (((-1 : ℂˣ) ^ (a + b).val : ℂˣ) : ℂ) = (-1 : ℂ) ^ (a + b).val by simp]
  rw [show (((-1 : ℂˣ) ^ a.val : ℂˣ) : ℂ) = (-1 : ℂ) ^ a.val by simp]
  rw [show (((-1 : ℂˣ) ^ b.val : ℂˣ) : ℂ) = (-1 : ℂ) ^ b.val by simp]
  rw [ZMod.val_add]
  calc
    (-1 : ℂ) ^ ((a.val + b.val) % n) = (-1 : ℂ) ^ (((a.val + b.val) % n) % 2) := by
      simpa using (neg_one_pow_eq_pow_mod_two (R := ℂ) ((a.val + b.val) % n))
    _ = (-1 : ℂ) ^ ((a.val + b.val) % 2) := by
      rw [Nat.mod_mod_of_dvd _ h2]
    _ = (-1 : ℂ) ^ ((a.val % 2) + (b.val % 2)) := by
      rw [Nat.add_mod]
      symm
      simpa using (neg_one_pow_eq_pow_mod_two (R := ℂ) ((a.val % 2) + (b.val % 2)))
    _ = (-1 : ℂ) ^ (a.val % 2) * (-1 : ℂ) ^ (b.val % 2) := by
      rw [pow_add]
    _ = (-1 : ℂ) ^ a.val * (-1 : ℂ) ^ b.val := by
      rw [← neg_one_pow_eq_pow_mod_two (R := ℂ) a.val,
        ← neg_one_pow_eq_pow_mod_two (R := ℂ) b.val]

/-- Helper for Proposition 5-5.3-2: negation preserves the parity sign on `ZMod n` when `n` is
even. -/
private theorem dihedralParityUnit_neg [NeZero n] [Fact (Even n)] (a : ZMod n) :
    dihedralParityUnit (-a) = dihedralParityUnit a := by
  apply Units.ext
  have h2 : 2 ∣ n := even_iff_two_dvd.mp (Fact.out : Even n)
  -- The residues `a` and `-a` have the same parity because `n` itself is even.
  rw [dihedralParityUnit, dihedralParityUnit]
  rw [show (((-1 : ℂˣ) ^ (-a).val : ℂˣ) : ℂ) = (-1 : ℂ) ^ (-a).val by simp]
  rw [show (((-1 : ℂˣ) ^ a.val : ℂˣ) : ℂ) = (-1 : ℂ) ^ a.val by simp]
  rw [ZMod.neg_val']
  calc
    (-1 : ℂ) ^ ((n - a.val) % n) = (-1 : ℂ) ^ (((n - a.val) % n) % 2) := by
      simpa using (neg_one_pow_eq_pow_mod_two (R := ℂ) ((n - a.val) % n))
    _ = (-1 : ℂ) ^ ((n - a.val) % 2) := by
      rw [Nat.mod_mod_of_dvd _ h2]
    _ = (-1 : ℂ) ^ a.val := by
      apply neg_one_pow_congr
      have hEvenSub : Even (n - a.val) ↔ Even a.val := by
        have h := Nat.even_sub (show a.val ≤ n by exact Nat.le_of_lt a.val_lt)
        simpa [Fact.out] using h
      exact (Even.mod_even_iff (n := n - a.val) (a := 2) (by decide : Even 2)).trans hEvenSub

/-- The degree-1 dihedral character affording Serre's even-`n` character `ψ₃`. -/
def dihedralRotationSignDegreeOneCharacter [Fact (Even n)] :
    DihedralGroup n →* ℂˣ where
  toFun
    | DihedralGroup.r k => dihedralParityUnit k
    | DihedralGroup.sr k => dihedralParityUnit k
  map_one' := by
    -- The identity element is `r 0`, and the parity sign is trivial there.
    rw [show (1 : DihedralGroup n) = DihedralGroup.r 0 by simp]
    exact dihedralParityUnit_zero n
  map_mul' x y := by
    -- The four normal-form products reduce to the additive parity formulas on `ZMod n`.
    cases x with
    | r a =>
        cases y with
        | r b =>
            simpa using dihedralParityUnit_add n a b
        | sr b =>
            calc
              dihedralParityUnit (b - a) = dihedralParityUnit (b + -a) := by
                  rw [sub_eq_add_neg]
              _ = dihedralParityUnit b * dihedralParityUnit (-a) := by
                  simpa using dihedralParityUnit_add n b (-a)
              _ = dihedralParityUnit a * dihedralParityUnit b := by
                  rw [dihedralParityUnit_neg, mul_comm]
    | sr a =>
        cases y with
        | r b =>
            simpa using dihedralParityUnit_add n a b
        | sr b =>
            calc
              dihedralParityUnit (b - a) = dihedralParityUnit (b + -a) := by
                  rw [sub_eq_add_neg]
              _ = dihedralParityUnit b * dihedralParityUnit (-a) := by
                  simpa using dihedralParityUnit_add n b (-a)
              _ = dihedralParityUnit a * dihedralParityUnit b := by
                  rw [dihedralParityUnit_neg, mul_comm]

/-- The degree-1 dihedral character affording Serre's even-`n` character `ψ₄`, obtained by
twisting `ψ₃` by the reflection-sign character `ψ₂`. -/
def dihedralRotationReflectionSignDegreeOneCharacter [Fact (Even n)] :
    DihedralGroup n →* ℂˣ :=
  dihedralRotationSignDegreeOneCharacter n * dihedralReflectionSignDegreeOneCharacter n

/- The source-facing even dihedral characters `ψ₃` and `ψ₄` are exported in the
`DihedralCharacter` scope. -/
scoped[DihedralCharacter] notation:max "ψ₃[" n "]" =>
  Representation.character
    (MonoidHom.toRepresentation (dihedralRotationSignDegreeOneCharacter n))
scoped[DihedralCharacter] notation:max "ψ₄[" n "]" =>
  Representation.character
    (MonoidHom.toRepresentation (dihedralRotationReflectionSignDegreeOneCharacter n))

section

variable [Fact (Even n)]

/-- The character `ψ₃` takes the value `(-1)^k` on `r^k`. -/
theorem dihedralRotationSignCharacter_apply_r (k : ZMod n) :
    ψ₃[n] (DihedralGroup.r k) = (-1 : ℂ) ^ k.val := by
  -- This is the direct character evaluation of the degree-one parity representation on a rotation.
  simpa [dihedralRotationSignDegreeOneCharacter, dihedralParityUnit] using
    (MonoidHom.toRepresentation_character_apply
      (dihedralRotationSignDegreeOneCharacter n) (DihedralGroup.r k))

/-- The character `ψ₃` takes the value `(-1)^k` on `sr^k`. -/
theorem dihedralRotationSignCharacter_apply_sr (k : ZMod n) :
    ψ₃[n] (DihedralGroup.sr k) = (-1 : ℂ) ^ k.val := by
  -- The same parity character has the same value on `sr^k`.
  simpa [dihedralRotationSignDegreeOneCharacter, dihedralParityUnit] using
    (MonoidHom.toRepresentation_character_apply
      (dihedralRotationSignDegreeOneCharacter n) (DihedralGroup.sr k))

/-- The character `ψ₄` takes the value `(-1)^k` on `r^k`. -/
theorem dihedralRotationReflectionSignCharacter_apply_r (k : ZMod n) :
    ψ₄[n] (DihedralGroup.r k) = (-1 : ℂ) ^ k.val := by
  -- On rotations, the `ψ₂` factor is trivial, so `ψ₄` agrees with `ψ₃`.
  simpa [dihedralRotationReflectionSignDegreeOneCharacter,
    dihedralRotationSignDegreeOneCharacter, dihedralReflectionSignDegreeOneCharacter,
    dihedralParityUnit] using
    (MonoidHom.toRepresentation_character_apply
      (dihedralRotationReflectionSignDegreeOneCharacter n) (DihedralGroup.r k))

/-- The character `ψ₄` takes the value `-(-1)^k` on `sr^k`. -/
theorem dihedralRotationReflectionSignCharacter_apply_sr (k : ZMod n) :
    ψ₄[n] (DihedralGroup.sr k) = -(-1 : ℂ) ^ k.val := by
  -- On reflections, the extra `ψ₂` factor contributes exactly one minus sign.
  simpa [dihedralRotationReflectionSignDegreeOneCharacter,
    dihedralRotationSignDegreeOneCharacter, dihedralReflectionSignDegreeOneCharacter,
    dihedralParityUnit, mul_comm] using
    (MonoidHom.toRepresentation_character_apply
      (dihedralRotationReflectionSignDegreeOneCharacter n) (DihedralGroup.sr k))

end

end

section

variable (n : ℕ) [NeZero n]

/-- Helper for Proposition 5-5.3-2: the even half-turn parameter in `ZMod n`. -/
private def dihedralHalfTurn [Fact (Even n)] : ZMod n :=
  (n / 2 : ℕ)

/-- Helper for Proposition 5-5.3-2: the half-turn parameter is self-opposite. -/
private theorem dihedralHalfTurn_add_self [Fact (Even n)] :
    dihedralHalfTurn n + dihedralHalfTurn n = (0 : ZMod n) := by
  have heven : Even n := Fact.out
  -- Doubling the half-turn gives the full period `n`, hence vanishes in `ZMod n`.
  calc
    dihedralHalfTurn n + dihedralHalfTurn n = ((2 * (n / 2) : ℕ) : ZMod n) := by
      simp [dihedralHalfTurn, two_mul, Nat.cast_add]
    _ = (n : ZMod n) := by
      rw [Nat.two_mul_div_two_of_even heven]
    _ = 0 := ZMod.natCast_self n

/-- Helper for Proposition 5-5.3-2: the half-turn parameter is nonzero. -/
private theorem dihedralHalfTurn_ne_zero [Fact (Even n)] :
    dihedralHalfTurn n ≠ (0 : ZMod n) := by
  have heven : Even n := Fact.out
  intro hzero
  -- A zero half-turn would force `n ≤ n / 2`, impossible for positive even `n`.
  have hcast : ((n / 2 : ℕ) : ZMod n) = 0 := by
    simpa [dihedralHalfTurn] using hzero
  have hdiv : n ∣ n / 2 := (ZMod.natCast_eq_zero_iff (n / 2) n).mp hcast
  have hhalfpos : 0 < n / 2 := by
    have hn : 2 * (n / 2) = n := Nat.two_mul_div_two_of_even heven
    have hpos : 0 < n := Nat.pos_of_neZero n
    omega
  have hle : n ≤ n / 2 := Nat.le_of_dvd hhalfpos hdiv
  omega

/-- Helper for Proposition 5-5.3-2: a nonzero self-opposite parameter must be the even half-turn
`n / 2`. -/
private theorem eq_dihedralHalfTurn_of_self_opposite_nonzero
    [Fact (Even n)] (h : ZMod n) (h0 : h ≠ 0) (hfix : h = -h) :
    h = dihedralHalfTurn n := by
  -- `ZMod.neg_eq_self_iff` classifies self-opposite elements as `0` or the half-turn.
  rcases (ZMod.neg_eq_self_iff h).mp hfix.symm with rfl | hval
  · exact (h0 rfl).elim
  · rw [← h.natCast_zmod_val]
    have hdiv : h.val = n / 2 := Nat.eq_div_of_mul_eq_right (by decide : 2 ≠ 0) (by omega)
    simp [dihedralHalfTurn, hdiv]

/-- Helper for Proposition 5-5.3-2: the half-turn parameter kills even residues. -/
private theorem dihedralHalfTurn_mul_of_even_val [Fact (Even n)]
    (k : ZMod n) (hk : Even k.val) :
    dihedralHalfTurn n * k = 0 := by
  have heven : Even n := Fact.out
  rcases hk with ⟨t, ht⟩
  -- Write `k` as an even natural residue and factor out the doubled half-turn.
  rw [← k.natCast_zmod_val, ht, show (t + t : ℕ) = 2 * t by omega, Nat.cast_mul]
  calc
    dihedralHalfTurn n * ((2 : ZMod n) * t) = (dihedralHalfTurn n * (2 : ZMod n)) * t := by
      ring
    _ = ((dihedralHalfTurn n + dihedralHalfTurn n) : ZMod n) * t := by
      ring
    _ = 0 := by
      simp [dihedralHalfTurn_add_self n]

/-- Helper for Proposition 5-5.3-2: the half-turn parameter fixes odd residues. -/
private theorem dihedralHalfTurn_mul_of_odd_val [Fact (Even n)]
    (k : ZMod n) (hk : Odd k.val) :
    dihedralHalfTurn n * k = dihedralHalfTurn n := by
  have heven : Even n := Fact.out
  rcases hk with ⟨t, ht⟩
  -- Write `k` as an odd residue and split off one copy of the half-turn.
  rw [← k.natCast_zmod_val, ht, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  calc
    dihedralHalfTurn n * ((2 : ZMod n) * t + (1 : ZMod n)) =
        dihedralHalfTurn n * ((2 : ZMod n) * t) + dihedralHalfTurn n := by
      ring
    _ = ((dihedralHalfTurn n * (2 : ZMod n)) * t) + dihedralHalfTurn n := by
      ring
    _ = ((dihedralHalfTurn n + dihedralHalfTurn n) : ZMod n) * t + dihedralHalfTurn n := by
      ring
    _ = dihedralHalfTurn n := by
      simp [dihedralHalfTurn_add_self n]

section

variable [Fact (Even n)]

/-- Helper for Proposition 5-5.3-2: the canonical half-turn character equals the parity sign. -/
private theorem zmodAddEquiv_dihedralHalfTurn_eq_parity (k : ZMod n) :
    zmodAddEquiv (dihedralHalfTurn n) k = (-1 : ℂ) ^ k.val := by
  have heven : Even n := Fact.out
  have hhalf_lt : n / 2 < n := by
    have hpos : 0 < n := Nat.pos_of_neZero n
    omega
  by_cases hk : Even k.val
  · have hmul : dihedralHalfTurn n * k = 0 := dihedralHalfTurn_mul_of_even_val n k hk
    -- Even residues map to the trivial character value.
    calc
      zmodAddEquiv (dihedralHalfTurn n) k =
          Complex.exp (2 * Real.pi * Complex.I * ↑((dihedralHalfTurn n * k).val) / ↑n) := by
            simpa [dihedralHalfTurn] using
              (AddChar.zmodAddEquiv_apply_eq_exp (n := n) (h := dihedralHalfTurn n) (k := k))
      _ = 1 := by
            rw [hmul]
            simp
      _ = (-1 : ℂ) ^ k.val := by
            symm
            exact Even.neg_one_pow hk
  · have hkodd : Odd k.val := Nat.not_even_iff_odd.mp hk
    have hmul : dihedralHalfTurn n * k = dihedralHalfTurn n :=
      dihedralHalfTurn_mul_of_odd_val n k hkodd
    have hval : (dihedralHalfTurn n).val = n / 2 := by
      simpa [dihedralHalfTurn] using
        (ZMod.val_natCast_of_lt hhalf_lt : ((n / 2 : ℕ) : ZMod n).val = n / 2)
    -- Odd residues land on the unique nontrivial value `exp(π i) = -1`.
    calc
      zmodAddEquiv (dihedralHalfTurn n) k =
          Complex.exp (2 * Real.pi * Complex.I * ↑((dihedralHalfTurn n * k).val) / ↑n) := by
            simpa [dihedralHalfTurn] using
              (AddChar.zmodAddEquiv_apply_eq_exp (n := n) (h := dihedralHalfTurn n) (k := k))
      _ = Complex.exp (2 * Real.pi * Complex.I * ↑(n / 2 : ℕ) / ↑n) := by
            rw [hmul, hval]
      _ = Complex.exp (Real.pi * Complex.I) := by
            have hpi : (2 * Real.pi * Complex.I * ↑(n / 2 : ℕ) / ↑n : ℂ) =
                Real.pi * Complex.I := by
              have hn : (n : ℂ) ≠ 0 := by
                exact_mod_cast (Nat.pos_of_neZero n).ne'
              field_simp [hn, Nat.two_mul_div_two_of_even heven]
              exact_mod_cast Nat.two_mul_div_two_of_even heven
            rw [hpi]
      _ = -1 := Complex.exp_pi_mul_I
      _ = (-1 : ℂ) ^ k.val := by
            symm
            exact Odd.neg_one_pow hkodd

/-- Helper for Proposition 5-5.3-2: every nonzero self-opposite parameter is the parity
character. -/
private theorem zmodAddEquiv_self_opposite_nonzero_eq_parity
    (h : ZMod n) (h0 : h ≠ 0) (hfix : h = -h) (k : ZMod n) :
    zmodAddEquiv h k = (-1 : ℂ) ^ k.val := by
  -- First identify `h` with the half-turn, then evaluate that half-turn explicitly.
  rw [eq_dihedralHalfTurn_of_self_opposite_nonzero n h h0 hfix]
  exact zmodAddEquiv_dihedralHalfTurn_eq_parity n k

/-- The exceptional self-opposite nonzero parameter yields the even-`n` decomposition
`χ_h = ψ₃ + ψ₄`. -/
theorem dihedralTwoDimensionalCharacter_eq_rotationSign_add_rotationReflectionSign_of_eq_neg
    (h : ZMod n) (h0 : h ≠ 0) (hfix : h = -h) :
    χ_ h = ψ₃[n] + ψ₄[n] := by
  ext g
  cases g with
  | r k =>
      -- On rotations, `χ_h` is twice the parity character, and `ψ₃ + ψ₄` has the same value.
      calc
        χ_ h (DihedralGroup.r k)
            = zmodAddEquiv h k + zmodAddEquiv (-h) k := by
                rw [dihedralTwoDimensionalCharacter_apply_r]
        _ = (-1 : ℂ) ^ k.val + zmodAddEquiv (-h) k := by
              rw [zmodAddEquiv_self_opposite_nonzero_eq_parity n h h0 hfix]
        _ = (-1 : ℂ) ^ k.val + (-1 : ℂ) ^ k.val := by
              rw [← hfix, zmodAddEquiv_self_opposite_nonzero_eq_parity n h h0 hfix]
        _ = ψ₃[n] (DihedralGroup.r k) + ψ₄[n] (DihedralGroup.r k) := by
              rw [dihedralRotationSignCharacter_apply_r,
                dihedralRotationReflectionSignCharacter_apply_r]
  | sr k =>
      -- On reflections, both sides vanish: `χ_h` by trace and `ψ₃ + ψ₄` by cancellation.
      calc
        χ_ h (DihedralGroup.sr k) = 0 := dihedralTwoDimensionalCharacter_apply_sr n h k
        _ = ψ₃[n] (DihedralGroup.sr k) + ψ₄[n] (DihedralGroup.sr k) := by
              rw [dihedralRotationSignCharacter_apply_sr,
                dihedralRotationReflectionSignCharacter_apply_sr]
              ring

end

end
