import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_59.Lemma_8_25
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_60.Definition_8_60_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

noncomputable section

-- Semantic search note: no `lean_leansearch`-style MCP tool was available in this runner, so the
-- canonical owners were checked directly against mathlib's manifold Lie bracket, Lie group Lie
-- algebra, associative Lie algebra, and matrix/endomorphism APIs.
-- Primitive data here is the bundled smooth-section owner and the left-invariance predicate.
-- The matrix and endomorphism commutator identities, as well as matrix-space dimensions, are
-- derived API from the canonical associative-Lie and finrank owners.

section SmoothVectorFields

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open VectorField

local notation "SmoothVectorField" => Cₛ^∞⟮I; E, fun p : M ↦ TangentSpace I p⟯

/- Example 8.36 (1): the canonical owner for the smooth vector fields on a smooth manifold `M` is
the bundled smooth-section type `Cₛ^∞⟮I; E, TangentSpace I⟯`. -/
#check (SmoothVectorField : Type _)

/-- The bracket on bundled smooth vector fields is induced by the manifold Lie bracket. -/
instance : Bracket SmoothVectorField SmoothVectorField where
  bracket X Y := ⟨mlieBracket I X Y, by
    haveI : IsManifold I (minSmoothness ℝ 2) M := .of_le (n := (∞ : ℕ∞ω)) <| by
      have h : (2 : ℕ∞ω) ≤ ∞ := by
        decide
      simpa [minSmoothness] using h
    haveI : IsManifold I ((∞ : ℕ∞ω) + 1) M := .of_le (n := (∞ : ℕ∞ω)) (by simp)
    simpa using
      ContDiff.mlieBracket_vectorField (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞))
        X.contMDiff Y.contMDiff (by simp)⟩

/-- Helper for Example 8.36: coercing the bundled bracket of smooth vector fields to a pointwise
vector field recovers `mlieBracket I X Y`. -/
@[simp]
theorem smoothVectorFieldBracket_apply (X Y : SmoothVectorField) :
    ((⁅X, Y⁆ : SmoothVectorField) : Π p : M, TangentSpace I p) = mlieBracket I X Y :=
  rfl

/-- Helper for Example 8.36: the bundled Lie bracket is additive in its first argument. -/
theorem smoothVectorField_add_lie (X Y Z : SmoothVectorField) :
    ⁅X + Y, Z⁆ = ⁅X, Z⁆ + ⁅Y, Z⁆ := by
  -- Normalize the bundled operations to pointwise vector fields at a fixed base point.
  ext p
  have hX : MDiffAt (fun q : M ↦ (X q : TangentBundle I M)) p :=
    X.contMDiff p |>.mdifferentiableAt (by simp)
  have hY : MDiffAt (fun q : M ↦ (Y q : TangentBundle I M)) p :=
    Y.contMDiff p |>.mdifferentiableAt (by simp)
  change
    mlieBracket I (((X : Π q : M, TangentSpace I q) + (Y : Π q : M, TangentSpace I q)))
      (Z : Π q : M, TangentSpace I q) p =
      (⁅X, Z⁆ + ⁅Y, Z⁆) p
  -- After this normalization, the canonical manifold bracket identity applies directly.
  rw [mlieBracket_add_left hX hY]
  rfl

/-- Helper for Example 8.36: the bundled Lie bracket is additive in its second argument. -/
theorem smoothVectorField_lie_add (X Y Z : SmoothVectorField) :
    ⁅X, Y + Z⁆ = ⁅X, Y⁆ + ⁅X, Z⁆ := by
  -- Normalize the bundled operations to pointwise vector fields at a fixed base point.
  ext p
  have hY : MDiffAt (fun q : M ↦ (Y q : TangentBundle I M)) p :=
    Y.contMDiff p |>.mdifferentiableAt (by simp)
  have hZ : MDiffAt (fun q : M ↦ (Z q : TangentBundle I M)) p :=
    Z.contMDiff p |>.mdifferentiableAt (by simp)
  change
    mlieBracket I (X : Π q : M, TangentSpace I q)
      (((Y : Π q : M, TangentSpace I q) + (Z : Π q : M, TangentSpace I q))) p =
      (⁅X, Y⁆ + ⁅X, Z⁆) p
  -- After this normalization, the canonical manifold bracket identity applies directly.
  rw [mlieBracket_add_right hY hZ]
  rfl

/-- Helper for Example 8.36: the bundled Lie bracket of a smooth vector field with itself
vanishes. -/
theorem smoothVectorField_lie_self (X : SmoothVectorField) :
    ⁅X, X⁆ = 0 := by
  -- Evaluate pointwise and reduce to the antisymmetry of the manifold Lie bracket.
  ext p
  change mlieBracket I (X : Π q : M, TangentSpace I q) X p = 0
  simpa using (VectorField.mlieBracket_self (I := I) (V := (X : Π q : M, TangentSpace I q)) (x := p))

/-- Helper for Example 8.36: the bundled Lie bracket satisfies the Leibniz identity. -/
theorem smoothVectorField_leibniz_lie (X Y Z : SmoothVectorField) :
    ⁅X, ⁅Y, Z⁆⁆ = ⁅⁅X, Y⁆, Z⁆ + ⁅Y, ⁅X, Z⁆⁆ := by
  haveI : IsManifold I (minSmoothness ℝ 3) M := .of_le (n := (∞ : ℕ∞ω)) <| by
    have h : (3 : ℕ∞ω) ≤ ∞ := by
      decide
    simpa [minSmoothness] using h
  -- Normalize the nested bundled brackets to the canonical pointwise manifold Lie bracket.
  ext p
  change
    mlieBracket I (X : Π q : M, TangentSpace I q) (mlieBracket I Y Z) p =
      mlieBracket I (mlieBracket I X Y) (Z : Π q : M, TangentSpace I q) p +
        mlieBracket I (Y : Π q : M, TangentSpace I q) (mlieBracket I X Z) p
  -- The pointwise Jacobi identity is exactly `leibniz_identity_mlieBracket_apply`.
  apply leibniz_identity_mlieBracket_apply
  · exact (X.contMDiff p).of_le (by
      have h : (2 : ℕ∞ω) ≤ ∞ := by
        decide
      simpa [minSmoothness] using h)
  · exact (Y.contMDiff p).of_le (by
      have h : (2 : ℕ∞ω) ≤ ∞ := by
        decide
      simpa [minSmoothness] using h)
  · exact (Z.contMDiff p).of_le (by
      have h : (2 : ℕ∞ω) ≤ ∞ := by
        decide
      simpa [minSmoothness] using h)

/-- The bundled smooth vector fields on `M` form a Lie ring under the manifold Lie bracket. -/
instance : LieRing SmoothVectorField where
  add_lie := smoothVectorField_add_lie
  lie_add := smoothVectorField_lie_add
  lie_self := smoothVectorField_lie_self
  leibniz_lie := smoothVectorField_leibniz_lie

/-- Helper for Example 8.36: the bundled Lie bracket is compatible with real scalar
multiplication in the second argument. -/
theorem smoothVectorField_lie_smul (c : ℝ) (X Y : SmoothVectorField) :
    ⁅X, c • Y⁆ = c • ⁅X, Y⁆ := by
  -- Normalize the bundled scalar multiplication to the pointwise vector-field operation.
  ext p
  have hY : MDiffAt (fun q : M ↦ (Y q : TangentBundle I M)) p :=
    Y.contMDiff p |>.mdifferentiableAt (by simp)
  change
    mlieBracket I (X : Π q : M, TangentSpace I q) (c • (Y : Π q : M, TangentSpace I q)) p =
      (c • ⁅X, Y⁆) p
  -- The canonical manifold bracket identity gives the desired scalar-compatibility.
  rw [mlieBracket_const_smul_right hY]
  rfl

/-- The bundled smooth vector fields on `M` form a real Lie algebra under the manifold Lie
bracket. -/
instance : LieAlgebra ℝ SmoothVectorField where
  lie_smul := smoothVectorField_lie_smul

end SmoothVectorFields

section LeftInvariantSmoothVectorFields

universe uE uH uG

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {G : Type uG} [TopologicalSpace G] [ChartedSpace H G] [Group G]
variable [IsManifold I ∞ G] [LieGroup I ∞ G]

open VectorField

local notation "SmoothVectorField" => Cₛ^∞⟮I; E, fun g : G ↦ TangentSpace I g⟯

/-- Helper for Example 8.36: the zero smooth vector field on a Lie group is left-invariant. -/
theorem isLeftInvariant_zero :
    IsLeftInvariant ((0 : SmoothVectorField) : Π g : G, TangentSpace I g) := by
  intro g
  -- Pullback preserves the zero vector field, so the pointwise evaluations agree.
  simpa using
    (VectorField.mpullback_zero (I := I) (I' := I) (f := fun x : G ↦ g * x))

/-- Helper for Example 8.36: the sum of left-invariant smooth vector fields is left-invariant. -/
theorem isLeftInvariant_add (X Y : SmoothVectorField)
    (hX : IsLeftInvariant (X : Π g : G, TangentSpace I g))
    (hY : IsLeftInvariant (Y : Π g : G, TangentSpace I g)) :
    IsLeftInvariant ((X + Y : SmoothVectorField) : Π g : G, TangentSpace I g) := by
  intro g
  -- Normalize the bundled sum to the pointwise sum of vector fields.
  ext h
  change
    mpullback I I (fun x : G ↦ g * x)
      ((X : Π q : G, TangentSpace I q) + (Y : Π q : G, TangentSpace I q)) h =
      (((X : Π q : G, TangentSpace I q) + (Y : Π q : G, TangentSpace I q)) h)
  -- Pullback is additive, so the left-invariance hypotheses rewrite the result.
  rw [VectorField.mpullback_add_apply]
  simp [hX g, hY g]

/-- Helper for Example 8.36: real scalar multiples of left-invariant smooth vector fields are
left-invariant. -/
theorem isLeftInvariant_smul (c : ℝ) (X : SmoothVectorField)
    (hX : IsLeftInvariant (X : Π g : G, TangentSpace I g)) :
    IsLeftInvariant ((c • X : SmoothVectorField) : Π g : G, TangentSpace I g) := by
  intro g
  -- Normalize the bundled scalar multiple to the pointwise scalar multiple.
  ext h
  change
    mpullback I I (fun x : G ↦ g * x) (c • (X : Π q : G, TangentSpace I q)) h =
      (c • (X : Π q : G, TangentSpace I q)) h
  -- Pullback commutes with constant scalar multiplication.
  rw [VectorField.mpullback_const_smul_apply]
  simp [hX g]

/-- Helper for Example 8.36: the Lie bracket of left-invariant smooth vector fields is
left-invariant. -/
theorem isLeftInvariant_lie (X Y : SmoothVectorField)
    (hX : IsLeftInvariant (X : Π g : G, TangentSpace I g))
    (hY : IsLeftInvariant (Y : Π g : G, TangentSpace I g)) :
    IsLeftInvariant ((⁅X, Y⁆ : SmoothVectorField) : Π g : G, TangentSpace I g) := by
  intro g
  haveI : IsManifold I (minSmoothness ℝ 2) G := .of_le (n := (∞ : ℕ∞ω)) <| by
    have h : (2 : ℕ∞ω) ≤ ∞ := by
      decide
    simpa [minSmoothness] using h
  -- Evaluate the pullback identity pointwise and transport the bracket through pullback.
  ext h
  rw [smoothVectorFieldBracket_apply]
  rw [VectorField.mpullback_mlieBracket
    (X.contMDiff (g * h) |>.mdifferentiableAt (by simp))
    (Y.contMDiff (g * h) |>.mdifferentiableAt (by simp))
    ((contMDiff_mul_left (I := I) (a := g) : ContMDiff I I ∞ (fun x : G ↦ g * x)).contMDiffAt)
    (by
      have h₂ : (2 : ℕ∞ω) ≤ ∞ := by
        decide
      simpa [minSmoothness] using h₂)]
  -- The left-invariance hypotheses identify the pulled-back bracket with the original one.
  rw [hX g, hY g]

/-- Example 8.36 (2): the smooth left-invariant vector fields on a Lie group `G`, viewed as the
Lie subalgebra of the bundled smooth vector fields cut out by `VectorField.IsLeftInvariant`. This
is a bridge/view on the canonical owner `GroupLieAlgebra I G`, not a second core owner. -/
def smooth_left_invariant_vector_fields : LieSubalgebra ℝ SmoothVectorField where
  carrier := { X | IsLeftInvariant (X : Π g : G, TangentSpace I g) }
  add_mem' := fun {X Y} hX hY ↦ isLeftInvariant_add X Y hX hY
  zero_mem' := isLeftInvariant_zero
  smul_mem' := fun c X hX ↦ isLeftInvariant_smul c X hX
  lie_mem' := fun {X Y} hX hY ↦ isLeftInvariant_lie X Y hX hY

/-- Membership in `smooth_left_invariant_vector_fields` is exactly smooth left-invariance. -/
@[simp]
theorem mem_smooth_left_invariant_vector_fields
    (X : SmoothVectorField) :
    X ∈ smooth_left_invariant_vector_fields ↔
      IsLeftInvariant (X : Π g : G, TangentSpace I g) := by
  -- Unfold the carrier set defining the Lie subalgebra.
  simpa [smooth_left_invariant_vector_fields]

end LeftInvariantSmoothVectorFields

section MatrixAndEndomorphismExamples

open Matrix

variable (n : ℕ)

/- Example 8.36 (3): on real `n × n` matrices, the Lie bracket is the commutator `AB - BA`. -/
#check
  (LieRing.of_associative_ring_bracket :
    ∀ A B : Matrix (Fin n) (Fin n) ℝ, ⁅A, B⁆ = A * B - B * A)

/-- Example 8.36 (4): the real matrix Lie algebra `Matrix (Fin n) (Fin n) ℝ` has dimension
`n^2` over `ℝ`. -/
theorem real_matrix_lie_algebra_finrank :
    Module.finrank ℝ (Matrix (Fin n) (Fin n) ℝ) = n ^ 2 := by
  rw [Module.finrank_matrix]
  simp [pow_two]

/- Example 8.36 (5): on complex `n × n` matrices, regarded as a real vector space, the Lie
bracket is again the commutator `AB - BA`. -/
#check
  (LieRing.of_associative_ring_bracket :
    ∀ A B : Matrix (Fin n) (Fin n) ℂ, ⁅A, B⁆ = A * B - B * A)

/-- Example 8.36 (6): the complex matrix Lie algebra `Matrix (Fin n) (Fin n) ℂ`, regarded as a
real Lie algebra, has real dimension `2 n^2`. -/
theorem complex_matrix_real_lie_algebra_finrank :
    Module.finrank ℝ (Matrix (Fin n) (Fin n) ℂ) = 2 * n ^ 2 := by
  rw [Module.finrank_matrix, Complex.finrank_real_complex]
  simp [pow_two, Nat.mul_assoc, Nat.mul_comm]

universe u

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- Example 8.36 (7): the Lie bracket on endomorphisms of a real vector space is the commutator
of linear maps. -/
theorem linear_endomorphism_commutator_apply
    (A B : Module.End ℝ V) (v : V) :
    ⁅A, B⁆ v = A (B v) - B (A v) := by
  simpa using congrFun (LieRing.of_associative_ring_bracket A B) v

/- Example 8.36 (8): under the standard basis of `ℝ^n`, the canonical matrix/endomorphism
equivalence `LinearMap.toMatrixAlgEquiv'` is already a Lie algebra equivalence via
`AlgEquiv.toLieEquiv`. -/
#check
  ((LinearMap.toMatrixAlgEquiv' :
      Module.End ℝ (Fin n → ℝ) ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℝ).toLieEquiv :
    Module.End ℝ (Fin n → ℝ) ≃ₗ⁅ℝ⁆ Matrix (Fin n) (Fin n) ℝ)

end MatrixAndEndomorphismExamples

section AbelianLieAlgebra

universe u

variable (V : Type u) [AddCommGroup V]

/-- Example 8.36 (9): any real vector space can be regarded as an abelian Lie algebra by keeping
the underlying vector space and declaring all brackets to be zero. -/
def abelian_lie_algebra : Type u := V

instance : AddCommGroup (abelian_lie_algebra V) :=
  inferInstanceAs (AddCommGroup V)

section

variable [Module ℝ V]

instance : Module ℝ (abelian_lie_algebra V) :=
  inferInstanceAs (Module ℝ V)

/-- The bracket on `abelian_lie_algebra V` is identically zero. -/
instance : Bracket (abelian_lie_algebra V) (abelian_lie_algebra V) where
  bracket _ _ := 0

/-- `abelian_lie_algebra V` is a Lie ring with the zero bracket. -/
instance : LieRing (abelian_lie_algebra V) where
  add_lie _ _ _ := by
    change (0 : abelian_lie_algebra V) = 0 + 0
    simp
  lie_add _ _ _ := by
    change (0 : abelian_lie_algebra V) = 0 + 0
    simp
  lie_self _ := by
    change (0 : abelian_lie_algebra V) = 0
    rfl
  leibniz_lie _ _ _ := by
    change (0 : abelian_lie_algebra V) = 0 + 0
    simp

/-- `abelian_lie_algebra V` is a real Lie algebra with the zero bracket. -/
instance : LieAlgebra ℝ (abelian_lie_algebra V) where
  lie_smul _ _ _ := by
    change (0 : abelian_lie_algebra V) = _ • 0
    simp

end

/-- Every bracket in `abelian_lie_algebra V` vanishes. -/
theorem abelian_lie_algebra_bracket_eq_zero
    (x y : abelian_lie_algebra V) :
    ⁅x, y⁆ = 0 := rfl

/-- `abelian_lie_algebra V` is abelian in the Lie-theoretic sense. -/
theorem abelian_lie_algebra_isLieAbelian :
    IsLieAbelian (abelian_lie_algebra V) :=
  ⟨fun _ _ ↦ rfl⟩

end AbelianLieAlgebra
