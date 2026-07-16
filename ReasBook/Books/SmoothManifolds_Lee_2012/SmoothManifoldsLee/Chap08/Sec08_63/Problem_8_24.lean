import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap07.Sec07_53.Problem_7_2
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_60.Corollary_8_38
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_60.Example_8_36

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold ContDiff
open VectorField

universe uH uE uG

variable {H : Type uH} [TopologicalSpace H]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {I : ModelWithCorners ℝ E H}
variable {G : Type uG} [TopologicalSpace G] [ChartedSpace H G] [Group G]
variable [LieGroup I ∞ G]

local instance : LieGroup I (minSmoothness ℝ 3) G := .of_le (n := (∞ : ℕ∞ω)) <| by
  have h : (3 : ℕ∞ω) ≤ ∞ := by
    decide
  simpa [minSmoothness] using h

-- Domain sampling for this file:
-- * source-facing layer: right-invariant smooth vector fields on a Lie group;
-- * chapter owner abstraction: bundled smooth vector fields
--   `Cₛ^∞⟮I; E, fun g : G ↦ TangentSpace I g⟯` and its
--   Lie-subalgebra specialization `smooth_left_invariant_vector_fields` from `Example_8_36`;
-- * relevant mathlib/project declarations checked here: `GroupLieAlgebra`,
--   `mulInvariantVectorField`, `VectorField.mpullback`, and `VectorField.mpullback_mlieBracket`.
-- Primitive data is the vector field itself; smoothness is carried by the bundled owner
-- `Cₛ^∞⟮I; E, fun g : G ↦ TangentSpace I g⟯`, not by a separate wrapper package.

local notation "SmoothVectorField" => Cₛ^∞⟮I; E, fun g : G ↦ TangentSpace I g⟯

namespace VectorField

/-- Right-invariance predicate for Problem 8-24: a smooth vector field on a Lie group is fixed by
pullback along every right translation. -/
def IsRightInvariant (X : Π g : G, TangentSpace I g) : Prop :=
  ∀ g : G,
    mpullback I I (· * g) X = X

end VectorField

/-- Helper for Problem 8-24: the zero smooth vector field on a Lie group is right-invariant. -/
theorem isRightInvariant_zero :
    VectorField.IsRightInvariant ((0 : SmoothVectorField) : Π g : G, TangentSpace I g) := by
  intro g
  -- Pullback by right translation preserves the zero vector field.
  exact VectorField.mpullback_zero (I := I) (I' := I) (f := fun x : G ↦ x * g)

/-- Helper for Problem 8-24: sums of right-invariant smooth vector fields are right-invariant. -/
theorem isRightInvariant_add (X Y : SmoothVectorField)
    (hX : VectorField.IsRightInvariant (X : Π g : G, TangentSpace I g))
    (hY : VectorField.IsRightInvariant (Y : Π g : G, TangentSpace I g)) :
    VectorField.IsRightInvariant ((X + Y : SmoothVectorField) : Π g : G, TangentSpace I g) := by
  intro g
  -- Evaluate the pullback pointwise and transport addition through `mpullback`.
  ext h
  change
    VectorField.mpullback I I (fun x : G ↦ x * g)
      ((X : Π q : G, TangentSpace I q) + (Y : Π q : G, TangentSpace I q)) h =
      (((X : Π q : G, TangentSpace I q) + (Y : Π q : G, TangentSpace I q)) h)
  rw [VectorField.mpullback_add_apply]
  simp [hX g, hY g]

/-- Helper for Problem 8-24: real scalar multiples of right-invariant smooth vector fields are
right-invariant. -/
theorem isRightInvariant_smul (c : ℝ) (X : SmoothVectorField)
    (hX : VectorField.IsRightInvariant (X : Π g : G, TangentSpace I g)) :
    VectorField.IsRightInvariant ((c • X : SmoothVectorField) : Π g : G, TangentSpace I g) := by
  intro g
  -- Evaluate the pullback pointwise and commute scalar multiplication through `mpullback`.
  ext h
  change
    VectorField.mpullback I I (fun x : G ↦ x * g) (c • (X : Π q : G, TangentSpace I q)) h =
      (c • (X : Π q : G, TangentSpace I q)) h
  rw [VectorField.mpullback_const_smul_apply]
  simp [hX g]

/-- Helper for Problem 8-24: the Lie bracket of right-invariant smooth vector fields is
right-invariant. -/
theorem isRightInvariant_lie (X Y : SmoothVectorField)
    (hX : VectorField.IsRightInvariant (X : Π g : G, TangentSpace I g))
    (hY : VectorField.IsRightInvariant (Y : Π g : G, TangentSpace I g)) :
    VectorField.IsRightInvariant ((⁅X, Y⁆ : SmoothVectorField) : Π g : G, TangentSpace I g) := by
  intro g
  haveI : IsManifold I (minSmoothness ℝ 2) G := .of_le (n := (∞ : ℕ∞ω)) <| by
    have h₂ : (2 : ℕ∞ω) ≤ ∞ := by
      decide
    simpa [minSmoothness] using h₂
  -- Transport the manifold Lie bracket through pullback by right translation.
  ext h
  rw [smoothVectorFieldBracket_apply]
  simpa [hX g, hY g] using
    (VectorField.mpullback_mlieBracket
      (I := I) (I' := I)
      (f := fun x : G ↦ x * g) (V := (X : Π q : G, TangentSpace I q))
      (W := (Y : Π q : G, TangentSpace I q)) (x₀ := h)
      (X.contMDiff (h * g) |>.mdifferentiableAt (by simp))
      (Y.contMDiff (h * g) |>.mdifferentiableAt (by simp))
      ((contMDiff_mul_right (I := I) (a := g) : ContMDiff I I ∞ (fun x : G ↦ x * g)) h)
      (by
        have h₂ : (2 : ℕ∞ω) ≤ ∞ := by
          decide
        simpa [minSmoothness] using h₂))

/-- Lie subalgebra for Problem 8-24: the smooth right-invariant vector fields on `G`. -/
def smooth_right_invariant_vector_fields : LieSubalgebra ℝ SmoothVectorField where
  carrier := { X | VectorField.IsRightInvariant X.1 }
  zero_mem' := isRightInvariant_zero
  add_mem' := fun {X Y} hX hY ↦ isRightInvariant_add X Y hX hY
  smul_mem' := fun c X hX ↦ isRightInvariant_smul c X hX
  lie_mem' := fun {X Y} hX hY ↦ isRightInvariant_lie X Y hX hY

local notation "RightInvariantSmoothVectorField" =>
  (smooth_right_invariant_vector_fields : LieSubalgebra ℝ SmoothVectorField)

/-- Membership in `smooth_right_invariant_vector_fields` is exactly smooth right-invariance. -/
@[simp] theorem mem_smooth_right_invariant_vector_fields
    (X : SmoothVectorField) :
    X ∈ RightInvariantSmoothVectorField ↔
      VectorField.IsRightInvariant X.1 := by
  rfl

/-- Closure result for Problem 8-24: the Lie bracket of two smooth right-invariant vector fields
is again smooth and right-invariant. -/
theorem lie_mem_smooth_right_invariant_vector_fields
    {X Y : SmoothVectorField}
    (hX : X ∈ RightInvariantSmoothVectorField)
    (hY : Y ∈ RightInvariantSmoothVectorField) :
    ⁅X, Y⁆ ∈ RightInvariantSmoothVectorField := by
  -- The Lie-subalgebra structure packages the closure result proved above.
  simpa using smooth_right_invariant_vector_fields.lie_mem hX hY

/-- Helper for Problem 8-24: the manifold derivative of inversion is invertible at every point of
the Lie group. -/
theorem mfderiv_inv_isInvertible (g : G) :
    (mfderiv% (fun x : G ↦ x⁻¹) g).IsInvertible := by
  have hInv : MDifferentiableAt I I (fun x : G ↦ x⁻¹) g := by
    simpa using (contMDiff_inv I (∞ : WithTop ℕ∞)).mdifferentiableAt (x := g)
  have hInv' : MDifferentiableAt I I (fun x : G ↦ x⁻¹) g⁻¹ := by
    simpa using (contMDiff_inv I (∞ : WithTop ℕ∞)).mdifferentiableAt (x := g⁻¹)
  -- Differentiate `inv ∘ inv = id` in both orders to produce explicit two-sided inverses.
  have hLeft :
      mfderiv% (fun x : G ↦ x⁻¹) (g⁻¹) ∘L mfderiv% (fun x : G ↦ x⁻¹) g =
        ContinuousLinearMap.id ℝ (TangentSpace I g) := by
    have hcomp :=
      mfderiv_comp (x := g) (I := I) (I' := I) (I'' := I)
        (g := fun x : G ↦ x⁻¹) (f := fun x : G ↦ x⁻¹) hInv' hInv
    have hfunComp : ((fun x : G ↦ x⁻¹) ∘ fun x : G ↦ x⁻¹) = id := by
      funext x
      simp [Function.comp]
    have hcomp' := hcomp.symm
    rw [hfunComp, mfderiv_id] at hcomp'
    have hgg : g⁻¹⁻¹ = g := by simp
    exact hgg ▸ hcomp'
  have hRight :
      mfderiv% (fun x : G ↦ x⁻¹) g ∘L mfderiv% (fun x : G ↦ x⁻¹) (g⁻¹) =
        ContinuousLinearMap.id ℝ (TangentSpace I g⁻¹) := by
    have hcomp :=
      mfderiv_comp (x := g⁻¹) (I := I) (I' := I) (I'' := I)
        (g := fun x : G ↦ x⁻¹) (f := fun x : G ↦ x⁻¹)
        (by simpa using hInv) hInv'
    have hfunComp : ((fun x : G ↦ x⁻¹) ∘ fun x : G ↦ x⁻¹) = id := by
      funext x
      simp [Function.comp]
    have hcomp' := hcomp.symm
    rw [hfunComp, mfderiv_id] at hcomp'
    have hRightRaw :
        mfderiv% (fun x : G ↦ x⁻¹) (g⁻¹⁻¹) ∘L mfderiv% (fun x : G ↦ x⁻¹) (g⁻¹) =
          ContinuousLinearMap.id ℝ (TangentSpace I g⁻¹) := hcomp'
    have hgg : g⁻¹⁻¹ = g := by simp
    rw [hgg] at hRightRaw
    exact hRightRaw
  exact ContinuousLinearMap.IsInvertible.of_inverse hRight hLeft

/-- Helper for Problem 8-24: inversion pullback turns left-invariant vector fields into
right-invariant vector fields. -/
theorem isRightInvariant_mpullback_inv_of_isLeftInvariant
    {X : Π g : G, TangentSpace I g}
    (hX : VectorField.IsLeftInvariant X) :
    VectorField.IsRightInvariant (VectorField.mpullback I I (fun g : G ↦ g⁻¹) X) := by
  intro g
  -- Rewrite the right-translation pullback through the factorization
  -- `(x * g)⁻¹ = g⁻¹ * x⁻¹`.
  ext x
  have hcomp₁ :=
    VectorField.mpullbackWithin_comp_of_left
      (I := I) (I' := I) (I'' := I)
      (g := fun y : G ↦ y⁻¹) (f := fun y : G ↦ y * g) (V := X)
      (s := Set.univ) (t := Set.univ) (x₀ := x)
      (by
        simpa using
          (mdifferentiableAt_mul_right (I := I) (a := g) (b := x) :
            MDiffAt (· * g) x))
      (by simp)
      (uniqueMDiffWithinAt_univ I)
      (by
        simpa [mfderivWithin_univ] using
          mfderiv_inv_isInvertible (I := I) (G := G) (g := x * g))
  have hcomp₂ :=
    VectorField.mpullbackWithin_comp_of_right
      (I := I) (I' := I) (I'' := I)
      (g := fun y : G ↦ g⁻¹ * y) (f := fun y : G ↦ y⁻¹) (V := X)
      (s := Set.univ) (t := Set.univ) (x₀ := x)
      (by
        simpa using
          (mdifferentiableAt_mul_left (I := I) (a := g⁻¹) (b := x⁻¹) :
            MDiffAt (g⁻¹ * ·) x⁻¹))
      (by simp)
      (uniqueMDiffWithinAt_univ I)
      (by
        simpa [mfderivWithin_univ] using
          mfderiv_inv_isInvertible (I := I) (G := G) (g := x))
  have hfun :
      ((fun y : G ↦ y⁻¹) ∘ fun y : G ↦ y * g) =
        (fun y : G ↦ g⁻¹ * y) ∘ fun y : G ↦ y⁻¹ := by
    funext y
    simp [Function.comp]
  calc
    VectorField.mpullback I I (fun y : G ↦ y * g)
        (VectorField.mpullback I I (fun y : G ↦ y⁻¹) X) x
      = VectorField.mpullback I I (((fun y : G ↦ y⁻¹) ∘ fun y : G ↦ y * g)) X x := by
          simpa [VectorField.mpullbackWithin_univ, Function.comp] using hcomp₁.symm
    _ = VectorField.mpullback I I ((fun y : G ↦ g⁻¹ * y) ∘ fun y : G ↦ y⁻¹) X x := by
          rw [hfun]
    _ = VectorField.mpullback I I (fun y : G ↦ y⁻¹)
          (VectorField.mpullback I I (fun y : G ↦ g⁻¹ * y) X) x := by
          simpa [VectorField.mpullbackWithin_univ, Function.comp] using hcomp₂
    _ = VectorField.mpullback I I (fun y : G ↦ y⁻¹) X x := by
          rw [hX g⁻¹]

/-- Helper for Problem 8-24: inversion pullback turns right-invariant vector fields into
left-invariant vector fields. -/
theorem isLeftInvariant_mpullback_inv_of_isRightInvariant
    {X : Π g : G, TangentSpace I g}
    (hX : VectorField.IsRightInvariant X) :
    VectorField.IsLeftInvariant (VectorField.mpullback I I (fun g : G ↦ g⁻¹) X) := by
  intro g
  -- Rewrite the left-translation pullback through the factorization
  -- `(g * x)⁻¹ = x⁻¹ * g⁻¹`.
  ext x
  have hcomp₁ :=
    VectorField.mpullbackWithin_comp_of_left
      (I := I) (I' := I) (I'' := I)
      (g := fun y : G ↦ y⁻¹) (f := fun y : G ↦ g * y) (V := X)
      (s := Set.univ) (t := Set.univ) (x₀ := x)
      (by
        simpa using
          (mdifferentiableAt_mul_left (I := I) (a := g) (b := x) :
            MDiffAt (g * ·) x))
      (by simp)
      (uniqueMDiffWithinAt_univ I)
      (by
        simpa [mfderivWithin_univ] using
          mfderiv_inv_isInvertible (I := I) (G := G) (g := g * x))
  have hcomp₂ :=
    VectorField.mpullbackWithin_comp_of_right
      (I := I) (I' := I) (I'' := I)
      (g := fun y : G ↦ y * g⁻¹) (f := fun y : G ↦ y⁻¹) (V := X)
      (s := Set.univ) (t := Set.univ) (x₀ := x)
      (by
        simpa using
          (mdifferentiableAt_mul_right (I := I) (a := g⁻¹) (b := x⁻¹) :
            MDiffAt (· * g⁻¹) x⁻¹))
      (by simp)
      (uniqueMDiffWithinAt_univ I)
      (by
        simpa [mfderivWithin_univ] using
          mfderiv_inv_isInvertible (I := I) (G := G) (g := x))
  have hfun :
      ((fun y : G ↦ y⁻¹) ∘ fun y : G ↦ g * y) =
        (fun y : G ↦ y * g⁻¹) ∘ fun y : G ↦ y⁻¹ := by
    funext y
    simp [Function.comp]
  calc
    VectorField.mpullback I I (fun y : G ↦ g * y)
        (VectorField.mpullback I I (fun y : G ↦ y⁻¹) X) x
      = VectorField.mpullback I I (((fun y : G ↦ y⁻¹) ∘ fun y : G ↦ g * y)) X x := by
          simpa [VectorField.mpullbackWithin_univ, Function.comp] using hcomp₁.symm
    _ = VectorField.mpullback I I ((fun y : G ↦ y * g⁻¹) ∘ fun y : G ↦ y⁻¹) X x := by
          rw [hfun]
    _ = VectorField.mpullback I I (fun y : G ↦ y⁻¹)
          (VectorField.mpullback I I (fun y : G ↦ y * g⁻¹) X) x := by
          simpa [VectorField.mpullbackWithin_univ, Function.comp] using hcomp₂
    _ = VectorField.mpullback I I (fun y : G ↦ y⁻¹) X x := by
          rw [hX g⁻¹]

/-- Helper for Problem 8-24: pulling back twice by inversion returns the original vector field. -/
theorem mpullback_inv_involutive
    (X : Π g : G, TangentSpace I g) :
    VectorField.mpullback I I (fun g : G ↦ g⁻¹)
      (VectorField.mpullback I I (fun g : G ↦ g⁻¹) X) = X := by
  ext x
  -- Route correction: normalize double pullback through the composition `inv ∘ inv = id`.
  have hcomp :=
    VectorField.mpullbackWithin_comp_of_left
      (I := I) (I' := I) (I'' := I)
      (g := fun y : G ↦ y⁻¹) (f := fun y : G ↦ y⁻¹) (V := X)
      (s := Set.univ) (t := Set.univ) (x₀ := x)
      (by
        simpa using
          (((contMDiff_inv I (∞ : WithTop ℕ∞)).mdifferentiableAt (x := x) (by simp)) :
            MDiffAt (fun y : G ↦ y⁻¹) x))
      (by simp)
      (uniqueMDiffWithinAt_univ I)
      (by
        simpa [mfderivWithin_univ] using
          mfderiv_inv_isInvertible (I := I) (G := G) (g := x⁻¹))
  simpa [VectorField.mpullbackWithin_univ, Function.comp] using hcomp.symm

/-- Helper for Problem 8-24: pulling a vector field back by inversion evaluates at the identity as
the negative of its original value there. -/
theorem inversion_pullback_apply_one
    (X : Π g : G, TangentSpace I g) :
    VectorField.mpullback I I (fun g : G ↦ g⁻¹) X 1 = -X 1 := by
  have hInv : (mfderiv% (fun g : G ↦ g⁻¹) (1 : G)).IsInvertible :=
    mfderiv_inv_isInvertible (I := I) (G := G) (g := 1)
  -- Use the characterization of the inverse linear map at the identity.
  rw [VectorField.mpullback_apply, inv_one]
  apply (hInv.inverse_apply_eq).2
  simpa using (mfderiv_inv_at_one_apply (I := I) (G := G) (-X 1)).symm

/-- Helper for Problem 8-24: the inversion pullback of `mulInvariantVectorField v` is smooth. -/
theorem inversion_pullback_mulInvariantVectorField_contMDiff
    (v : GroupLieAlgebra I G) :
    ContMDiff I I.tangent ∞
      (T% (VectorField.mpullback I I (fun g : G ↦ g⁻¹) (mulInvariantVectorField v))) := by
  -- Pullback by inversion preserves smoothness because inversion has invertible derivative.
  have hLeftInvariant : VectorField.IsLeftInvariant (mulInvariantVectorField v) := by
    intro g
    simpa using mpullback_mulInvariantVectorField (I := I) (g := g) v
  have hSmooth :
      ContMDiff I I.tangent ∞ (T% (mulInvariantVectorField v)) :=
    left_invariant_rough_vector_field_smooth (I := I) (G := G)
      (X := mulInvariantVectorField v) hLeftInvariant
  simpa using
    hSmooth.mpullback_vectorField
      (I := I) (I' := I)
      (f := fun g : G ↦ g⁻¹)
      (hf := contMDiff_inv I (∞ : WithTop ℕ∞))
      (hf' := fun g ↦ mfderiv_inv_isInvertible (I := I) (G := G) (g := g))
      (hmn := by simp)

/-- The inversion pullback of the left-invariant vector field determined by `v`. -/
def inversion_pushforward_mulInvariantVectorField (v : GroupLieAlgebra I G) : SmoothVectorField :=
  ⟨VectorField.mpullback I I (fun g : G ↦ g⁻¹) (mulInvariantVectorField v),
    inversion_pullback_mulInvariantVectorField_contMDiff (I := I) (G := G) v⟩

/-- Helper for Problem 8-24: the inversion pushforward of a left-invariant field evaluates at the
identity as the negative of the original tangent vector. -/
theorem inversion_pushforward_mulInvariantVectorField_apply_one
    (v : GroupLieAlgebra I G) :
    inversion_pushforward_mulInvariantVectorField (I := I) (G := G) v 1 = -v := by
  -- Evaluate the inversion pullback at the identity and simplify the left-invariant field there.
  have hmul : mulInvariantVectorField v 1 = v := by
    have hfun : (fun x : G ↦ (1 : G) * x) = id := by
      funext x
      simp
    change (mfderiv% (fun x : G ↦ (1 : G) * x) 1) v = v
    rw [hfun, mfderiv_id]
    rfl
  calc
    inversion_pushforward_mulInvariantVectorField (I := I) (G := G) v 1
        = -(mulInvariantVectorField v 1) := by
            simpa [inversion_pushforward_mulInvariantVectorField] using
              inversion_pullback_apply_one (I := I) (G := G) (X := mulInvariantVectorField v)
    _ = -v := by rw [hmul]

/-- The inversion pullback of a left-invariant vector field is smooth and right-invariant. -/
  theorem inversion_pushforward_mulInvariantVectorField_mem_smooth_right_invariant_vector_fields
    (v : GroupLieAlgebra I G) :
    inversion_pushforward_mulInvariantVectorField v ∈
      RightInvariantSmoothVectorField := by
  -- The left-invariant source field becomes right-invariant after pullback by inversion.
  simpa
      [mem_smooth_right_invariant_vector_fields, inversion_pushforward_mulInvariantVectorField]
    using
    isRightInvariant_mpullback_inv_of_isLeftInvariant (I := I)
      (X := mulInvariantVectorField v) (by
        intro g
        simpa using mpullback_mulInvariantVectorField (I := I) (g := g) v)

/-- The inversion pullback intertwines addition on left-invariant vector fields. -/
theorem inversion_pushforward_mulInvariantVectorField_add (v w : GroupLieAlgebra I G) :
    inversion_pushforward_mulInvariantVectorField (v + w) =
      inversion_pushforward_mulInvariantVectorField v +
        inversion_pushforward_mulInvariantVectorField w := by
  -- Pullback is additive, so the bundled smooth fields agree pointwise.
  ext g
  simpa [inversion_pushforward_mulInvariantVectorField, mulInvariantVectorField_add] using
    congrFun
      (VectorField.mpullback_add
        (I := I) (I' := I) (f := fun x : G ↦ x⁻¹)
        (V := mulInvariantVectorField v) (V₁ := mulInvariantVectorField w))
      g

/-- The inversion pullback intertwines scalar multiplication on left-invariant vector fields. -/
theorem inversion_pushforward_mulInvariantVectorField_smul
    (c : ℝ) (v : GroupLieAlgebra I G) :
    inversion_pushforward_mulInvariantVectorField (c • v) =
      c • inversion_pushforward_mulInvariantVectorField v := by
  -- Pullback commutes with constant scalar multiplication.
  ext g
  simpa [inversion_pushforward_mulInvariantVectorField, mulInvariantVectorField_smul] using
    congrFun
      (VectorField.mpullback_const_smul
        (I := I) (I' := I) (f := fun x : G ↦ x⁻¹)
        (c := c) (V := mulInvariantVectorField v))
      g

/-- Linear map for Problem 8-24: pushforward by inversion sends `GroupLieAlgebra I G` to the
smooth right-invariant vector fields on `G`. -/
def inversion_pushforward_on_groupLieAlgebra :
    GroupLieAlgebra I G →ₗ[ℝ] RightInvariantSmoothVectorField where
  toFun v :=
    ⟨inversion_pushforward_mulInvariantVectorField v,
      inversion_pushforward_mulInvariantVectorField_mem_smooth_right_invariant_vector_fields v⟩
  map_add' v w := by
    apply Subtype.ext
    simpa using inversion_pushforward_mulInvariantVectorField_add v w
  map_smul' c v := by
    apply Subtype.ext
    simpa using inversion_pushforward_mulInvariantVectorField_smul c v

/-- Bijectivity statement for Problem 8-24: pushforward by inversion gives a bijection from the
Lie algebra of `G` to the smooth right-invariant vector fields on `G`. -/
theorem inversion_pushforward_on_groupLieAlgebra_bijective :
    Function.Bijective
      (inversion_pushforward_on_groupLieAlgebra :
        GroupLieAlgebra I G → RightInvariantSmoothVectorField) := by
  refine ⟨?_, ?_⟩
  · intro v w h
    -- Evaluate at the identity to recover the negative of the source tangent vectors.
    have hEval :
        inversion_pushforward_mulInvariantVectorField (I := I) (G := G) v 1 =
          inversion_pushforward_mulInvariantVectorField (I := I) (G := G) w 1 := by
      simpa [inversion_pushforward_on_groupLieAlgebra] using
        congrArg (fun X : RightInvariantSmoothVectorField => X.1 1) h
    have hNeg : -v = -w := by
      simpa [inversion_pushforward_mulInvariantVectorField_apply_one] using hEval
    exact neg_injective hNeg
  · intro X
    rcases X with ⟨X, hXmem⟩
    refine ⟨-X 1, ?_⟩
    apply Subtype.ext
    ext g
    have hX : VectorField.IsRightInvariant (X : Π h : G, TangentSpace I h) := by
      simpa using hXmem
    have hLeft :
        VectorField.IsLeftInvariant
          (VectorField.mpullback I I (fun h : G ↦ h⁻¹) (X : Π h : G, TangentSpace I h)) := by
      exact isLeftInvariant_mpullback_inv_of_isRightInvariant (I := I) (X := X) hX
    have hPullback :
        VectorField.mpullback I I (fun h : G ↦ h⁻¹) (X : Π h : G, TangentSpace I h) =
          mulInvariantVectorField (-X 1) := by
      -- Identify the left-invariant pullback by its value at the identity.
      calc
        VectorField.mpullback I I (fun h : G ↦ h⁻¹) (X : Π h : G, TangentSpace I h)
            = mulInvariantVectorField
                ((VectorField.mpullback I I (fun h : G ↦ h⁻¹)
                  (X : Π h : G, TangentSpace I h)) 1) := by
                    simpa using
                      (left_invariant_rough_vector_field_eq_mulInvariantVectorField
                        (I := I) (G := G)
                        (X := VectorField.mpullback I I (fun h : G ↦ h⁻¹)
                          (X : Π h : G, TangentSpace I h))
                        hLeft)
        _ = mulInvariantVectorField (-X 1) := by
              congr 1
              simpa using
                inversion_pullback_apply_one (I := I) (G := G)
                  (X := (X : Π h : G, TangentSpace I h))
    have hRecovered :
        VectorField.mpullback I I (fun h : G ↦ h⁻¹) (mulInvariantVectorField (-X 1)) = X := by
      -- Pulling back again by inversion cancels the first pullback.
      calc
        VectorField.mpullback I I (fun h : G ↦ h⁻¹) (mulInvariantVectorField (-X 1))
            = VectorField.mpullback I I (fun h : G ↦ h⁻¹)
                (VectorField.mpullback I I (fun h : G ↦ h⁻¹)
                  (X : Π h : G, TangentSpace I h)) := by
                    rw [hPullback.symm]
        _ = X := mpullback_inv_involutive (I := I) (G := G) X
    simpa
        [inversion_pushforward_on_groupLieAlgebra, inversion_pushforward_mulInvariantVectorField]
      using
      congrFun hRecovered g

/-- Problem 8-24: pushforward by inversion preserves the Lie bracket on the smooth
right-invariant vector fields associated to `GroupLieAlgebra I G`. -/
theorem inversion_pushforward_on_groupLieAlgebra_map_lie
    (v w : GroupLieAlgebra I G) :
    inversion_pushforward_on_groupLieAlgebra ⁅v, w⁆ =
      ⁅inversion_pushforward_on_groupLieAlgebra v, inversion_pushforward_on_groupLieAlgebra w⁆ :=
  by
  apply Subtype.ext
  ext g
  -- Reduce both sides to the naturality of the manifold Lie bracket under pullback by inversion.
  simpa
      [inversion_pushforward_on_groupLieAlgebra, inversion_pushforward_mulInvariantVectorField,
        smoothVectorFieldBracket_apply, GroupLieAlgebra.bracket_def,
        mulInvariantVector_mlieBracket]
    using
    (VectorField.mpullback_mlieBracket
      (I := I) (I' := I)
      (f := fun x : G ↦ x⁻¹)
      (V := mulInvariantVectorField v) (W := mulInvariantVectorField w) (x₀ := g)
      (n := minSmoothness ℝ 3)
      (mdifferentiableAt_mulInvariantVectorField (I := I) (v := v) (g := g⁻¹))
      (mdifferentiableAt_mulInvariantVectorField (I := I) (v := w) (g := g⁻¹))
      ((contMDiff_inv I (minSmoothness ℝ 3)).contMDiffAt (x := g))
      (minSmoothness_monotone (𝕜 := ℝ) (by norm_num)))
