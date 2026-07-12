import Mathlib
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Topology.Algebra.Group.Matrix

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold
open scoped Matrix.Norms.L2Operator
open VectorField

local notation "Vec" n => Fin n → ℝ
local notation "End" n => (Vec n) →L[ℝ] Vec n
local notation "Mat" n => Matrix (Fin n) (Fin n) ℝ
local notation "GL" n => (End n)ˣ
local notation "I" n => 𝓘(ℝ, End n)
local notation "LieGL" n => GroupLieAlgebra (I n) (GL n)

-- Domain sampling pass: this item lies in the Lie-group / matrix-Lie-algebra interface for the
-- standard endomorphism model of `GL(n, ℝ) = GL(ℝ^n)`. Relevant owner declarations checked before
-- refinement:
-- `GroupLieAlgebra` from `Mathlib.Geometry.Manifold.GroupLieAlgebra` as the core/canonical owner,
-- `LinearMap.toMatrixAlgEquiv'` from the matrix/endomorphism API (canonical bridge/view from
-- `Module.End ℝ (Fin n → ℝ)` to matrices),
-- `Module.End.toContinuousLinearMap` as the intrinsic mathlib bridge underlying that owner,
-- and the matrix commutator Lie algebra from `Mathlib.Algebra.Lie.OfAssociative` /
-- `Mathlib.Algebra.Lie.Matrix`.
-- Primitive data here is the Lie algebra `Lie(GL(ℝ^n)) = GroupLieAlgebra (I n) (GL n)`;
-- the matrix presentation is derived bridge/view API.

section

variable (n : ℕ)

/-- Helper for Proposition 8.41: the singleton-chart inclusion `GL n → End n` has identity
manifold derivative at every point. -/
theorem generalLinearGroup_val_mfderiv_eq_id
    (g : GL n) :
    mfderiv (I n) (𝓘(ℝ, End n)) (fun h : GL n ↦ (h : End n)) g =
      ContinuousLinearMap.id ℝ (End n) := by
  -- In the units manifold, the preferred chart is the ambient inclusion itself.
  have hchart :
      extChartAt (I n) g = fun h : GL n ↦ (h : End n) := by
    ext h
    simp
  -- The manifold derivative of that preferred chart at its basepoint is the identity.
  rw [← hchart]
  have hself :
      mfderiv (I n) (𝓘(ℝ, End n)) (extChartAt (I n) g) g =
        ContinuousLinearMap.id ℝ (End n) :=
    mfderiv_extChartAt_self
  simpa using hself

/-- Helper for Proposition 8.41: after composing left multiplication in `GL n` with the ambient
inclusion into `End n`, the derivative at the identity is left multiplication by `g`. -/
theorem generalLinearGroup_leftMulToAmbient_hasMFDerivAt
    (g : GL n) :
    HasMFDerivAt (I n) (𝓘(ℝ, End n))
      (fun h : GL n ↦ (g : End n) * (h : End n))
      (1 : GL n)
      ((g : End n) • ContinuousLinearMap.id ℝ (End n)) := by
  -- Differentiate the ambient product of the constant field `g` and the inclusion `GL n → End n`.
  have hconst :
      HasMFDerivAt (I n) (𝓘(ℝ, End n))
        (fun _ : GL n ↦ (g : End n))
        (1 : GL n)
        (0 : (LieGL n) →L[ℝ] End n) :=
    by
      simpa using
        (show
          HasMFDerivAt (I n) (𝓘(ℝ, End n))
            (fun _ : GL n ↦ (g : End n))
            (1 : GL n)
            (0 : (LieGL n) →L[ℝ] End n) from
          hasMFDerivAt_const (c := (g : End n)) (x := (1 : GL n)))
  have hvalDiff :
      MDifferentiableAt (I n) (𝓘(ℝ, End n)) (fun h : GL n ↦ (h : End n)) (1 : GL n) := by
    -- The inclusion is the preferred chart, hence smooth.
    rw [show (fun h : GL n ↦ (h : End n)) = extChartAt (I n) (1 : GL n) by
      ext h
      simp]
    have hdiff :
        MDifferentiableAt (I n) (𝓘(ℝ, End n)) (extChartAt (I n) (1 : GL n)) (1 : GL n) :=
      by
        apply mdifferentiableAt_extChartAt
        simp
    simpa using hdiff
  have hval :
      HasMFDerivAt (I n) (𝓘(ℝ, End n))
        (fun h : GL n ↦ (h : End n))
        (1 : GL n)
        (ContinuousLinearMap.id ℝ (End n)) := by
    -- Upgrade differentiability using the explicit derivative computation of the inclusion.
    exact hvalDiff.hasMFDerivAt.congr_mfderiv
      (generalLinearGroup_val_mfderiv_eq_id (n := n) (g := (1 : GL n)))
  -- The product rule reduces the derivative to left multiplication by `g`.
  have hmul := hconst.mul' hval
  have hderiv :
      (↑g • ContinuousLinearMap.id ℝ (End n) + MulOpposite.op (1 : End n) •
          (0 : (End n) →L[ℝ] End n)) =
        (↑g • ContinuousLinearMap.id ℝ (End n)) := by
    ext v x i
    simp [ContinuousLinearMap.smul_apply]
  exact hmul.congr_mfderiv hderiv

/-- Helper for Proposition 8.41: the left-invariant vector field determined by `A` is the ambient
field `g ↦ g * A`. -/
theorem generalLinearGroupMulInvariant_apply
    [LieGroup (I n) (minSmoothness ℝ 3) (GL n)]
    (A : LieGL n) (g : GL n) :
    mulInvariantVectorField A g = (g : End n) * (show End n from A) := by
  let valMap : (GL n) → (End n) := fun h ↦ (h : End n)
  have hmin : minSmoothness ℝ 3 ≠ 0 :=
    lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
  have hValAtg : MDifferentiableAt (I n) (𝓘(ℝ, End n)) valMap g := by
    -- The units inclusion is a chart, so it is smooth at every point.
    rw [show valMap = extChartAt (I n) g by
      ext h
      simp [valMap]]
    have hdiff :
        MDifferentiableAt (I n) (𝓘(ℝ, End n)) (extChartAt (I n) g) g :=
      by
        apply mdifferentiableAt_extChartAt
        simp
    simpa using hdiff
  have hLeft : MDifferentiableAt (I n) (I n) (g * ·) (1 : GL n) :=
    contMDiff_mul_left.contMDiffAt.mdifferentiableAt hmin
  have hcomp :
      mfderiv (I n) (𝓘(ℝ, End n)) valMap g (mulInvariantVectorField A g) =
        mfderiv (I n) (𝓘(ℝ, End n)) (valMap ∘ (g * ·)) (1 : GL n) A := by
    -- Differentiate the composite `val ∘ L_g` at the identity.
    simpa [valMap, mulInvariantVectorField] using
      (mfderiv_comp_apply_of_eq (1 : GL n) hValAtg hLeft (mul_one g) A).symm
  have hambient :
      mfderiv (I n) (𝓘(ℝ, End n)) (valMap ∘ (g * ·)) (1 : GL n) A =
        (g : End n) * (show End n from A) := by
    -- Rewrite the composite as the ambient multiplication map and use its computed derivative.
    have hEq :
        valMap ∘ (g * ·) = fun h : GL n ↦ (g : End n) * (h : End n) := by
      ext h
      rfl
    rw [hEq]
    simpa [ContinuousLinearMap.id_apply] using
      congrArg (fun f : (LieGL n) →L[ℝ] End n ↦ f A)
        (HasMFDerivAt.mfderiv (generalLinearGroup_leftMulToAmbient_hasMFDerivAt (n := n) g))
  -- The derivative of the inclusion is the identity, so the tangent vector itself is `g * A`.
  simpa [valMap, generalLinearGroup_val_mfderiv_eq_id (n := n) (g := g)] using
    hcomp.trans hambient

/-- Helper for Proposition 8.41: pulling back the ambient right-multiplication field along the
inclusion `GL n → End n` leaves the same explicit formula. -/
theorem generalLinearGroupAmbientPullback_mulField
    (A : End n) :
    mpullback (I n) (𝓘(ℝ, End n)) (fun g : GL n ↦ (g : End n))
      (fun X : End n ↦ X * A) =
        fun g : GL n ↦ (g : End n) * A := by
  ext g
  -- The singleton chart on units is the ambient inclusion, so its derivative is the identity.
  rw [mpullback_apply]
  rw [generalLinearGroup_val_mfderiv_eq_id (n := n) (g := g)]
  exact ((ContinuousLinearMap.id ℝ (End n)).isInvertible.inverse_apply_eq).2 rfl

/-- Helper for Proposition 8.41: the manifold bracket of the explicit invariant fields is the
ambient Lie bracket pulled back through the inclusion `GL n → End n`. -/
theorem generalLinearGroupBracketAtOne_eq_ambientLieBracket
    [LieGroup (I n) (minSmoothness ℝ 3) (GL n)]
    (A B : End n) :
    mlieBracket (I n) (fun g : GL n ↦ (g : End n) * A) (fun g : GL n ↦ (g : End n) * B)
      (1 : GL n) =
      VectorField.lieBracket ℝ (fun X : End n ↦ X * A) (fun X : End n ↦ X * B) (1 : End n) := by
  have hA :=
    -- Right multiplication by a fixed endomorphism is linear, hence differentiable as a vector field.
    ((contMDiffAt_vectorSpace_iff_contDiffAt (V := fun X : End n ↦ X * A) (x := (1 : End n))).2
      (by
        simpa using (((ContinuousLinearMap.mul ℝ (End n)).flip A).contDiffAt
          (n := 1) (x := (1 : End n))))).mdifferentiableAt one_ne_zero
  have hB :=
    -- The same linearity argument applies to the second field.
    ((contMDiffAt_vectorSpace_iff_contDiffAt (V := fun X : End n ↦ X * B) (x := (1 : End n))).2
      (by
        simpa using (((ContinuousLinearMap.mul ℝ (End n)).flip B).contDiffAt
          (n := 1) (x := (1 : End n))))).mdifferentiableAt one_ne_zero
  have hval : CMDiffAt (minSmoothness ℝ 2) (fun g : GL n ↦ (g : End n)) (1 : GL n) := by
    -- The inclusion of the units into the ambient algebra is smooth.
    simpa using
      (Units.contMDiff_val (𝕜 := ℝ) (R := End n) (n := minSmoothness ℝ 2)).contMDiffAt
        (x := (1 : GL n))
  have hpull :=
    mpullback_mlieBracket (I := I n) (I' := 𝓘(ℝ, End n)) (f := fun g : GL n ↦ (g : End n))
      (V := fun X : End n ↦ X * A) (W := fun X : End n ↦ X * B) (x₀ := (1 : GL n))
      hA hB hval le_rfl
  -- Route correction: use pullback invariance for the inclusion instead of unfolding the chart-level
  -- definition of `mlieBracket` by hand.
  rw [mpullback_apply, generalLinearGroupAmbientPullback_mulField (n := n),
    generalLinearGroupAmbientPullback_mulField (n := n),
    generalLinearGroup_val_mfderiv_eq_id (n := n) (g := (1 : GL n)),
    ← VectorField.mlieBracketWithin_univ, VectorField.mlieBracketWithin_eq_lieBracketWithin,
    VectorField.lieBracketWithin_univ] at hpull
  exact hpull.symm

/-- Helper for Proposition 8.41: in the ambient endomorphism algebra, the bracket of the linear
fields `X ↦ X * A` and `X ↦ X * B` is right multiplication by the commutator `A * B - B * A`. -/
theorem generalLinearGroupAmbientLieBracket_apply
    (A B X : End n) :
    VectorField.lieBracket ℝ (fun Y : End n ↦ Y * A) (fun Y : End n ↦ Y * B) X =
      X * (A * B - B * A) := by
  -- Differentiate the two linear right-multiplication fields.
  have hBderiv :
      fderiv ℝ (fun Y : End n ↦ Y * B) X =
        (ContinuousLinearMap.id ℝ (End n)) <• B := by
    simpa using
      (fderiv_mul_const' (𝕜 := ℝ) (a := fun Y : End n ↦ Y) (x := X) differentiableAt_id B)
  have hAderiv :
      fderiv ℝ (fun Y : End n ↦ Y * A) X =
        (ContinuousLinearMap.id ℝ (End n)) <• A := by
    simpa using
      (fderiv_mul_const' (𝕜 := ℝ) (a := fun Y : End n ↦ Y) (x := X) differentiableAt_id A)
  rw [VectorField.lieBracket]
  rw [hBderiv, hAderiv, fderiv_id]
  -- The resulting commutator is just associative multiplication regrouped on the right.
  simp [sub_eq_add_neg, mul_assoc]

/-- Helper for Proposition 8.41: under the ambient identification
`Lie(GL(ℝ^n)) = T₁(GL n) = End n`, the Lie bracket is the associative commutator. -/
theorem generalLinearGroupBracket_eq_commutator
    [LieGroup (I n) (minSmoothness ℝ 3) (GL n)]
    (A B : LieGL n) :
    ⁅A, B⁆ =
      (show LieGL n from
        (show End n from A) * (show End n from B) -
          (show End n from B) * (show End n from A)) := by
  -- Route correction: normalize the invariant fields first, then use pullback invariance for the
  -- inclusion `GL n → End n` to compute the remaining bracket in the ambient algebra.
  rw [GroupLieAlgebra.bracket_def]
  have hA :
      mulInvariantVectorField A =
        fun g : GL n ↦ (g : End n) * (show End n from A) := by
    ext g
    simpa using generalLinearGroupMulInvariant_apply (n := n) A g
  have hB :
      mulInvariantVectorField B =
        fun g : GL n ↦ (g : End n) * (show End n from B) := by
    ext g
    simpa using generalLinearGroupMulInvariant_apply (n := n) B g
  rw [hA, hB, generalLinearGroupBracketAtOne_eq_ambientLieBracket]
  -- The ambient Lie bracket of the linear fields is the associative commutator.
  simpa [one_mul] using
    generalLinearGroupAmbientLieBracket_apply (n := n)
      (A := (show End n from A)) (B := (show End n from B)) (X := (1 : End n))

/-- Helper for Proposition 8.41: the canonical Lie algebra of `GL(ℝ^n)` is the ambient Banach
algebra `End n`, with bracket transported from left-invariant vector fields. -/
def generalLinearGroupLieEquivContinuousEnd
    [LieGroup (I n) (minSmoothness ℝ 3) (GL n)] :
    (LieGL n) ≃ₗ⁅ℝ⁆ End n where
  -- The underlying tangent-space identification is definitionally the identity.
  toFun := fun A ↦ show End n from A
  invFun := fun A ↦ show LieGL n from A
  map_add' := by
    intro A B
    rfl
  map_smul' := by
    intro c A
    rfl
  -- Route correction: the missing content is exactly the commutator computation above.
  map_lie' := by
    intro A B
    simpa using
      congrArg (fun X : LieGL n ↦ (show End n from X))
        (generalLinearGroupBracket_eq_commutator (n := n) A B)
  left_inv := by
    intro A
    rfl
  right_inv := by
    intro A
    rfl

/-- The Lie algebra of `GL(ℝ^n)` is canonically the algebra of linear endomorphisms of `ℝ^n`,
using the standard Lie-group model on invertible continuous endomorphisms and the intrinsic
finite-dimensional identification between continuous and algebraic endomorphisms. -/
def general_linear_group_lie_equiv_end [LieGroup (I n) (minSmoothness ℝ 3) (GL n)] :
    (LieGL n) ≃ₗ⁅ℝ⁆ Module.End ℝ (Vec n) :=
  (generalLinearGroupLieEquivContinuousEnd n).trans
    (Module.End.toContinuousLinearMap (Vec n)).symm.toLieEquiv

/-- Proposition 8.41 (Lie Algebra of the General Linear Group): the Lie algebra of `GL(n, ℝ)`,
formalized as the Lie algebra of the Lie group of invertible continuous endomorphisms of
`ℝ^n = Fin n → ℝ`, is canonically identified with the matrix Lie algebra
`𝔤𝔩(n, ℝ) = Mat n` by taking matrices in the standard basis. -/
def general_linear_group_lie_equiv_matrix [LieGroup (I n) (minSmoothness ℝ 3) (GL n)] :
    (LieGL n) ≃ₗ⁅ℝ⁆ Mat n :=
  (general_linear_group_lie_equiv_end n).trans
    (LinearMap.toMatrixAlgEquiv' : Module.End ℝ (Vec n) ≃ₐ[ℝ] Mat n).toLieEquiv

end
