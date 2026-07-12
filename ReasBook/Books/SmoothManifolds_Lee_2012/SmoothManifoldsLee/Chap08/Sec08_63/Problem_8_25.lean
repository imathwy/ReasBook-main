import Mathlib.Algebra.Lie.Abelian
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import SmoothManifolds_Lee_2012.Chap08.Sec08_60.Corollary_8_38
import SmoothManifolds_Lee_2012.Chap08.Sec08_63.Problem_8_23

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold
open VectorField

-- Domain sampling pass:
-- * primary domain: Lie groups and their canonical Lie algebras;
-- * core/canonical owner: `GroupLieAlgebra I G`;
-- * relevant declarations checked in this domain: `GroupLieAlgebra`, `AddGroupLieAlgebra`, the
--   canonical `LieRing`/`LieAlgebra` instances on those owners from
--   `Mathlib.Geometry.Manifold.GroupLieAlgebra`, and `IsLieAbelian`.
-- The primitive data here is the commutative Lie-group or additive Lie-group structure together
-- with the ambient completeness hypothesis required by the canonical owner-level Lie bracket.
-- Abelianity of `GroupLieAlgebra I G` and `AddGroupLieAlgebra I G` is derived structure on those
-- owners, so the public surface should stay at owner-level `IsLieAbelian` instances rather than
-- parallel theorem wrappers.

section AbelianLieGroup

universe u𝕜 uE uH uG

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type uG} [CommGroup G] [TopologicalSpace G] [ChartedSpace H G]
variable [LieGroup I (minSmoothness 𝕜 3) G]

namespace GroupLieAlgebra

/-- Helper for Problem 8-25: the derivative of multiplication at `((1 : G), (1 : G))` sends
`(X, Y)` to `X + Y`. -/
theorem mfderivMulAtIdentityPair_apply
    (X Y : GroupLieAlgebra I G) :
    mfderiv% (fun p : G × G ↦ p.1 * p.2) ((1 : G), (1 : G)) (X, Y) = X + Y := by
  -- Differentiate multiplication by splitting it into the two coordinate directions.
  have hMul : MDiffAt (fun p : G × G ↦ p.1 * p.2) ((1 : G), (1 : G)) := by
    have hNonzero : minSmoothness 𝕜 3 ≠ 0 := lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
    simpa using (contMDiff_mul I (minSmoothness 𝕜 3)).mdifferentiableAt hNonzero
  have mulRight_eq_id : (fun z : G ↦ z * 1) = id := by
    funext z
    simp
  have oneMul_eq_id : (fun z : G ↦ 1 * z) = id := by
    funext z
    simp
  have happly :=
    mfderiv_prod_eq_add_apply
      (I := I) (I' := I) (I'' := I)
      (M := G) (M' := G) (M'' := G)
      (f := fun p : G × G ↦ p.1 * p.2)
      (p := ((1 : G), (1 : G)))
      (v := (X, Y))
      hMul
  rw [mulRight_eq_id, oneMul_eq_id] at happly
  simpa using happly

/-- Helper for Problem 8-25: the derivative of `g ↦ (g, g⁻¹)` at the identity packages the
identity derivative with the derivative of inversion. -/
lemma pairWithInvMfderiv_apply
    (X : GroupLieAlgebra I G) :
    mfderiv% (fun g : G ↦ (g, g⁻¹)) (1 : G) X =
      (X, mfderiv% (fun g : G ↦ g⁻¹) (1 : G) X) := by
  -- Differentiate the two coordinates separately and repackage them in the product tangent space.
  have hInv : MDiffAt (fun g : G ↦ g⁻¹) (1 : G) := by
    have hNonzero : minSmoothness 𝕜 3 ≠ 0 := lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
    simpa using (contMDiff_inv I (minSmoothness 𝕜 3)).mdifferentiableAt hNonzero (x := (1 : G))
  have hmfderiv :
      mfderiv% (fun g : G ↦ ((id : G → G) g, (fun g : G ↦ g⁻¹) g)) (1 : G) =
        (mfderiv% (id : G → G) (1 : G)).prod (mfderiv% (fun g : G ↦ g⁻¹) (1 : G)) :=
    mfderiv_prodMk mdifferentiableAt_id hInv
  have happly := congrArg
    (fun F : TangentSpace I (1 : G) →L[𝕜] TangentSpace (I.prod I) ((1 : G), (1 : G)⁻¹) ↦ F X)
    hmfderiv
  simpa using happly

/-- Helper for Problem 8-25: differentiating `g ↦ g * g⁻¹` at the identity gives zero. -/
lemma mulInvCompositeMfderiv_apply_eq_zero
    (X : GroupLieAlgebra I G) :
    mfderiv% (fun g : G ↦ g * g⁻¹) (1 : G) X = 0 := by
  -- Rewrite `fun g ↦ g * g⁻¹` to the constant identity map before differentiating.
  have hfun : (fun g : G ↦ g * g⁻¹) = fun _ : G ↦ (1 : G) := by
    funext g
    simp
  rw [hfun, mfderiv_const]
  rfl

/-- Helper for Problem 8-25: transport the derivative of inversion at `1` back to
`GroupLieAlgebra I G`. -/
noncomputable abbrev invMfderivAtIdentity
    (X : GroupLieAlgebra I G) :
    GroupLieAlgebra I G :=
  Eq.ndrec (motive := fun g => TangentSpace I g)
    (mfderiv% (fun g : G ↦ g⁻¹) (1 : G) X) inv_one

/-- Helper for Problem 8-25: the transported inversion derivative agrees with the raw derivative at
`1`. -/
lemma invMfderivAtIdentity_eq
    (X : GroupLieAlgebra I G) :
    invMfderivAtIdentity (I := I) X = mfderiv% (fun g : G ↦ g⁻¹) (1 : G) X := by
  -- The codomain transport is along `inv_one`, so both spellings coincide.
  exact eq_of_heq <|
    rec_heq_of_heq
      (e := (inv_one : (1 : G)⁻¹ = (1 : G)))
      (x := mfderiv% (fun g : G ↦ g⁻¹) (1 : G) X)
      HEq.rfl

/-- Helper for Problem 8-25: multiplying `(X, d(inv)₁ X)` at the identity pair gives
`X + invMfderivAtIdentity X`. -/
lemma mfderivMulAtIdentityInv_apply
    (X : GroupLieAlgebra I G) :
    mfderiv% (fun p : G × G ↦ p.1 * p.2) ((1 : G), (1 : G)⁻¹)
      (X, mfderiv% (fun g : G ↦ g⁻¹) (1 : G) X) = X + invMfderivAtIdentity (I := I) X := by
  -- Rewrite the codomain point using `inv_one` and reuse the identity-pair computation.
  rw [inv_one]
  simpa [invMfderivAtIdentity_eq] using
    (mfderivMulAtIdentityPair_apply (I := I) X (invMfderivAtIdentity (I := I) X))

/-- Helper for Problem 8-25: the derivative of inversion at the identity is negation on
`GroupLieAlgebra I G`. -/
theorem mfderivInvAtIdentity_apply
    (X : GroupLieAlgebra I G) :
    mfderiv% (fun g : G ↦ g⁻¹) (1 : G) X = -X := by
  -- Route correction: differentiate `g ↦ g * g⁻¹` as a genuine composition through
  -- `g ↦ (g, g⁻¹)` and compare with the constant map `1`.
  have hNonzero : minSmoothness 𝕜 3 ≠ 0 := lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
  have hMul : MDiffAt (fun p : G × G ↦ p.1 * p.2) ((1 : G), (1 : G)⁻¹) := by
    simpa using (contMDiff_mul I (minSmoothness 𝕜 3)).mdifferentiableAt hNonzero
  have hInv : MDiffAt (fun g : G ↦ g⁻¹) (1 : G) := by
    simpa using (contMDiff_inv I (minSmoothness 𝕜 3)).mdifferentiableAt hNonzero (x := (1 : G))
  have hPair : MDiffAt (fun g : G ↦ (g, g⁻¹)) (1 : G) := by
    exact mdifferentiableAt_id.prodMk hInv
  have hcomp :
      mfderiv% (fun g : G ↦ g * g⁻¹) (1 : G) X =
        mfderiv% (fun p : G × G ↦ p.1 * p.2) ((1 : G), (1 : G)⁻¹)
          (mfderiv% (fun g : G ↦ (g, g⁻¹)) (1 : G) X) := by
    have hfun :
        (fun g : G ↦ g * g⁻¹) =
          (fun p : G × G ↦ p.1 * p.2) ∘ fun g : G ↦ (g, g⁻¹) := by
      rfl
    rw [hfun]
    simpa using (mfderiv_comp_apply (x := (1 : G))
      (g := fun p : G × G ↦ p.1 * p.2)
      (f := fun g : G ↦ (g, g⁻¹))
      hMul hPair X)
  have hneg : X + invMfderivAtIdentity (I := I) X = 0 := by
    calc
      X + invMfderivAtIdentity (I := I) X
          = mfderiv% (fun p : G × G ↦ p.1 * p.2) ((1 : G), (1 : G)⁻¹)
              (mfderiv% (fun g : G ↦ (g, g⁻¹)) (1 : G) X) := by
                rw [pairWithInvMfderiv_apply]
                exact (mfderivMulAtIdentityInv_apply (I := I) X).symm
      _ = mfderiv% (fun g : G ↦ g * g⁻¹) (1 : G) X := hcomp.symm
      _ = 0 := mulInvCompositeMfderiv_apply_eq_zero (I := I) X
  calc
    mfderiv% (fun g : G ↦ g⁻¹) (1 : G) X = invMfderivAtIdentity (I := I) X := by
      exact (invMfderivAtIdentity_eq (I := I) X).symm
    _ = -X := by
      exact ((neg_eq_iff_add_eq_zero).2 hneg).symm

/-- Helper for Problem 8-25: the invariant vector field determined by `v` takes the value `v` at
the identity. -/
lemma mulInvariantVectorField_apply_one
    (v : GroupLieAlgebra I G) :
    mulInvariantVectorField v 1 = v := by
  -- Evaluate the invariant field at `1` by identifying left multiplication by `1` with `id`.
  have hfun : (fun x : G ↦ (1 : G) * x) = id := by
    funext x
    simp
  change (mfderiv% (fun x : G ↦ (1 : G) * x) (1 : G)) v = v
  rw [hfun, mfderiv_id]
  rfl

/-- Helper for Problem 8-25: the derivative of inversion is invertible at every point. -/
theorem mfderivInvIsInvertible
    (g : G) :
    (mfderiv% (fun x : G ↦ x⁻¹) g).IsInvertible := by
  -- Differentiate `inv ∘ inv = id` in both orders to exhibit an explicit inverse.
  have hNonzero : minSmoothness 𝕜 3 ≠ 0 := lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
  have hInv : MDifferentiableAt I I (fun x : G ↦ x⁻¹) g := by
    simpa using (contMDiff_inv I (minSmoothness 𝕜 3)).mdifferentiableAt hNonzero (x := g)
  have hInv' : MDifferentiableAt I I (fun x : G ↦ x⁻¹) g⁻¹ := by
    simpa using (contMDiff_inv I (minSmoothness 𝕜 3)).mdifferentiableAt hNonzero (x := g⁻¹)
  have hLeft :
      mfderiv% (fun x : G ↦ x⁻¹) (g⁻¹) ∘L mfderiv% (fun x : G ↦ x⁻¹) g =
        ContinuousLinearMap.id 𝕜 (TangentSpace I g) := by
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
        ContinuousLinearMap.id 𝕜 (TangentSpace I g⁻¹) := by
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
          ContinuousLinearMap.id 𝕜 (TangentSpace I g⁻¹) := hcomp'
    have hgg : g⁻¹⁻¹ = g := by simp
    rw [hgg] at hRightRaw
    exact hRightRaw
  exact ContinuousLinearMap.IsInvertible.of_inverse hRight hLeft

/-- Helper for Problem 8-25: on a commutative Lie group, inversion pullback sends the invariant
field `mulInvariantVectorField X` to a left-invariant field. -/
theorem inversionPullback_mulInvariantVectorField_isLeftInvariant
    (X : GroupLieAlgebra I G) :
    VectorField.IsLeftInvariant
      (VectorField.mpullback I I (fun g : G ↦ g⁻¹) (mulInvariantVectorField X)) := by
  have hNonzero : minSmoothness 𝕜 3 ≠ 0 := lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
  intro g
  -- Rewrite the left-translation pullback using `(g * x)⁻¹ = x⁻¹ * g⁻¹`.
  ext x
  have hcomp₁ :=
    VectorField.mpullbackWithin_comp_of_left
      (I := I) (I' := I) (I'' := I)
      (g := fun y : G ↦ y⁻¹) (f := fun y : G ↦ g * y) (V := mulInvariantVectorField X)
      (s := Set.univ) (t := Set.univ) (x₀ := x)
      (by
        simpa using
          (contMDiffAt_mul_left (I := I) (n := minSmoothness 𝕜 3) (a := g) (b := x)).mdifferentiableAt
            hNonzero)
      (by simp)
      (uniqueMDiffWithinAt_univ I)
      (by
        simpa [mfderivWithin_univ] using
          mfderivInvIsInvertible (I := I) (g := g * x))
  have hcomp₂ :=
    VectorField.mpullbackWithin_comp_of_right
      (I := I) (I' := I) (I'' := I)
      (g := fun y : G ↦ y * g⁻¹) (f := fun y : G ↦ y⁻¹) (V := mulInvariantVectorField X)
      (s := Set.univ) (t := Set.univ) (x₀ := x)
      (by
        simpa using
          (contMDiffAt_mul_right (I := I) (n := minSmoothness 𝕜 3) (a := g⁻¹) (b := x⁻¹)).mdifferentiableAt
            hNonzero)
      (by simp)
      (uniqueMDiffWithinAt_univ I)
      (by
        simpa [mfderivWithin_univ] using
          mfderivInvIsInvertible (I := I) (g := x))
  have hfun :
      ((fun y : G ↦ y⁻¹) ∘ fun y : G ↦ g * y) =
        (fun y : G ↦ y * g⁻¹) ∘ fun y : G ↦ y⁻¹ := by
    funext y
    simp [Function.comp]
  calc
    VectorField.mpullback I I (fun y : G ↦ g * y)
        (VectorField.mpullback I I (fun y : G ↦ y⁻¹) (mulInvariantVectorField X)) x
      = VectorField.mpullback I I (((fun y : G ↦ y⁻¹) ∘ fun y : G ↦ g * y))
          (mulInvariantVectorField X) x := by
          simpa [VectorField.mpullbackWithin_univ, Function.comp] using hcomp₁.symm
    _ = VectorField.mpullback I I ((fun y : G ↦ y * g⁻¹) ∘ fun y : G ↦ y⁻¹)
          (mulInvariantVectorField X) x := by
          rw [hfun]
    _ = VectorField.mpullback I I (fun y : G ↦ y⁻¹)
          (VectorField.mpullback I I (fun y : G ↦ y * g⁻¹) (mulInvariantVectorField X)) x := by
          simpa [VectorField.mpullbackWithin_univ, Function.comp] using hcomp₂
    _ = VectorField.mpullback I I (fun y : G ↦ y⁻¹) (mulInvariantVectorField X) x := by
          have hInvariant :
              VectorField.mpullback I I (fun y : G ↦ y * g⁻¹) (mulInvariantVectorField X) =
                mulInvariantVectorField X := by
            simpa [mul_comm] using
              (mpullback_mulInvariantVectorField (I := I) (g := g⁻¹) X)
          rw [hInvariant]

/-- Helper for Problem 8-25: inversion pullback sends `mulInvariantVectorField X` to
`mulInvariantVectorField (-X)` on a commutative Lie group. -/
theorem inversionPullback_mulInvariantVectorField_eq
    (X : GroupLieAlgebra I G) :
    VectorField.mpullback I I (fun g : G ↦ g⁻¹) (mulInvariantVectorField X) =
      mulInvariantVectorField (-X) := by
  -- Identify the pullback as the unique left-invariant field with value `-X` at the identity.
  have hLeftInvariant :
      VectorField.IsLeftInvariant
        (VectorField.mpullback I I (fun g : G ↦ g⁻¹) (mulInvariantVectorField X)) := by
    exact inversionPullback_mulInvariantVectorField_isLeftInvariant (I := I) X
  have hAtOne :
      VectorField.mpullback I I (fun g : G ↦ g⁻¹) (mulInvariantVectorField X) 1 = -X := by
    have hInv : (mfderiv% (fun g : G ↦ g⁻¹) (1 : G)).IsInvertible :=
      mfderivInvIsInvertible (I := I) (g := (1 : G))
    rw [VectorField.mpullback_apply, inv_one]
    apply (hInv.inverse_apply_eq).2
    simpa [mulInvariantVectorField_apply_one] using
      (mfderivInvAtIdentity_apply (I := I) (-X)).symm
  calc
    VectorField.mpullback I I (fun g : G ↦ g⁻¹) (mulInvariantVectorField X)
        = mulInvariantVectorField
            ((VectorField.mpullback I I (fun g : G ↦ g⁻¹) (mulInvariantVectorField X)) 1) := by
              simpa using
                (left_invariant_rough_vector_field_eq_mulInvariantVectorField
                  (I := I)
                  (G := G)
                  (X := VectorField.mpullback I I (fun g : G ↦ g⁻¹) (mulInvariantVectorField X))
                  hLeftInvariant)
    _ = mulInvariantVectorField (-X) := by
          rw [hAtOne]

/-- Helper for Problem 8-25: on a commutative Lie group, the invariant vector field associated to
`X` is also fixed by pullback along every right translation. -/
theorem mpullback_mulInvariantVectorField_right
    (g : G) (X : GroupLieAlgebra I G) :
    VectorField.mpullback I I (fun y : G ↦ y * g) (mulInvariantVectorField X) =
      mulInvariantVectorField X := by
  -- On a commutative group, right translation by `g` is the same map as left translation by `g`.
  simpa [mul_comm] using mpullback_mulInvariantVectorField (I := I) (g := g) X

/-- Helper for Problem 8-25: on a commutative Lie group, the bracket field of two invariant
vector fields is also fixed by pullback along every right translation. -/
theorem mpullback_mulInvariantVector_mlieBracket_right
    (g : G) (X Y : GroupLieAlgebra I G) :
    VectorField.mpullback I I (fun y : G ↦ y * g)
      (mlieBracket I (mulInvariantVectorField X) (mulInvariantVectorField Y)) =
        mlieBracket I (mulInvariantVectorField X) (mulInvariantVectorField Y) := by
  -- Rewrite the bracket field as the invariant field of the Lie bracket element, then use the
  -- commutative right-invariance of invariant vector fields.
  rw [← mulInvariantVector_mlieBracket (I := I) (v := X) (w := Y)]
  exact mpullback_mulInvariantVectorField_right (I := I) g ⁅X, Y⁆

/-- Helper for Problem 8-25: the commutative shear map on `G × G`. -/
private def productShear (p : G × G) : G × G :=
  (p.1 * p.2, p.2)

/-- Helper for Problem 8-25: the inverse commutative shear map on `G × G`. -/
private def productUnshear (p : G × G) : G × G :=
  (p.1 * p.2⁻¹, p.2)

/-- Helper for Problem 8-25: the commutative product shear has the explicit inverse
`productUnshear`. -/
private theorem productUnshear_comp_productShear :
    productUnshear (I := I) ∘ productShear (I := I) = id := by
  -- Expand the two maps and cancel the second-coordinate factor.
  funext p
  ext <;> simp [productShear, productUnshear, mul_assoc]

/-- Helper for Problem 8-25: the commutative product shear is inverted on the other side by
`productUnshear`. -/
private theorem productShear_comp_productUnshear :
    productShear (I := I) ∘ productUnshear (I := I) = id := by
  -- Expand the two maps and cancel the inverse factor in the first coordinate.
  funext p
  ext <;> simp [productShear, productUnshear, mul_assoc]

/-- Helper for Problem 8-25: the derivative of the commutative product shear is invertible at every
point of `G × G`. -/
private theorem productShear_mfderivIsInvertible
    (p : G × G) :
    (mfderiv% (productShear (I := I)) p).IsInvertible := by
  have hNonzero : minSmoothness 𝕜 3 ≠ 0 := lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
  have hShear :
      MDifferentiableAt (I.prod I) (I.prod I) (productShear (I := I)) p := by
    have hMul :
        MDifferentiableAt (I.prod I) I (fun q : G × G ↦ q.1 * q.2) p := by
      simpa using
        (show ContMDiff (I.prod I) I (minSmoothness 𝕜 3) (fun q : G × G ↦ q.1 * q.2) from
          contMDiff_fst.mul contMDiff_snd).mdifferentiableAt hNonzero
    exact hMul.prodMk mdifferentiableAt_snd
  have hUnshear :
      MDifferentiableAt (I.prod I) (I.prod I) (productUnshear (I := I))
        (productShear (I := I) p) := by
    have hMulInv :
        MDifferentiableAt (I.prod I) I (fun q : G × G ↦ q.1 * q.2⁻¹)
          (productShear (I := I) p) := by
      simpa using
        (show ContMDiff (I.prod I) I (minSmoothness 𝕜 3) (fun q : G × G ↦ q.1 * q.2⁻¹) from
          contMDiff_fst.mul ((contMDiff_inv I (minSmoothness 𝕜 3)).comp contMDiff_snd))
          .mdifferentiableAt hNonzero
    exact hMulInv.prodMk mdifferentiableAt_snd
  have hLeft :
      mfderiv% (productUnshear (I := I)) (productShear (I := I) p) ∘L
          mfderiv% (productShear (I := I)) p =
        ContinuousLinearMap.id 𝕜 (TangentSpace (I.prod I) p) := by
    have hcomp :=
      mfderiv_comp (x := p) (I := I.prod I) (I' := I.prod I) (I'' := I.prod I)
        (g := productUnshear (I := I)) (f := productShear (I := I)) hUnshear hShear
    have hcomp' := hcomp.symm
    rw [productUnshear_comp_productShear (I := I), mfderiv_id] at hcomp'
    exact hcomp'
  have hRight :
      mfderiv% (productShear (I := I)) p ∘L
          mfderiv% (productUnshear (I := I)) (productShear (I := I) p) =
        ContinuousLinearMap.id 𝕜 (TangentSpace (I.prod I) (productShear (I := I) p)) := by
    have hcomp :=
      mfderiv_comp (x := productShear (I := I) p)
        (I := I.prod I) (I' := I.prod I) (I'' := I.prod I)
        (g := productShear (I := I)) (f := productUnshear (I := I))
        hShear hUnshear
    have hcomp' := hcomp.symm
    rw [productShear_comp_productUnshear (I := I), mfderiv_id] at hcomp'
    exact hcomp'
  exact ContinuousLinearMap.IsInvertible.of_inverse hRight hLeft

/-- Helper for Problem 8-25: the derivative of the commutative product shear at the identity pair
sends `(A, B)` to `(A + B, B)`. -/
private theorem productShear_mfderiv_apply_one
    (A B : GroupLieAlgebra I G) :
    mfderiv% (productShear (I := I)) ((1 : G), (1 : G))
      (((A, B) : GroupLieAlgebra (I.prod I) (G × G))) =
        (((A + B, B) : GroupLieAlgebra (I.prod I) (G × G))) := by
  -- Differentiate the two coordinates of the shear separately at the identity pair.
  have hNonzero : minSmoothness 𝕜 3 ≠ 0 := lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
  have hMul :
      MDiffAt (fun q : G × G ↦ q.1 * q.2) ((1 : G), (1 : G)) := by
    simpa using
      (show ContMDiff (I.prod I) I (minSmoothness 𝕜 3) (fun q : G × G ↦ q.1 * q.2) from
        contMDiff_fst.mul contMDiff_snd).mdifferentiableAt hNonzero
  have hPair :
      mfderiv% (productShear (I := I)) ((1 : G), (1 : G))
          (((A, B) : GroupLieAlgebra (I.prod I) (G × G))) =
        (mfderiv% (fun q : G × G ↦ q.1 * q.2) ((1 : G), (1 : G))
            (((A, B) : GroupLieAlgebra (I.prod I) (G × G))),
          mfderiv% (fun q : G × G ↦ q.2) ((1 : G), (1 : G))
            (((A, B) : GroupLieAlgebra (I.prod I) (G × G)))) := by
    have hderiv := mfderiv_prodMk hMul mdifferentiableAt_snd
    have happly := congrArg
      (fun F : TangentSpace (I.prod I) ((1 : G), (1 : G)) →L[𝕜]
          TangentSpace (I.prod I) (productShear (I := I) ((1 : G), (1 : G))) ↦
        F (((A, B) : GroupLieAlgebra (I.prod I) (G × G))))
      hderiv
    simpa [productShear] using happly
  rw [hPair, mfderiv_snd]
  simpa using mfderivMulAtIdentityPair_apply (I := I) A B

/-- Helper for Problem 8-25: the commutative product shear pushes the invariant field attached to
`(A, B)` forward to the invariant field attached to `(A + B, B)`. -/
private theorem productShear_mulInvariantVectorField_pushforward
    (A B : GroupLieAlgebra I G) (p : G × G) :
    mfderiv% (productShear (I := I)) p
      ((((A, B) : GroupLieAlgebra (I.prod I) (G × G)))ᴸ p) =
        ((((A + B, B) : GroupLieAlgebra (I.prod I) (G × G)))ᴸ
          (productShear (I := I) p)) := by
  -- Route correction: use the homomorphism identity
  -- `productShear (p * q) = productShear p * productShear q` and differentiate it at the identity.
  let e : G × G := ((1 : G), (1 : G))
  have hNonzero : minSmoothness 𝕜 3 ≠ 0 := lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
  have hShearAtP :
      MDifferentiableAt (I.prod I) (I.prod I) (productShear (I := I)) p := by
    have hMul :
        MDifferentiableAt (I.prod I) I (fun q : G × G ↦ q.1 * q.2) p := by
      simpa using
        (show ContMDiff (I.prod I) I (minSmoothness 𝕜 3) (fun q : G × G ↦ q.1 * q.2) from
          contMDiff_fst.mul contMDiff_snd).mdifferentiableAt hNonzero
    exact hMul.prodMk mdifferentiableAt_snd
  have hShearAtOne :
      MDifferentiableAt (I.prod I) (I.prod I) (productShear (I := I)) e := by
    simpa [e] using hShearAtP (p := e)
  have hTranslate :
      MDifferentiableAt (I.prod I) (I.prod I) (fun q : G × G ↦ p * q) e := by
    simpa [e] using
      (contMDiffAt_mul_left (I := I.prod I) (n := minSmoothness 𝕜 3) (a := p) (b := e))
        .mdifferentiableAt hNonzero
  have hTargetTranslate :
      MDifferentiableAt (I.prod I) (I.prod I)
        (fun q : G × G ↦ productShear (I := I) p * q) e := by
    simpa [e] using
      (contMDiffAt_mul_left (I := I.prod I) (n := minSmoothness 𝕜 3)
        (a := productShear (I := I) p) (b := e)).mdifferentiableAt hNonzero
  have hSource :
      mfderiv% (productShear (I := I)) p
          ((((A, B) : GroupLieAlgebra (I.prod I) (G × G)))ᴸ p) =
        mfderiv% ((productShear (I := I)) ∘ fun q : G × G ↦ p * q) e
          (((A, B) : GroupLieAlgebra (I.prod I) (G × G))) := by
    simpa [e, mulInvariantVectorField] using
      (mfderiv_comp_apply_of_eq (x := e)
        (g := productShear (I := I))
        (f := fun q : G × G ↦ p * q)
        hShearAtP hTranslate
        (by simp [e])
        (((A, B) : GroupLieAlgebra (I.prod I) (G × G)))).symm
  have hMiddle :
      mfderiv% ((productShear (I := I)) ∘ fun q : G × G ↦ p * q) e
          (((A, B) : GroupLieAlgebra (I.prod I) (G × G))) =
        mfderiv% (fun q : G × G ↦ productShear (I := I) p * productShear (I := I) q) e
          (((A, B) : GroupLieAlgebra (I.prod I) (G × G))) := by
    have hfun :
        (productShear (I := I)) ∘ fun q : G × G ↦ p * q =
          fun q : G × G ↦ productShear (I := I) p * productShear (I := I) q := by
      funext q
      ext <;> simp [productShear, mul_assoc, mul_left_comm, mul_comm]
    simpa using congrArg
      (fun F : TangentSpace (I.prod I) e →L[𝕜] TangentSpace (I.prod I) (productShear (I := I) p) ↦
        F (((A, B) : GroupLieAlgebra (I.prod I) (G × G))))
      (show mfderiv% ((productShear (I := I)) ∘ fun q : G × G ↦ p * q) e =
          mfderiv% (fun q : G × G ↦ productShear (I := I) p * productShear (I := I) q) e by
        simpa [hfun] using mfderiv_congr hfun)
  have hTarget :
      mfderiv% (fun q : G × G ↦ productShear (I := I) p * productShear (I := I) q) e
          (((A, B) : GroupLieAlgebra (I.prod I) (G × G))) =
        mfderiv% (fun q : G × G ↦ productShear (I := I) p * q) e
          (mfderiv% (productShear (I := I)) e
            (((A, B) : GroupLieAlgebra (I.prod I) (G × G)))) := by
    simpa [e] using
      mfderiv_comp_apply_of_eq (x := e)
        (g := fun q : G × G ↦ productShear (I := I) p * q)
        (f := productShear (I := I))
        hTargetTranslate hShearAtOne
        (by simp [productShear, e])
        (((A, B) : GroupLieAlgebra (I.prod I) (G × G)))
  calc
    mfderiv% (productShear (I := I)) p
        ((((A, B) : GroupLieAlgebra (I.prod I) (G × G)))ᴸ p)
      = mfderiv% ((productShear (I := I)) ∘ fun q : G × G ↦ p * q) e
          (((A, B) : GroupLieAlgebra (I.prod I) (G × G))) := hSource
    _ = mfderiv% (fun q : G × G ↦ productShear (I := I) p * productShear (I := I) q) e
          (((A, B) : GroupLieAlgebra (I.prod I) (G × G))) := hMiddle
    _ = mfderiv% (fun q : G × G ↦ productShear (I := I) p * q) e
          (mfderiv% (productShear (I := I)) e
            (((A, B) : GroupLieAlgebra (I.prod I) (G × G)))) := hTarget
    _ = mfderiv% (fun q : G × G ↦ productShear (I := I) p * q) e
          (((A + B, B) : GroupLieAlgebra (I.prod I) (G × G))) := by
            rw [productShear_mfderiv_apply_one (I := I)]
    _ = ((((A + B, B) : GroupLieAlgebra (I.prod I) (G × G)))ᴸ
          (productShear (I := I) p)) := by
            rfl

/-- Helper for Problem 8-25: pulling back an invariant product field by the commutative product
shear replaces `(A, B)` with `(A - B, B)`. -/
private theorem productShear_mpullback_mulInvariantVectorField
    (A B : GroupLieAlgebra I G) :
    VectorField.mpullback (I.prod I) (I.prod I) (productShear (I := I))
      ((((A, B) : GroupLieAlgebra (I.prod I) (G × G)))ᴸ) =
        ((((A - B, B) : GroupLieAlgebra (I.prod I) (G × G)))ᴸ) := by
  -- Convert the pullback identity to the corresponding pushforward identity through the inverse
  -- derivative of the shear.
  ext p
  have hInv :
      (mfderiv% (productShear (I := I)) p).IsInvertible :=
    productShear_mfderivIsInvertible (I := I) p
  rw [VectorField.mpullback_apply]
  apply (hInv.inverse_apply_eq).2
  simpa [productShear, sub_eq_add_neg, add_assoc] using
    productShear_mulInvariantVectorField_pushforward (I := I) (A := A - B) (B := B) p

/-- Helper for Problem 8-25: after pulling back by the commutative product shear, the bracket of
the fields attached to `(X, 0)` and `(Y, Y)` becomes the zero cross-bracket of `(X, 0)` and
`(0, Y)`. -/
private theorem productShear_crossBracket_apply_one_eq_zero
    (X Y : GroupLieAlgebra I G) :
    VectorField.mlieBracket (I.prod I)
      ((((X, 0) : GroupLieAlgebra (I.prod I) (G × G)))ᴸ)
      ((((Y, Y) : GroupLieAlgebra (I.prod I) (G × G)))ᴸ)
      ((1 : G), (1 : G)) = 0 := by
  let e : G × G := ((1 : G), (1 : G))
  let V : ∀ p : G × G, TangentSpace (I.prod I) p :=
    ((((X, 0) : GroupLieAlgebra (I.prod I) (G × G)))ᴸ)
  let W : ∀ p : G × G, TangentSpace (I.prod I) p :=
    ((((Y, Y) : GroupLieAlgebra (I.prod I) (G × G)))ᴸ)
  have hPullback :
      VectorField.mpullback (I.prod I) (I.prod I) (productShear (I := I))
          (VectorField.mlieBracket (I.prod I) V W) e =
        VectorField.mlieBracket (I.prod I)
          (VectorField.mpullback (I.prod I) (I.prod I) (productShear (I := I)) V)
          (VectorField.mpullback (I.prod I) (I.prod I) (productShear (I := I)) W) e := by
    -- Use the existing bracket naturality API at the finite-smoothness surface.
    simpa [V, W, e, productShear] using
      (VectorField.mpullback_mlieBracket
        (I := I.prod I) (I' := I.prod I)
        (f := productShear (I := I))
        (V := V) (W := W)
        (x₀ := e) (n := minSmoothness 𝕜 3)
        (mdifferentiableAt_mulInvariantVectorField
          (I := I.prod I) (v := ((X, 0) : GroupLieAlgebra (I.prod I) (G × G)))
          (g := productShear (I := I) e))
        (mdifferentiableAt_mulInvariantVectorField
          (I := I.prod I) (v := ((Y, Y) : GroupLieAlgebra (I.prod I) (G × G)))
          (g := productShear (I := I) e))
        ((show ContMDiff (I.prod I) (I.prod I) (minSmoothness 𝕜 3) (productShear (I := I)) from
          by
            exact (show ContMDiff (I.prod I) (I.prod I) (minSmoothness 𝕜 3)
              (fun q : G × G ↦ (q.1 * q.2, q.2)) from
                (contMDiff_fst.mul contMDiff_snd).prodMk contMDiff_snd)).contMDiffAt
          (x := e))
        (minSmoothness_monotone (𝕜 := 𝕜) (by norm_num)))
  have hV :
      VectorField.mpullback (I.prod I) (I.prod I) (productShear (I := I)) V =
        ((((X, 0) : GroupLieAlgebra (I.prod I) (G × G)))ᴸ) := by
    -- The first field is fixed because subtracting zero leaves `(X, 0)` unchanged.
    simpa [V] using
      productShear_mpullback_mulInvariantVectorField (I := I) (A := X) (B := 0)
  have hW :
      VectorField.mpullback (I.prod I) (I.prod I) (productShear (I := I)) W =
        ((((0, Y) : GroupLieAlgebra (I.prod I) (G × G)))ᴸ) := by
    -- The second field becomes the split field `(0, Y)` because `Y - Y = 0`.
    simpa [W, sub_eq_add_neg] using
      productShear_mpullback_mulInvariantVectorField (I := I) (A := Y) (B := Y)
  have hZeroSplitPair :
      GroupLieAlgebra.prodToProd (I := I) (J := I)
        (VectorField.mlieBracket (I.prod I)
          ((((X, 0) : GroupLieAlgebra (I.prod I) (G × G)))ᴸ)
          ((((0, Y) : GroupLieAlgebra (I.prod I) (G × G)))ᴸ) e) =
        (0, 0) := by
    -- Rewrite the split invariant product fields componentwise and read off the zero cross-bracket.
    rw [GroupLieAlgebra.mulInvariantVectorField_prod, GroupLieAlgebra.mulInvariantVectorField_prod]
    simpa [e] using
      (GroupLieAlgebra.prodToProd_mlieBracket_prod_apply_one
        (I := I) (J := I)
        (X₁ := Xᴸ) (X₂ := 0ᴸ) (Y₁ := 0ᴸ) (Y₂ := Yᴸ)
        (mdifferentiableAt_mulInvariantVectorField (I := I) (v := X))
        (mdifferentiableAt_mulInvariantVectorField (I := I) (v := (0 : GroupLieAlgebra I G)))
        (mdifferentiableAt_mulInvariantVectorField (I := I) (v := (0 : GroupLieAlgebra I G)))
        (mdifferentiableAt_mulInvariantVectorField (I := I) (v := Y)))
  have hZeroSplit :
      VectorField.mlieBracket (I.prod I)
        ((((X, 0) : GroupLieAlgebra (I.prod I) (G × G)))ᴸ)
        ((((0, Y) : GroupLieAlgebra (I.prod I) (G × G)))ᴸ) e = 0 := by
    -- The product tangent-space splitting is a linear equivalence, so zero on both coordinates
    -- means the vector itself is zero.
    exact (GroupLieAlgebra.prodLinearEquiv (I := I) (J := I)).injective <|
      by simpa [GroupLieAlgebra.prodLinearEquiv] using hZeroSplitPair
  have hPullbackZero :
      VectorField.mpullback (I.prod I) (I.prod I) (productShear (I := I))
          (VectorField.mlieBracket (I.prod I) V W) e = 0 := by
    -- Replace the two pulled-back fields by the normalized split fields from the shear formula.
    calc
      VectorField.mpullback (I.prod I) (I.prod I) (productShear (I := I))
          (VectorField.mlieBracket (I.prod I) V W) e
        = VectorField.mlieBracket (I.prod I)
            (VectorField.mpullback (I.prod I) (I.prod I) (productShear (I := I)) V)
            (VectorField.mpullback (I.prod I) (I.prod I) (productShear (I := I)) W) e := hPullback
      _ = VectorField.mlieBracket (I.prod I)
            ((((X, 0) : GroupLieAlgebra (I.prod I) (G × G)))ᴸ)
            ((((0, Y) : GroupLieAlgebra (I.prod I) (G × G)))ᴸ) e := by
              rw [hV, hW]
      _ = 0 := hZeroSplit
  have hInv :
      (mfderiv% (productShear (I := I)) e).IsInvertible :=
    productShear_mfderivIsInvertible (I := I) e
  rw [VectorField.mpullback_apply, e, productShear] at hPullbackZero
  -- Since the derivative of the shear is invertible at `((1, 1))`, the original bracket already
  -- vanishes if its pullback does.
  exact by
    have hForward :=
      (ContinuousLinearMap.IsInvertible.inverse_apply_eq hInv).1 hPullbackZero
    simpa [e] using hForward

/-- Problem 8-25: if `G` is an abelian Lie group, then its canonical Lie algebra
`GroupLieAlgebra I G = TₑG` is abelian. -/
instance instIsLieAbelian_of_commGroup :
    IsLieAbelian (GroupLieAlgebra I G) where
  trivial X Y := by
    -- Route correction: work on `G × G` and use the commutative product shear
    -- `(g, h) ↦ (g * h, h)` to transport the obvious zero cross-bracket to the bracket whose first
    -- coordinate is `⁅X, Y⁆`.
    let e : G × G := ((1 : G), (1 : G))
    have hZero :
        VectorField.mlieBracket (I.prod I)
          ((((X, 0) : GroupLieAlgebra (I.prod I) (G × G)))ᴸ)
          ((((Y, Y) : GroupLieAlgebra (I.prod I) (G × G)))ᴸ) e = 0 :=
      productShear_crossBracket_apply_one_eq_zero (I := I) X Y
    have hZeroPair :
        GroupLieAlgebra.prodToProd (I := I) (J := I)
          (VectorField.mlieBracket (I.prod I)
            ((((X, 0) : GroupLieAlgebra (I.prod I) (G × G)))ᴸ)
            ((((Y, Y) : GroupLieAlgebra (I.prod I) (G × G)))ᴸ) e) =
          (0, 0) := by
      -- Apply the product tangent-space splitting to the vanishing bracket at the identity pair.
      simpa [e] using congrArg (GroupLieAlgebra.prodToProd (I := I) (J := I)) hZero
    have hBracketPair :
        GroupLieAlgebra.prodToProd (I := I) (J := I)
          (VectorField.mlieBracket (I.prod I)
            ((((X, 0) : GroupLieAlgebra (I.prod I) (G × G)))ᴸ)
            ((((Y, Y) : GroupLieAlgebra (I.prod I) (G × G)))ᴸ) e) =
          (⁅X, Y⁆, 0) := by
      -- Rewrite both invariant product fields in split form and then read off the componentwise
      -- product bracket formula from Problem 8-23.
      rw [GroupLieAlgebra.mulInvariantVectorField_prod, GroupLieAlgebra.mulInvariantVectorField_prod]
      simpa [e] using
        (GroupLieAlgebra.prodToProd_mlieBracket_prod_apply_one
          (I := I) (J := I)
          (X₁ := Xᴸ) (X₂ := Yᴸ) (Y₁ := 0ᴸ) (Y₂ := Yᴸ)
          (mdifferentiableAt_mulInvariantVectorField (I := I) (v := X))
          (mdifferentiableAt_mulInvariantVectorField (I := I) (v := Y))
          (mdifferentiableAt_mulInvariantVectorField (I := I) (v := (0 : GroupLieAlgebra I G)))
          (mdifferentiableAt_mulInvariantVectorField (I := I) (v := Y)))
    have hEq : (⁅X, Y⁆, 0) = (0, 0) := hBracketPair.trans hZeroPair
    -- The first coordinate of the normalized product bracket is exactly the Lie bracket in `G`.
    simpa using congrArg Prod.fst hEq

end GroupLieAlgebra

namespace AddGroupLieAlgebra

variable {G : Type uG} [TopologicalSpace G] [ChartedSpace H G] [AddCommGroup G]
variable [LieAddGroup I (minSmoothness 𝕜 3) G]

/-- Additive variant of Problem 8-25: if `G` is an abelian additive Lie group, then its canonical
Lie algebra `AddGroupLieAlgebra I G = T₀G` is abelian. -/
instance instIsLieAbelian_of_addCommGroup :
    IsLieAbelian (AddGroupLieAlgebra I G) where
  trivial X Y := by
    -- Transport the multiplicative abelianity result through `Multiplicative G`.
    letI : TopologicalSpace (Multiplicative G) := by
      simpa [Multiplicative] using (inferInstance : TopologicalSpace G)
    letI : ChartedSpace H (Multiplicative G) := by
      simpa [Multiplicative] using (inferInstance : ChartedSpace H G)
    letI : IsManifold I (minSmoothness 𝕜 3) (Multiplicative G) := by
      simpa [Multiplicative] using (inferInstance : IsManifold I (minSmoothness 𝕜 3) G)
    letI : LieGroup I (minSmoothness 𝕜 3) (Multiplicative G) := by
      refine { contMDiff_mul := ?_, contMDiff_inv := ?_ }
      · simpa [Multiplicative] using
          (contMDiff_add I (n := minSmoothness 𝕜 3) (G := G))
      simpa [Multiplicative] using
        (LieAddGroup.contMDiff_neg (I := I) (n := minSmoothness 𝕜 3) (G := G))
    simpa using
      (GroupLieAlgebra.instIsLieAbelian_of_commGroup
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (G := Multiplicative G)).trivial X Y

end AddGroupLieAlgebra

end AbelianLieGroup
