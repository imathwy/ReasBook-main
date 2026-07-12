import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold
open VectorField

noncomputable section

universe u𝕜 uH uE uG

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {H : Type uH} [TopologicalSpace H]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type uG} [TopologicalSpace G] [ChartedSpace H G] [Group G]

-- Domain sampling pass:
-- * primary domain: vector fields on Lie groups and invariance under left translations;
-- * source-facing layer: Lee's left-invariance property of a vector field;
-- * core/canonical owners sampled before refinement:
--   `mpullback`, `mpullback_apply`, `inverse_mfderiv_mul_left`, and
--   `GroupLieAlgebra.mulInvariantVectorField`.
-- The primitive data here is only the vector field `X`; left-invariance is a predicate on `X`,
-- and the pointwise `mfderiv` formula is a derived bridge theorem.

namespace VectorField

/-- The predicate from Definition 8.60-extra-1 asserting that pullback by every left translation
fixes the vector field. -/
def IsLeftInvariant (X : ∀ g : G, TangentSpace I g) : Prop :=
  ∀ g : G, mpullback I I (g * ·) X = X

section

variable [LieGroup I 1 G]

/-- Helper for Definition 8.60-extra-1: the manifold derivative of left translation by `g` at `g'`
is invertible, with inverse induced by left translation by `g⁻¹`. -/
lemma leftTranslationMfderivIsInvertible (g g' : G) :
    (mfderiv% (g * ·) g').IsInvertible := by
  -- View left translation as a `C^1` diffeomorphism so its derivative is automatically invertible.
  have hLeftInv : Function.LeftInverse (fun x : G ↦ g⁻¹ * x) (fun x : G ↦ g * x) := by
    intro x
    simp
  have hRightInv : Function.RightInverse (fun x : G ↦ g⁻¹ * x) (fun x : G ↦ g * x) := by
    intro x
    simp
  have hToFun : ContMDiff I I 1 (fun x : G ↦ g * x) := by
    simpa using (contMDiff_mul_left (I := I) (a := g) : ContMDiff I I 1 (fun x : G ↦ g * x))
  have hInvFun : ContMDiff I I 1 (fun x : G ↦ g⁻¹ * x) := by
    simpa using
      (contMDiff_mul_left (I := I) (a := g⁻¹) : ContMDiff I I 1 (fun x : G ↦ g⁻¹ * x))
  let Φ : G ≃ₘ^1⟮I, I⟯ G :=
    { toEquiv :=
        { toFun := fun x ↦ g * x
          invFun := fun x ↦ g⁻¹ * x
          left_inv := hLeftInv
          right_inv := hRightInv }
      contMDiff_toFun := hToFun
      contMDiff_invFun := hInvFun }
  let e : TangentSpace I g' ≃L[𝕜] TangentSpace I (g * g') :=
    Φ.mfderivToContinuousLinearEquiv one_ne_zero g'
  refine ⟨e, ?_⟩
  -- Identify the differential of the diffeomorphism with the differential of `g * ·`.
  simpa [e, Φ] using
    (Φ.mfderivToContinuousLinearEquiv_coe one_ne_zero (x := g') :
      ↑(Φ.mfderivToContinuousLinearEquiv one_ne_zero g') = mfderiv% Φ g').symm

/-- Definition 8.60-extra-1: A vector field is left-invariant iff the differential of each left
translation sends its value at `g'` to its value at `g * g'`. -/
theorem isLeftInvariant_iff_mfderiv
    (X : ∀ g : G, TangentSpace I g) :
    IsLeftInvariant X ↔
      ∀ g g' : G, (mfderiv% (g * ·) g') (X g') = X (g * g') := by
  constructor
  · intro h g g'
    let A := mfderiv% (g * ·) g'
    have hA : A.IsInvertible := leftTranslationMfderivIsInvertible (I := I) g g'
    -- Evaluate the pullback identity at `g'` to get an equality involving `A.inverse`.
    have hPoint : A.inverse (X (g * g')) = X g' := by
      have hEval : mpullback I I (g * ·) X g' = X g' := congrFun (h g) g'
      simpa [A, mpullback_apply] using hEval
    -- Convert the pullback equality into the forward differential formula.
    exact ((ContinuousLinearMap.IsInvertible.inverse_apply_eq hA).1 hPoint).symm
  · intro h g
    ext g'
    let A := mfderiv% (g * ·) g'
    have hA : A.IsInvertible := leftTranslationMfderivIsInvertible (I := I) g g'
    -- Rewrite the target pullback identity pointwise and solve it by inverting the derivative.
    rw [mpullback_apply]
    simpa [A] using (ContinuousLinearMap.IsInvertible.inverse_apply_eq hA).2 (h g g').symm

end

end VectorField
