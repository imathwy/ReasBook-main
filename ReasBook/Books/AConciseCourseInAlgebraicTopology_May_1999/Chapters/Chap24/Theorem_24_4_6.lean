import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.UnitSphereTangent
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

open Bundle
open scoped Manifold

noncomputable section

/-- The standard unit sphere realizing the even sphere `S^(2n)`. -/
abbrev evenUnitSphere (n : ℕ+) :=
  unitSphere (2 * (n : ℕ))

/-- The standard smooth manifold model for the even sphere `S^(2n)`. -/
abbrev evenUnitSphereModel (n : ℕ+) :=
  modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (n : ℕ))))

/-- The tangent space of the standard even sphere `S^(2n)` at a point `x`. -/
abbrev evenUnitSphereTangentSpace (n : ℕ+) (x : evenUnitSphere n) :=
  TangentSpace (evenUnitSphereModel n) x

/-- The model fiber for tangent endomorphisms on `S^(2n)`. -/
abbrev evenUnitSphereTangentEndomorphismFiber (n : ℕ+) :=
  EuclideanSpace ℝ (Fin (2 * (n : ℕ))) →L[ℝ]
    EuclideanSpace ℝ (Fin (2 * (n : ℕ)))

/-- The tangent-endomorphism bundle of `S^(2n)`. -/
abbrev evenUnitSphereTangentEndomorphismBundle (n : ℕ+) (x : evenUnitSphere n) :=
  evenUnitSphereTangentSpace n x →L[ℝ] evenUnitSphereTangentSpace n x

instance evenUnitSphereTangentEndomorphismBundleFiberBundle (n : ℕ+) :
    FiberBundle (evenUnitSphereTangentEndomorphismFiber n)
      (evenUnitSphereTangentEndomorphismBundle n) := by
  exact inferInstanceAs
    (FiberBundle
      (EuclideanSpace ℝ (Fin (2 * (n : ℕ))) →L[ℝ] EuclideanSpace ℝ (Fin (2 * (n : ℕ))))
      (fun x : evenUnitSphere n ↦
        TangentSpace (evenUnitSphereModel n) x →L[ℝ] TangentSpace (evenUnitSphereModel n) x))

instance evenUnitSphereTangentEndomorphismBundleVectorBundle (n : ℕ+) :
    VectorBundle ℝ (evenUnitSphereTangentEndomorphismFiber n)
      (evenUnitSphereTangentEndomorphismBundle n) := by
  exact inferInstanceAs
    (VectorBundle ℝ
      (EuclideanSpace ℝ (Fin (2 * (n : ℕ))) →L[ℝ] EuclideanSpace ℝ (Fin (2 * (n : ℕ))))
      (fun x : evenUnitSphere n ↦
        TangentSpace (evenUnitSphereModel n) x →L[ℝ] TangentSpace (evenUnitSphereModel n) x))

instance evenUnitSphereTangentEndomorphismBundleContMDiffVectorBundle
    (n : ℕ+) (m : WithTop ℕ∞) :
    ContMDiffVectorBundle m (evenUnitSphereTangentEndomorphismFiber n)
      (evenUnitSphereTangentEndomorphismBundle n) (evenUnitSphereModel n) := by
  exact inferInstanceAs
    (ContMDiffVectorBundle m
      (EuclideanSpace ℝ (Fin (2 * (n : ℕ))) →L[ℝ] EuclideanSpace ℝ (Fin (2 * (n : ℕ))))
      (fun x : evenUnitSphere n ↦
        TangentSpace (evenUnitSphereModel n) x →L[ℝ] TangentSpace (evenUnitSphereModel n) x)
      (evenUnitSphereModel n))

/-- The smooth sections of the tangent-endomorphism bundle of `S^(2n)`. -/
abbrev evenUnitSphereTangentEndomorphismSection (n : ℕ+) :=
  Cₛ^⊤⟮evenUnitSphereModel n; evenUnitSphereTangentEndomorphismFiber n,
    evenUnitSphereTangentEndomorphismBundle n⟯

/-- A smooth tangent endomorphism section `J` on `S^(2n)` is an almost complex structure if
`J² = -id` on each tangent space. -/
structure IsEvenSphereAlmostComplexStructure {n : ℕ+}
    (J : evenUnitSphereTangentEndomorphismSection n) : Prop where
  /-- On each tangent space, the square of `J` is `-id`. -/
  sq_eq_neg_id (x : evenUnitSphere n) :
      (J x).comp (J x) =
        -ContinuousLinearMap.id ℝ (evenUnitSphereTangentSpace n x)

/-- Applying an almost complex structure twice on `S^(2n)` is pointwise `-id`. -/
theorem IsEvenSphereAlmostComplexStructure.sq_apply_eq_neg
    {n : ℕ+} {J : evenUnitSphereTangentEndomorphismSection n}
    (hJ : IsEvenSphereAlmostComplexStructure J) (x : evenUnitSphere n)
    (v : evenUnitSphereTangentSpace n x) :
    J x (J x v) = -v := by
  have hv := congrArg (fun f ↦ f v) (hJ.sq_eq_neg_id x)
  simpa using hv

/-- The even sphere `S^(2n)` admits an almost complex structure if its tangent-endomorphism bundle
has a smooth section squaring fiberwise to `-id`. -/
def evenSphereHasAlmostComplexStructure (n : ℕ+) : Prop :=
  ∃ J : evenUnitSphereTangentEndomorphismSection n, IsEvenSphereAlmostComplexStructure J

/-- Theorem 24.4.6. Among the positive even-dimensional spheres `S^(2n)`, the only ones admitting
almost complex structures are `S^2` and `S^6`; equivalently, `S^(2n)` admits such a structure if
and only if `n = 1` or `n = 3`. -/
theorem evenSphere_hasAlmostComplexStructure_iff (n : ℕ+) :
    evenSphereHasAlmostComplexStructure n ↔ n = 1 ∨ n = 3 := sorry
