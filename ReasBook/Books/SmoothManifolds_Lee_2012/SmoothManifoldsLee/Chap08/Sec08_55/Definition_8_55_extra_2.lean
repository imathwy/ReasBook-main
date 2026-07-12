import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

noncomputable section

-- Semantic recall note: `lean_leansearch` was unavailable in this agent environment, so this item
-- uses mathlib's `IsLocalFrameOn` together with `NormedSpace.fromTangentSpace` after local
-- repository inspection.

section

variable {n k : ℕ}

namespace VectorField

/-- Definition 8.55-extra-2 (1): a `k`-tuple of vector fields on a subset `A ⊆ ℝⁿ` is orthonormal
if for each `x ∈ A`, its values at `x` are orthonormal with respect to the Euclidean inner
product, using the canonical identification
`TangentSpace (𝓡 n) x ≃L[ℝ] EuclideanSpace ℝ (Fin n)`. -/
def OrthonormalOn (A : Set (EuclideanSpace ℝ (Fin n)))
    (E : Fin k → (x : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) x) : Prop :=
  ∀ x ∈ A, Orthonormal ℝ (fun i : Fin k ↦ NormedSpace.fromTangentSpace x (E i x))

/-- Pointwise characterization of `VectorField.OrthonormalOn`. -/
theorem orthonormalOn_iff (A : Set (EuclideanSpace ℝ (Fin n)))
    (E : Fin k → (x : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) x) :
    OrthonormalOn A E ↔
      ∀ x ∈ A, Orthonormal ℝ (fun i : Fin k ↦ NormedSpace.fromTangentSpace x (E i x)) :=
  Iff.rfl

end VectorField

/-- Definition 8.55-extra-2 (2): A local frame on a subset `A ⊆ ℝⁿ` is an orthonormal frame if it
is pointwise orthonormal; the global case is obtained by taking `A = Set.univ`. -/
class IsOrthonormalFrameOn (A : Set (EuclideanSpace ℝ (Fin n)))
    (E : Fin n → (x : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) x) : Prop
    extends IsLocalFrameOn (𝓡 n) (EuclideanSpace ℝ (Fin n)) ∞ E A where
  orthonormal : VectorField.OrthonormalOn A E

/-- The vector fields of an orthonormal frame are pointwise orthonormal. -/
theorem IsOrthonormalFrameOn.pointwise_orthonormal
    {A : Set (EuclideanSpace ℝ (Fin n))}
    {E : Fin n → (x : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) x}
    (hE : IsOrthonormalFrameOn A E) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ A) :
    Orthonormal ℝ (fun i : Fin n ↦ NormedSpace.fromTangentSpace x (E i x)) :=
  hE.orthonormal x hx

end
