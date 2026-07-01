import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.SmoothEmbedding
import SmoothManifoldsLee.Chap05.Sec05_28.Definition_5_28_extra_1

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic search tool unavailable in this environment; local mathlib and repository APIs were
-- checked directly for the tangent-space and tangent-bundle surface used below.

open Manifold
open scoped ContDiff Manifold

noncomputable section

section UnitTangentBundle

variable (n m : ℕ)
variable (S : Set (EuclideanSpace ℝ (Fin n)))
variable [ChartedSpace (EuclideanSpace ℝ (Fin m)) S]

/-- The unit tangent bundle of the embedded submanifold `S`, owned intrinsically as the unit-norm
locus in `TS`, where the norm is measured after applying the canonical tangent map of the subtype
inclusion `S ↪ ℝ^n`. -/
def unitTangentBundle :=
  { v : TangentBundle (𝓡 m) S |
      let w := tangentMap (𝓡 m) (𝓡 n) ((↑) : S → EuclideanSpace ℝ (Fin n)) v
      ‖NormedSpace.fromTangentSpace w.proj w.2‖ = 1 }

namespace unitTangentBundle

/-- The canonical inclusion of the unit tangent bundle into the ambient tangent bundle `Tℝ^n`. -/
def inclusion :
    unitTangentBundle n m S → TangentBundle (𝓡 n) (EuclideanSpace ℝ (Fin n)) :=
  tangentMap (𝓡 m) (𝓡 n) ((↑) : S → EuclideanSpace ℝ (Fin n)) ∘ Subtype.val

/-- Under the canonical inclusion into the ambient tangent bundle, a point of the unit tangent
bundle has ambient tangent norm `1`. -/
@[simp] theorem norm_eq_one
    (v : unitTangentBundle n m S) :
    ‖NormedSpace.fromTangentSpace
        (inclusion n m S v).proj
        (inclusion n m S v).2‖ = 1 := by
  exact v.2

end unitTangentBundle

end UnitTangentBundle

section EmbeddedUnitTangentBundle

variable (n m : ℕ)
variable (S : Set (EuclideanSpace ℝ (Fin n)))
variable [ChartedSpace (EuclideanSpace ℝ (Fin m)) S]
variable [IsManifold (𝓡 m) (∞ : ℕ∞ω) S]
variable [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) S]

-- Proof sketch: work in local slice coordinates for the embedded submanifold. There the tangent
-- bundle of `S` identifies with `U × ℝ^m`, and the unit condition cuts out `U × S^{m-1}`. The
-- standard sphere charts then supply a smooth `(2m - 1)`-manifold structure, and the canonical
-- inclusion into `Tℝ^n` is a smooth embedding.
/-- Problem 5-6: if `S ⊆ ℝ^n` is a smooth embedded `m`-manifold, then its intrinsic unit tangent
bundle admits a smooth `(2m - 1)`-manifold structure whose canonical inclusion into the ambient
tangent bundle `Tℝ^n` is a smooth embedding. -/
theorem unitTangentBundle_exists_isSmoothEmbedding :
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin (2 * m - 1))) (unitTangentBundle n m S),
      letI := cs
      ∃ hs : IsManifold (𝓡 (2 * m - 1)) (∞ : ℕ∞ω) (unitTangentBundle n m S),
        letI := hs
        IsSmoothEmbedding (𝓡 (2 * m - 1)) (𝓡 n).tangent (∞ : ℕ∞ω)
          (unitTangentBundle.inclusion n m S) := sorry

end EmbeddedUnitTangentBundle
