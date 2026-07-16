import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap02.Sec02_09.Proposition_2_15
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01_06.Exercise_1_44
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Manifold ContDiff

noncomputable section

universe uK uE uE' uH uH' uM uN

variable {𝕜 : Type uK} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners 𝕜 E H}
variable {I' : ModelWithCorners 𝕜 E' H'}

section BoundaryInterior

variable {n : ℕ∞ω} [IsManifold I n M] [IsManifold I' n N]

/- Theorem 2.18 (1) (core/canonical recall): a smooth diffeomorphism carries the boundary of a
smooth manifold onto the boundary of the target manifold. -/
#check Diffeomorph.image_boundary

namespace Diffeomorph

private theorem restrictOpenImage_interiorOpens (Φ : M ≃ₘ^n⟮I, I'⟯ N) (hn : n ≠ 0) :
    Φ.restrictOpenImage (I.interiorOpens M hn) = I'.interiorOpens N hn := by
  ext x
  change x ∈ Set.range (fun y : I.interiorOpens M hn ↦ Φ y) ↔ x ∈ I'.interior N
  simpa [ModelWithCorners.interiorOpens] using
    congrArg (fun s : Set N ↦ x ∈ s) (Φ.image_interior hn)

/-- Theorem 2.18 (2) (bridge/view): in the canonical `C^n` form, the restriction of a
diffeomorphism to manifold interiors is a diffeomorphism. The source smooth statement is the
specialization `n = ∞`. -/
abbrev restrictInterior (Φ : M ≃ₘ^n⟮I, I'⟯ N) (hn : n ≠ 0) :
    I.interiorOpens M hn ≃ₘ^n⟮I, I'⟯ I'.interiorOpens N hn :=
  restrictOpenImage_interiorOpens Φ hn ▸ Φ.restrictOpen (I.interiorOpens M hn)

/-- The canonical interior restriction of `Φ` acts on underlying points by `Φ` itself. -/
@[simp] theorem restrictInterior_apply (Φ : M ≃ₘ^n⟮I, I'⟯ N) (hn : n ≠ 0)
    (x : I.interiorOpens M hn) : ((Φ.restrictInterior hn x : I'.interiorOpens N hn) : N) = Φ x :=
  sorry

end Diffeomorph

end BoundaryInterior
