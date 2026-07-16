import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Topology.Constructible
import StacksProject_2024.stacks_project.Chap28.Lemma_28_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open Topology

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X Y : Scheme.{u}}

#check AlgebraicGeometry.Scheme.Hom.isConstructible_preimage

/- Lemma 29.22.1 (2): if `E` is locally constructible in `Y`, then `f ⁻¹' E` is locally
constructible in `X`. -/
@[stacks 054I "(2)"]
theorem isLocallyConstructible_preimage (f : X ⟶ Y) {E : Set Y}
    (hE : IsLocallyConstructible E) :
    IsLocallyConstructible (f ⁻¹' E) := by
  let cover : Y.affineOpens → Y.Opens := fun V ↦ V
  let preimageCover : Y.affineOpens → X.Opens :=
    fun V ↦ (TopologicalSpace.Opens.map f.base).obj (cover V)
  have hcover : TopologicalSpace.IsOpenCover cover := by
    exact TopologicalSpace.IsOpenCover.mk (by simpa [cover] using iSup_affineOpens_eq_top Y)
  have hpreimageCover : TopologicalSpace.IsOpenCover preimageCover := hcover.comap f.base.hom
  refine IsLocallyConstructible.of_isOpenCover hpreimageCover ?_
  intro V
  simpa [cover, preimageCover, AlgebraicGeometry.morphismRestrict_base] using
    (Scheme.Hom.isConstructible_preimage (f ∣_ (cover V))
      (Scheme.IsLocallyConstructible.isConstructible_affineOpen hE V)).isLocallyConstructible

end Scheme.Hom
end AlgebraicGeometry
