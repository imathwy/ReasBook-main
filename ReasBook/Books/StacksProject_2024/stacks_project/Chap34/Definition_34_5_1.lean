import Mathlib
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import StacksProject_2024.Chap07.Definition_7_8_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe u v

namespace AlgebraicGeometry.Scheme

-- Source/core/bridge triage:
-- `source-facing`: the Stacks notion of an indexed smooth covering family over a fixed target `T`;
-- `core/canonical`: the smooth precoverage `Scheme.precoverage @Smooth`;
-- `bridge/view`: the chapter-wide fixed-target family owner
-- `CategoryTheory.SemiRepresentableFamily.Over.IsCovering`.
--
-- The source notion is still a predicate on an explicit indexed family `ι → Over T`, but its
-- public owner should reuse the canonical project covering predicate on `SemiRepresentableFamily`
-- rather than duplicating the precoverage-membership data in a second local class.

variable {T : Scheme.{u}} {ι : Type v}

/-- The sigma-indexed map on underlying points attached to a family of schemes over `T`. -/
abbrev smoothCoveringPointMap (family : ι → Over T) : (Σ i, (family i).left) → T :=
  fun p ↦ (family p.1).hom.base p.2

/-- The sigma-indexed point map evaluates by applying the corresponding structure morphism. -/
@[simp] theorem smoothCoveringPointMap_apply (family : ι → Over T) (p : Σ i, (family i).left) :
    smoothCoveringPointMap family p = (family p.1).hom.base p.2 :=
  rfl

/-- Definition 34.5.1: a family `family : ι → Over T` is a smooth covering of `T` if each member
`(family i).hom : (family i).left ⟶ T` is smooth and the induced sigma-indexed map on underlying
points is surjective onto `T`. -/
@[stacks 01V7]
abbrev SmoothCovering (family : ι → Over T) : Prop :=
  IsCovering (Scheme.precoverage @Smooth)
    (ofArrows (fun i ↦ (family i).left) fun i ↦ (family i).hom)

/-- The source-facing smooth-covering condition is exactly membership in the canonical smooth
precoverage on schemes, expressed for the fixed-target family `family`. -/
theorem smoothCovering_iff_mem_precoverage (family : ι → Over T) :
    SmoothCovering family ↔
      Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
        (Scheme.precoverage @Smooth).coverings T := by
  simp [SmoothCovering, IsCovering]

/-- Unfold a smooth covering into memberwise smoothness and joint surjectivity on the target. -/
theorem smoothCovering_iff (family : ι → Over T) :
    SmoothCovering family ↔
      (∀ i : ι, Smooth (family i).hom) ∧
        Function.Surjective (smoothCoveringPointMap family) := by
  rw [smoothCovering_iff_mem_precoverage, Scheme.ofArrows_mem_precoverage_iff]
  constructor
  · rintro ⟨hsurj, hsmooth⟩
    refine ⟨hsmooth, ?_⟩
    intro x
    rcases hsurj x with ⟨i, ⟨y, hy⟩⟩
    exact ⟨⟨i, y⟩, by simpa [smoothCoveringPointMap] using hy⟩
  · rintro ⟨hsmooth, hsurj⟩
    refine ⟨?_, hsmooth⟩
    intro x
    rcases hsurj x with ⟨⟨i, y⟩, hy⟩
    exact ⟨i, ⟨y, by simpa [smoothCoveringPointMap] using hy⟩⟩

/-- Source-facing specification for Definition 34.5.1: a smooth covering consists of memberwise
smooth morphisms together with surjectivity of the induced sigma-indexed point map. -/
theorem SmoothCovering.source_spec {family : ι → Over T} (h : SmoothCovering family) :
    (∀ i : ι, Smooth (family i).hom) ∧
      Function.Surjective (smoothCoveringPointMap family) :=
  (smoothCovering_iff family).mp h

/-- The raw indexed-family smooth-covering predicate agrees with the canonical fixed-target
covering predicate on `SemiRepresentableFamily.Over T`. -/
theorem smoothCovering_obj_iff_isCovering
    (𝒰 : CategoryTheory.SemiRepresentableFamily.Over T) :
    SmoothCovering 𝒰.obj ↔
      CategoryTheory.SemiRepresentableFamily.Over.IsCovering
        (Scheme.precoverage @Smooth) 𝒰 :=
  Iff.rfl

/-- Every member of a smooth covering is a smooth morphism. -/
theorem SmoothCovering.smooth {family : ι → Over T} (h : SmoothCovering family) (i : ι) :
    Smooth (family i).hom :=
  h.source_spec.1 i

/-- The underlying sigma-indexed point map of a smooth covering is surjective. -/
theorem SmoothCovering.surjective_pointMap {family : ι → Over T} (h : SmoothCovering family) :
    Function.Surjective (smoothCoveringPointMap family) :=
  h.source_spec.2

/-- A point of the target lies in the image of some member of a smooth covering. -/
theorem SmoothCovering.exists_preimage
    {family : ι → Over T} (h : SmoothCovering family) (x : T) :
    ∃ p : Σ i, (family i).left, smoothCoveringPointMap family p = x :=
  h.surjective_pointMap x

/-- A smooth covering family presents a covering family in the canonical smooth precoverage on
schemes. -/
theorem SmoothCovering.mem_smooth_precoverage {family : ι → Over T} (h : SmoothCovering family) :
    Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
      (precoverage @Smooth).coverings T :=
  (smoothCovering_iff_mem_precoverage family).mp h

end AlgebraicGeometry.Scheme
