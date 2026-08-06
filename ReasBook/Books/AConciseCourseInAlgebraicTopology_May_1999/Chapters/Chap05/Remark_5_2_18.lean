import Mathlib.Topology.UnitInterval
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Example_5_1_11
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Proposition_5_2_17

open scoped unitInterval
open scoped Topology

universe u v

namespace CompactlyGenerated

-- Semantic recall via `lean_leansearch`: `ContinuousMap.Homotopy.curry` identifies a homotopy
-- with a path-space map in the ordinary topological setting, while Proposition 5.2.17 provides
-- the compactly generated curry homeomorphism needed for the Chapter 5 owner surface.

section

variable (X : Type u) [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace X]
  (Y : Type v) [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace Y]

/-- Remark 5.2.18. For compactly generated spaces `X` and `Y`, a map `X × I → Y` may equivalently
be regarded as a map `X → Y^I`; this is the adjoint viewpoint used later for cofibrations and
fibrations. -/
abbrev homotopyAdjointHomeomorph :
    (Y ^ Kified (X × I)) ≃ₜ ((Y ^ I) ^ X) :=
  mapSpaceCurryHomeomorph X I Y

/-- Evaluating `homotopyAdjointHomeomorph` agrees with the explicit currying map for the interval
parameter. -/
theorem homotopyAdjointHomeomorph_spec
    (F : Y ^ Kified (X × I)) :
    homotopyAdjointHomeomorph X Y F = mapSpaceCurry X I Y F :=
  rfl

/-- `homotopyAdjointHomeomorph` is the `I`-specialization of Proposition 5.2.17's curry
homeomorphism. -/
@[simp] theorem homotopyAdjointHomeomorph_def :
    homotopyAdjointHomeomorph X Y =
      mapSpaceCurryHomeomorph X I Y :=
  rfl

/-- Evaluating `homotopyAdjointHomeomorph` gives the usual adjoint map `x ↦ (t ↦ F (x, t))`. -/
@[simp] theorem homotopyAdjointHomeomorph_apply
    (F : Y ^ Kified (X × I)) (x : X) (t : I) :
    homotopyAdjointHomeomorph X Y F x t = F (Kified.mk (x, t)) :=
  rfl

/-- `homotopyAdjointHomeomorph` is inverted by its uncurry map on adjoint homotopies. -/
@[simp] theorem homotopyAdjointHomeomorph_left_inv
    (F : Y ^ Kified (X × I)) :
    (homotopyAdjointHomeomorph X Y).symm (homotopyAdjointHomeomorph X Y F) = F := by
  simpa [homotopyAdjointHomeomorph] using
    mapSpaceCurry_leftInverse X I Y F

/-- The inverse of `homotopyAdjointHomeomorph` is the interval-specialized uncurry map. -/
@[simp] theorem homotopyAdjointHomeomorph_symm_def :
    ((homotopyAdjointHomeomorph X Y).symm :
      ((Y ^ I) ^ X) → (Y ^ Kified (X × I))) =
      mapSpaceUncurry X I Y :=
  rfl

/-- `homotopyAdjointHomeomorph` is inverted by its curry map on adjoint path-space maps. -/
@[simp] theorem homotopyAdjointHomeomorph_right_inv
    (G : (Y ^ I) ^ X) :
    homotopyAdjointHomeomorph X Y ((homotopyAdjointHomeomorph X Y).symm G) = G := by
  simpa [homotopyAdjointHomeomorph] using
    mapSpaceCurry_rightInverse X I Y G

/-- Evaluating the inverse of `homotopyAdjointHomeomorph` recovers the usual uncurried map. -/
@[simp] theorem homotopyAdjointHomeomorph_symm_apply
    (G : (Y ^ I) ^ X) (p : Kified (X × I)) :
    (homotopyAdjointHomeomorph X Y).symm G p = G p.of.1 p.of.2 :=
  rfl

end

end CompactlyGenerated
