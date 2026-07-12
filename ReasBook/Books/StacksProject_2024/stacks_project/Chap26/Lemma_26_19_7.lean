import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Topology

namespace AlgebraicGeometry

-- Semantic recall: for quasi-compact morphisms of schemes, mathlib's canonical map-level owner is
-- `AlgebraicGeometry.isClosedMap_iff_specializingMap`. This file keeps the exact source-facing
-- range statement rather than replacing it by the stronger closed-map/specializing-map reformulation.

/-- Lemma 26.19.7: for a quasi-compact morphism of schemes, the image is closed if and only if it
is stable under specialization. -/
theorem Scheme.Hom.isClosed_range_iff_stableUnderSpecialization {X S : Scheme} (f : X ⟶ S)
    [QuasiCompact f] :
    IsClosed (Set.range f.base) ↔ StableUnderSpecialization (Set.range f.base) := by
  constructor
  · exact IsClosed.stableUnderSpecialization
  · intro hrange
    sorry

/-- Companion bridge: if a quasi-compact morphism is a closed map on underlying spaces, then its
range is stable under specialization. This packages the range-level consequence of the canonical
map-level owner `AlgebraicGeometry.isClosedMap_iff_specializingMap`. -/
theorem Scheme.Hom.stableUnderSpecialization_range_of_isClosedMap {X S : Scheme} (f : X ⟶ S)
    [QuasiCompact f] (hf : IsClosedMap f.base) :
    StableUnderSpecialization (Set.range f.base) := by
  exact SpecializingMap.stableUnderSpecialization_range <|
    (AlgebraicGeometry.isClosedMap_iff_specializingMap f).1 hf

end AlgebraicGeometry
