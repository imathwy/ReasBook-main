import Mathlib
import StacksProject_2024.Chap29.Definition_29_57_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

-- Semantic recall: `lean_leansearch` recalled the canonical owner `LocallyQuasiFinite`.
-- Local Section 29.57 precedent fixes the target property as
-- `Scheme.Hom.universallyBoundedFibres`, while local scheme precedent represents
-- quasi-compactness of the source scheme as `[CompactSpace X]`.

/-- Lemma 29.57.9: if `f : X ⟶ Y` is locally quasi-finite and `X` is quasi-compact, then
`f` has universally bounded fibres. -/
@[stacks 03JA]
theorem universallyBoundedFibres_of_locallyQuasiFinite_of_compactSpace
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [CompactSpace X] :
    universallyBoundedFibres f := sorry

end Scheme.Hom
end AlgebraicGeometry
