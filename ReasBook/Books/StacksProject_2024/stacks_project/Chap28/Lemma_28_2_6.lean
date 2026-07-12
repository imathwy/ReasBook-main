import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Topology.Constructible

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open Topology
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme

section

variable {X : Scheme.{u}} {E : Set X}

-- Semantic recall: `IsRetrocompact` is the ambient topological owner, while for schemes the source
-- tests it on affine opens. The explicit affine-open binder is the source-facing statement, and
-- the `X.affineOpens` packaging is the canonical companion view.

/-- Lemma 28.2.6: a subset `E` of a scheme `X` is retrocompact in `X` if and only if `E ∩ U` is
quasi-compact for every affine open `U` of `X`. -/
@[stacks 01KV]
theorem isRetrocompact_iff_forall_inter_isCompact_of_isAffineOpen :
    IsRetrocompact E ↔ ∀ U : X.Opens, IsAffineOpen U → IsCompact (E ∩ U) := by
  sorry

/-- Companion form of `isRetrocompact_iff_forall_inter_isCompact_of_isAffineOpen`, packaged over
`X.affineOpens`. -/
theorem isRetrocompact_iff_forall_isAffineOpen_inter_isCompact :
    IsRetrocompact E ↔ ∀ U : X.affineOpens, IsCompact (E ∩ U) := by
  constructor
  · intro hE U
    exact isRetrocompact_iff_forall_inter_isCompact_of_isAffineOpen.mp hE U U.2
  · intro hE
    exact isRetrocompact_iff_forall_inter_isCompact_of_isAffineOpen.mpr fun U hU ↦ hE ⟨U, hU⟩

end

end Scheme
end AlgebraicGeometry
