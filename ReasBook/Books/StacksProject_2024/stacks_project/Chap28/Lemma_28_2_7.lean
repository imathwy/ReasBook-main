import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Constructible
import Mathlib.Topology.LocallyFinite

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open Topology
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry
namespace Scheme

variable {X : Scheme.{u}} {I : Type v} {parts : I → Set X}

-- Semantic recall: `lean_leansearch` surfaced
-- `Topology.IsLocallyConstructible.iff_isConstructible_of_isOpenCover`,
-- `IsRetrocompact.isConstructible`, and `Topology.IsLocallyConstructible.isConstructible`.
-- Together with the affine-open criterion from `Lemma_28_2_1`, the source is best exposed as a
-- scheme theorem for an indexed partition with retrocompact pieces.

/-- Lemma 28.2.7: an indexed partition `parts` of a scheme `X` with retrocompact parts is locally
finite if and only if every part is locally constructible. -/
@[stacks 0F2M]
theorem locallyFinite_iff_forall_isLocallyConstructible_of_retrocompact
    (hparts : IndexedPartition parts) (hretro : ∀ i, IsRetrocompact (parts i)) :
    LocallyFinite parts ↔ ∀ i, IsLocallyConstructible (parts i) := sorry

/-- If an indexed partition of a scheme is locally finite and each part is retrocompact, then each
part is locally constructible. -/
theorem LocallyFinite.forall_isLocallyConstructible_of_retrocompact
    (hloc : LocallyFinite parts) (hparts : IndexedPartition parts)
    (hretro : ∀ i, IsRetrocompact (parts i)) :
    ∀ i, IsLocallyConstructible (parts i) :=
  (locallyFinite_iff_forall_isLocallyConstructible_of_retrocompact hparts hretro).1 hloc

namespace IndexedPartition

/-- If every part of a retrocompact indexed partition of a scheme is locally constructible, then
the partition is locally finite. -/
theorem locallyFinite_of_forall_isLocallyConstructible_of_retrocompact
    (hparts : IndexedPartition parts) (hretro : ∀ i, IsRetrocompact (parts i))
    (hloc : ∀ i, IsLocallyConstructible (parts i)) :
    LocallyFinite parts :=
  (locallyFinite_iff_forall_isLocallyConstructible_of_retrocompact hparts hretro).2 hloc

end IndexedPartition

end Scheme
end AlgebraicGeometry
