import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Constructible

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open Topology
open scoped Set.Notation

universe u

namespace AlgebraicGeometry
namespace Scheme

variable {X : Scheme.{u}} {E : Set X}

-- Semantic recall: the canonical owner theorem is `Topology.IsLocallyConstructible.iff_of_isOpenCover`.
-- For an affine open, "constructible in `U`" means constructible on the open subspace `U`; since
-- each `U : X.affineOpens` is an affine scheme, local constructibility on that subspace upgrades
-- canonically to constructibility there.

/-- The affine-open-subtype form of the local constructibility criterion on a scheme. -/
theorem isLocallyConstructible_iff_forall_affineOpens_isConstructible :
    IsLocallyConstructible E ↔
      ∀ U : X.affineOpens, IsConstructible ((U : Set X) ↓∩ E) := sorry

/-- Affine-open traces of a locally constructible subset of a scheme are constructible in the
corresponding affine-open subspaces. -/
theorem IsLocallyConstructible.isConstructible_affineOpen
    (hE : IsLocallyConstructible E) (U : X.affineOpens) :
    IsConstructible ((U : Set X) ↓∩ E) := sorry

/-- If the trace of `E` on every affine open of `X` is constructible in that affine-open subspace,
then `E` is locally constructible in `X`. -/
theorem isLocallyConstructible_of_forall_affineOpens_isConstructible
    (hE : ∀ U : X.affineOpens, IsConstructible ((U : Set X) ↓∩ E)) :
    IsLocallyConstructible E := sorry

/-- Lemma 28.2.1: a subset `E` of a scheme `X` is locally constructible in `X` if and only if
for every affine open `U` of `X`, the trace `E ∩ U` is constructible in `U`. -/
@[stacks 054C]
theorem isLocallyConstructible_iff_forall_isAffineOpen_inter_isConstructible :
    IsLocallyConstructible E ↔
      ∀ U : X.Opens, IsAffineOpen U → IsConstructible ((U : Set X) ↓∩ E) := sorry

end Scheme
end AlgebraicGeometry
