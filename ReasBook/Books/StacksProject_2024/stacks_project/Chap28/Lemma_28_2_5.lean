import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open Topology
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

section

variable {X : Scheme.{u}} {E : Set X}
variable [CompactSpace X] [QuasiSeparatedSpace X]

-- Semantic recall: `lean_leansearch` pointed to the canonical owner theorem
-- `Topology.IsLocallyConstructible.isConstructible`; this Stacks item is its scheme specialization
-- for a quasi-compact and quasi-separated scheme.

/-- Lemma 28.2.5: let `X` be a quasi-compact and quasi-separated scheme. Any locally constructible
subset of `X` is constructible. -/
@[stacks 054E]
theorem isConstructible_of_isLocallyConstructible (hE : IsLocallyConstructible E) :
    IsConstructible E :=
  hE.isConstructible

end

end AlgebraicGeometry.Scheme
