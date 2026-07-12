import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Topology.Constructible

-- Declarations for this item will be appended below by the statement pipeline.

open Topology

universe u

namespace AlgebraicGeometry
namespace Scheme

variable {X : Scheme.{u}} {x : X} {E : Set X}

-- Semantic recall: `lean_leansearch` surfaced the canonical topological owners
-- `Topology.IsLocallyConstructible` and `Specializes`; nearby Stacks files use `E ∈ 𝓝 x`
-- for "some open neighbourhood of `x` is contained in `E`". The tag evidence is consistent:
-- item tag `05LW` matches the source URL `/tag/05LW`.

/-- Lemma 29.22.4: let `X` be a scheme, let `x ∈ X`, and let `E ⊆ X` be locally
constructible. If every generalization of `x` lies in `E`, then `E` contains an open
neighbourhood of `x`. -/
@[stacks 05LW]
theorem isLocallyConstructible_mem_nhds_of_generizations_subset
    (hE : IsLocallyConstructible E) (hx : {x' : X | x' ⤳ x} ⊆ E) :
    E ∈ 𝓝 x := sorry

end Scheme
end AlgebraicGeometry
