import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Constructible
import Mathlib.Topology.Sober

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open Topology
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme

variable {X : Scheme.{u}} {E : Set X} {ξ : X}

-- Semantic recall: `lean_leansearch` surfaced the canonical topological owners
-- `Topology.IsLocallyConstructible` and `genericPoints`. The source condition “`ξ` is a generic
-- point of an irreducible component of `X`” is exactly membership in the canonical owner
-- `genericPoints X`, so the public API is stated directly in that form.

/-- At a generic point of an irreducible component of a scheme, a locally constructible subset
contains an open neighborhood exactly when it contains the generic point. This is the canonical
`genericPoints`-owner form. -/
theorem isLocallyConstructible_mem_nhds_iff_mem_of_mem_genericPoints
    (hE : IsLocallyConstructible E) (hξ : ξ ∈ genericPoints X) :
    E ∈ 𝓝 ξ ↔ ξ ∈ E := by
  constructor
  · exact mem_of_mem_nhds
  · intro hmem
    sorry

/-- At a generic point of an irreducible component of a scheme, the complement of a locally
constructible subset contains an open neighborhood exactly when the subset omits the generic
point. This is the canonical `genericPoints`-owner form. -/
theorem compl_mem_nhds_iff_not_mem_of_isLocallyConstructible_of_mem_genericPoints
    (hE : IsLocallyConstructible E) (hξ : ξ ∈ genericPoints X) :
    Eᶜ ∈ 𝓝 ξ ↔ ξ ∉ E := by
  constructor
  · intro hcompl
    simpa using mem_of_mem_nhds hcompl
  · intro hnotmem
    sorry

/-- Lemma 28.2.2 (1): let `X` be a scheme, let `E ⊆ X` be a locally constructible subset, and let
`ξ ∈ X` be a generic point of an irreducible component of `X`. If `ξ ∈ E`, then some open
neighborhood of `ξ` is contained in `E`. -/
@[stacks 0AAW]
theorem exists_open_neighborhood_subset_of_mem_isLocallyConstructible_of_mem_genericPoints
    (hE : IsLocallyConstructible E)
    (hξ : ξ ∈ genericPoints X) (hmem : ξ ∈ E) :
    E ∈ 𝓝 ξ :=
  (isLocallyConstructible_mem_nhds_iff_mem_of_mem_genericPoints hE hξ).2 hmem

/-- Lemma 28.2.2 (2): let `X` be a scheme, let `E ⊆ X` be a locally constructible subset, and let
`ξ ∈ X` be a generic point of an irreducible component of `X`. If `ξ ∉ E`, then some open
neighborhood of `ξ` is disjoint from `E`. -/
@[stacks 0AAW]
theorem exists_open_neighborhood_disjoint_of_not_mem_isLocallyConstructible_of_mem_genericPoints
    (hE : IsLocallyConstructible E)
    (hξ : ξ ∈ genericPoints X) (hnotmem : ξ ∉ E) :
    Eᶜ ∈ 𝓝 ξ :=
  (compl_mem_nhds_iff_not_mem_of_isLocallyConstructible_of_mem_genericPoints hE hξ).2 hnotmem

end Scheme
end AlgebraicGeometry
