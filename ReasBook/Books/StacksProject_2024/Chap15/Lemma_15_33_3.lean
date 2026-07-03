import Mathlib
import StacksProject_2024.Chap15.Definition_15_33_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace RingHom

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Domain-style sampling:
- primary domain: target-local properties of commutative ring homomorphisms, specialized here to
  local complete intersections;
- sampled owner declarations:
  `RingHom.IsLocalCompleteIntersection`,
  `RingHom.OfLocalizationSpanTarget`,
  `RingHom.OfLocalizationFiniteSpanTarget`,
  `RingHom.ofLocalizationSpanTarget_iff_finite`;
- best owner abstraction: the locality statement belongs at the meta-property owner
  `RingHom.OfLocalizationSpanTarget` for the ring-hom predicate
  `RingHom.IsLocalCompleteIntersection`; the finite principal-open version is only the bridge
  supplied by `RingHom.ofLocalizationSpanTarget_iff_finite`;
- primitive vs. derived: the primitive owner inputs are the ring map `f`, a spanning set
  `s : Set S`, and the localized `IsLocalCompleteIntersection` hypotheses on the maps
  `R → S[1 / g]`; any theorem specialized to one chosen finite family is derived API obtained by
  applying `RingHom.ofLocalizationSpanTarget_iff_finite`.

Source/core/bridge triage:
- `source-facing`: target-local descent of `RingHom.IsLocalCompleteIntersection` from a finite
  principal-open cover;
- `core/canonical`: `RingHom.OfLocalizationSpanTarget RingHom.IsLocalCompleteIntersection`;
- `bridge/view`: the finite-family specialization
  `RingHom.OfLocalizationFiniteSpanTarget RingHom.IsLocalCompleteIntersection`, recovered via
  `RingHom.ofLocalizationSpanTarget_iff_finite`. -/

namespace IsLocalCompleteIntersection

-- Proof sketch: first reduce to the finite-spanning formulation via
-- `RingHom.ofLocalizationSpanTarget_iff_finite`. Then choose a finite polynomial presentation of
-- `S` over `R`. For each `g ∈ s`, the localization `S[1 / g]` inherits a presentation whose
-- kernel ideal is obtained by adjoining one equation `x * h_j - 1`. The local complete
-- intersection hypothesis on each principal chart makes these localized kernel ideals
-- Koszul-regular. Since the elements of `s` generate the unit ideal, every prime of the global
-- presentation misses some `g ∈ s`, so Lemmas `15.30.15` and `15.30.14` descend the local
-- Koszul-regular generators back to a Zariski neighborhood of that prime in the original
-- presentation. Hence the original kernel ideal is locally Koszul-regular.
/-- Lemma 15.33.3: local complete intersection is local on the target for principal-open covers. -/
theorem ofLocalizationSpanTarget :
    OfLocalizationSpanTarget IsLocalCompleteIntersection := by
  rw [RingHom.ofLocalizationSpanTarget_iff_finite]
  sorry

/-- Source-facing finite-cover specialization of
`IsLocalCompleteIntersection.ofLocalizationSpanTarget`. -/
theorem ofLocalizationFiniteSpanTarget :
    OfLocalizationFiniteSpanTarget IsLocalCompleteIntersection := by
  rw [← RingHom.ofLocalizationSpanTarget_iff_finite]
  exact ofLocalizationSpanTarget

end IsLocalCompleteIntersection

end

end RingHom
