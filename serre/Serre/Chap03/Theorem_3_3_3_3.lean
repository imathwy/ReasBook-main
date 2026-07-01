import Mathlib.RepresentationTheory.Induced

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {k : Type u} {G : Type v} [CommRing k] [Group G]
variable (H : Subgroup G)

-- Source/core/bridge triage:
-- * source-facing: the theorem only asserts existence of the representation induced from a
--   subgroup representation along `H ≤ G`.
-- * core/canonical: mathlib's owner for induction is `Rep.ind`.
-- * bridge/view: the source theorem is the subgroup specialization `Rep.ind H.subtype`.
--
-- Primitive data are only the subgroup inclusion and a representation of `H`; the induced
-- `G`-representation is derived directly from the owner abstraction, so no local wrapper or
-- auxiliary packaging is needed.
/- Theorem 3-3.3-3: every linear representation of a subgroup `H` admits an induced
representation of `G`. The core/canonical owner is the subgroup-induction construction
`Rep.ind H.subtype : Rep k H → Rep k G`. -/
#check (Rep.ind H.subtype : Rep k H → Rep k G)

end
