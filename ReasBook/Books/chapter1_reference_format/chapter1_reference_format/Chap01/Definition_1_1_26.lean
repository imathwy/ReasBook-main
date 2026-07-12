import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 1.1.26: for a group `G`, a subgroup of `G` is a subset `H` that is itself a group
under the group operation of `G`; this is the standard bundled notion `Subgroup G`. -/
recall Subgroup (G : Type u) [Group G] : Type u
