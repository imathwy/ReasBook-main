import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable (G : Type u) [Group G] (H : Subgroup G)

/- Definition 1.1.51: a subgroup `H` of a group `G` is normal if it is invariant under
conjugation by every element of `G`; this is the canonical predicate `Subgroup.Normal H`. -/
#check H.Normal

/- The textbook condition that every left coset `gH` equals the corresponding right coset `Hg`
is exactly the canonical characterization `normal_iff_eq_cosets`. -/
#check normal_iff_eq_cosets H
