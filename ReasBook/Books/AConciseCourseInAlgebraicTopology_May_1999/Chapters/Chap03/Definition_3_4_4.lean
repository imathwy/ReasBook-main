import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Subgroup

variable {G : Type u} [Group G]

/- Definition 3.4.4: for a subgroup `H` of `G`, its normalizer is the canonical subgroup
`Subgroup.normalizer (H : Set G)`. -/
recall Subgroup.normalizer (H : Set G) : Subgroup G

/-- Definition 3.4.4: the Weyl group of `H` is the quotient of its normalizer by `H`, viewed as a
subgroup of `normalizer H`. -/
abbrev weylGroup (H : Subgroup G) :=
  normalizer H ⧸ H.subgroupOf (normalizer H)

end Subgroup
