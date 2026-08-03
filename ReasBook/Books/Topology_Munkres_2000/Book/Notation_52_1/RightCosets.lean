module

public import Mathlib.GroupTheory.Coset.Defs

public section

universe u

namespace QuotientGroup

/-- The type of right cosets of `H` in `G`. -/
abbrev RightCosets (G : Type u) [Group G] (H : Subgroup G) :=
  Quotient (rightRel H)

end QuotientGroup

/-- The type of right cosets of `H` in `G`. -/
notation:35 G " ⧸ᵣ " H:34 => QuotientGroup.RightCosets G H
