import Mathlib

open TopCat TopologicalSpace

universe u

namespace TopCat

/-- The inclusion morphism of a subset into its ambient topological space. -/
abbrev subsetInclusion (X : TopCat.{u}) (Z : Set X) : TopCat.of Z ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion morphism of a closed subset into its ambient topological space. -/
abbrev closedSubsetInclusion (X : TopCat.{u}) (Z : Set X) : TopCat.of Z ⟶ X :=
  subsetInclusion X Z

end TopCat
