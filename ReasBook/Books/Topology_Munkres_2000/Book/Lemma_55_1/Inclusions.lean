module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

public section

universe u

namespace FundamentalGroup

/-- The homomorphism on fundamental groups induced by an inclusion of subspaces. -/
noncomputable def mapOfSubset {X : Type u} [TopologicalSpace X] {U V : Set X}
    (h : U ⊆ V) (x : U) :
    FundamentalGroup U x →* FundamentalGroup V ⟨x, h x.property⟩ :=
  map (ContinuousMap.inclusion h) x

/-- Helper for Exercise 62.4: the subset-induced map is the fundamental-group
map of the bundled continuous inclusion. -/
lemma mapOfSubset_eq_map_inclusion
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    (h : U ⊆ V) (x : U) :
    mapOfSubset h x = map (ContinuousMap.inclusion h) x := by
  -- This exposes the defining computation rule to importing modules.
  rfl

/-- The homomorphism on fundamental groups induced by inclusion into the ambient space. -/
noncomputable def mapOfSubtype {X : Type u} [TopologicalSpace X]
    (U : Set X) (x : U) : FundamentalGroup U x →* FundamentalGroup X x :=
  map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) x

end FundamentalGroup
