module

public import Topology_Munkres_2000.Book.Lemma_55_1.Inclusions

public section

universe u

namespace FundamentalGroup

/-- The least normal subgroup containing the image of the fundamental-group map induced by
an inclusion of subspaces. -/
noncomputable abbrev normalClosureOfSubset {X : Type u} [TopologicalSpace X]
    {A B : Set X} (h : A ⊆ B) (x : A) :
    Subgroup (FundamentalGroup B ⟨x, h x.property⟩) :=
  Subgroup.normalClosure (Set.range (mapOfSubset h x))

end FundamentalGroup

/-- The least normal subgroup of `π₁(U, x₀)` containing the image from `π₁(U ∩ V, x₀)`. -/
noncomputable abbrev vanKampenLeftNormalClosure {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    Subgroup (FundamentalGroup U ⟨x₀, hx₀.1⟩) :=
  FundamentalGroup.normalClosureOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩

/-- The least normal subgroup of `π₁(V, x₀)` containing the image from `π₁(U ∩ V, x₀)`. -/
noncomputable abbrev vanKampenRightNormalClosure {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    Subgroup (FundamentalGroup V ⟨x₀, hx₀.2⟩) :=
  FundamentalGroup.normalClosureOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩
