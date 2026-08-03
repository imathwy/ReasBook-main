module

public import Topology_Munkres_2000.Book.Notation_52_1.RightCosets

public section

universe u

/- Notation 52.1: For a subgroup `H` of a group `G`, including when `H` is not
normal, the source's `G/H` denotes the type `G ⧸ᵣ H` of right cosets. -/
#check fun (G : Type u) [Group G] (H : Subgroup G) ↦ G ⧸ᵣ H
