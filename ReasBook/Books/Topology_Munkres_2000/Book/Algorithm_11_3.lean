module

public import Topology_Munkres_2000.Book.Definition_11_3.GreedyChain

public section

universe u

/-- Algorithm 11.3. Well-order the underlying type and run the transfinite greedy
construction to obtain a maximal simply ordered subset. -/
noncomputable def wellOrderedGreedyChain {A : Type u} (r : A → A → Prop) : Set A :=
  GreedyChain.set r WellOrderingRel id

/-- The subset constructed in Algorithm 11.3 is a maximal chain. -/
theorem wellOrderedGreedyChain_isMaxChain {A : Type u} (r : A → A → Prop)
    [IsStrictOrder A r] : IsMaxChain r (wellOrderedGreedyChain r) :=
  GreedyChain.isMaxChain r WellOrderingRel id Function.surjective_id


end
