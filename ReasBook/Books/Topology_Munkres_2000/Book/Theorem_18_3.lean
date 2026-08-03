module

public import Topology_Munkres_2000.Book.Theorem_18_3.Pasting

public section

universe u v

/-- Theorem 18.3 (The pasting lemma). Continuous maps on two closed sets that cover the
space and agree on their intersection extend to a continuous map on the whole space. -/
theorem existsContinuousMap_of_isClosed_cover
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hcover : A ∪ B = Set.univ)
    (f : ContinuousMap A Y) (g : ContinuousMap B Y)
    (hfg : ∀ x : (A ∩ B : Set X), f ⟨x, x.property.1⟩ = g ⟨x, x.property.2⟩) :
    ∃ h : ContinuousMap X Y, (∀ x : A, h x = f x) ∧ ∀ x : B, h x = g x := by
  exact ⟨ContinuousMap.pasteClosed hA hB hcover f g hfg, by simp⟩
