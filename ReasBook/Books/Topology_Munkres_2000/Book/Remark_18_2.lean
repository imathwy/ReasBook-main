module

public import Topology_Munkres_2000.Book.Remark_18_2.Pasting

public section

universe u v

/-- Remark 18.2. The open-set form of the pasting lemma: continuous maps on two open
sets that cover the space and agree on their intersection extend to the whole space. -/
theorem existsContinuousMap_of_isOpen_cover
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (f : ContinuousMap A Y) (g : ContinuousMap B Y)
    (hfg : ∀ x : (A ∩ B : Set X), f ⟨x, x.property.1⟩ = g ⟨x, x.property.2⟩) :
    ∃ h : ContinuousMap X Y, (∀ x : A, h x = f x) ∧ ∀ x : B, h x = g x := by
  refine ⟨ContinuousMap.pasteOpen hA hB hcover f g hfg, ?_, ?_⟩
  · intro x
    have hx := DFunLike.congr_fun (ContinuousMap.pasteOpen_restrict_left hA hB hcover f g hfg) x
    exact hx
  · intro x
    have hx := DFunLike.congr_fun (ContinuousMap.pasteOpen_restrict_right hA hB hcover f g hfg) x
    exact hx
