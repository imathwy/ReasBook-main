module

public import Topology_Munkres_2000.Book.Proposition_38_1.StoneCech

@[expose] public section

universe u

namespace Compactification

/-- Helper for Proposition 38.1: the source of a compactification is completely regular. -/
lemma t35Space {X : Type u} [TopologicalSpace X] (C : Compactification.{u, u} X) : T35Space X := by
  -- Pull complete regularity back from the compact Hausdorff target along the stored embedding.
  exact C.isDenseEmbedding.isEmbedding.t35Space

end Compactification

/-- Proposition 38.1: A space has a compact Hausdorff compactification if and only if it is
completely regular in Munkres's sense. -/
theorem t35Space_iff_nonempty_compactification (X : Type u) [TopologicalSpace X] :
    T35Space X ↔ Nonempty (Compactification.{u, u} X) := by
  constructor
  · intro hX
    -- Use complete regularity to form the canonical Stone–Čech compactification.
    letI : T35Space X := hX
    exact ⟨Compactification.stoneCech X⟩
  · rintro ⟨C⟩
    -- Apply the compactification interface lemma to the chosen witness.
    exact C.t35Space
