module

public import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Constructions

public section

universe u

/-- Theorem 17.2: A set in a subspace is closed if and only if its image is the
intersection of the subspace with a closed set of the ambient space. -/
theorem isClosed_iff_exists_closed_image_eq_inter {X : Type u} [TopologicalSpace X]
    (Y : Set X) (A : Set Y) :
    IsClosed A ↔ ∃ C : Set X, IsClosed C ∧ Subtype.val '' A = C ∩ Y := by
  constructor
  · exact IsClosed.image_val
  · rintro ⟨C, hC, hA⟩
    have hpreimage : A = Subtype.val ⁻¹' C := by
      apply Subtype.val_injective.image_injective
      simpa [Set.inter_comm] using hA
    rw [hpreimage]
    exact hC.preimage_val
