import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set Submodule

universe u v

/-- Theorem 1.4.20: if `G` spans `V` and `L ⊆ G` is linearly independent, then there exists a
basis of `V` containing `L` and contained in `G`. -/
-- Proof sketch: use the canonical basis-extension owner `Module.Basis.extendLe` as the witness;
-- the two containment statements are exactly `Module.Basis.subset_extendLe` and
-- `Module.Basis.extendLe_subset`.
theorem exists_basis_between_of_linearIndepOn_of_span_eq_top
    {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]
    {L G : Set V} (hL : LinearIndepOn K id L) (hLG : L ⊆ G) (hG : span K G = ⊤) :
    ∃ (ι : Type v) (b : Module.Basis ι K V), L ⊆ Set.range b ∧ Set.range b ⊆ G := by
  refine ⟨hL.extend hLG, Module.Basis.extendLe hL hLG hG.ge, ?_, ?_⟩
  · exact Module.Basis.subset_extendLe hL hLG hG.ge
  · exact Module.Basis.extendLe_subset hL hLG hG.ge
