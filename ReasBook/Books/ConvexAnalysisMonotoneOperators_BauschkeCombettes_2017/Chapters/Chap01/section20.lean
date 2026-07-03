import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_1_20 (from Chap01) -/
universe u v

/-- Lemma 1.20: if `X` and `Y` are Hausdorff spaces, `T : X → Y` is continuous, and `C ⊆ X` is
compact, then `T(C)` is compact. This is the textbook Hausdorff-space specialization of the
canonical theorem `IsCompact.image`. -/
theorem lemma_1_20
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]
    {C : Set X} {T : X → Y} (hC : IsCompact C) (hT : Continuous T) :
    IsCompact (T '' C) :=
  hC.image hT
