import Mathlib.Topology.Maps.Proper.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-- Definition 5.28-extra-2: A subset `S ⊆ M` is properly embedded when its inclusion into the
ambient space is a proper map. For an embedded submanifold, this is Lee's notion of proper
embedding. -/
abbrev Set.IsProperlyEmbedded {M : Type u} [TopologicalSpace M] (S : Set M) : Prop :=
  IsProperMap ((↑) : S → M)

/-- Closed subsets are properly embedded. -/
-- Proof sketch: use the existing theorem `IsClosed.isProperMap_subtypeVal` for the subtype
-- inclusion and then unfold `Set.IsProperlyEmbedded`.
theorem IsClosed.isProperlyEmbedded {M : Type u} [TopologicalSpace M] {S : Set M}
    (hS : IsClosed S) : S.IsProperlyEmbedded :=
  hS.isProperMap_subtypeVal

/-- A properly embedded subset of a `T₁` space is closed. -/
theorem Set.IsProperlyEmbedded.isClosed {M : Type u} [TopologicalSpace M] [T1Space M]
    {S : Set M} (hS : S.IsProperlyEmbedded) : IsClosed S := by
  simpa using (hS.isClosed_range : IsClosed (Set.range ((↑) : S → M)))

/-- A subset of a `T₁` space is properly embedded exactly when it is closed. -/
theorem Set.isProperlyEmbedded_iff_isClosed {M : Type u} [TopologicalSpace M] [T1Space M]
    {S : Set M} : S.IsProperlyEmbedded ↔ IsClosed S :=
  ⟨Set.IsProperlyEmbedded.isClosed, IsClosed.isProperlyEmbedded⟩
