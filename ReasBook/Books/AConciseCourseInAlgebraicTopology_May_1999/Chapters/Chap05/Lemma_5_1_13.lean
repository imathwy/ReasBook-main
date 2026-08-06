import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_9

universe u v w

-- Semantic recall: `continuous_from_uCompactlyGeneratedSpace` is the canonical k-space owner.
-- This source-facing compact-subspace reformulation only uses the `UCompactlyGeneratedSpace`
-- part of Definition 5.1.10, so the public API is stated at that more canonical level.

/-- In a `UCompactlyGeneratedSpace`, continuity can be checked on every compact subspace. -/
theorem continuous_of_forall_isCompact_continuous_subspace
    {X : Type u} [TopologicalSpace X] [UCompactlyGeneratedSpace.{v} X]
    {Y : Type w} [TopologicalSpace Y] (f : X → Y)
    (hf : ∀ K : Set X, IsCompact K → Continuous (fun x : K ↦ f x)) :
    Continuous f := by
  refine continuous_from_uCompactlyGeneratedSpace f ?_
  intro S g
  let gRange : S → Set.range g := fun s ↦ ⟨g s, ⟨s, rfl⟩⟩
  have hgRange : Continuous gRange :=
    Continuous.subtype_mk g.continuous fun _ ↦ ⟨_, rfl⟩
  simpa [Function.comp, gRange] using (hf (Set.range g) (isCompact_range g.continuous)).comp hgRange

/-- Lemma 5.1.13: if `X` is compactly generated and `Y` is any space, then a function
`f : X → Y` is continuous if and only if, for each compact subset `K` of `X`, the restriction
`fun x : K ↦ f x` is continuous. -/
theorem continuous_iff_forall_isCompact_continuous_subspace
    {X : Type u} [TopologicalSpace X] [UCompactlyGeneratedSpace.{v} X]
    {Y : Type w} [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔
      ∀ K : Set X, IsCompact K → Continuous (fun x : K ↦ f x) := by
  constructor
  · intro hf K hK
    exact hf.comp continuous_subtype_val
  · exact continuous_of_forall_isCompact_continuous_subspace f
