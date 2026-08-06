import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {X : Type u} [TopologicalSpace X]

-- `lean_leansearch` returned HTTP 500 here, so the owner/API choice was verified directly against
-- local mathlib: May's `k`-spaces use `UCompactlyGeneratedSpace`, while the proof below reuses
-- `uCompactlyGeneratedSpace_of_isClosed` and the canonical closed-subtype map API.

/-- Problem 5.3.2: every closed subspace of a `k`-space is a `k`-space. -/
instance Subtype.uCompactlyGeneratedSpace [UCompactlyGeneratedSpace.{v} X]
    {s : Set X} (hs : IsClosed s) : UCompactlyGeneratedSpace.{v} s := by
  refine uCompactlyGeneratedSpace_of_isClosed fun t ht ↦ ?_
  refine hs.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.2 <|
    UCompactlyGeneratedSpace.isClosed fun K g ↦ ?_
  let A : Set K := g ⁻¹' s
  have hA : IsClosed A := hs.preimage g.continuous
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA.isCompact
  let g' : C(A, s) :=
    ⟨fun x : A ↦ ⟨g x, x.2⟩,
      (g.continuous.comp continuous_subtype_val).subtype_mk fun x : A ↦ x.2⟩
  have hclosed : IsClosed (g' ⁻¹' t) := ht (CompHaus.of A) g'
  have himage : IsClosed (((↑) : A → K) '' (g' ⁻¹' t)) :=
    hA.isClosedMap_subtype_val _ hclosed
  suffices ((↑) : A → K) '' (g' ⁻¹' t) = g ⁻¹' ((↑) '' (t : Set s)) by
    simpa [this] using himage
  ext x
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨g' x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have hxA : x ∈ A := by
      change g x ∈ s
      simpa [hyx] using y.2
    refine ⟨⟨x, hxA⟩, ?_, rfl⟩
    change (⟨g x, hxA⟩ : s) ∈ t
    have hxy : (⟨g x, hxA⟩ : s) = y := by
      apply Subtype.ext
      simp [hyx]
    simpa [hxy] using hy
