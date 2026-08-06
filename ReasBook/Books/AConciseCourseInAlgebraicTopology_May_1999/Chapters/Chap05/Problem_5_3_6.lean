import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Proposition_5_1_16

universe u

-- Semantic search hit: `TopologicalSpace.compactlyGenerated`; local Chapter 5 precedent uses this
-- as the canonical owner for k-ification, while `Subtype.weaklyHausdorffSpace` and
-- `instCompactlyGeneratedWeakHausdorffSpaceCompactlyGenerated` show that the k-ification of an
-- arbitrary subtype of a compactly generated weak Hausdorff space is again compactly generated
-- weak Hausdorff.

section

variable {X : Type u} [TopologicalSpace X]

/-- Problem 5.3.6. For an arbitrary subset `s ⊆ X` of a compactly generated space `X`, the
subspace that should be used is the subset carrier `s` equipped with the compactly generated
replacement of its ordinary subtype topology. -/
abbrev compactlyGeneratedSubspaceTopology (s : Set X) : TopologicalSpace s :=
  TopologicalSpace.compactlyGenerated.{u, u} s

/-- The compactly generated subspace on `s` uses the same carrier as the subtype `s`, but its
default topology is `compactlyGeneratedSubspaceTopology s`. -/
def compactlyGeneratedSubspace (s : Set X) : Type u := s

/-- The compactly generated subspace carries the k-ification of the ordinary subtype topology. -/
instance instTopologicalSpaceCompactlyGeneratedSubspace (s : Set X) :
    TopologicalSpace (compactlyGeneratedSubspace s) :=
  compactlyGeneratedSubspaceTopology s

/-- The compactly generated subspace topology is the k-ification of the ordinary subtype
topology on `s`. -/
@[simp]
theorem compactlyGeneratedSubspaceTopology_def (s : Set X) :
    compactlyGeneratedSubspaceTopology s = TopologicalSpace.compactlyGenerated.{u, u} s := rfl

/-- If `X` is compactly generated in the textbook sense, then every subset `s ⊆ X` becomes
compactly generated in the same sense when equipped with
`compactlyGeneratedSubspaceTopology s`. -/
instance instCompactlyGeneratedWeakHausdorffSpaceCompactlyGeneratedSubspace
    [CompactlyGeneratedWeakHausdorffSpace.{u, u} X] (s : Set X) :
    CompactlyGeneratedWeakHausdorffSpace.{u, u} (compactlyGeneratedSubspace s) := by
  -- Recover the ambient weak Hausdorff structure carried by the textbook package.
  let _ : WeaklyHausdorffSpace.{u, u} X := inferInstance
  -- The ordinary subtype of a weak Hausdorff space is weak Hausdorff.
  let _ : WeaklyHausdorffSpace.{u, u} s := Subtype.weaklyHausdorffSpace
  -- Route correction: rewrite once to the canonical k-ification owner before packaging the
  -- weak Hausdorff and compact-generation components explicitly.
  change @CompactlyGeneratedWeakHausdorffSpace.{u, u} s (compactlyGeneratedSubspaceTopology s)
  rw [compactlyGeneratedSubspaceTopology_def]
  refine
    @CompactlyGeneratedWeakHausdorffSpace.mk.{u, u} s
      (TopologicalSpace.compactlyGenerated.{u, u} s)
      (instWeaklyHausdorffSpaceCompactlyGenerated (X := s) (t := inferInstance))
      (instUCompactlyGeneratedSpaceCompactlyGenerated (X := s))

end
