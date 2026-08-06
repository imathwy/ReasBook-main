import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Remark_5_1_5

universe u

open Set
open scoped Set.Notation

-- Semantic recall: `↓∩`, `IsClosed.preimage_val`, and `IsClosed.inter_preimage_val_iff`
-- bridge subspace-closedness with ambient intersections once compact subsets are known to be
-- closed.

/-- In a weak Hausdorff space, every compact subset is closed. -/
theorem IsCompact.isClosed_of_weaklyHausdorff
    {X : Type u} [TopologicalSpace X] [WeaklyHausdorffSpace.{u, u} X] {K : Set X}
    (hK : IsCompact K) : IsClosed K := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let _ : WeaklyHausdorffSpace.{u, u} K := Subtype.weaklyHausdorffSpace
  let _ : T2Space K := CompactSpace.toT2Space_of_weaklyHausdorffSpace K
  have hClosedRange : IsClosed (Set.range (Subtype.val : K → X)) :=
    Continuous.isClosed_range continuous_subtype_val
  simpa using hClosedRange

/-- Lemma 5.1.8: when `X` is weak Hausdorff, a subset `A` is compactly closed if and only if,
for each compact subset `K` of `X`, the intersection `A ∩ K` is closed in the subspace `K`. -/
theorem isCompactlyClosed_iff_forall_isCompact_isClosed_subspace
    {X : Type u} [TopologicalSpace X] [WeaklyHausdorffSpace.{u, u} X] {A : Set X} :
    IsCompactlyClosed.{u, u} A ↔
      ∀ K : Set X, IsCompact K → IsClosed (K ↓∩ A) := by
  constructor
  · intro hA K hK
    let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
    simpa using hA.isClosed_preimage (Subtype.val : K → X) continuous_subtype_val
  · intro hA K _ _ g
    have hRange : IsCompact (Set.range g) := isCompact_range g.continuous
    let g' : K → Set.range g := fun x ↦ ⟨g x, ⟨x, rfl⟩⟩
    have hg' : Continuous g' := g.continuous.subtype_mk (fun x ↦ ⟨x, rfl⟩)
    have hClosed : IsClosed (Set.range g ↓∩ A) := hA _ hRange
    simpa [g'] using hClosed.preimage hg'

/-- In a weak Hausdorff space, a subset is compactly closed exactly when its intersections with
compact subsets are closed in the ambient space. -/
theorem isCompactlyClosed_iff_forall_isCompact_isClosed_inter
    {X : Type u} [TopologicalSpace X] [WeaklyHausdorffSpace.{u, u} X] {A : Set X} :
    IsCompactlyClosed.{u, u} A ↔ ∀ K : Set X, IsCompact K → IsClosed (A ∩ K) := by
  rw [isCompactlyClosed_iff_forall_isCompact_isClosed_subspace]
  constructor
  · intro h K hK
    have hKA : IsClosed (K ∩ A) :=
      (IsClosed.inter_preimage_val_iff hK.isClosed_of_weaklyHausdorff).mp (h K hK)
    simpa [inter_comm] using hKA
  · intro h K hK
    have hKA : IsClosed (K ∩ A) := by
      simpa [inter_comm] using h K hK
    exact (IsClosed.inter_preimage_val_iff hK.isClosed_of_weaklyHausdorff).mpr hKA
