module

public import Topology_Munkres_2000.Book.Theorem_29_1
public import Topology_Munkres_2000.Book.Definition_29_2

public section

universe u v w

namespace Compactification

/-- Helper for Theorem 29.3: `of` has the same range as its supplied embedding. -/
lemma range_of {X : Type u} [TopologicalSpace X]
    (Y : Type v) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (i : X → Y) (hi : IsDenseEmbedding i) :
    Set.range (of Y i hi) = Set.range i := by
  -- Reduce range membership to the pointwise computation rule for `of`.
  ext y
  simp only [Set.mem_range, of_apply]
  rfl

/-- Helper for Theorem 29.3: a compact source has full image in every compactification. -/
lemma range_eq_univ_of_compact {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (C : Compactification.{u, v} X) : Set.range C = Set.univ := by
  -- Compactness makes the range closed in the Hausdorff target.
  have hClosed : IsClosed (Set.range C) :=
    (isCompact_range C.isDenseEmbedding.continuous).isClosed
  -- A closed dense range is the whole compactification.
  calc
    Set.range C = closure (Set.range C) := hClosed.closure_eq.symm
    _ = Set.univ := C.isDenseEmbedding.dense.closure_range

/-- Helper for Theorem 29.3: the source of a one-point compactification is noncompact. -/
lemma IsOnePoint.noncompactSpace {X : Type u} [TopologicalSpace X]
    {C : Compactification.{u, v} X} (hC : C.IsOnePoint) : NoncompactSpace X := by
  -- If the source were compact, density would force the compactification map to be surjective.
  rw [← not_compactSpace_iff]
  intro hCompact
  letI : CompactSpace X := hCompact
  -- This contradicts the properness forced by the omitted point.
  exact hC.isProper (range_eq_univ_of_compact C)

/-- Theorem 29.3 (1): A space has a one-point compactification exactly when it is weakly
locally compact, Hausdorff, and noncompact. -/
theorem existsOnePoint_iff {X : Type u} [TopologicalSpace X] :
    (∃ C : Compactification.{u, u} X, C.IsOnePoint) ↔
      WeaklyLocallyCompactSpace X ∧ T2Space X ∧ NoncompactSpace X := by
  constructor
  · rintro ⟨C, hC⟩
    -- The omitted point puts the compactification in the form characterized by Theorem 29.1.
    obtain ⟨y, hy⟩ := (isOnePoint_iff C).mp hC
    have hLocalHausdorff : WeaklyLocallyCompactSpace X ∧ T2Space X :=
      OnePoint.existsCompactification_iff.mpr
        ⟨C.toCompHaus, C, y, C.isDenseEmbedding.isEmbedding, hy⟩
    -- Proper density supplies the remaining noncompactness conjunct.
    exact ⟨hLocalHausdorff.1, hLocalHausdorff.2, hC.noncompactSpace⟩
  · rintro ⟨hLocal, hHausdorff, hNoncompact⟩
    -- Install the hypotheses needed by the canonical one-point construction.
    letI : WeaklyLocallyCompactSpace X := hLocal
    letI : T2Space X := hHausdorff
    letI : NoncompactSpace X := hNoncompact
    let C : Compactification.{u, u} X :=
      of (OnePoint X) ((↑) : X → OnePoint X) OnePoint.isDenseEmbedding_coe
    refine ⟨C, ?_⟩
    -- The canonical embedding omits exactly the point at infinity.
    dsimp only [C]
    unfold IsOnePoint
    refine ⟨(OnePoint.infty : OnePoint X), ?_⟩
    rw [range_of]
    exact OnePoint.compl_range_coe

/-- Theorem 29.3 (2): Any two one-point compactifications are equivalent by a homeomorphism
that agrees with their embeddings of the original space. -/
theorem IsOnePoint.equivalent {X : Type u} [TopologicalSpace X]
    {C : Compactification.{u, v} X} {D : Compactification.{u, w} X}
    (hC : C.IsOnePoint) (hD : D.IsOnePoint) :
    ∃ e : C ≃ₜ D, ∀ x, e (C x) = D x := by
  -- Present both compactifications as compact Hausdorff extensions omitting one point.
  obtain ⟨y, hy⟩ := (isOnePoint_iff C).mp hC
  obtain ⟨z, hz⟩ := (isOnePoint_iff D).mp hD
  let e : C ≃ₜ D :=
    OnePoint.compactificationEquiv C.toCompHaus D.toCompHaus C D y z
      C.isDenseEmbedding.isEmbedding D.isDenseEmbedding.isEmbedding hy hz
  refine ⟨e, ?_⟩
  -- The canonical equivalence agrees with both embeddings on every source point.
  intro x
  exact OnePoint.compactificationEquiv_apply C.toCompHaus D.toCompHaus C D y z
    C.isDenseEmbedding.isEmbedding D.isDenseEmbedding.isEmbedding hy hz x

end Compactification
