module

public import Topology_Munkres_2000.Book.Definition_6_0_2.SigmaLocallyFiniteFamily

public section

open Set

universe u

/-- Definition 6.0.2: A space has a sigma-locally finite basis if some topological
basis is a sigma-locally finite family. -/
def HasSigmaLocallyFiniteBasis (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ 𝓑 : Set (Set X),
    TopologicalSpace.IsTopologicalBasis 𝓑 ∧
      SigmaLocallyFinite (Subtype.val : 𝓑 → Set X)

/-- Companion to Definition 6.0.2: a space has a sigma-locally finite basis exactly when
it has a basis that is a countable union of locally finite subcollections. -/
theorem hasSigmaLocallyFiniteBasis_iff (X : Type u) [TopologicalSpace X] :
    HasSigmaLocallyFiniteBasis X ↔
      ∃ 𝓑 : Set (Set X), ∃ pieces : ℕ → Set (Set X),
        TopologicalSpace.IsTopologicalBasis 𝓑 ∧
          𝓑 = ⋃ n, pieces n ∧
            ∀ n, (pieces n).LocallyFinite := by
  constructor
  · rintro ⟨𝓑, hbasis, hsigma⟩
    -- Replace sigma-local finiteness by its countable-union presentation.
    rcases sigmaLocallyFinite_subtype_iff.mp hsigma with ⟨pieces, hcover, hfinite⟩
    exact ⟨𝓑, pieces, hbasis, hcover, hfinite⟩
  · rintro ⟨𝓑, pieces, hbasis, hcover, hfinite⟩
    -- Assemble the abstract basis condition from the concrete locally finite pieces.
    refine ⟨𝓑, hbasis, ?_⟩
    exact sigmaLocallyFinite_subtype_iff.mpr ⟨pieces, hcover, hfinite⟩
