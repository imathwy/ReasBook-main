import Mathlib.Topology.Homotopy.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_1_6

universe u

-- Semantic recall via `lean_leansearch`: `ContinuousMap.HomotopicRel` is the canonical owner for
-- homotopy relative to a subspace. Local Chapter 10 precedent already formalizes pair maps by
-- `SpacePair.Hom` and relative cellularity by `IsCellularMap` on `relativeSpacePair`.

namespace Topology.RelCWComplex

/-- Theorem 10.4.5: any map `f : (X, A) ⟶ (Y, B)` between relative CW complexes is homotopic
relative to `A` to a cellular map. The map of pairs is formalized as a `SpacePair.Hom` between
the canonical relative pairs `relativeSpacePair (Set.univ : Set X) A` and
`relativeSpacePair (Set.univ : Set Y) B`; the homotopy is recorded on the underlying continuous
maps relative to the distinguished source subspace. -/
theorem exists_relativeCellularApproximation
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y)
    [RelCWComplex (Set.univ : Set X) A]
    [RelCWComplex (Set.univ : Set Y) B]
    (f :
      relativeSpacePair (Set.univ : Set X) A ⟶
        relativeSpacePair (Set.univ : Set Y) B) :
      ∃ g :
        relativeSpacePair (Set.univ : Set X) A ⟶
          relativeSpacePair (Set.univ : Set Y) B,
      IsCellularMap g ∧
        ContinuousMap.HomotopicRel f.hom.hom g.hom.hom
          (relativeSpacePair (Set.univ : Set X) A).subspace := sorry

end Topology.RelCWComplex
