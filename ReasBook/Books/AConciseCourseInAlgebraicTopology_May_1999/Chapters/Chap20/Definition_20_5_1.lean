import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Topology.Sets.Compacts
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.SubsetPair
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_1_1

open CategoryTheory Limits
open SpacePair

universe u

-- Semantic recall via `lean_leansearch` did not surface a separate compact-support owner beyond
-- the existing relative pair-cohomology surface. Local Chapter 14/18 precedent already fixes the
-- canonical pair object `subsetPair` and the graded contravariant owner `PairCohomologyTheory`,
-- so compactly supported cohomology is recorded directly as a colimit of those relative groups.

/-- The compact-subset pair diagram `K ↦ (M, M \ K)` valued in `SpacePairᵒᵖ`. -/
def compactlySupportedPairDiagram (M : TopCat.{u}) :
    TopologicalSpace.Compacts M ⥤ SpacePair.{u}ᵒᵖ where
  obj K := Opposite.op (subsetPair M ((K : Set M)ᶜ))
  map {K L} h :=
    (subsetPairInclusion (Set.compl_subset_compl.mpr h.le)).op
  map_id := by
    intro K
    exact
      congrArg (fun f ↦ f.op)
        (subsetPairInclusion_rfl ((K : Set M)ᶜ))
  map_comp := by
    intro K L N hKL hLN
    exact
      congrArg (fun f ↦ f.op)
        (subsetPairInclusion_comp
          (Set.compl_subset_compl.mpr hKL.le)
          (Set.compl_subset_compl.mpr hLN.le))

/-- Evaluating `compactlySupportedPairDiagram M` at `K` gives the opposite of the pair
`(M, M \ K)`. -/
theorem compactlySupportedPairDiagram_obj
    (M : TopCat.{u}) (K : TopologicalSpace.Compacts M) :
    (compactlySupportedPairDiagram M).obj K =
      Opposite.op (subsetPair M ((K : Set M)ᶜ)) := rfl

/-- On a morphism `h : K ⟶ L`, `compactlySupportedPairDiagram M` uses the pair map induced by the
inclusion `(L : Set M)ᶜ ⊆ (K : Set M)ᶜ`. -/
@[simp] theorem compactlySupportedPairDiagram_map
    (M : TopCat.{u}) {K L : TopologicalSpace.Compacts M} (h : K ⟶ L) :
    (compactlySupportedPairDiagram M).map h =
      (subsetPairInclusion (Set.compl_subset_compl.mpr h.le)).op := rfl

/-- The compact-subset diagram `K ↦ H^p(M, M \ K)` attached to a pair cohomology theory `H`. -/
abbrev compactlySupportedCohomologyDiagram
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (M : TopCat.{u}) (p : ℤ) :
    TopologicalSpace.Compacts M ⥤ AddCommGrpCat.{u} :=
  compactlySupportedPairDiagram M ⋙ H.cohomology p

/-- Evaluating `compactlySupportedCohomologyDiagram H M p` at `K` recovers
`H^p(M, M \ K)`. -/
theorem compactlySupportedCohomologyDiagram_obj
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (M : TopCat.{u}) (p : ℤ) (K : TopologicalSpace.Compacts M) :
    (compactlySupportedCohomologyDiagram H M p).obj K =
      (H.cohomology p).obj (Opposite.op (subsetPair M ((K : Set M)ᶜ))) := rfl

/-- On a morphism `h : K ⟶ L`, `compactlySupportedCohomologyDiagram H M p` uses the
inclusion-induced map attached to `(L : Set M)ᶜ ⊆ (K : Set M)ᶜ`. -/
@[simp] theorem compactlySupportedCohomologyDiagram_map
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (M : TopCat.{u}) (p : ℤ)
    {K L : TopologicalSpace.Compacts M} (h : K ⟶ L) :
    (compactlySupportedCohomologyDiagram H M p).map h =
      (H.cohomology p).map
        (subsetPairInclusion (Set.compl_subset_compl.mpr h.le)).op := rfl

/-- Definition 20.5.1. For a pair cohomology theory `H^*(-; π)`, compactly supported
cohomology `H_c^p(M)` is the colimit of the relative groups `H^p(M, M \ K; π)` over compact
subsets `K ⊂ M`. -/
noncomputable def compactlySupportedCohomology
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (M : TopCat.{u}) (p : ℤ) : AddCommGrpCat.{u} :=
  colimit (compactlySupportedCohomologyDiagram H M p)

/- The source-facing notation `H_c^p(M; π)` depends in Lean on the chosen pair cohomology theory
`H : PairCohomologyTheory π`, so the notation records that theory in the final slot. -/
notation3 "H_c^" p "(" M "; " H ")" => compactlySupportedCohomology H M p

/-- Unfolding `H_c^p(M; H)` identifies it with the colimit of its compact-subset diagram. -/
theorem compactlySupportedCohomology_def
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (M : TopCat.{u}) (p : ℤ) :
    H_c^p(M; H) =
      colimit (compactlySupportedCohomologyDiagram H M p) := rfl
