module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Topology.Sets.OpenCover

universe u v

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace.Opens
open scoped FundamentalGroupoid

noncomputable section

variable {ι : Type v} {X : Type u} [TopologicalSpace X]

namespace TopologicalSpace.IsOpenCover

/-- An indexed open cover is closed under nonempty finite intersections when every nonempty finite
intersection of members of the cover is itself another member of the cover. -/
public def ClosedUnderNonemptyFiniteIntersections
    (O : ι → TopologicalSpace.Opens X) : Prop :=
  ∀ s : Finset ι, ∀ hs : s.Nonempty, ∃ i, s.inf' hs O = O i

/-- The index category of an indexed open cover, whose morphisms are inclusions between cover
members. -/
public abbrev Index (O : ι → TopologicalSpace.Opens X) :=
  InducedCategory (TopologicalSpace.Opens X) O

end TopologicalSpace.IsOpenCover

/-- The diagram sending each member of an open cover to its fundamental groupoid. -/
public abbrev fundamental_groupoid_cover_diagram
    (O : ι → TopologicalSpace.Opens X) :
    TopologicalSpace.IsOpenCover.Index O ⥤ Grpd :=
  inducedFunctor O ⋙ toTopCat (TopCat.of X) ⋙ π

/-- The canonical inclusion of a cover member into the ambient topological space. -/
@[expose] public abbrev openCoverInclusion (U : TopologicalSpace.Opens X) :
    (toTopCat (TopCat.of X)).obj U ⟶ TopCat.of X :=
  let U' : TopologicalSpace.Opens (TopCat.of X) := U
  TopologicalSpace.Opens.inclusion' U'

/-- Naturality of the canonical inclusion functors from the fundamental groupoids of cover
elements into the fundamental groupoid of the ambient space. -/
public theorem fundamental_groupoid_cover_cocone_naturality
    (O : ι → TopologicalSpace.Opens X)
    {i j : TopologicalSpace.IsOpenCover.Index O} (f : i ⟶ j) :
    (fundamental_groupoid_cover_diagram O).map f ≫
        πₘ (openCoverInclusion (O j)) =
      πₘ (openCoverInclusion (O i)) := by
  have hcomp :
      ((toTopCat (TopCat.of X)).map f.hom) ≫ openCoverInclusion (O j) =
        openCoverInclusion (O i) := by
    ext x
    cases x
    rfl
  change
    πₘ ((toTopCat (TopCat.of X)).map f.hom) ≫ πₘ (openCoverInclusion (O j)) =
      πₘ (openCoverInclusion (O i))
  simpa [FundamentalGroupoid.map_comp] using congrArg πₘ hcomp

namespace TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections

/-- Closure under nonempty finite intersections produces a cover member realizing any chosen
nonempty finite intersection. -/
public theorem exists_eq_inf_finset
    {O : ι → TopologicalSpace.Opens X}
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (s : Finset ι) (hs : s.Nonempty) :
    ∃ i, s.inf' hs O = O i := by
  simpa [TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections] using hinter s hs

/-- Closure under nonempty finite intersections produces a cover member realizing the binary
overlap of two chosen opens. -/
public theorem exists_eq_inf
    {O : ι → TopologicalSpace.Opens X}
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (i j : ι) :
    ∃ k, O k = O i ⊓ O j := by
  classical
  obtain ⟨k, hk⟩ := exists_eq_inf_finset hinter ({i, j} : Finset ι) (by simp)
  refine ⟨k, ?_⟩
  simpa [Finset.inf'_insert, Finset.inf'_singleton] using hk.symm

end TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections

/-- The canonical cocone from the fundamental groupoids of the members of an open cover to the
fundamental groupoid of the ambient space. -/
@[expose] public def fundamental_groupoid_cover_cocone
    (O : ι → TopologicalSpace.Opens X) :
    Cocone (fundamental_groupoid_cover_diagram O) where
  pt := πₓ (TopCat.of X)
  ι :=
    { app := fun i ↦ πₘ (openCoverInclusion (O i))
      naturality := fun _ _ f ↦ fundamental_groupoid_cover_cocone_naturality O f }
