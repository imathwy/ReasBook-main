module

public import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.FundamentalGroupoidOpenCover

public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory
open scoped FundamentalGroupoid

variable {X : Type u} [TopologicalSpace X]

/-- ProofStep 2.7.4: inside one open set `U`, endpoint-fixed homotopic paths define the same
morphism in the fundamental groupoid `Π(U)`. This is the local relation used in the van Kampen
subdivision argument before applying any cocone leg or other functor out of `Π(U)`. -/
-- Proof sketch: `Π(U)` is defined by quotienting paths by endpoint-fixed homotopy, and
-- `FundamentalGroupoid.fromPath` sends homotopic representatives to the same morphism.
theorem fromPath_eq_of_homotopic_paths_in_open
    (U : TopologicalSpace.Opens X)
    {x y : U} {p q : Path x y}
    (h : Path.Homotopic p q) :
    FundamentalGroupoid.fromPath ⟦p⟧ = FundamentalGroupoid.fromPath ⟦q⟧ := by
  simpa using (FundamentalGroupoid.fromPath_eq_iff_homotopic p q).2 h

namespace CategoryTheory.Functor

/-- ProofStep 2.7.4 companion: any functor out of `Π(U)` identifies endpoint-fixed homotopic
paths in `U`. -/
-- Proof sketch: apply `F.map` to the equality in `Π(U)` provided by
-- `fromPath_eq_of_homotopic_paths_in_open`.
theorem map_eq_of_homotopic_paths_in_open
    {C : Type v} [Category C]
    {U : TopologicalSpace.Opens X}
    (F : πₓ (TopCat.of U) ⥤ C)
    {x y : U} {p q : Path x y}
    (h : Path.Homotopic p q) :
    F.map (FundamentalGroupoid.fromPath ⟦p⟧) =
      F.map (FundamentalGroupoid.fromPath ⟦q⟧) := by
  simpa using congrArg F.map (fromPath_eq_of_homotopic_paths_in_open U h)

end CategoryTheory.Functor
