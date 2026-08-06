import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.RelativeHelp
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_7_3

universe u v w

open Set

-- Semantic recall via `lean_leansearch`: the closest hits were covering-space and path-lifting
-- constructions, not a canonical owner for the relative HELP property used in this proof step.
-- The source is therefore recorded with an explicit relative-lifting predicate and the CW-triad
-- cover data `K_A ∪ K_B = K`.

variable {W : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace W] [TopologicalSpace Y] [TopologicalSpace Z]

namespace Set

/-- The inclusion `L ↪ W` of a subspace into the ambient space, with the codomain formalized as
`Set.univ`. -/
abbrev univInclusion (L : Set W) : C(L, (univ : Set W)) :=
  ContinuousMap.inclusion (by
    intro x hx
    simp)

end Set

namespace Triad

/-- The part of the boundary `L` lying in the common subspace `A ∩ B` of a triad `(W; A, B)`. -/
abbrev intersectionBoundary (T : Triad W) (L : Set W) : Set W :=
  L ∩ T.intersection

/-- The boundary data on `A` enlarged by the already-lifted overlap `A ∩ B`. -/
abbrev augmentedLeftBoundary (T : Triad W) (L : Set W) : Set W :=
  (L ∩ T.subspaceA) ∪ T.intersection

/-- The boundary data on `B` enlarged by the already-lifted overlap `A ∩ B`. -/
abbrev augmentedRightBoundary (T : Triad W) (L : Set W) : Set W :=
  (L ∩ T.subspaceB) ∪ T.intersection

/-- The inclusion of the boundary portion lying in `A ∩ B` into the overlap. -/
def intersectionBoundaryInclusion (T : Triad W) (L : Set W) :
    C(T.intersectionBoundary L, T.intersection) :=
  ContinuousMap.inclusion (by
    intro x hx
    exact hx.2)

/-- The inclusion of the enlarged boundary data into the left subspace `A`. -/
def augmentedLeftBoundaryInclusion (T : Triad W) (L : Set W) :
    C(T.augmentedLeftBoundary L, T.subspaceA) :=
  ContinuousMap.inclusion (by
    intro x hx
    rcases hx with hx | hx
    · exact hx.2
    · exact hx.1)

/-- The inclusion of the enlarged boundary data into the right subspace `B`. -/
def augmentedRightBoundaryInclusion (T : Triad W) (L : Set W) :
    C(T.augmentedRightBoundary L, T.subspaceB) :=
  ContinuousMap.inclusion (by
    intro x hx
    rcases hx with hx | hx
    · exact hx.2
    · exact hx.2)

end Triad

namespace CWTriad

/-- ProofStep 10.7.13: HELP first lifts on `K_A ∩ K_B`, then on `K_A` and `K_B` with that
overlap added to the boundary data, and thereby yields a global lift together with a homotopy
relative to the original boundary `L`. -/
theorem hasRelativeHelp_of_liftsOnIntersection_thenPieces
    (K : CWTriad W) (L : Set W) (e : C(Y, Z))
    (h_intersection : HasRelativeHelp (K.intersectionBoundaryInclusion L) e)
    (h_left : HasRelativeHelp (K.augmentedLeftBoundaryInclusion L) e)
    (h_right : HasRelativeHelp (K.augmentedRightBoundaryInclusion L) e) :
    HasRelativeHelp (Set.univInclusion L) e := sorry

end CWTriad
