import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.RelativeHelp
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Theorem_10_3_1

universe u v w

open Set
open scoped Topology.Homotopy

-- Semantic recall via `lean_leansearch`: `Topology.RelCWComplex.skeleton_top` exposes the
-- `⊤`-skeleton as the whole relative CW complex, so the source remark is best recorded as the
-- weak-equivalence form of Theorem 10.3.1 rather than as a separate colimit wrapper.

variable {W : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace W] [TopologicalSpace Y] [TopologicalSpace Z] [T2Space W]

/-- Remark 10.3.3: HELP may be used with `n = ∞` by passing to colimits over the finite skeleta.
In the project API, this is recorded as the statement that a weak equivalence has the relative
HELP with respect to the base inclusion of any relative CW complex. -/
theorem relCWComplexBaseInclusion_hasRelativeHelp_of_isWeakEquivalence
    {X A : Set W} [Topology.RelCWComplex X A] (e : C(Y, Z)) [IsWeakEquivalence e] :
    HasRelativeHelp (relCWComplexBaseInclusion X) e := by
  sorry

/-- Source-facing existential form of Remark 10.3.3: if `(X, A)` is a relative CW complex and
`e : C(Y, Z)` is a weak equivalence, then any compatible maps `A → Y` and `X → Z` admit an
extension `X → Y` whose composite with `e` is homotopic to the given map rel `A`. -/
theorem exists_extensionLift_of_relCWComplex_of_isWeakEquivalence
    {X A : Set W} [Topology.RelCWComplex X A] (e : C(Y, Z)) [IsWeakEquivalence e]
    (fA : C(A, Y)) (fX : C(X, Z))
    (h_compat : e.comp fA = fX.comp (relCWComplexBaseInclusion X)) :
    ∃ (F : C(X, Y)) (_ : (e.comp F).HomotopyRel fX (range (relCWComplexBaseInclusion X))),
      F.comp (relCWComplexBaseInclusion X) = fA :=
  relCWComplexBaseInclusion_hasRelativeHelp_of_isWeakEquivalence e fA fX h_compat
