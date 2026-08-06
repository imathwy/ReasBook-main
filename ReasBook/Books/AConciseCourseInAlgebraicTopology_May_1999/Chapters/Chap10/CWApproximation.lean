import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_2
import Mathlib.Topology.CWComplex.Abstract.Basic

open scoped ContinuousMap

universe u v

/-- A chosen CW approximation structure on `γ : C(Γ, X)` packages the canonical ambient owners
`TopCat.CWComplex Γ` and `IsWeakEquivalence γ`. -/
class IsCWApproximation {Γ : TopCat.{u}} {X : TopCat.{v}} (γ : C(Γ, X))
    extends TopCat.CWComplex Γ, IsWeakEquivalence γ

/-- A chosen CW approximation of `X` records a CW model `Γ`, a comparison map `γ : C(Γ, X)`,
and the Chapter 10 owner `IsCWApproximation γ` on that map. -/
structure CWApproximation (X : TopCat.{v}) where
  Γ : TopCat.{u}
  γ : C(Γ, X)
  isCWApproximation : IsCWApproximation γ

attribute [instance] CWApproximation.isCWApproximation
