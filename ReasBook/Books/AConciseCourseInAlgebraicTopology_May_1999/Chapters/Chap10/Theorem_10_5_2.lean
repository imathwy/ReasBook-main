import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.CWApproximation
import Mathlib.Topology.Homotopy.Basic

open scoped ContinuousMap Topology.Homotopy

universe u v

section

variable {X ΓX : TopCat.{u}} {Y ΓY : TopCat.{v}}
variable (γX : C(ΓX, X)) [IsCWApproximation γX]
variable (γY : C(ΓY, Y)) [IsCWApproximation γY]
variable (f : C(X, Y))

/-- Theorem 10.5.2 (1): if `f : C(X, Y)` and `γX : C(ΓX, X)`, `γY : C(ΓY, Y)` are CW
approximations, then there is a map `Γf : C(ΓX, ΓY)` such that the square with sides `γX`, `γY`,
and `f` commutes up to homotopy. -/
theorem exists_map_between_cwApproximations :
    ∃ Γf : C(ΓX, ΓY), ContinuousMap.Homotopic (γY.comp Γf) (f.comp γX) := sorry

/-- Theorem 10.5.2 (2): two maps `Γf₀, Γf₁ : C(ΓX, ΓY)` between CW approximations of
`f : C(X, Y)` that make the comparison square commute up to homotopy are themselves homotopic. -/
theorem homotopic_of_maps_between_cwApproximations
    {Γf₀ Γf₁ : C(ΓX, ΓY)}
    (hΓf₀ : ContinuousMap.Homotopic (γY.comp Γf₀) (f.comp γX))
    (hΓf₁ : ContinuousMap.Homotopic (γY.comp Γf₁) (f.comp γX)) :
    ContinuousMap.Homotopic Γf₀ Γf₁ := sorry

end
