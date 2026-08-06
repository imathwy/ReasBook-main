import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_7_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Theorem_10_7_10

open scoped ContinuousMap

universe u

-- Semantic recall via `lean_leansearch`: no dedicated mathlib owner for CW approximations of
-- excisive triads surfaced in the current environment. Local Chapter 10 precedent already fixes
-- `CWTriad` as the canonical CW-triad owner, now inheriting the ordinary triad API
-- `Triad.IsMap`, `Triad.mapSubspaceA`, `Triad.mapSubspaceB`, and `Triad.mapIntersection`
-- directly for the maps on `ΓA`, `ΓB`, and `ΓC = ΓA ∩ ΓB`.

/-- A map from a CW triad to a triad is a CW-triad approximation when it is a weak equivalence on
the ambient spaces, on the `A`- and `B`-subspaces, and on the intersection `A ∩ B`. -/
class IsCWTriadApproximation {X ΓX : TopCat.{u}} (ΓT : CWTriad ΓX) (T : Triad X)
    (γX : C(ΓX, X)) (hMap : ΓT.IsMap T γX) : Prop extends IsWeakEquivalence γX where
  /-- The induced map on the distinguished `A`-subspaces is a weak equivalence. -/
  isWeakEquivalence_subspaceA : IsWeakEquivalence (ΓT.mapSubspaceA T γX hMap)
  /-- The induced map on the distinguished `B`-subspaces is a weak equivalence. -/
  isWeakEquivalence_subspaceB : IsWeakEquivalence (ΓT.mapSubspaceB T γX hMap)
  /-- The induced map on the intersection `A ∩ B` is a weak equivalence. -/
  isWeakEquivalence_intersection : IsWeakEquivalence (ΓT.mapIntersection T γX hMap)

namespace IsCWTriadApproximation

variable {X ΓX : TopCat.{u}} {ΓT : CWTriad ΓX} {T : Triad X}
variable {γX : C(ΓX, X)} {hMap : ΓT.IsMap T γX}

/-- The ambient map of a CW-triad approximation is a weak equivalence. -/
theorem isWeakEquivalence_toAmbient (hγ : IsCWTriadApproximation ΓT T γX hMap) :
    IsWeakEquivalence γX := by
  letI : IsCWTriadApproximation ΓT T γX hMap := hγ
  infer_instance

/-- A CW-triad approximation supplies weak equivalences on the ambient spaces and on the
distinguished `A`, `B`, and `A ∩ B` subspaces. -/
theorem spec (hγ : IsCWTriadApproximation ΓT T γX hMap) :
    IsWeakEquivalence γX ∧
      IsWeakEquivalence (ΓT.mapSubspaceA T γX hMap) ∧
      IsWeakEquivalence (ΓT.mapSubspaceB T γX hMap) ∧
      IsWeakEquivalence (ΓT.mapIntersection T γX hMap) := by
  exact ⟨hγ.isWeakEquivalence_toAmbient, hγ.isWeakEquivalence_subspaceA,
    hγ.isWeakEquivalence_subspaceB, hγ.isWeakEquivalence_intersection⟩

instance [hγ : IsCWTriadApproximation ΓT T γX hMap] :
    IsWeakEquivalence (ΓT.mapSubspaceA T γX hMap) :=
  hγ.isWeakEquivalence_subspaceA

instance [hγ : IsCWTriadApproximation ΓT T γX hMap] :
    IsWeakEquivalence (ΓT.mapSubspaceB T γX hMap) :=
  hγ.isWeakEquivalence_subspaceB

instance [hγ : IsCWTriadApproximation ΓT T γX hMap] :
    IsWeakEquivalence (ΓT.mapIntersection T γX hMap) :=
  hγ.isWeakEquivalence_intersection

end IsCWTriadApproximation

/-- Theorem 10.7.4: every excisive triad `(X; A, B)`, with `C = A ∩ B`, admits a CW triad
approximation `(ΓX; ΓA, ΓB)` over `X`, formalized by a CW triad `ΓT : CWTriad ΓX`, a triad map
`γX : ΓX ⟶ X`, and weak equivalences on the ambient space `ΓX`, on the distinguished subspaces
`ΓA` and `ΓB`, and on the intersection `ΓC = ΓA ∩ ΓB`. -/
theorem exists_cwTriadApproximation (X : TopCat.{u}) (T : Triad X) (hT : T.IsExcisive) :
    ∃ (ΓX : TopCat.{u}) (ΓT : CWTriad ΓX) (γX : C(ΓX, X)) (hMap : ΓT.IsMap T γX),
      IsCWTriadApproximation ΓT T γX hMap := sorry
