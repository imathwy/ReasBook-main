import Mathlib.Topology.Homotopy.Equiv
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_7_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_7_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Theorem_10_7_10

universe u

open Set
open scoped ContinuousMap unitInterval

noncomputable section

-- Semantic recall via `lean_leansearch`: no canonical mathlib owner for CW-triad approximation by
-- an excisive double mapping cylinder surfaced in the current environment. The local Chapter 10
-- owners `CWTriad`, `Triad.IsExcisive`, and `ContinuousMap.doubleMappingCylinder` therefore give
-- the source-faithful formalization layer here.

namespace CWTriad

variable {X : Type u} [TopologicalSpace X]

/-- The intersection inclusion `A ∩ B ↪ A` attached to a CW triad. -/
def intersectionInclusionA (T : CWTriad X) :
    C((T.subspaceA ∩ T.subspaceB : Set X), T.subspaceA) :=
  ⟨fun x ↦ ⟨x.1, x.2.1⟩, continuous_subtype_val.subtype_mk fun x ↦ x.2.1⟩

/-- The intersection inclusion `A ∩ B ↪ B` attached to a CW triad. -/
def intersectionInclusionB (T : CWTriad X) :
    C((T.subspaceA ∩ T.subspaceB : Set X), T.subspaceB) :=
  ⟨fun x ↦ ⟨x.1, x.2.2⟩, continuous_subtype_val.subtype_mk fun x ↦ x.2.2⟩

/-- The double mapping cylinder built from the intersection inclusions of a CW triad. -/
abbrev doubleMappingCylinderSpace (T : CWTriad X) : TopCat :=
  M(intersectionInclusionA T, intersectionInclusionB T)

/-- The shared cylinder/intersection subspace inside the double mapping cylinder attached to a CW
triad. -/
def doubleMappingCylinderIntersectionSubspace (T : CWTriad X) : Set T.doubleMappingCylinderSpace :=
  Set.range fun z : ((T.subspaceA ∩ T.subspaceB : Set X) × I) ↦
    ContinuousMap.doubleMappingCylinderCylinderInclusion
        (intersectionInclusionA T) (intersectionInclusionB T)
      z

/-- The distinguished `A`-piece of the double-mapping-cylinder triad attached to a CW triad,
consisting of the `A`-end summand together with the shared cylinder image. -/
def doubleMappingCylinderSubspaceA (T : CWTriad X) : Set T.doubleMappingCylinderSpace :=
  Set.range
      (fun a : T.subspaceA ↦
        ContinuousMap.doubleMappingCylinderCoprodInclusion
            (intersectionInclusionA T) (intersectionInclusionB T)
          (Sum.inl a)) ∪
    T.doubleMappingCylinderIntersectionSubspace

/-- The distinguished `B`-piece of the double-mapping-cylinder triad attached to a CW triad,
consisting of the `B`-end summand together with the shared cylinder image. -/
def doubleMappingCylinderSubspaceB (T : CWTriad X) : Set T.doubleMappingCylinderSpace :=
  Set.range
      (fun b : T.subspaceB ↦
        ContinuousMap.doubleMappingCylinderCoprodInclusion
            (intersectionInclusionA T) (intersectionInclusionB T)
          (Sum.inr b)) ∪
    T.doubleMappingCylinderIntersectionSubspace

/-- The triad on the double mapping cylinder whose pieces are the two mapping-cylinder pieces:
the `A`-end summand and the `B`-end summand, each enlarged by the shared cylinder image. -/
def doubleMappingCylinderTriad (T : CWTriad X) : Triad T.doubleMappingCylinderSpace where
  subspaceA := T.doubleMappingCylinderSubspaceA
  subspaceB := T.doubleMappingCylinderSubspaceB

/-- The actual intersection of the two distinguished pieces of the double-mapping-cylinder triad
is the shared cylinder/intersection subspace. -/
@[simp] theorem doubleMappingCylinderTriad_intersection_eq (T : CWTriad X) :
    T.doubleMappingCylinderTriad.intersection = T.doubleMappingCylinderIntersectionSubspace := sorry

/-- A homotopy equivalence `e : X ≃ₕ M(A ∩ B ↪ A, A ∩ B ↪ B)` is compatible with the CW-triad
`(X; A, B)` when its forward and inverse maps form maps of triads and the induced restriction maps
on `A`, `B`, and `A ∩ B` are homotopy equivalences compatible with those ambient triad maps. -/
structure IsDoubleMappingCylinderTriadHomotopyEquiv (T : CWTriad X)
    (e : X ≃ₕ T.doubleMappingCylinderSpace) : Prop where
  /-- The forward map of `e` is a map from the source CW triad to the double-mapping-cylinder
  triad. -/
  toDoubleMappingCylinderTriad :
    T.toTriad.IsMap T.doubleMappingCylinderTriad e.toFun
  /-- The inverse map of `e` is a map from the double-mapping-cylinder triad back to the source CW
  triad. -/
  fromDoubleMappingCylinderTriad :
    T.doubleMappingCylinderTriad.IsMap T.toTriad e.symm.toFun
  /-- There is an induced homotopy equivalence on the `A`-piece compatible with `e` and `e.symm`. -/
  subspaceAHomotopyEquiv :
    ∃ eA : T.subspaceA ≃ₕ T.doubleMappingCylinderSubspaceA,
      eA.toFun =
          T.toTriad.mapSubspaceA T.doubleMappingCylinderTriad e.toFun
            toDoubleMappingCylinderTriad ∧
        eA.symm.toFun =
          T.doubleMappingCylinderTriad.mapSubspaceA T.toTriad e.symm.toFun
            fromDoubleMappingCylinderTriad
  /-- There is an induced homotopy equivalence on the `B`-piece compatible with `e` and `e.symm`. -/
  subspaceBHomotopyEquiv :
    ∃ eB : T.subspaceB ≃ₕ T.doubleMappingCylinderSubspaceB,
      eB.toFun =
          T.toTriad.mapSubspaceB T.doubleMappingCylinderTriad e.toFun
            toDoubleMappingCylinderTriad ∧
        eB.symm.toFun =
          T.doubleMappingCylinderTriad.mapSubspaceB T.toTriad e.symm.toFun
            fromDoubleMappingCylinderTriad
  /-- There is an induced homotopy equivalence on `A ∩ B` compatible with `e` and `e.symm`,
  landing in the actual intersection of the target triad pieces. -/
  intersectionHomotopyEquiv :
    ∃ eAB : T.toTriad.intersection ≃ₕ T.doubleMappingCylinderTriad.intersection,
      eAB.toFun =
          T.toTriad.mapIntersection T.doubleMappingCylinderTriad e.toFun
            toDoubleMappingCylinderTriad ∧
        eAB.symm.toFun =
          T.doubleMappingCylinderTriad.mapIntersection T.toTriad e.symm.toFun
            fromDoubleMappingCylinderTriad

namespace IsDoubleMappingCylinderTriadHomotopyEquiv

variable {T : CWTriad X} {e : X ≃ₕ T.doubleMappingCylinderSpace}

/-- The forward map of a compatible homotopy equivalence sends `A` into the distinguished `A`-piece
of the double-mapping-cylinder triad. -/
theorem mapsTo_subspaceA (h : IsDoubleMappingCylinderTriadHomotopyEquiv T e) :
    MapsTo e.toFun T.subspaceA T.doubleMappingCylinderSubspaceA :=
  h.toDoubleMappingCylinderTriad.mapsTo_subspaceA

/-- The forward map of a compatible homotopy equivalence sends `B` into the distinguished `B`-piece
of the double-mapping-cylinder triad. -/
theorem mapsTo_subspaceB (h : IsDoubleMappingCylinderTriadHomotopyEquiv T e) :
    MapsTo e.toFun T.subspaceB T.doubleMappingCylinderSubspaceB :=
  h.toDoubleMappingCylinderTriad.mapsTo_subspaceB

/-- The forward map of a compatible homotopy equivalence sends `A ∩ B` into the actual intersection
of the double-mapping-cylinder triad pieces. -/
theorem mapsTo_intersection (h : IsDoubleMappingCylinderTriadHomotopyEquiv T e) :
    MapsTo e.toFun T.toTriad.intersection T.doubleMappingCylinderTriad.intersection :=
  h.toDoubleMappingCylinderTriad.mapsTo_intersection

/-- The inverse map of a compatible homotopy equivalence sends the distinguished `A`-piece of the
double-mapping-cylinder triad back into `A`. -/
theorem symm_mapsTo_subspaceA (h : IsDoubleMappingCylinderTriadHomotopyEquiv T e) :
    MapsTo e.symm.toFun T.doubleMappingCylinderSubspaceA T.subspaceA :=
  h.fromDoubleMappingCylinderTriad.mapsTo_subspaceA

/-- The inverse map of a compatible homotopy equivalence sends the distinguished `B`-piece of the
double-mapping-cylinder triad back into `B`. -/
theorem symm_mapsTo_subspaceB (h : IsDoubleMappingCylinderTriadHomotopyEquiv T e) :
    MapsTo e.symm.toFun T.doubleMappingCylinderSubspaceB T.subspaceB :=
  h.fromDoubleMappingCylinderTriad.mapsTo_subspaceB

/-- The inverse map of a compatible homotopy equivalence sends the actual intersection of the
double-mapping-cylinder triad pieces back into `A ∩ B`. -/
theorem symm_mapsTo_intersection (h : IsDoubleMappingCylinderTriadHomotopyEquiv T e) :
    MapsTo e.symm.toFun T.doubleMappingCylinderTriad.intersection T.toTriad.intersection :=
  h.fromDoubleMappingCylinderTriad.mapsTo_intersection

/-- The canonical restriction of the ambient forward map `e.toFun` to the distinguished `A`-pieces
of the source and target triads. -/
abbrev mapSubspaceA (h : IsDoubleMappingCylinderTriadHomotopyEquiv T e) :
    C(T.subspaceA, T.doubleMappingCylinderSubspaceA) :=
  T.toTriad.mapSubspaceA T.doubleMappingCylinderTriad e.toFun h.toDoubleMappingCylinderTriad

/-- The canonical restriction of the ambient forward map `e.toFun` to the distinguished `B`-pieces
of the source and target triads. -/
abbrev mapSubspaceB (h : IsDoubleMappingCylinderTriadHomotopyEquiv T e) :
    C(T.subspaceB, T.doubleMappingCylinderSubspaceB) :=
  T.toTriad.mapSubspaceB T.doubleMappingCylinderTriad e.toFun h.toDoubleMappingCylinderTriad

/-- The canonical restriction of the ambient forward map `e.toFun` to the intersection pieces of
the source and target triads. -/
abbrev mapIntersection (h : IsDoubleMappingCylinderTriadHomotopyEquiv T e) :
    C(T.toTriad.intersection, T.doubleMappingCylinderTriad.intersection) :=
  T.toTriad.mapIntersection T.doubleMappingCylinderTriad e.toFun h.toDoubleMappingCylinderTriad

end IsDoubleMappingCylinderTriadHomotopyEquiv

/-- Corollary 10.7.9 (1): the triad on the double mapping cylinder of the inclusions
`A ∩ B ↪ A` and `A ∩ B ↪ B` attached to a CW triad is excisive. -/
theorem doubleMappingCylinderTriad_isExcisive (T : CWTriad X) :
    T.doubleMappingCylinderTriad.IsExcisive := sorry

/-- Corollary 10.7.9 (2): a CW triad is homotopy equivalent to the double-mapping-cylinder triad
by a homotopy equivalence whose restrictions to `A`, `B`, and `A ∩ B` are homotopy equivalences
compatible with the ambient maps in both directions. -/
theorem exists_homotopyEquiv_doubleMappingCylinderTriad (T : CWTriad X) :
    ∃ e : X ≃ₕ T.doubleMappingCylinderSpace,
      IsDoubleMappingCylinderTriadHomotopyEquiv T e := sorry

end CWTriad
