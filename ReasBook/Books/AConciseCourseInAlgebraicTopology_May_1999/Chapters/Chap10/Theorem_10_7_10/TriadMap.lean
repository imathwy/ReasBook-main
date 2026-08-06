import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_7_2

universe u v

open Set
open scoped Topology Topology.Homotopy

namespace Triad

variable {X : Type u} {X' : Type v} [TopologicalSpace X] [TopologicalSpace X']
variable (T : Triad X) (T' : Triad X') (e : C(X, X'))

/-- A continuous map `e : X ⟶ X'` is a map `(X; A, B) ⟶ (X'; A', B')` of triads when it sends
`A` into `A'` and `B` into `B'`. -/
def IsMap : Prop :=
  MapsTo e T.subspaceA T'.subspaceA ∧ MapsTo e T.subspaceB T'.subspaceB

/-- A triad map is exactly a continuous map preserving the distinguished `A`- and
`B`-subspaces. -/
@[simp] theorem isMap_iff :
    T.IsMap T' e ↔ MapsTo e T.subspaceA T'.subspaceA ∧ MapsTo e T.subspaceB T'.subspaceB :=
  Iff.rfl

/-- A triad map sends the distinguished `A`-subspace into the target `A`-subspace. -/
theorem IsMap.mapsTo_subspaceA (hMap : T.IsMap T' e) : MapsTo e T.subspaceA T'.subspaceA :=
  hMap.1

/-- A triad map sends the distinguished `B`-subspace into the target `B`-subspace. -/
theorem IsMap.mapsTo_subspaceB (hMap : T.IsMap T' e) : MapsTo e T.subspaceB T'.subspaceB :=
  hMap.2

/-- A triad map sends the intersection `A ∩ B` into the target intersection `A' ∩ B'`. -/
theorem IsMap.mapsTo_intersection (hMap : T.IsMap T' e) : MapsTo e T.intersection T'.intersection :=
  fun _ hx ↦ ⟨hMap.1 hx.1, hMap.2 hx.2⟩

/-- A map of triads restricts to a continuous map on the `A`-subspaces. -/
def mapSubspaceA (hMap : T.IsMap T' e) : C(T.subspaceA, T'.subspaceA) where
  toFun x := ⟨e x, hMap.1 x.2⟩
  continuous_toFun :=
    (e.continuous.comp continuous_subtype_val).subtype_mk fun x ↦ hMap.1 x.2

/-- The restriction of a triad map to the `A`-subspace acts by the ambient map `e`. -/
@[simp] theorem mapSubspaceA_apply (hMap : T.IsMap T' e) (x : T.subspaceA) :
    T.mapSubspaceA T' e hMap x = ⟨e x, hMap.1 x.2⟩ :=
  rfl

/-- A map of triads restricts to a continuous map on the `B`-subspaces. -/
def mapSubspaceB (hMap : T.IsMap T' e) : C(T.subspaceB, T'.subspaceB) where
  toFun x := ⟨e x, hMap.2 x.2⟩
  continuous_toFun :=
    (e.continuous.comp continuous_subtype_val).subtype_mk fun x ↦ hMap.2 x.2

/-- The restriction of a triad map to the `B`-subspace acts by the ambient map `e`. -/
@[simp] theorem mapSubspaceB_apply (hMap : T.IsMap T' e) (x : T.subspaceB) :
    T.mapSubspaceB T' e hMap x = ⟨e x, hMap.2 x.2⟩ :=
  rfl

/-- A map of triads restricts to a continuous map on the intersection `C = A ∩ B`. -/
def mapIntersection (hMap : T.IsMap T' e) : C(T.intersection, T'.intersection) where
  toFun x := ⟨e x, ⟨hMap.1 x.2.1, hMap.2 x.2.2⟩⟩
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk fun x ↦
    ⟨hMap.1 x.2.1, hMap.2 x.2.2⟩

/-- The restriction of a triad map to `A ∩ B` acts by the ambient map `e`. -/
@[simp] theorem mapIntersection_apply (hMap : T.IsMap T' e) (x : T.intersection) :
    T.mapIntersection T' e hMap x = ⟨e x, ⟨hMap.1 x.2.1, hMap.2 x.2.2⟩⟩ :=
  rfl

end Triad
