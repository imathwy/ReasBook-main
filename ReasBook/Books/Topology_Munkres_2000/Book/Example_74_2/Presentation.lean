module

public import Topology_Munkres_2000.Book.Example_74_2.UnitSquare
public import Topology_Munkres_2000.Book.Notation_74_1.SignedLetter
public import Topology_Munkres_2000.Book.Proposition_76_1.Realization

public section

open scoped SignedLetter

namespace SphereSquare

/-- The signed boundary letters `a a⁻¹ b b⁻¹`, with labels `0 = a` and `1 = b`. -/
def boundaryLetters : List (Fin 2 × Bool) :=
  [(0 : Fin 2), (0 : Fin 2)⁻¹, (1 : Fin 2), (1 : Fin 2)⁻¹]

/-- The polygon word encoding the oriented boundary scheme `a a⁻¹ b b⁻¹`. -/
def boundaryWord : PolygonWord (Fin 2) :=
  ⟨boundaryLetters, by decide⟩

/-- The singleton labelling scheme whose boundary word is `a a⁻¹ b b⁻¹`. -/
def scheme : LabellingScheme (Fin 2) :=
  boundaryWord ::ₘ 0

/-- The unit square with its ordered boundary edges prescribed by `a a⁻¹ b b⁻¹`. -/
@[expose]
def regions : LabellingScheme.PolygonalRegions scheme where
  Point _ := unitInterval × unitInterval
  topology _ := inferInstance
  edge _ edge t := UnitSquare.edge edge t

/-- The unique polygonal-region occurrence in the sphere-square presentation. -/
noncomputable def region : LabellingScheme.Occurrence scheme :=
  (LabellingScheme.consOccurrenceEquiv boundaryWord 0).symm none

/-- The four square vertices as points of the presentation's source region. -/
noncomputable def vertex (i : Fin 4) : regions.Source :=
  ⟨region, UnitSquare.edge i 0⟩

/-- The labelled-edge realization of the square with boundary word `a a⁻¹ b b⁻¹`. -/
abbrev Realization := regions.Realization


end SphereSquare
