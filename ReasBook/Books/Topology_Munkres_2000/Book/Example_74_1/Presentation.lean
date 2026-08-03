module

public import Topology_Munkres_2000.Book.Notation_74_1.SignedLetter
public import Topology_Munkres_2000.Book.Proposition_55_1.Triangle
public import Topology_Munkres_2000.Book.Proposition_76_1.Realization

public section

open scoped SignedLetter

namespace TriangleDisk

/-- The cyclic parametrization of the three edges of `standardTriangle`. -/
@[expose]
def edgeCoordinates (edge : Fin 3) (t : unitInterval) : EuclideanSpace ℝ (Fin 2) :=
  match edge with
  | ⟨0, _⟩ => !₂[(t : ℝ), 0]
  | ⟨1, _⟩ => !₂[(unitInterval.symm t : ℝ), (t : ℝ)]
  | ⟨2, _⟩ => !₂[0, (unitInterval.symm t : ℝ)]

/-- Every point produced by `edgeCoordinates` lies in `standardTriangle`. -/
theorem edgeCoordinates_mem (edge : Fin 3) (t : unitInterval) :
    edgeCoordinates edge t ∈ standardTriangle := by
  rcases t with ⟨t, ht⟩
  rcases ht with ⟨ht0, ht1⟩
  fin_cases edge
  · rw [mem_standardTriangle]
    simp [edgeCoordinates, ht0, ht1]
  · rw [mem_standardTriangle]
    simp [edgeCoordinates, ht0, ht1]
  · rw [mem_standardTriangle]
    simp [edgeCoordinates, ht0, ht1]

/-- The cyclically parametrized point on an edge of `standardTriangle`. -/
@[expose]
def edgePoint (edge : Fin 3) (t : unitInterval) : standardTriangle :=
  ⟨edgeCoordinates edge t, edgeCoordinates_mem edge t⟩

/-- The signed boundary letters `a⁻¹ b a`, with labels `0 = a` and `1 = b`. -/
def boundaryLetters : List (Fin 2 × Bool) :=
  [(0 : Fin 2)⁻¹, (1 : Fin 2), (0 : Fin 2)]

/-- The polygon word encoding the oriented boundary scheme `a⁻¹ b a`. -/
def boundaryWord : PolygonWord (Fin 2) :=
  ⟨boundaryLetters, by decide⟩

/-- The singleton labelling scheme whose boundary word is `a⁻¹ b a`. -/
def scheme : LabellingScheme (Fin 2) :=
  boundaryWord ::ₘ 0

/-- Every polygon occurrence in the triangular scheme has three edges. -/
theorem occurrence_length (region : LabellingScheme.Occurrence scheme) :
    region.1.1.length = 3 := by
  have hregion : region =
      (LabellingScheme.consOccurrenceEquiv boundaryWord 0).symm none := by
    apply (LabellingScheme.consOccurrenceEquiv boundaryWord 0).injective
    rw [Equiv.apply_symm_apply]
    cases h : LabellingScheme.consOccurrenceEquiv boundaryWord 0 region with
    | none => rfl
    | some remaining =>
        exact (Nat.not_lt_zero remaining.2 remaining.2.isLt).elim
  rw [hregion]
  decide

/-- The standard triangle with its ordered boundary edges prescribed by `a⁻¹ b a`. -/
@[expose]
def regions : LabellingScheme.PolygonalRegions scheme where
  Point _ := standardTriangle
  topology _ := inferInstance
  edge region edge t := edgePoint (Fin.cast (occurrence_length region) edge) t

/-- The unique polygonal-region occurrence in the triangular presentation. -/
noncomputable def region : LabellingScheme.Occurrence scheme :=
  (LabellingScheme.consOccurrenceEquiv boundaryWord 0).symm none

/-- The three vertices as points of the triangular presentation's source region. -/
noncomputable def vertex (i : Fin 3) : regions.Source :=
  ⟨region, edgePoint i 0⟩

/-- The quotient of `standardTriangle` specified by the scheme `a⁻¹ b a`. -/
abbrev Realization := regions.Realization

@[simp]
theorem edgePoint_val (edge : Fin 3) (t : unitInterval) :
    (edgePoint edge t).val = edgeCoordinates edge t := rfl


end TriangleDisk
