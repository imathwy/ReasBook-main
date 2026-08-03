module

public import Topology_Munkres_2000.Book.Definition_74_3.Pasting
import all Topology_Munkres_2000.Book.Definition_74_3

public section

namespace PolygonVertices

universe u v w

/-- A map identifies an indexed family of polygon vertices when all their images agree. -/
def Identified {ι : Type u} {P : Type v} {X : Type w}
    (π : P → X) (vertex : ι → P) : Prop :=
  ∀ i j, π (vertex i) = π (vertex j)

/-- For a nonempty vertex family, identification is equivalent to having one common image. -/
theorem identified_iff_exists {ι : Type u} [Nonempty ι] {P : Type v} {X : Type w}
    (π : P → X) (vertex : ι → P) :
    Identified π vertex ↔ ∃ x₀ : X, ∀ i, π (vertex i) = x₀ := by
  constructor
  · intro h
    let i₀ : ι := Classical.choice inferInstance
    exact ⟨π (vertex i₀), fun i ↦ h i i₀⟩
  · rintro ⟨x₀, h⟩ i j
    exact (h i).trans (h j).symm

/-- Quotient images of the vertices agree exactly when their representatives are related. -/
theorem identified_iff_quotient {ι : Type u} {P : Type v}
    (relation : Setoid P) (vertex : ι → P) :
    Identified (Quotient.mk relation) vertex ↔ ∀ i j, relation (vertex i) (vertex j) := by
  simp only [Identified, Quotient.eq]

end PolygonVertices

namespace CyclicPolygon

noncomputable section

universe v

variable {n : ℕ}

namespace EdgePasting

variable {poly : CyclicPolygon n} {S : Type v}

/-- All vertices of the polygon have the same image in the pasted realization. -/
abbrev VerticesIdentified (pasting : poly.EdgePasting S) : Prop :=
  PolygonVertices.Identified pasting.quotientMap poly.vertexPoint

/-- Having all vertex images equal is equivalent to their sharing one common image. -/
theorem verticesIdentified_iff_exists (pasting : poly.EdgePasting S) :
    pasting.VerticesIdentified ↔
      ∃ x₀ : pasting.Realization,
        ∀ i : Fin n, pasting.quotientMap (poly.vertexPoint i) = x₀ := by
  constructor
  · intro h
    let i₀ : Fin n := ⟨0, lt_of_lt_of_le (by decide) poly.three_le⟩
    exact ⟨pasting.quotientMap (poly.vertexPoint i₀), fun i ↦ h i i₀⟩
  · rintro ⟨x₀, h⟩ i j
    exact (h i).trans (h j).symm

/-- Vertex images agree in the quotient exactly when all vertex representatives are identified. -/
theorem verticesIdentified_iff_identified (pasting : poly.EdgePasting S) :
    pasting.VerticesIdentified ↔
      ∀ i j : Fin n, pasting.Identified (poly.vertexPoint i) (poly.vertexPoint j) := by
  -- Equality of canonical quotient classes is exactly the underlying setoid relation.
  simp only [VerticesIdentified, PolygonVertices.Identified, quotientMap, Quotient.eq]

end EdgePasting

end

end CyclicPolygon
