module

public import Topology_Munkres_2000.Book.Algorithm_76_1.EdgeGluing
public import Topology_Munkres_2000.Book.Definition_76_1.Cut
public import Topology_Munkres_2000.Book.Definition_76_2.Translation

public section

open Set

namespace CyclicPolygon.Cut

noncomputable section

variable {n : ℕ}

/-- The translated closing edge of the left cut polygon, oriented from `q₀` to `qₖ`. -/
def leftDiagonal (P : CyclicPolygon n) (k : Fin n) (hk₁ : 1 < k.val)
    (translation : EuclideanSpace ℝ (Fin 2)) :
    ((left P k hk₁).translate translation).DirectedEdge where
  index := Fin.last k.val
  forward := false

/-- The initial edge of the right cut polygon, oriented from `p₀` to `pₖ`. -/
def rightDiagonal (P : CyclicPolygon n) (k : Fin n) (hk₁ : 1 < k.val)
    (hk₂ : k.val < n - 1) :
    (right P k hk₁ hk₂).DirectedEdge where
  index := 0
  forward := true

/-- The canonical edge gluing of the translated left cut polygon to the right cut polygon. -/
def edgeGluing (P : CyclicPolygon n) (k : Fin n) (hk₁ : 1 < k.val)
    (hk₂ : k.val < n - 1) (translation : EuclideanSpace ℝ (Fin 2))
    (h_disjoint : Disjoint ((left P k hk₁).translate translation).region
      (right P k hk₁ hk₂).region) :
    EdgeGluing ((left P k hk₁).translate translation) (right P k hk₁ hk₂) where
  leftEdge := leftDiagonal P k hk₁ translation
  rightEdge := rightDiagonal P k hk₁ hk₂
  regions_disjoint := h_disjoint

/-- Helper for Definition 76.2: the canonical gluing uses the translated closing
edge of the left cut polygon. -/
lemma edgeGluing_leftEdge (P : CyclicPolygon n) (k : Fin n) (hk₁ : 1 < k.val)
    (hk₂ : k.val < n - 1) (translation : EuclideanSpace ℝ (Fin 2))
    (h_disjoint : Disjoint ((left P k hk₁).translate translation).region
      (right P k hk₁ hk₂).region) :
    (edgeGluing P k hk₁ hk₂ translation h_disjoint).leftEdge =
      { index := Fin.last k.val, forward := false } := by
  -- Route correction: compute the projection where both canonical definitions are reducible.
  rfl

/-- Helper for Definition 76.2: the canonical gluing uses the initial forward edge
of the right cut polygon. -/
lemma edgeGluing_rightEdge (P : CyclicPolygon n) (k : Fin n) (hk₁ : 1 < k.val)
    (hk₂ : k.val < n - 1) (translation : EuclideanSpace ℝ (Fin 2))
    (h_disjoint : Disjoint ((left P k hk₁).translate translation).region
      (right P k hk₁ hk₂).region) :
    (edgeGluing P k hk₁ hk₂ translation h_disjoint).rightEdge =
      { index := 0, forward := true } := by
  -- Reduce the stored right diagonal to its index and orientation fields.
  rfl


end

end CyclicPolygon.Cut
