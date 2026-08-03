module

public import Topology_Munkres_2000.Book.Definition_76_3.Reassembly

public section

/-- Definition 76.3: Oppositely oriented distinguished edges can be pasted by replacing
the left polygon with one on the circle of the right polygon, so that corresponding
vertices and the attaching edge agree and the edge-gluing realization is homeomorphic
to the resulting union of cyclic polygonal regions. -/
theorem CyclicPolygon.EdgeGluing.existsReassembly {m n : ℕ}
    {left : CyclicPolygon m} {right : CyclicPolygon n}
    (gluing : EdgeGluing left right)
    (h_oppositeOrientation : gluing.leftEdge.forward ≠ gluing.rightEdge.forward) :
    ∃ (replacement : CyclicPolygon m) (combined : CyclicPolygon (m + n - 2))
      (leftHomeomorph : left.region ≃ₜ replacement.region)
      (realizationHomeomorph : gluing.Realization ≃ₜ combined.region),
      replacement.center = right.center ∧
      replacement.radius = right.radius ∧
      (∀ i : Fin m,
        (leftHomeomorph (left.vertexPoint i) : EuclideanSpace ℝ (Fin 2)) =
          replacement.vertexPoint i) ∧
      (∀ x : gluing.attachingSubset,
        (leftHomeomorph x : EuclideanSpace ℝ (Fin 2)) = gluing.attachingMap x) ∧
      combined.region = replacement.region ∪ right.region ∧
      (∀ x : left.region,
      (realizationHomeomorph (gluing.includeLeft x) : EuclideanSpace ℝ (Fin 2)) =
          leftHomeomorph x) ∧
      (∀ y : right.region,
        (realizationHomeomorph (gluing.includeRight y) : EuclideanSpace ℝ (Fin 2)) = y) := by
  -- First splice a reversed copy of the selected right edge into one cyclic union.
  obtain ⟨replacement, combined, hcenter, hradius, hinitial, hfinal, hunion, hinter⟩ :=
    CyclicPolygon.existsCyclicEdgeInsertion left.three_le right
      gluing.leftEdge.index gluing.rightEdge.index
  -- The canonical radial extension preserves all indexed vertices and edge parameters.
  obtain ⟨leftHomeomorph, hvertices, hparameters⟩ :=
    CyclicPolygon.existsVertexAndEdgeParameterPreservingRegionHomeomorph left replacement
  have hverticesAmbient : ∀ i : Fin m,
      (leftHomeomorph (left.vertexPoint i) : EuclideanSpace ℝ (Fin 2)) =
        replacement.vertexPoint i := by
    intro i
    exact congrArg Subtype.val (hvertices i)
  have hattaching :=
    gluing.regionHomeomorphAgreesWithAttachingMapOfReversedEdge replacement
      leftHomeomorph hparameters hinitial hfinal h_oppositeOrientation
  -- Descend the two planar inclusions through the adjunction quotient.
  obtain ⟨realizationHomeomorph, hrealLeft, hrealRight⟩ :=
    gluing.existsRealizationHomeomorphOfRegionUnion replacement combined
      leftHomeomorph h_oppositeOrientation hattaching hunion hinter
  exact ⟨replacement, combined, leftHomeomorph, realizationHomeomorph,
    hcenter, hradius, hverticesAmbient, hattaching, hunion, hrealLeft, hrealRight⟩
