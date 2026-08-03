module

public import Topology_Munkres_2000.Book.Theorem_57_6.BoundaryRidgeExtremeCorner

public section

noncomputable section

namespace StandardSphere.CubicalTucker

/-- Helper for Theorem 57.6: package the exchanged active presentation with
its endpoint certificate. -/
def EndpointBoundaryFaceOccurrence.exchangedActiveEndpointOccurrence
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (inner : NormalizedSharedFacet d m) : EndpointStaircaseFaceOccurrence d m :=
  ⟨occurrence.exchangedActiveOccurrence inner,
    occurrence.exchangedActiveOccurrence_endpoint inner⟩

/-- Helper for Theorem 57.6: the explicit top-corner mate is again an
endpoint boundary-face occurrence. -/
def EndpointBoundaryFaceOccurrence.extremeTopMateEndpoint
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (lower : PositiveNormalizedSharedFacet d m)
    (htop : lower.1.1.level.1 = 2 * m) :
    EndpointBoundaryFaceOccurrence (d + 1) m :=
  ⟨occurrence.extremeTopMate lower htop,
    (occurrence.extremeTopMate_omitted lower htop) ▸
      occurrence.exchangedActiveOccurrence_endpoint lower.1⟩

/-- Helper for Theorem 57.6: the explicit bottom-corner mate is again an
endpoint boundary-face occurrence. -/
def EndpointBoundaryFaceOccurrence.extremeBottomMateEndpoint
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (upper : BelowTopNormalizedSharedFacet d m)
    (hbottom : upper.1.1.level.1 = 0) :
    EndpointBoundaryFaceOccurrence (d + 1) m :=
  ⟨occurrence.extremeBottomMate upper hbottom,
    (occurrence.extremeBottomMate_omitted upper hbottom) ▸
      occurrence.exchangedActiveOccurrence_endpoint upper.1⟩

/-- Helper for Theorem 57.6: active compression of a top-corner mate is the
exchanged endpoint presentation used to build it. -/
theorem EndpointBoundaryFaceOccurrence.extremeTopMateEndpoint_activeOccurrence
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (lower : PositiveNormalizedSharedFacet d m)
    (htop : lower.1.1.level.1 = 2 * m) :
    (occurrence.extremeTopMateEndpoint lower htop).activeOccurrence =
      occurrence.exchangedActiveEndpointOccurrence lower.1 := by
  -- Compare the compressed simplex and omitted endpoint through their named
  -- projection laws, then rebuild the two-field occurrence.
  apply Subtype.ext
  let first := (occurrence.extremeTopMateEndpoint lower htop).activeOccurrence.1
  let second := (occurrence.exchangedActiveEndpointOccurrence lower.1).1
  have hsimplex : first.simplex = second.simplex := by
    calc
      first.simplex =
          (occurrence.extremeTopMate lower htop).facet.normalizedFacet.1.activeStaircase :=
        (occurrence.extremeTopMateEndpoint lower htop).activeOccurrence_simplex
      _ = (occurrence.exchangedActiveOccurrence lower.1).simplex :=
        occurrence.extremeTopMate_activeStaircase lower htop
      _ = second.simplex := rfl
  have homitted : first.omitted = second.omitted := by
    calc
      first.omitted = (occurrence.extremeTopMate lower htop).omitted :=
        (occurrence.extremeTopMateEndpoint lower htop).activeOccurrence_omitted
      _ = (occurrence.exchangedActiveOccurrence lower.1).omitted :=
        occurrence.extremeTopMate_omitted lower htop
      _ = second.omitted := rfl
  exact first.mk_eq_self.symm.trans
    ((congrArg₂ StaircaseFaceOccurrence.mk hsimplex homitted).trans second.mk_eq_self)

/-- Helper for Theorem 57.6: active compression of a bottom-corner mate is
the exchanged endpoint presentation used to build it. -/
theorem EndpointBoundaryFaceOccurrence.extremeBottomMateEndpoint_activeOccurrence
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (upper : BelowTopNormalizedSharedFacet d m)
    (hbottom : upper.1.1.level.1 = 0) :
    (occurrence.extremeBottomMateEndpoint upper hbottom).activeOccurrence =
      occurrence.exchangedActiveEndpointOccurrence upper.1 := by
  -- Compare the compressed simplex and omitted endpoint through their named
  -- projection laws, then rebuild the two-field occurrence.
  apply Subtype.ext
  let first := (occurrence.extremeBottomMateEndpoint upper hbottom).activeOccurrence.1
  let second := (occurrence.exchangedActiveEndpointOccurrence upper.1).1
  have hsimplex : first.simplex = second.simplex := by
    calc
      first.simplex =
          (occurrence.extremeBottomMate upper hbottom).facet.normalizedFacet.1.activeStaircase :=
        (occurrence.extremeBottomMateEndpoint upper hbottom).activeOccurrence_simplex
      _ = (occurrence.exchangedActiveOccurrence upper.1).simplex :=
        occurrence.extremeBottomMate_activeStaircase upper hbottom
      _ = second.simplex := rfl
  have homitted : first.omitted = second.omitted := by
    calc
      first.omitted = (occurrence.extremeBottomMate upper hbottom).omitted :=
        (occurrence.extremeBottomMateEndpoint upper hbottom).activeOccurrence_omitted
      _ = (occurrence.exchangedActiveOccurrence upper.1).omitted :=
        occurrence.extremeBottomMate_omitted upper hbottom
      _ = second.omitted := rfl
  exact first.mk_eq_self.symm.trans
    ((congrArg₂ StaircaseFaceOccurrence.mk hsimplex homitted).trans second.mk_eq_self)

/-- Helper for Theorem 57.6: the top-corner mate's normal form is obtained by
normalizing the exchanged active endpoint occurrence. -/
theorem EndpointBoundaryFaceOccurrence.extremeTopMateEndpoint_normalForm
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (lower : PositiveNormalizedSharedFacet d m)
    (htop : lower.1.1.level.1 = 2 * m) :
    (occurrence.extremeTopMateEndpoint lower htop).normalForm =
      endpointStaircaseFaceEquiv d m
        (occurrence.exchangedActiveEndpointOccurrence lower.1) := by
  -- Rewrite normalization through the verified active-compression equation.
  calc
    (occurrence.extremeTopMateEndpoint lower htop).normalForm =
        endpointStaircaseFaceEquiv d m
          (occurrence.extremeTopMateEndpoint lower htop).activeOccurrence :=
      (occurrence.extremeTopMateEndpoint lower htop).normalForm_eq
    _ = endpointStaircaseFaceEquiv d m
          (occurrence.exchangedActiveEndpointOccurrence lower.1) :=
      congrArg (endpointStaircaseFaceEquiv d m)
        (occurrence.extremeTopMateEndpoint_activeOccurrence lower htop)

/-- Helper for Theorem 57.6: the bottom-corner mate's normal form is obtained
by normalizing the exchanged active endpoint occurrence. -/
theorem EndpointBoundaryFaceOccurrence.extremeBottomMateEndpoint_normalForm
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (upper : BelowTopNormalizedSharedFacet d m)
    (hbottom : upper.1.1.level.1 = 0) :
    (occurrence.extremeBottomMateEndpoint upper hbottom).normalForm =
      endpointStaircaseFaceEquiv d m
        (occurrence.exchangedActiveEndpointOccurrence upper.1) := by
  -- Rewrite normalization through the verified active-compression equation.
  calc
    (occurrence.extremeBottomMateEndpoint upper hbottom).normalForm =
        endpointStaircaseFaceEquiv d m
          (occurrence.extremeBottomMateEndpoint upper hbottom).activeOccurrence :=
      (occurrence.extremeBottomMateEndpoint upper hbottom).normalForm_eq
    _ = endpointStaircaseFaceEquiv d m
          (occurrence.exchangedActiveEndpointOccurrence upper.1) :=
      congrArg (endpointStaircaseFaceEquiv d m)
        (occurrence.extremeBottomMateEndpoint_activeOccurrence upper hbottom)

/-- Helper for Theorem 57.6: the top-corner mate preserves the complete
unordered ridge, not only its pointwise enumeration. -/
theorem EndpointBoundaryFaceOccurrence.extremeTopMate_ridgeVertexSet
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (lower : PositiveNormalizedSharedFacet d m)
    (hnormal : occurrence.normalForm = Sum.inl lower)
    (htop : lower.1.1.level.1 = 2 * m) :
    (occurrence.extremeTopMate lower htop).ridgeVertexSet =
      occurrence.1.ridgeVertexSet := by
  -- Lift the existing pointwise corner computation through the two finite
  -- vertex images.
  rw [(occurrence.extremeTopMate lower htop).ridgeVertexSet_eq_vertexImage,
    occurrence.1.ridgeVertexSet_eq_vertexImage]
  apply Finset.image_congr
  intro j _
  exact occurrence.extremeTopMate_vertex lower hnormal htop j

/-- Helper for Theorem 57.6: the bottom-corner mate preserves the complete
unordered ridge, not only its pointwise enumeration. -/
theorem EndpointBoundaryFaceOccurrence.extremeBottomMate_ridgeVertexSet
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (upper : BelowTopNormalizedSharedFacet d m)
    (hnormal : occurrence.normalForm = Sum.inr upper)
    (hbottom : upper.1.1.level.1 = 0) :
    (occurrence.extremeBottomMate upper hbottom).ridgeVertexSet =
      occurrence.1.ridgeVertexSet := by
  -- Lift the existing pointwise corner computation through the two finite
  -- vertex images.
  rw [(occurrence.extremeBottomMate upper hbottom).ridgeVertexSet_eq_vertexImage,
    occurrence.1.ridgeVertexSet_eq_vertexImage]
  apply Finset.image_congr
  intro j _
  exact occurrence.extremeBottomMate_vertex upper hnormal hbottom j

/-- Helper for Theorem 57.6: an endpoint occurrence equipped with the
specific extreme normal form used by the corner transpose. -/
structure ExtremeCornerBoundaryFaceOccurrence (d m : ℕ) where
  occurrence : EndpointBoundaryFaceOccurrence (d + 1) m
  normal :
    {lower : PositiveNormalizedSharedFacet d m //
        lower.1.1.level.1 = 2 * m} ⊕
      {upper : BelowTopNormalizedSharedFacet d m //
        upper.1.1.level.1 = 0}
  normal_eq : occurrence.normalForm =
    Sum.map Subtype.val Subtype.val normal

/-- Helper for Theorem 57.6: transpose an extreme corner by exchanging the
old outer and inner fixed-coordinate roles. -/
def ExtremeCornerBoundaryFaceOccurrence.transposeOccurrence
    {d m : ℕ} (corner : ExtremeCornerBoundaryFaceOccurrence d m) :
    BoundaryFaceOccurrence (d + 1) m :=
  Sum.elim
    (fun lower ↦ corner.occurrence.extremeTopMate lower.1 lower.2)
    (fun upper ↦ corner.occurrence.extremeBottomMate upper.1 upper.2)
    corner.normal

/-- Helper for Theorem 57.6: the transposed extreme corner remains an
endpoint occurrence, so it can be normalized and transposed again. -/
theorem ExtremeCornerBoundaryFaceOccurrence.transposeOccurrence_endpoint
    {d m : ℕ} (corner : ExtremeCornerBoundaryFaceOccurrence d m) :
    ¬(corner.transposeOccurrence.omitted ≠ 0 ∧
      corner.transposeOccurrence.omitted ≠ Fin.last (d + 1)) := by
  -- Both corner constructors retain the endpoint omission of the exchanged
  -- active occurrence.
  cases hnormal : corner.normal with
  | inl lower =>
      rw [ExtremeCornerBoundaryFaceOccurrence.transposeOccurrence, hnormal,
        Sum.elim_inl,
        corner.occurrence.extremeTopMate_omitted]
      exact corner.occurrence.exchangedActiveOccurrence_endpoint lower.1.1
  | inr upper =>
      rw [ExtremeCornerBoundaryFaceOccurrence.transposeOccurrence, hnormal,
        Sum.elim_inr,
        corner.occurrence.extremeBottomMate_omitted]
      exact corner.occurrence.exchangedActiveOccurrence_endpoint upper.1.1

/-- Helper for Theorem 57.6: package the transposed corner as an endpoint
occurrence for the next normalization step. -/
def ExtremeCornerBoundaryFaceOccurrence.transpose
    {d m : ℕ} (corner : ExtremeCornerBoundaryFaceOccurrence d m) :
    EndpointBoundaryFaceOccurrence (d + 1) m :=
  ⟨corner.transposeOccurrence, corner.transposeOccurrence_endpoint⟩

/-- Helper for Theorem 57.6: transposing an extreme corner preserves its
unordered ridge. -/
theorem ExtremeCornerBoundaryFaceOccurrence.transpose_ridgeVertexSet
    {d m : ℕ} (corner : ExtremeCornerBoundaryFaceOccurrence d m) :
    corner.transpose.1.ridgeVertexSet = corner.occurrence.1.ridgeVertexSet := by
  -- Select the stored normal form and invoke the corresponding directed
  -- corner-ridge computation.
  cases hnormal : corner.normal with
  | inl lower =>
      have hoccurrenceNormal :
          corner.occurrence.normalForm = Sum.inl lower.1 := by
        simpa only [hnormal, Sum.map_inl] using corner.normal_eq
      simpa only [ExtremeCornerBoundaryFaceOccurrence.transpose,
        ExtremeCornerBoundaryFaceOccurrence.transposeOccurrence, hnormal,
        Sum.elim_inl] using
        corner.occurrence.extremeTopMate_ridgeVertexSet lower.1
          hoccurrenceNormal lower.2
  | inr upper =>
      have hoccurrenceNormal :
          corner.occurrence.normalForm = Sum.inr upper.1 := by
        simpa only [hnormal, Sum.map_inr] using corner.normal_eq
      simpa only [ExtremeCornerBoundaryFaceOccurrence.transpose,
        ExtremeCornerBoundaryFaceOccurrence.transposeOccurrence, hnormal,
        Sum.elim_inr] using
        corner.occurrence.extremeBottomMate_ridgeVertexSet upper.1
          hoccurrenceNormal upper.2

end StandardSphere.CubicalTucker
