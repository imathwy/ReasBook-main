module

public import Topology_Munkres_2000.Book.Theorem_57_6.BoundaryRidgePivot

public section

noncomputable section

namespace StandardSphere.CubicalTucker

/-- Helper for Theorem 57.6: the active coordinate occupying a nonzero rank
in a shared facet's leading order. -/
def SharedFacet.activeCoordinate {d m : ℕ} (facet : SharedFacet d m)
    (rank : Fin d) : Fin (d + 1) :=
  Equiv.swap 0 facet.fixed rank.succ

/-- Helper for Theorem 57.6: the active-coordinate map is the standard
transposition applied to a successor rank. -/
theorem SharedFacet.activeCoordinate_eq_swap {d m : ℕ}
    (facet : SharedFacet d m) (rank : Fin d) :
    facet.activeCoordinate rank = Equiv.swap 0 facet.fixed rank.succ := by
  -- Expose the defining formula for downstream coordinate transports.
  rfl

/-- Helper for Theorem 57.6: every shared-facet vertex has the stored level
at its distinguished coordinate. -/
theorem SharedFacet.vertex_fixed {d m : ℕ} (facet : SharedFacet d m)
    (j : Fin (d + 1)) : facet.vertex j facet.fixed = facet.level := by
  -- Evaluate the fixed branch of the canonical vertex formula.
  apply Fin.ext
  rw [facet.vertex_value]
  simp only [if_pos]

/-- Helper for Theorem 57.6: an active coordinate is never the distinguished
fixed coordinate. -/
theorem SharedFacet.activeCoordinate_ne_fixed {d m : ℕ}
    (facet : SharedFacet d m) (rank : Fin d) :
    facet.activeCoordinate rank ≠ facet.fixed := by
  -- Cancel the defining transposition and separate a successor from zero.
  intro hfixed
  have hzero : Equiv.swap 0 facet.fixed 0 = facet.fixed :=
    Equiv.swap_apply_left 0 facet.fixed
  have hsuccZero : rank.succ = 0 :=
    (Equiv.swap 0 facet.fixed).injective (hfixed.trans hzero.symm)
  exact Fin.succ_ne_zero rank hsuccZero

/-- Helper for Theorem 57.6: the active-coordinate transposition identifies
nonzero ranks with ambient coordinates other than the fixed one. -/
theorem SharedFacet.activeCoordinateComplement_iff {d m : ℕ}
    (facet : SharedFacet d m) (i : Fin (d + 1)) :
    i ≠ 0 ↔ Equiv.swap 0 facet.fixed i ≠ facet.fixed := by
  -- Transport equality through the injective transposition and evaluate zero.
  constructor
  · intro hi hfixed
    apply hi
    apply (Equiv.swap 0 facet.fixed).injective
    exact hfixed.trans (Equiv.swap_apply_left 0 facet.fixed).symm
  · intro hi hzero
    apply hi
    rw [hzero, Equiv.swap_apply_left]

/-- Helper for Theorem 57.6: active ranks are canonically equivalent to the
ambient coordinates complementary to a shared facet's fixed coordinate. -/
def SharedFacet.activeCoordinateEquiv {d m : ℕ}
    (facet : SharedFacet d m) :
    Fin d ≃ {i : Fin (d + 1) // i ≠ facet.fixed} :=
  (finSuccAboveEquiv 0).trans
    (Equiv.subtypeEquiv (Equiv.swap 0 facet.fixed)
      facet.activeCoordinateComplement_iff)

/-- Helper for Theorem 57.6: the active-coordinate equivalence has the same
ambient value as the explicit active-coordinate map. -/
theorem SharedFacet.activeCoordinateEquiv_apply {d m : ℕ}
    (facet : SharedFacet d m) (rank : Fin d) :
    (facet.activeCoordinateEquiv rank).1 = facet.activeCoordinate rank := by
  -- Both complement equivalences compute to the same transposed successor.
  rfl

/-- Helper for Theorem 57.6: replace a shared facet's active staircase while
retaining its fixed coordinate and level. -/
def SharedFacet.withActiveStaircase {d m : ℕ}
    (facet : SharedFacet (d + 1) m)
    (staircase : ElementaryStaircase (d + 1) m) : SharedFacet (d + 1) m :=
  { fixed := facet.fixed
    level := facet.level
    corner := fun i ↦ if hi : i = facet.fixed then facet.corner i
      else staircase.corner (facet.activeCoordinateEquiv.symm ⟨i, hi⟩)
    activeOrder := staircase.order }

/-- Helper for Theorem 57.6: active replacement retains the distinguished
fixed coordinate. -/
theorem SharedFacet.withActiveStaircase_fixed {d m : ℕ}
    (facet : SharedFacet (d + 1) m)
    (staircase : ElementaryStaircase (d + 1) m) :
    (facet.withActiveStaircase staircase).fixed = facet.fixed := by
  -- Project the unchanged fixed-coordinate field.
  rfl

/-- Helper for Theorem 57.6: active replacement retains the stored fixed
level. -/
theorem SharedFacet.withActiveStaircase_level {d m : ℕ}
    (facet : SharedFacet (d + 1) m)
    (staircase : ElementaryStaircase (d + 1) m) :
    (facet.withActiveStaircase staircase).level = facet.level := by
  -- Project the unchanged level field.
  rfl

/-- Helper for Theorem 57.6: active replacement preserves the normalized
fixed-corner value. -/
theorem SharedFacet.withActiveStaircase_corner_fixed {d m : ℕ}
    (facet : SharedFacet (d + 1) m)
    (staircase : ElementaryStaircase (d + 1) m) :
    (facet.withActiveStaircase staircase).corner facet.fixed =
      facet.corner facet.fixed := by
  -- The distinguished coordinate selects the retained-corner branch.
  simp only [SharedFacet.withActiveStaircase, dite_true]

/-- Helper for Theorem 57.6: active replacement preserves a normalized
shared facet's normalization certificate. -/
theorem SharedFacet.withActiveStaircase_normalized {d m : ℕ}
    (facet : NormalizedSharedFacet (d + 1) m)
    (staircase : ElementaryStaircase (d + 1) m) :
    ((facet.1.withActiveStaircase staircase).corner
      (facet.1.withActiveStaircase staircase).fixed).1 = 0 := by
  -- Rewrite the retained fixed coordinate and use the original certificate.
  change ((facet.1.withActiveStaircase staircase).corner facet.1.fixed).1 = 0
  rw [facet.1.withActiveStaircase_corner_fixed staircase]
  exact facet.2

/-- Helper for Theorem 57.6: active replacement does not change the ambient
coordinate represented by an active rank. -/
theorem SharedFacet.withActiveStaircase_activeCoordinate {d m : ℕ}
    (facet : SharedFacet (d + 1) m)
    (staircase : ElementaryStaircase (d + 1) m) (rank : Fin (d + 1)) :
    (facet.withActiveStaircase staircase).activeCoordinate rank =
      facet.activeCoordinate rank := by
  -- The active-coordinate formula depends only on the retained fixed coordinate.
  rfl

/-- Helper for Theorem 57.6: compress a shared facet to the elementary
staircase on its active coordinates. -/
def SharedFacet.activeStaircase {d m : ℕ} (facet : SharedFacet d m) :
    ElementaryStaircase d m :=
  { corner := fun rank ↦ facet.corner (facet.activeCoordinate rank)
    order := facet.activeOrder }

/-- Helper for Theorem 57.6: active-staircase compression preserves every
shared-facet vertex after projection to the active coordinates. -/
theorem SharedFacet.activeStaircase_vertex {d m : ℕ}
    (facet : SharedFacet d m) (j : Fin (d + 1)) :
    facet.activeStaircase.vertex j =
      fun rank ↦ facet.vertex j (facet.activeCoordinate rank) := by
  -- Compare the common corner and align the leading-order successor rank.
  funext rank
  apply Fin.ext
  rw [ElementaryStaircase.vertex_value, facet.vertex_value]
  simp only [SharedFacet.activeStaircase,
    facet.activeCoordinate_ne_fixed rank, if_false]
  have hrank :
      facet.leadingOrder.symm (facet.activeCoordinate rank) =
        (facet.activeOrder.symm rank).succ := by
    apply facet.leadingOrder.injective
    rw [facet.leadingOrder.apply_symm_apply, facet.leadingOrder_succ]
    simp only [SharedFacet.activeCoordinate, Equiv.apply_symm_apply]
  rw [hrank]
  simp only [Fin.val_succ]
  split_ifs <;> omega

/-- Helper for Theorem 57.6: active compression after replacing an active
staircase recovers the replacement staircase. -/
theorem SharedFacet.activeStaircase_withActiveStaircase {d m : ℕ}
    (facet : SharedFacet (d + 1) m)
    (staircase : ElementaryStaircase (d + 1) m) :
    (facet.withActiveStaircase staircase).activeStaircase = staircase := by
  -- Compare the replacement corner and order on every active rank.
  apply congrArg₂ ElementaryStaircase.mk
  · funext rank
    rw [facet.withActiveStaircase_activeCoordinate staircase rank]
    simp only [SharedFacet.withActiveStaircase]
    rw [dif_neg (facet.activeCoordinate_ne_fixed rank)]
    apply congrArg staircase.corner
    apply facet.activeCoordinateEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext (facet.activeCoordinateEquiv_apply rank).symm
  · rfl

/-- Helper for Theorem 57.6: replacing a normalized facet's active staircase
produces another normalized facet. -/
def SharedFacet.normalizedWithActiveStaircase {d m : ℕ}
    (facet : NormalizedSharedFacet (d + 1) m)
    (staircase : ElementaryStaircase (d + 1) m) :
    NormalizedSharedFacet (d + 1) m :=
  ⟨facet.1.withActiveStaircase staircase,
    SharedFacet.withActiveStaircase_normalized facet staircase⟩

/-- Helper for Theorem 57.6: replacing the active staircase preserves each
fixed-coordinate vertex value. -/
theorem SharedFacet.withActiveStaircase_vertex_fixed {d m : ℕ}
    (facet : SharedFacet (d + 1) m)
    (staircase : ElementaryStaircase (d + 1) m) (j : Fin (d + 2)) :
    (facet.withActiveStaircase staircase).vertex j facet.fixed =
      facet.vertex j facet.fixed := by
  -- Both vertex formulas use the unchanged fixed level.
  apply Fin.ext
  rw [(facet.withActiveStaircase staircase).vertex_value, facet.vertex_value]
  simp only [SharedFacet.withActiveStaircase, if_pos]

/-- Helper for Theorem 57.6: active replacement makes the supplied staircase
the active-coordinate projection of the new facet. -/
theorem SharedFacet.withActiveStaircase_vertex_activeCoordinate {d m : ℕ}
    (facet : SharedFacet (d + 1) m)
    (staircase : ElementaryStaircase (d + 1) m)
    (j : Fin (d + 2)) (rank : Fin (d + 1)) :
    (facet.withActiveStaircase staircase).vertex j
        (facet.activeCoordinate rank) = staircase.vertex j rank := by
  -- Pass through active compression, whose replacement computation is exact.
  calc
    (facet.withActiveStaircase staircase).vertex j
          (facet.activeCoordinate rank) =
        (facet.withActiveStaircase staircase).vertex j
          ((facet.withActiveStaircase staircase).activeCoordinate rank) :=
      congrArg ((facet.withActiveStaircase staircase).vertex j)
        (facet.withActiveStaircase_activeCoordinate staircase rank).symm
    _ = (facet.withActiveStaircase staircase).activeStaircase.vertex j rank :=
      (congrFun
        ((facet.withActiveStaircase staircase).activeStaircase_vertex j)
        rank).symm
    _ = staircase.vertex j rank :=
      congrArg (fun active ↦ active.vertex j rank)
        (facet.activeStaircase_withActiveStaircase staircase)

/-- Helper for Theorem 57.6: replace a boundary facet's active staircase
without changing its top-or-bottom boundary tag. -/
def BoundarySharedFacet.withActiveStaircase {d m : ℕ}
    (facet : BoundarySharedFacet (d + 1) m)
    (staircase : ElementaryStaircase (d + 1) m) :
    BoundarySharedFacet (d + 1) m :=
  match facet with
  | Sum.inl top => Sum.inl
      ⟨SharedFacet.normalizedWithActiveStaircase top.1 staircase, top.2⟩
  | Sum.inr bottom => Sum.inr
      ⟨SharedFacet.normalizedWithActiveStaircase bottom.1 staircase, bottom.2⟩

/-- Helper for Theorem 57.6: boundary active replacement preserves every
fixed-coordinate vertex value. -/
theorem BoundarySharedFacet.withActiveStaircase_vertex_fixed {d m : ℕ}
    (facet : BoundarySharedFacet (d + 1) m)
    (staircase : ElementaryStaircase (d + 1) m) (j : Fin (d + 2)) :
    (facet.withActiveStaircase staircase).vertex j
        facet.normalizedFacet.1.fixed =
      facet.vertex j facet.normalizedFacet.1.fixed := by
  -- Remove the boundary tag and use the raw fixed-coordinate computation.
  cases facet with
  | inl top =>
      simpa only [BoundarySharedFacet.withActiveStaircase,
        BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.normalizedFacet_inl,
        SharedFacet.normalizedWithActiveStaircase] using
        top.1.1.withActiveStaircase_vertex_fixed staircase j
  | inr bottom =>
      simpa only [BoundarySharedFacet.withActiveStaircase,
        BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.normalizedFacet_inr,
        SharedFacet.normalizedWithActiveStaircase] using
        bottom.1.1.withActiveStaircase_vertex_fixed staircase j

/-- Helper for Theorem 57.6: boundary active replacement makes the supplied
staircase the active-coordinate projection of the new facet. -/
theorem BoundarySharedFacet.withActiveStaircase_vertex_activeCoordinate
    {d m : ℕ} (facet : BoundarySharedFacet (d + 1) m)
    (staircase : ElementaryStaircase (d + 1) m)
    (j : Fin (d + 2)) (rank : Fin (d + 1)) :
    (facet.withActiveStaircase staircase).vertex j
        (facet.normalizedFacet.1.activeCoordinate rank) =
      staircase.vertex j rank := by
  -- Remove the boundary tag and use the raw active-coordinate computation.
  cases facet with
  | inl top =>
      simpa only [BoundarySharedFacet.withActiveStaircase,
        BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.normalizedFacet_inl,
        SharedFacet.normalizedWithActiveStaircase] using
        top.1.1.withActiveStaircase_vertex_activeCoordinate staircase j rank
  | inr bottom =>
      simpa only [BoundarySharedFacet.withActiveStaircase,
        BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.normalizedFacet_inr,
        SharedFacet.normalizedWithActiveStaircase] using
        bottom.1.1.withActiveStaircase_vertex_activeCoordinate staircase j rank

/-- Helper for Theorem 57.6: active compression of a replaced boundary facet
recovers the replacement staircase. -/
theorem BoundarySharedFacet.activeStaircase_withActiveStaircase
    {d m : ℕ} (facet : BoundarySharedFacet (d + 1) m)
    (staircase : ElementaryStaircase (d + 1) m) :
    (facet.withActiveStaircase staircase).normalizedFacet.1.activeStaircase =
      staircase := by
  -- Remove the boundary tag and apply raw active-compression recovery.
  cases facet with
  | inl top =>
      simpa only [BoundarySharedFacet.withActiveStaircase,
        BoundarySharedFacet.normalizedFacet_inl,
        SharedFacet.normalizedWithActiveStaircase] using
        top.1.1.activeStaircase_withActiveStaircase staircase
  | inr bottom =>
      simpa only [BoundarySharedFacet.withActiveStaircase,
        BoundarySharedFacet.normalizedFacet_inr,
        SharedFacet.normalizedWithActiveStaircase] using
        bottom.1.1.activeStaircase_withActiveStaircase staircase

/-- Helper for Theorem 57.6: a boundary facet's fixed coordinate has the same
value at every vertex. -/
theorem BoundarySharedFacet.vertex_fixed_eq {d m : ℕ}
    (facet : BoundarySharedFacet (d + 1) m) (j k : Fin (d + 2)) :
    facet.vertex j facet.normalizedFacet.1.fixed =
      facet.vertex k facet.normalizedFacet.1.fixed := by
  -- On either boundary side the fixed branch is the unchanged stored level.
  cases facet with
  | inl top =>
      apply Fin.ext
      rw [BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.normalizedFacet_inl,
        top.1.1.vertex_value, top.1.1.vertex_value]
      simp only [if_pos]
  | inr bottom =>
      apply Fin.ext
      rw [BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.normalizedFacet_inr,
        bottom.1.1.vertex_value, bottom.1.1.vertex_value]
      simp only [if_pos]

/-- Helper for Theorem 57.6: endpoint ambient boundary-face occurrences are
exactly those whose omitted position is not internal. -/
abbrev EndpointBoundaryFaceOccurrence (d m : ℕ) :=
  {occurrence : BoundaryFaceOccurrence d m //
    ¬(occurrence.omitted ≠ 0 ∧ occurrence.omitted ≠ Fin.last d)}

/-- Helper for Theorem 57.6: an endpoint boundary-face occurrence omits the
initial or final staircase vertex. -/
theorem EndpointBoundaryFaceOccurrence.omitted_eq_zero_or_last
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence d m) :
    occurrence.1.omitted = 0 ∨ occurrence.1.omitted = Fin.last d := by
  -- Eliminate the internal alternative from the finite endpoint dichotomy.
  by_cases hzero : occurrence.1.omitted = 0
  · exact Or.inl hzero
  · right
    by_contra hlast
    exact occurrence.2 ⟨hzero, hlast⟩

/-- Helper for Theorem 57.6: every retained vertex of a boundary-face
occurrence has the boundary facet's stored level at its fixed coordinate. -/
theorem BoundaryFaceOccurrence.vertex_fixed {d m : ℕ}
    (occurrence : BoundaryFaceOccurrence d m) (j : Fin d) :
    occurrence.vertex j occurrence.facet.normalizedFacet.1.fixed =
      occurrence.facet.normalizedFacet.1.level := by
  -- Rewrite to the ambient facet vertex and evaluate its fixed coordinate.
  rw [occurrence.vertex_eq_facetVertex,
    occurrence.facet.vertex_eq_normalizedFacet]
  exact occurrence.facet.normalizedFacet.1.vertex_fixed _

/-- Helper for Theorem 57.6: compress an endpoint boundary-face occurrence
to the endpoint occurrence of its active elementary staircase. -/
def EndpointBoundaryFaceOccurrence.activeOccurrence {d m : ℕ}
    (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m) :
    EndpointStaircaseFaceOccurrence d m :=
  ⟨⟨occurrence.1.facet.normalizedFacet.1.activeStaircase,
      occurrence.1.omitted⟩, occurrence.2⟩

/-- Helper for Theorem 57.6: active compression stores exactly the boundary
facet's active staircase. -/
theorem EndpointBoundaryFaceOccurrence.activeOccurrence_simplex
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m) :
    occurrence.activeOccurrence.1.simplex =
      occurrence.1.facet.normalizedFacet.1.activeStaircase := by
  -- Project the simplex field of active compression.
  rfl

/-- Helper for Theorem 57.6: active compression retains the ambient omitted
position. -/
theorem EndpointBoundaryFaceOccurrence.activeOccurrence_omitted
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m) :
    occurrence.activeOccurrence.1.omitted = occurrence.1.omitted := by
  -- Project the omitted field of active compression.
  rfl

/-- Helper for Theorem 57.6: active compression preserves every retained
ridge vertex after projecting away the boundary facet's fixed coordinate. -/
theorem EndpointBoundaryFaceOccurrence.activeOccurrence_vertex
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (j rank : Fin (d + 1)) :
    occurrence.activeOccurrence.1.vertex j rank =
      occurrence.1.vertex j
        (occurrence.1.facet.normalizedFacet.1.activeCoordinate rank) := by
  -- First use active-staircase compression at the retained simplex position.
  rw [EndpointBoundaryFaceOccurrence.activeOccurrence,
    StaircaseFaceOccurrence.mk_vertex, occurrence.1.vertex_eq_facetVertex]
  rw [occurrence.1.facet.vertex_eq_normalizedFacet]
  exact congrFun
    (occurrence.1.facet.normalizedFacet.1.activeStaircase_vertex
      (occurrence.1.omitted.succAbove j)) rank

/-- Helper for Theorem 57.6: lift a compressed staircase-face occurrence to
the original ambient boundary side. -/
def EndpointBoundaryFaceOccurrence.liftActiveOccurrence {d m : ℕ}
    (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (active : StaircaseFaceOccurrence (d + 1) m) :
    BoundaryFaceOccurrence (d + 1) m :=
  ⟨occurrence.1.facet.withActiveStaircase active.simplex, active.omitted⟩

/-- Helper for Theorem 57.6: lift a compressed endpoint occurrence while
retaining its endpoint certificate. -/
def EndpointBoundaryFaceOccurrence.liftActiveEndpointOccurrence
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (active : EndpointStaircaseFaceOccurrence d m) :
    EndpointBoundaryFaceOccurrence (d + 1) m :=
  ⟨occurrence.liftActiveOccurrence active.1, active.2⟩

/-- Helper for Theorem 57.6: compressing a lifted endpoint occurrence returns
the endpoint occurrence that was lifted. -/
theorem EndpointBoundaryFaceOccurrence.activeOccurrence_liftActiveEndpoint
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (active : EndpointStaircaseFaceOccurrence d m) :
    (occurrence.liftActiveEndpointOccurrence active).activeOccurrence = active := by
  -- The lifted facet compresses to the supplied simplex and retains its omission.
  apply Subtype.ext
  rw [← active.1.mk_eq_self]
  exact congrArg₂ StaircaseFaceOccurrence.mk
    (occurrence.1.facet.activeStaircase_withActiveStaircase active.1.simplex) rfl

/-- Helper for Theorem 57.6: a lifted compressed occurrence with the original
compressed vertices preserves every ambient retained vertex. -/
theorem EndpointBoundaryFaceOccurrence.liftActiveOccurrence_vertex
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (active : StaircaseFaceOccurrence (d + 1) m)
    (hvertex : active.vertex = occurrence.activeOccurrence.1.vertex)
    (j : Fin (d + 1)) :
    (occurrence.liftActiveOccurrence active).vertex j =
      occurrence.1.vertex j := by
  -- The fixed coordinate is constant; every other coordinate has a unique active rank.
  funext i
  by_cases hi : i = occurrence.1.facet.normalizedFacet.1.fixed
  · subst i
    calc
      (occurrence.liftActiveOccurrence active).vertex j
            occurrence.1.facet.normalizedFacet.1.fixed =
          occurrence.1.facet.vertex (active.omitted.succAbove j)
            occurrence.1.facet.normalizedFacet.1.fixed :=
        by
          rw [(occurrence.liftActiveOccurrence active).vertex_eq_facetVertex]
          exact occurrence.1.facet.withActiveStaircase_vertex_fixed active.simplex
            (active.omitted.succAbove j)
      _ = occurrence.1.facet.vertex
            (occurrence.1.omitted.succAbove j)
            occurrence.1.facet.normalizedFacet.1.fixed :=
        occurrence.1.facet.vertex_fixed_eq _ _
      _ = occurrence.1.vertex j
            occurrence.1.facet.normalizedFacet.1.fixed :=
        congrArg
          (fun vertex : CenteredGrid (d + 2) m ↦
            vertex occurrence.1.facet.normalizedFacet.1.fixed)
          (occurrence.1.vertex_eq_facetVertex j).symm
  · let rank : Fin (d + 1) :=
      occurrence.1.facet.normalizedFacet.1.activeCoordinateEquiv.symm ⟨i, hi⟩
    have hrank :
        occurrence.1.facet.normalizedFacet.1.activeCoordinate rank = i := by
      calc
        occurrence.1.facet.normalizedFacet.1.activeCoordinate rank =
            (occurrence.1.facet.normalizedFacet.1.activeCoordinateEquiv rank).1 :=
          (occurrence.1.facet.normalizedFacet.1.activeCoordinateEquiv_apply rank).symm
        _ = i := congrArg Subtype.val
          (Equiv.apply_symm_apply
            occurrence.1.facet.normalizedFacet.1.activeCoordinateEquiv ⟨i, hi⟩)
    calc
      (occurrence.liftActiveOccurrence active).vertex j i =
          (occurrence.liftActiveOccurrence active).vertex j
            (occurrence.1.facet.normalizedFacet.1.activeCoordinate rank) :=
        congrArg ((occurrence.liftActiveOccurrence active).vertex j) hrank.symm
      _ = active.simplex.vertex (active.omitted.succAbove j) rank :=
        by
          rw [(occurrence.liftActiveOccurrence active).vertex_eq_facetVertex]
          exact occurrence.1.facet.withActiveStaircase_vertex_activeCoordinate
            active.simplex (active.omitted.succAbove j) rank
      _ = (StaircaseFaceOccurrence.mk active.simplex active.omitted).vertex j
            rank :=
        congrArg (fun vertex ↦ vertex rank)
          (StaircaseFaceOccurrence.mk_vertex active.simplex active.omitted j).symm
      _ = active.vertex j rank :=
        congrArg (fun face ↦ face.vertex j rank) active.mk_eq_self
      _ = occurrence.activeOccurrence.1.vertex j rank :=
        congrArg (fun vertex ↦ vertex j rank) hvertex
      _ = occurrence.1.vertex j
            (occurrence.1.facet.normalizedFacet.1.activeCoordinate rank) :=
        occurrence.activeOccurrence_vertex j rank
      _ = occurrence.1.vertex j i :=
        congrArg (occurrence.1.vertex j) hrank

/-- Helper for Theorem 57.6: equality of compressed vertex enumerations lifts
to equality of the ambient unordered ridge. -/
theorem EndpointBoundaryFaceOccurrence.liftActiveOccurrence_preserves_ridge
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (active : StaircaseFaceOccurrence (d + 1) m)
    (hvertex : active.vertex = occurrence.activeOccurrence.1.vertex) :
    (occurrence.liftActiveOccurrence active).ridgeVertexSet =
      occurrence.1.ridgeVertexSet := by
  -- Lift the pointwise ambient computation through the two finite images.
  rw [(occurrence.liftActiveOccurrence active).ridgeVertexSet_eq_vertexImage,
    occurrence.1.ridgeVertexSet_eq_vertexImage]
  apply Finset.image_congr
  intro j _
  exact occurrence.liftActiveOccurrence_vertex active hvertex j

/-- Helper for Theorem 57.6: normalize a compressed endpoint ridge into its
lower or upper shared-facet presentation. -/
def EndpointBoundaryFaceOccurrence.normalForm {d m : ℕ}
    (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m) :
    PositiveNormalizedSharedFacet d m ⊕ BelowTopNormalizedSharedFacet d m :=
  endpointStaircaseFaceEquiv d m occurrence.activeOccurrence

/-- Helper for Theorem 57.6: endpoint normalization is the canonical
endpoint-occurrence equivalence applied to active compression. -/
theorem EndpointBoundaryFaceOccurrence.normalForm_eq
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m) :
    occurrence.normalForm =
      endpointStaircaseFaceEquiv d m occurrence.activeOccurrence := by
  -- Expose the owner definition as a directed proposition.
  rfl

/-- Helper for Theorem 57.6: the endpoint normal form enumerates precisely the
active-coordinate projection of the original ambient ridge. -/
theorem EndpointBoundaryFaceOccurrence.normalForm_vertex
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (j rank : Fin (d + 1)) :
    Sum.elim (fun facet ↦ facet.1.1.vertex)
        (fun facet ↦ facet.1.1.vertex) occurrence.normalForm j rank =
      occurrence.1.vertex j
        (occurrence.1.facet.normalizedFacet.1.activeCoordinate rank) := by
  -- Compose the endpoint-equivalence computation with active compression.
  calc
    Sum.elim (fun facet ↦ facet.1.1.vertex)
          (fun facet ↦ facet.1.1.vertex) occurrence.normalForm j rank =
        occurrence.activeOccurrence.1.vertex j rank := by
      exact congrArg (fun vertex ↦ vertex j rank)
        (endpointStaircaseFaceEquiv_vertex occurrence.activeOccurrence).symm
    _ = occurrence.1.vertex j
          (occurrence.1.facet.normalizedFacet.1.activeCoordinate rank) :=
      occurrence.activeOccurrence_vertex j rank

/-- Helper for Theorem 57.6: every endpoint normal form either has an
adjacent opposite side or is one of the two extreme coordinate corners. -/
theorem EndpointBoundaryFaceOccurrence.normalForm_interior_or_corner
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m) :
    (∃ lower : PositiveNormalizedSharedFacet d m,
      occurrence.normalForm = Sum.inl lower ∧ lower.1.1.level.1 < 2 * m) ∨
    (∃ upper : BelowTopNormalizedSharedFacet d m,
      occurrence.normalForm = Sum.inr upper ∧ 0 < upper.1.1.level.1) ∨
    (∃ lower : PositiveNormalizedSharedFacet d m,
      occurrence.normalForm = Sum.inl lower ∧ lower.1.1.level.1 = 2 * m) ∨
    (∃ upper : BelowTopNormalizedSharedFacet d m,
      occurrence.normalForm = Sum.inr upper ∧ upper.1.1.level.1 = 0) := by
  -- Split by side, then compare its level with the only missing endpoint.
  cases hnormal : occurrence.normalForm with
  | inl lower =>
      by_cases htop : lower.1.1.level.1 = 2 * m
      · exact Or.inr (Or.inr (Or.inl ⟨lower, rfl, htop⟩))
      · left
        refine ⟨lower, rfl, ?_⟩
        omega
  | inr upper =>
      by_cases hbottom : upper.1.1.level.1 = 0
      · exact Or.inr (Or.inr (Or.inr ⟨upper, rfl, hbottom⟩))
      · exact Or.inr (Or.inl ⟨upper, rfl, Nat.pos_of_ne_zero hbottom⟩)

/-- Helper for Theorem 57.6: every endpoint occurrence whose normal form has
an adjacent cube on the opposite side has a distinct ambient mate. -/
theorem EndpointBoundaryFaceOccurrence.exists_distinct_mate_of_interior
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (hinterior : Sum.elim
      (fun lower : PositiveNormalizedSharedFacet d m ↦
        lower.1.1.level.1 < 2 * m)
      (fun upper : BelowTopNormalizedSharedFacet d m ↦
        0 < upper.1.1.level.1) occurrence.normalForm) :
    ∃ mate : BoundaryFaceOccurrence (d + 1) m,
      mate ≠ occurrence.1 ∧ mate.ridgeVertexSet = occurrence.1.ridgeVertexSet := by
  -- Choose the opposite normalized side and lift its endpoint occurrence.
  cases hnormal : occurrence.normalForm with
  | inl lower =>
      have hupper : lower.1.1.level.1 < 2 * m := by
        simpa only [hnormal, Sum.elim_inl] using hinterior
      let upper : BelowTopNormalizedSharedFacet d m := ⟨lower.1, hupper⟩
      let opposite : EndpointStaircaseFaceOccurrence d m :=
        (endpointStaircaseFaceEquiv d m).symm (Sum.inr upper)
      have hoppositeNormal :
          endpointStaircaseFaceEquiv d m opposite = Sum.inr upper :=
        Equiv.apply_symm_apply (endpointStaircaseFaceEquiv d m) (Sum.inr upper)
      have hvertex : opposite.1.vertex = occurrence.activeOccurrence.1.vertex := by
        calc
          opposite.1.vertex = Sum.elim
              (fun facet ↦ facet.1.1.vertex)
              (fun facet ↦ facet.1.1.vertex)
              (endpointStaircaseFaceEquiv d m opposite) :=
            endpointStaircaseFaceEquiv_vertex opposite
          _ = lower.1.1.vertex := by
            simp only [hoppositeNormal, Sum.elim_inr, upper]
          _ = Sum.elim
              (fun facet ↦ facet.1.1.vertex)
              (fun facet ↦ facet.1.1.vertex) occurrence.normalForm := by
            simp only [hnormal, Sum.elim_inl]
          _ = occurrence.activeOccurrence.1.vertex :=
            (endpointStaircaseFaceEquiv_vertex occurrence.activeOccurrence).symm
      let lifted := occurrence.liftActiveEndpointOccurrence opposite
      refine ⟨lifted.1, ?_,
        occurrence.liftActiveOccurrence_preserves_ridge opposite.1 hvertex⟩
      intro heq
      have hlifted : lifted = occurrence := Subtype.ext heq
      have hactive := congrArg
        EndpointBoundaryFaceOccurrence.activeOccurrence hlifted
      rw [occurrence.activeOccurrence_liftActiveEndpoint opposite] at hactive
      have hnormalEq := congrArg (endpointStaircaseFaceEquiv d m) hactive
      have hcontradiction : Sum.inr upper = Sum.inl lower := by
        calc
          Sum.inr upper = endpointStaircaseFaceEquiv d m opposite :=
            hoppositeNormal.symm
          _ = endpointStaircaseFaceEquiv d m occurrence.activeOccurrence :=
            hnormalEq
          _ = occurrence.normalForm := rfl
          _ = Sum.inl lower := hnormal
      exact (Sum.inr_ne_inl hcontradiction).elim
  | inr upper =>
      have hlower : 0 < upper.1.1.level.1 := by
        simpa only [hnormal, Sum.elim_inr] using hinterior
      let lower : PositiveNormalizedSharedFacet d m := ⟨upper.1, hlower⟩
      let opposite : EndpointStaircaseFaceOccurrence d m :=
        (endpointStaircaseFaceEquiv d m).symm (Sum.inl lower)
      have hoppositeNormal :
          endpointStaircaseFaceEquiv d m opposite = Sum.inl lower :=
        Equiv.apply_symm_apply (endpointStaircaseFaceEquiv d m) (Sum.inl lower)
      have hvertex : opposite.1.vertex = occurrence.activeOccurrence.1.vertex := by
        calc
          opposite.1.vertex = Sum.elim
              (fun facet ↦ facet.1.1.vertex)
              (fun facet ↦ facet.1.1.vertex)
              (endpointStaircaseFaceEquiv d m opposite) :=
            endpointStaircaseFaceEquiv_vertex opposite
          _ = upper.1.1.vertex := by
            simp only [hoppositeNormal, Sum.elim_inl, lower]
          _ = Sum.elim
              (fun facet ↦ facet.1.1.vertex)
              (fun facet ↦ facet.1.1.vertex) occurrence.normalForm := by
            simp only [hnormal, Sum.elim_inr]
          _ = occurrence.activeOccurrence.1.vertex :=
            (endpointStaircaseFaceEquiv_vertex occurrence.activeOccurrence).symm
      let lifted := occurrence.liftActiveEndpointOccurrence opposite
      refine ⟨lifted.1, ?_,
        occurrence.liftActiveOccurrence_preserves_ridge opposite.1 hvertex⟩
      intro heq
      have hlifted : lifted = occurrence := Subtype.ext heq
      have hactive := congrArg
        EndpointBoundaryFaceOccurrence.activeOccurrence hlifted
      rw [occurrence.activeOccurrence_liftActiveEndpoint opposite] at hactive
      have hnormalEq := congrArg (endpointStaircaseFaceEquiv d m) hactive
      have hcontradiction : Sum.inl lower = Sum.inr upper := by
        calc
          Sum.inl lower = endpointStaircaseFaceEquiv d m opposite :=
            hoppositeNormal.symm
          _ = endpointStaircaseFaceEquiv d m occurrence.activeOccurrence :=
            hnormalEq
          _ = occurrence.normalForm := rfl
          _ = Sum.inr upper := hnormal
      exact (Sum.inl_ne_inr hcontradiction).elim

end StandardSphere.CubicalTucker
