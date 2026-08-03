module

public import Topology_Munkres_2000.Book.Theorem_57_6.BoundaryRidgeEndpoint

public section

noncomputable section

namespace StandardSphere.CubicalTucker

/-- Helper for Theorem 57.6: the existence of a shared-facet corner forces a
positive mesh radius. -/
theorem SharedFacet.meshRadius_pos {d m : ℕ} (facet : SharedFacet d m) :
    0 < m := by
  -- A stored corner coordinate inhabits `Fin (2 * m)`.
  have hcorner := (facet.corner facet.fixed).isLt
  omega

/-- Helper for Theorem 57.6: distinct active ranks determine distinct ambient
coordinates. -/
theorem SharedFacet.activeCoordinate_injective {d m : ℕ}
    (facet : SharedFacet d m) : Function.Injective facet.activeCoordinate := by
  -- Pass through the canonical complement equivalence, whose value projection
  -- is the active-coordinate map.
  intro rank₁ rank₂ heq
  apply facet.activeCoordinateEquiv.injective
  apply Subtype.ext
  rw [facet.activeCoordinateEquiv_apply, facet.activeCoordinateEquiv_apply]
  exact heq

/-- Helper for Theorem 57.6: transposing zero with a chosen fixed coordinate
carries the nonzero coordinates precisely to its complement. -/
theorem SharedFacet.activeCoordinateComplementAt_iff {d : ℕ}
    (fixed i : Fin (d + 1)) :
    i ≠ 0 ↔ Equiv.swap 0 fixed i ≠ fixed := by
  -- Reflect equality through the transposition and evaluate its image of zero.
  constructor
  · intro hi hfixed
    apply hi
    apply (Equiv.swap 0 fixed).injective
    exact hfixed.trans (Equiv.swap_apply_left 0 fixed).symm
  · intro hi hzero
    apply hi
    rw [hzero, Equiv.swap_apply_left]

/-- Helper for Theorem 57.6: the standard rank enumeration identifies the
coordinates complementary to any chosen fixed coordinate. -/
def SharedFacet.activeCoordinateEquivAt {d : ℕ} (fixed : Fin (d + 1)) :
    Fin d ≃ {i : Fin (d + 1) // i ≠ fixed} :=
  (finSuccAboveEquiv 0).trans
    (Equiv.subtypeEquiv (Equiv.swap 0 fixed)
      (SharedFacet.activeCoordinateComplementAt_iff fixed))

/-- Helper for Theorem 57.6: the fixed-coordinate complement equivalence has
the expected ambient-coordinate formula. -/
theorem SharedFacet.activeCoordinateEquivAt_apply {d : ℕ}
    (fixed : Fin (d + 1)) (rank : Fin d) :
    (SharedFacet.activeCoordinateEquivAt fixed rank).1 =
      Equiv.swap 0 fixed rank.succ := by
  -- Both complement equivalences compute directly on a successor rank.
  rfl

/-- Helper for Theorem 57.6: exchanging a facet's fixed coordinate with one
active coordinate carries the old complement to the new complement. -/
theorem SharedFacet.coordinateExchangeComplement_iff {d m : ℕ}
    (facet : SharedFacet d m) (innerFixed : Fin d) (i : Fin (d + 1)) :
    i ≠ facet.fixed ↔
      Equiv.swap facet.fixed (facet.activeCoordinate innerFixed) i ≠
        facet.activeCoordinate innerFixed := by
  -- Reflect equality through the ambient transposition at the old fixed point.
  constructor
  · intro hi hnew
    apply hi
    apply (Equiv.swap facet.fixed (facet.activeCoordinate innerFixed)).injective
    exact hnew.trans
      (Equiv.swap_apply_left facet.fixed
        (facet.activeCoordinate innerFixed)).symm
  · intro hi hold
    apply hi
    rw [hold, Equiv.swap_apply_left]

/-- Helper for Theorem 57.6: exchange active-coordinate ranks when the outer
fixed coordinate and a selected active coordinate trade roles. -/
def SharedFacet.activeCoordinateExchangeEquiv {d m : ℕ}
    (facet : SharedFacet d m) (innerFixed : Fin d) : Equiv.Perm (Fin d) :=
  facet.activeCoordinateEquiv |>.trans
    ((Equiv.subtypeEquiv
      (Equiv.swap facet.fixed (facet.activeCoordinate innerFixed))
      (facet.coordinateExchangeComplement_iff innerFixed)).trans
    (SharedFacet.activeCoordinateEquivAt
      (facet.activeCoordinate innerFixed)).symm)

/-- Helper for Theorem 57.6: the rank exchange agrees in ambient coordinates
with transposing the two distinguished coordinates. -/
theorem SharedFacet.activeCoordinateExchangeEquiv_ambient {d m : ℕ}
    (facet : SharedFacet d m) (innerFixed rank : Fin d) :
    (SharedFacet.activeCoordinateEquivAt (facet.activeCoordinate innerFixed)
      (facet.activeCoordinateExchangeEquiv innerFixed rank)).1 =
        Equiv.swap facet.fixed (facet.activeCoordinate innerFixed)
          (facet.activeCoordinate rank) := by
  -- Apply the new complement equivalence to the transported old coordinate.
  let transported :
      {i : Fin (d + 1) // i ≠ facet.activeCoordinate innerFixed} :=
    Equiv.subtypeEquiv
      (Equiv.swap facet.fixed (facet.activeCoordinate innerFixed))
      (facet.coordinateExchangeComplement_iff innerFixed)
      (facet.activeCoordinateEquiv rank)
  calc
    (SharedFacet.activeCoordinateEquivAt (facet.activeCoordinate innerFixed)
        (facet.activeCoordinateExchangeEquiv innerFixed rank)).1 =
        transported.1 := congrArg Subtype.val
      ((SharedFacet.activeCoordinateEquivAt
        (facet.activeCoordinate innerFixed)).apply_symm_apply transported)
    _ = Equiv.swap facet.fixed (facet.activeCoordinate innerFixed)
        (facet.activeCoordinate rank) := by
      simp only [transported, Equiv.subtypeEquiv_apply]
      exact congrArg
        (Equiv.swap facet.fixed (facet.activeCoordinate innerFixed))
        (facet.activeCoordinateEquiv_apply rank)

/-- Helper for Theorem 57.6: after exchanging fixed roles, the old inner
fixed rank represents the old outer fixed coordinate. -/
theorem SharedFacet.activeCoordinateExchangeEquiv_fixed_ambient {d m : ℕ}
    (facet : SharedFacet d m) (innerFixed : Fin d) :
    (SharedFacet.activeCoordinateEquivAt (facet.activeCoordinate innerFixed)
      (facet.activeCoordinateExchangeEquiv innerFixed innerFixed)).1 =
        facet.fixed := by
  -- The ambient exchange sends its right endpoint back to the left endpoint.
  rw [facet.activeCoordinateExchangeEquiv_ambient innerFixed innerFixed]
  exact Equiv.swap_apply_right facet.fixed (facet.activeCoordinate innerFixed)

/-- Helper for Theorem 57.6: every residual active coordinate is unchanged
by exchanging the two fixed roles. -/
theorem SharedFacet.activeCoordinateExchangeEquiv_residual_ambient
    {d m : ℕ} (facet : SharedFacet d m) (innerFixed rank : Fin d)
    (hrank : rank ≠ innerFixed) :
    (SharedFacet.activeCoordinateEquivAt (facet.activeCoordinate innerFixed)
      (facet.activeCoordinateExchangeEquiv innerFixed rank)).1 =
        facet.activeCoordinate rank := by
  -- A residual coordinate differs from both endpoints of the transposition.
  rw [facet.activeCoordinateExchangeEquiv_ambient innerFixed rank]
  apply Equiv.swap_apply_of_ne_of_ne
  · exact facet.activeCoordinate_ne_fixed rank
  · intro heq
    exact hrank (facet.activeCoordinate_injective heq)

/-- Helper for Theorem 57.6: outside the newly fixed coordinate, every
ambient coordinate is the old fixed coordinate or a residual active one. -/
theorem SharedFacet.exchangeCoordinate_eq_fixed_or_active {d m : ℕ}
    (facet : SharedFacet d m) (innerFixed : Fin d) {i : Fin (d + 1)}
    (hi : i ≠ facet.activeCoordinate innerFixed) :
    i = facet.fixed ∨
      ∃ rank, rank ≠ innerFixed ∧ i = facet.activeCoordinate rank := by
  -- Split off the old fixed coordinate and invert the active-coordinate map.
  by_cases hfixed : i = facet.fixed
  · exact Or.inl hfixed
  · let rank := facet.activeCoordinateEquiv.symm ⟨i, hfixed⟩
    have hrankCoordinate : facet.activeCoordinate rank = i := by
      calc
        facet.activeCoordinate rank = (facet.activeCoordinateEquiv rank).1 :=
          (facet.activeCoordinateEquiv_apply rank).symm
        _ = i := congrArg Subtype.val
          (facet.activeCoordinateEquiv.apply_symm_apply ⟨i, hfixed⟩)
    right
    refine ⟨rank, ?_, hrankCoordinate.symm⟩
    intro hrank
    apply hi
    calc
      i = facet.activeCoordinate rank := hrankCoordinate.symm
      _ = facet.activeCoordinate innerFixed := congrArg facet.activeCoordinate hrank

/-- Helper for Theorem 57.6: transport a shared facet along an ambient
coordinate permutation. -/
def SharedFacet.reindex {d m : ℕ} (facet : SharedFacet d m)
    (e : Equiv.Perm (Fin (d + 1))) : SharedFacet d m :=
  { fixed := (Equiv.Perm.decomposeFin (e * facet.leadingOrder)).1
    level := facet.level
    corner := fun i ↦ facet.corner (e.symm i)
    activeOrder := (Equiv.Perm.decomposeFin (e * facet.leadingOrder)).2 }

/-- Helper for Theorem 57.6: reindexing sends the distinguished coordinate
through the supplied permutation. -/
theorem SharedFacet.reindex_fixed {d m : ℕ} (facet : SharedFacet d m)
    (e : Equiv.Perm (Fin (d + 1))) :
    (facet.reindex e).fixed = e facet.fixed := by
  -- Recover the full order from its canonical decomposition at rank zero.
  calc
    (facet.reindex e).fixed =
        Equiv.Perm.decomposeFin.symm
          (Equiv.Perm.decomposeFin (e * facet.leadingOrder)) 0 := by
      rw [SharedFacet.reindex, Equiv.Perm.decomposeFin_symm_apply_zero]
    _ = (e * facet.leadingOrder) 0 := congrArg
      (fun order : Equiv.Perm (Fin (d + 1)) ↦ order 0)
      (Equiv.symm_apply_apply Equiv.Perm.decomposeFin
        (e * facet.leadingOrder))
    _ = e facet.fixed := by
      rw [Equiv.Perm.mul_apply, facet.leadingOrder_zero]

/-- Helper for Theorem 57.6: the full order of a reindexed facet is the
transported original full order. -/
theorem SharedFacet.reindex_leadingOrder {d m : ℕ}
    (facet : SharedFacet d m) (e : Equiv.Perm (Fin (d + 1))) :
    (facet.reindex e).leadingOrder = e * facet.leadingOrder := by
  -- Check rank zero and each successor using the decomposition equations.
  apply Equiv.ext
  intro i
  refine Fin.cases ?_ (fun rank ↦ ?_) i
  · rw [(facet.reindex e).leadingOrder_zero, facet.reindex_fixed e,
      Equiv.Perm.mul_apply, facet.leadingOrder_zero]
  · calc
      (facet.reindex e).leadingOrder rank.succ =
          Equiv.swap 0 (facet.reindex e).fixed
            ((facet.reindex e).activeOrder rank).succ :=
        (facet.reindex e).leadingOrder_succ rank
      _ = Equiv.Perm.decomposeFin.symm
          (Equiv.Perm.decomposeFin (e * facet.leadingOrder)) rank.succ := by
        rw [Equiv.Perm.decomposeFin_symm_apply_succ]
        rfl
      _ = (e * facet.leadingOrder) rank.succ := congrArg
        (fun order : Equiv.Perm (Fin (d + 1)) ↦ order rank.succ)
        (Equiv.symm_apply_apply Equiv.Perm.decomposeFin
          (e * facet.leadingOrder))

/-- Helper for Theorem 57.6: inverse full-order ranks are unchanged after
transporting both a facet and a coordinate. -/
theorem SharedFacet.reindex_leadingOrder_symm_apply {d m : ℕ}
    (facet : SharedFacet d m) (e : Equiv.Perm (Fin (d + 1)))
    (i : Fin (d + 1)) :
    (facet.reindex e).leadingOrder.symm (e i) = facet.leadingOrder.symm i := by
  -- Apply the transported order and cancel both permutations.
  rw [facet.reindex_leadingOrder e]
  apply (e * facet.leadingOrder).injective
  rw [(e * facet.leadingOrder).apply_symm_apply,
    Equiv.Perm.mul_apply, facet.leadingOrder.apply_symm_apply]

/-- Helper for Theorem 57.6: coordinate transport preserves the normalized
fixed-corner certificate. -/
theorem SharedFacet.reindex_normalized {d m : ℕ}
    (facet : NormalizedSharedFacet d m) (e : Equiv.Perm (Fin (d + 1))) :
    ((facet.1.reindex e).corner (facet.1.reindex e).fixed).1 = 0 := by
  -- Pull the transported fixed coordinate back to the original coordinate.
  rw [facet.1.reindex_fixed e]
  simp only [SharedFacet.reindex, Equiv.symm_apply_apply]
  exact facet.2

/-- Helper for Theorem 57.6: reindexing transports every canonical facet
vertex pointwise. -/
theorem SharedFacet.reindex_vertex {d m : ℕ} (facet : SharedFacet d m)
    (e : Equiv.Perm (Fin (d + 1))) (j : Fin (d + 1)) (i : Fin (d + 1)) :
    (facet.reindex e).vertex j (e i) = facet.vertex j i := by
  -- Compare fixed branches, corners, and inverse full-order ranks.
  apply Fin.ext
  rw [(facet.reindex e).vertex_value, facet.vertex_value,
    facet.reindex_fixed e, facet.reindex_leadingOrder_symm_apply e i]
  simp only [SharedFacet.reindex, Equiv.symm_apply_apply, e.injective.eq_iff]

/-- Helper for Theorem 57.6: coordinate transport of a normalized facet is
again normalized. -/
def SharedFacet.normalizedReindex {d m : ℕ}
    (facet : NormalizedSharedFacet d m) (e : Equiv.Perm (Fin (d + 1))) :
    NormalizedSharedFacet d m :=
  ⟨facet.1.reindex e, SharedFacet.reindex_normalized facet e⟩

/-- Helper for Theorem 57.6: replace only the fixed-coordinate level of a
normalized shared facet. -/
def SharedFacet.withLevel {d m : ℕ} (facet : NormalizedSharedFacet d m)
    (level : Fin (2 * m + 1)) : NormalizedSharedFacet d m :=
  ⟨{ facet.1 with level := level }, facet.2⟩

/-- Helper for Theorem 57.6: replacing a normalized facet's level preserves
its distinguished coordinate. -/
theorem SharedFacet.withLevel_fixed {d m : ℕ}
    (facet : NormalizedSharedFacet d m) (level : Fin (2 * m + 1)) :
    (SharedFacet.withLevel facet level).1.fixed = facet.1.fixed := by
  -- The record update changes only the level field.
  rfl

/-- Helper for Theorem 57.6: replacing a normalized facet's level gives that
level at every fixed-coordinate vertex. -/
theorem SharedFacet.withLevel_vertex_fixed {d m : ℕ}
    (facet : NormalizedSharedFacet d m) (level : Fin (2 * m + 1))
    (j : Fin (d + 1)) :
    (SharedFacet.withLevel facet level).1.vertex j facet.1.fixed = level := by
  -- Evaluate the fixed branch of the canonical vertex formula.
  apply Fin.ext
  rw [(SharedFacet.withLevel facet level).1.vertex_value]
  simp only [SharedFacet.withLevel, if_pos]

/-- Helper for Theorem 57.6: replacing a facet's fixed level preserves its
full coordinate order. -/
theorem SharedFacet.withLevel_leadingOrder {d m : ℕ}
    (facet : NormalizedSharedFacet d m) (level : Fin (2 * m + 1)) :
    (SharedFacet.withLevel facet level).1.leadingOrder =
      facet.1.leadingOrder := by
  -- The full order uses only the unchanged fixed coordinate and active order.
  apply Equiv.ext
  intro i
  refine Fin.cases ?_ (fun rank ↦ ?_) i
  · rw [(SharedFacet.withLevel facet level).1.leadingOrder_zero,
      facet.1.leadingOrder_zero]
    rfl
  · rw [(SharedFacet.withLevel facet level).1.leadingOrder_succ,
      facet.1.leadingOrder_succ]
    rfl

/-- Helper for Theorem 57.6: replacing a normalized facet's level leaves
every nonfixed vertex coordinate unchanged. -/
theorem SharedFacet.withLevel_vertex_of_ne {d m : ℕ}
    (facet : NormalizedSharedFacet d m) (level : Fin (2 * m + 1))
    (j : Fin (d + 1)) {i : Fin (d + 1)} (hi : i ≠ facet.1.fixed) :
    (SharedFacet.withLevel facet level).1.vertex j i = facet.1.vertex j i := by
  -- Both nonfixed branches use the same corner and full order.
  apply Fin.ext
  rw [(SharedFacet.withLevel facet level).1.vertex_value, facet.1.vertex_value]
  rw [SharedFacet.withLevel_leadingOrder]
  simp only [SharedFacet.withLevel, hi, if_false]

/-- Helper for Theorem 57.6: the exchanged inner facet transports its
coordinates and replaces its fixed level by the outer facet's level. -/
def SharedFacet.exchangedActiveFacet {d m : ℕ}
    (outer : NormalizedSharedFacet (d + 1) m)
    (inner : NormalizedSharedFacet d m) : NormalizedSharedFacet d m :=
  SharedFacet.withLevel
    (SharedFacet.normalizedReindex inner
      (outer.1.activeCoordinateExchangeEquiv inner.1.fixed)) outer.1.level

/-- Helper for Theorem 57.6: the exchanged inner facet fixes the transported
old inner fixed rank. -/
theorem SharedFacet.exchangedActiveFacet_fixed {d m : ℕ}
    (outer : NormalizedSharedFacet (d + 1) m)
    (inner : NormalizedSharedFacet d m) :
    (SharedFacet.exchangedActiveFacet outer inner).1.fixed =
      outer.1.activeCoordinateExchangeEquiv inner.1.fixed inner.1.fixed := by
  -- The level update preserves the fixed rank produced by reindexing.
  rw [SharedFacet.exchangedActiveFacet, SharedFacet.withLevel_fixed,
    SharedFacet.normalizedReindex]
  exact inner.1.reindex_fixed
    (outer.1.activeCoordinateExchangeEquiv inner.1.fixed)

/-- Helper for Theorem 57.6: the exchanged inner facet stores the old outer
facet's level. -/
theorem SharedFacet.exchangedActiveFacet_level {d m : ℕ}
    (outer : NormalizedSharedFacet (d + 1) m)
    (inner : NormalizedSharedFacet d m) :
    (SharedFacet.exchangedActiveFacet outer inner).1.level = outer.1.level := by
  -- Reindexing preserves the level before the final replacement.
  rfl

/-- Helper for Theorem 57.6: the exchanged inner facet has the outer level at
its new fixed rank. -/
theorem SharedFacet.exchangedActiveFacet_vertex_fixed {d m : ℕ}
    (outer : NormalizedSharedFacet (d + 1) m)
    (inner : NormalizedSharedFacet d m) (j : Fin (d + 1)) :
    (SharedFacet.exchangedActiveFacet outer inner).1.vertex j
        (outer.1.activeCoordinateExchangeEquiv inner.1.fixed inner.1.fixed) =
      outer.1.level := by
  -- Rewrite the exchanged fixed rank and evaluate the level update.
  rw [← SharedFacet.exchangedActiveFacet_fixed outer inner]
  exact SharedFacet.withLevel_vertex_fixed
    (SharedFacet.normalizedReindex inner
      (outer.1.activeCoordinateExchangeEquiv inner.1.fixed)) outer.1.level j

/-- Helper for Theorem 57.6: away from the exchanged fixed rank, the inner
facet's vertices are transported pointwise. -/
theorem SharedFacet.exchangedActiveFacet_vertex_exchange {d m : ℕ}
    (outer : NormalizedSharedFacet (d + 1) m)
    (inner : NormalizedSharedFacet d m) (j : Fin (d + 1))
    (rank : Fin (d + 1)) (hrank : rank ≠ inner.1.fixed) :
    (SharedFacet.exchangedActiveFacet outer inner).1.vertex j
        (outer.1.activeCoordinateExchangeEquiv inner.1.fixed rank) =
      inner.1.vertex j rank := by
  -- Remove the level update and then apply coordinate reindexing.
  have hne :
      outer.1.activeCoordinateExchangeEquiv inner.1.fixed rank ≠
        (SharedFacet.normalizedReindex inner
          (outer.1.activeCoordinateExchangeEquiv inner.1.fixed)).1.fixed := by
    rw [SharedFacet.normalizedReindex,
      inner.1.reindex_fixed
        (outer.1.activeCoordinateExchangeEquiv inner.1.fixed)]
    exact fun heq ↦ hrank
      ((outer.1.activeCoordinateExchangeEquiv inner.1.fixed).injective heq)
  calc
    (SharedFacet.exchangedActiveFacet outer inner).1.vertex j
          (outer.1.activeCoordinateExchangeEquiv inner.1.fixed rank) =
        (SharedFacet.normalizedReindex inner
          (outer.1.activeCoordinateExchangeEquiv inner.1.fixed)).1.vertex j
            (outer.1.activeCoordinateExchangeEquiv inner.1.fixed rank) :=
      SharedFacet.withLevel_vertex_of_ne
        (SharedFacet.normalizedReindex inner
          (outer.1.activeCoordinateExchangeEquiv inner.1.fixed)) outer.1.level j hne
    _ = inner.1.vertex j rank :=
      inner.1.reindex_vertex
        (outer.1.activeCoordinateExchangeEquiv inner.1.fixed) j rank

/-- Helper for Theorem 57.6: a normalized seed stores a chosen fixed
coordinate and level before an active staircase is inserted. -/
def SharedFacet.activeStaircaseSeed {d m : ℕ} (hm : 0 < m)
    (fixed : Fin (d + 2)) (level : Fin (2 * m + 1)) :
    SharedFacet (d + 1) m :=
  { fixed := fixed
    level := level
    corner := fun _ ↦ ⟨0, Nat.mul_pos (Nat.succ_pos 1) hm⟩
    activeOrder := 1 }

/-- Helper for Theorem 57.6: the seed's fixed corner is normalized. -/
theorem SharedFacet.activeStaircaseSeed_normalized {d m : ℕ}
    (hm : 0 < m) (fixed : Fin (d + 2)) (level : Fin (2 * m + 1)) :
    ((SharedFacet.activeStaircaseSeed hm fixed level).corner
      (SharedFacet.activeStaircaseSeed hm fixed level).fixed).1 = 0 := by
  -- Every seed corner is the canonical zero coordinate.
  rfl

/-- Helper for Theorem 57.6: insert an elementary staircase into the ambient
coordinates complementary to a chosen fixed coordinate. -/
def SharedFacet.fromActiveStaircase {d m : ℕ} (hm : 0 < m)
    (fixed : Fin (d + 2)) (level : Fin (2 * m + 1))
    (staircase : ElementaryStaircase (d + 1) m) :
    NormalizedSharedFacet (d + 1) m :=
  ⟨(SharedFacet.activeStaircaseSeed hm fixed level).withActiveStaircase staircase,
    SharedFacet.withActiveStaircase_normalized
      ⟨SharedFacet.activeStaircaseSeed hm fixed level,
        SharedFacet.activeStaircaseSeed_normalized hm fixed level⟩ staircase⟩

/-- Helper for Theorem 57.6: inserting an active staircase retains the chosen
fixed coordinate. -/
theorem SharedFacet.fromActiveStaircase_fixed {d m : ℕ} (hm : 0 < m)
    (fixed : Fin (d + 2)) (level : Fin (2 * m + 1))
    (staircase : ElementaryStaircase (d + 1) m) :
    (SharedFacet.fromActiveStaircase hm fixed level staircase).1.fixed =
      fixed := by
  -- Active replacement does not alter the seed's fixed coordinate.
  have hfixed :
      (SharedFacet.activeStaircaseSeed hm fixed level).fixed = fixed := rfl
  simp only [SharedFacet.fromActiveStaircase]
  rw [(SharedFacet.activeStaircaseSeed hm fixed level)
    |>.withActiveStaircase_fixed staircase]
  exact hfixed

/-- Helper for Theorem 57.6: inserting an active staircase retains the chosen
fixed-coordinate level. -/
theorem SharedFacet.fromActiveStaircase_level {d m : ℕ} (hm : 0 < m)
    (fixed : Fin (d + 2)) (level : Fin (2 * m + 1))
    (staircase : ElementaryStaircase (d + 1) m) :
    (SharedFacet.fromActiveStaircase hm fixed level staircase).1.level =
      level := by
  -- Active replacement does not alter the seed's level.
  have hlevel :
      (SharedFacet.activeStaircaseSeed hm fixed level).level = level := rfl
  simp only [SharedFacet.fromActiveStaircase]
  rw [(SharedFacet.activeStaircaseSeed hm fixed level)
    |>.withActiveStaircase_level staircase]
  exact hlevel

/-- Helper for Theorem 57.6: active compression recovers an inserted
elementary staircase exactly. -/
theorem SharedFacet.activeStaircase_fromActiveStaircase {d m : ℕ}
    (hm : 0 < m) (fixed : Fin (d + 2)) (level : Fin (2 * m + 1))
    (staircase : ElementaryStaircase (d + 1) m) :
    (SharedFacet.fromActiveStaircase hm fixed level staircase).1.activeStaircase =
      staircase := by
  -- Apply the compression rule to the normalized seed replacement.
  simp only [SharedFacet.fromActiveStaircase]
  exact (SharedFacet.activeStaircaseSeed hm fixed level)
    |>.activeStaircase_withActiveStaircase staircase

/-- Helper for Theorem 57.6: an inserted facet's active coordinates follow
the standard complement equivalence at its chosen fixed coordinate. -/
theorem SharedFacet.fromActiveStaircase_activeCoordinate {d m : ℕ}
    (hm : 0 < m) (fixed : Fin (d + 2)) (level : Fin (2 * m + 1))
    (staircase : ElementaryStaircase (d + 1) m) (rank : Fin (d + 1)) :
    (SharedFacet.fromActiveStaircase hm fixed level staircase).1.activeCoordinate rank =
      (SharedFacet.activeCoordinateEquivAt fixed rank).1 := by
  -- Both sides apply the same transposition to the successor rank.
  simp only [SharedFacet.fromActiveStaircase,
    (SharedFacet.activeStaircaseSeed hm fixed level)
      |>.withActiveStaircase_activeCoordinate staircase rank]
  simp only [SharedFacet.activeCoordinate_eq_swap,
    SharedFacet.activeCoordinateEquivAt_apply]
  have hseedFixed :
      (SharedFacet.activeStaircaseSeed hm fixed level).fixed = fixed := rfl
  rw [hseedFixed]

/-- Helper for Theorem 57.6: every vertex of an inserted facet has the chosen
level at its fixed coordinate. -/
theorem SharedFacet.fromActiveStaircase_vertex_fixed {d m : ℕ}
    (hm : 0 < m) (fixed : Fin (d + 2)) (level : Fin (2 * m + 1))
    (staircase : ElementaryStaircase (d + 1) m) (j : Fin (d + 2)) :
    (SharedFacet.fromActiveStaircase hm fixed level staircase).1.vertex j fixed =
      level := by
  -- Discard the inserted active data and evaluate the seed's fixed branch.
  have hfixed :
      (SharedFacet.activeStaircaseSeed hm fixed level).fixed = fixed := rfl
  calc
    (SharedFacet.fromActiveStaircase hm fixed level staircase).1.vertex j fixed =
        (SharedFacet.activeStaircaseSeed hm fixed level).vertex j fixed :=
      by
        rw [← hfixed]
        simp only [SharedFacet.fromActiveStaircase]
        exact (SharedFacet.activeStaircaseSeed hm fixed level)
          |>.withActiveStaircase_vertex_fixed staircase j
    _ = level := by
      apply Fin.ext
      rw [(SharedFacet.activeStaircaseSeed hm fixed level).vertex_value]
      simp only [SharedFacet.activeStaircaseSeed, if_pos]

/-- Helper for Theorem 57.6: every active-coordinate vertex of an inserted
facet is the corresponding vertex of the supplied staircase. -/
theorem SharedFacet.fromActiveStaircase_vertex_activeCoordinate
    {d m : ℕ} (hm : 0 < m) (fixed : Fin (d + 2))
    (level : Fin (2 * m + 1)) (staircase : ElementaryStaircase (d + 1) m)
    (j : Fin (d + 2)) (rank : Fin (d + 1)) :
    (SharedFacet.fromActiveStaircase hm fixed level staircase).1.vertex j
        (SharedFacet.activeCoordinateEquivAt fixed rank).1 =
      staircase.vertex j rank := by
  -- Rewrite the complement coordinate as the seed's active coordinate.
  have hcoordinate :
      (SharedFacet.activeStaircaseSeed hm fixed level).activeCoordinate rank =
        (SharedFacet.activeCoordinateEquivAt fixed rank).1 := by
    simp only [SharedFacet.activeCoordinate_eq_swap,
      SharedFacet.activeCoordinateEquivAt_apply]
    have hseedFixed :
        (SharedFacet.activeStaircaseSeed hm fixed level).fixed = fixed := rfl
    rw [hseedFixed]
  rw [← hcoordinate]
  simp only [SharedFacet.fromActiveStaircase]
  exact (SharedFacet.activeStaircaseSeed hm fixed level)
    |>.withActiveStaircase_vertex_activeCoordinate staircase j rank

/-- Helper for Theorem 57.6: a top outer facet gives the exchanged inner
facet a lower adjacent cube. -/
theorem SharedFacet.exchangedActiveFacet_level_pos_of_top {d m : ℕ}
    (outer : TopBoundaryNormalizedSharedFacet (d + 1) m)
    (inner : NormalizedSharedFacet d m) :
    0 < (SharedFacet.exchangedActiveFacet outer.1 inner).1.level.1 := by
  -- The exchanged level is the positive top grid level.
  rw [SharedFacet.exchangedActiveFacet_level, outer.2]
  have hm := inner.1.meshRadius_pos
  omega

/-- Helper for Theorem 57.6: exchanging against a top outer facet puts the
inner facet exactly at the top grid level. -/
theorem SharedFacet.exchangedActiveFacet_level_eq_top {d m : ℕ}
    (outer : TopBoundaryNormalizedSharedFacet (d + 1) m)
    (inner : NormalizedSharedFacet d m) :
    (SharedFacet.exchangedActiveFacet outer.1 inner).1.level.1 = 2 * m := by
  -- Transfer the outer facet's top-boundary certificate across the named
  -- exchanged-level equation.
  rw [SharedFacet.exchangedActiveFacet_level, outer.2]

/-- Helper for Theorem 57.6: a bottom outer facet gives the exchanged inner
facet an upper adjacent cube. -/
theorem SharedFacet.exchangedActiveFacet_level_lt_of_bottom {d m : ℕ}
    (outer : BottomBoundaryNormalizedSharedFacet (d + 1) m)
    (inner : NormalizedSharedFacet d m) :
    (SharedFacet.exchangedActiveFacet outer.1 inner).1.level.1 < 2 * m := by
  -- The exchanged level is zero and the inner facet forces positive mesh.
  rw [SharedFacet.exchangedActiveFacet_level, outer.2]
  have hm := inner.1.meshRadius_pos
  omega

/-- Helper for Theorem 57.6: exchanging against a bottom outer facet puts the
inner facet exactly at grid level zero. -/
theorem SharedFacet.exchangedActiveFacet_level_eq_zero {d m : ℕ}
    (outer : BottomBoundaryNormalizedSharedFacet (d + 1) m)
    (inner : NormalizedSharedFacet d m) :
    (SharedFacet.exchangedActiveFacet outer.1 inner).1.level.1 = 0 := by
  -- Transfer the outer facet's bottom-boundary certificate across the named
  -- exchanged-level equation.
  rw [SharedFacet.exchangedActiveFacet_level, outer.2]

/-- Helper for Theorem 57.6: present the exchanged inner facet on the side
selected by the old outer boundary tag. -/
def EndpointBoundaryFaceOccurrence.exchangedActiveOccurrence
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (inner : NormalizedSharedFacet d m) : StaircaseFaceOccurrence (d + 1) m :=
  match occurrence.1.facet with
  | Sum.inl top =>
      (SharedFacet.exchangedActiveFacet top.1 inner).1.lowerOccurrence
        (SharedFacet.exchangedActiveFacet_level_pos_of_top top inner)
  | Sum.inr bottom =>
      (SharedFacet.exchangedActiveFacet bottom.1 inner).1.upperOccurrence
        (SharedFacet.exchangedActiveFacet_level_lt_of_bottom bottom inner)

/-- Helper for Theorem 57.6: when the old outer facet is top, the exchanged
active occurrence is the canonical lower presentation. -/
theorem EndpointBoundaryFaceOccurrence.exchangedActiveOccurrence_of_facet_eq_top
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (inner : NormalizedSharedFacet d m)
    (top : TopBoundaryNormalizedSharedFacet (d + 1) m)
    (hfacet : occurrence.1.facet = Sum.inl top) :
    occurrence.exchangedActiveOccurrence inner =
      (SharedFacet.exchangedActiveFacet top.1 inner).1.lowerOccurrence
        (SharedFacet.exchangedActiveFacet_level_pos_of_top top inner) := by
  -- Select the top branch of the construction at its owner boundary.
  rw [EndpointBoundaryFaceOccurrence.exchangedActiveOccurrence, hfacet]

/-- Helper for Theorem 57.6: when the old outer facet is bottom, the exchanged
active occurrence is the canonical upper presentation. -/
theorem EndpointBoundaryFaceOccurrence.exchangedActiveOccurrence_of_facet_eq_bottom
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (inner : NormalizedSharedFacet d m)
    (bottom : BottomBoundaryNormalizedSharedFacet (d + 1) m)
    (hfacet : occurrence.1.facet = Sum.inr bottom) :
    occurrence.exchangedActiveOccurrence inner =
      (SharedFacet.exchangedActiveFacet bottom.1 inner).1.upperOccurrence
        (SharedFacet.exchangedActiveFacet_level_lt_of_bottom bottom inner) := by
  -- Select the bottom branch of the construction at its owner boundary.
  rw [EndpointBoundaryFaceOccurrence.exchangedActiveOccurrence, hfacet]

/-- Helper for Theorem 57.6: the exchanged active presentation still omits
an endpoint, irrespective of the outer boundary side. -/
theorem EndpointBoundaryFaceOccurrence.exchangedActiveOccurrence_endpoint
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (inner : NormalizedSharedFacet d m) :
    ¬((occurrence.exchangedActiveOccurrence inner).omitted ≠ 0 ∧
      (occurrence.exchangedActiveOccurrence inner).omitted ≠ Fin.last (d + 1)) := by
  -- The top branch is a lower occurrence and the bottom branch is an upper
  -- occurrence, so one endpoint inequality is impossible.
  cases hfacet : occurrence.1.facet with
  | inl top =>
      intro hinterior
      apply hinterior.1
      simp only [EndpointBoundaryFaceOccurrence.exchangedActiveOccurrence,
        hfacet, SharedFacet.lowerOccurrence_omitted]
  | inr bottom =>
      intro hinterior
      apply hinterior.2
      simp only [EndpointBoundaryFaceOccurrence.exchangedActiveOccurrence,
        hfacet, SharedFacet.upperOccurrence_omitted]

/-- Helper for Theorem 57.6: a retained occurrence vertex is its simplex
vertex at the corresponding successor-above position. -/
theorem StaircaseFaceOccurrence.vertex_eq_simplexVertex {d m : ℕ}
    (occurrence : StaircaseFaceOccurrence d m) (j : Fin d) :
    occurrence.vertex j =
      occurrence.simplex.vertex (occurrence.omitted.succAbove j) := by
  -- Rebuild the occurrence and apply its constructor computation rule.
  rw [← occurrence.mk_eq_self]
  exact StaircaseFaceOccurrence.mk_vertex _ _ j

/-- Helper for Theorem 57.6: the exchanged active occurrence enumerates the
vertices of its exchanged inner facet. -/
theorem EndpointBoundaryFaceOccurrence.exchangedActiveOccurrence_vertex
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (inner : NormalizedSharedFacet d m) (j : Fin (d + 1)) :
    (occurrence.exchangedActiveOccurrence inner).vertex j =
      (SharedFacet.exchangedActiveFacet
        occurrence.1.facet.normalizedFacet inner).1.vertex j := by
  -- Select the lower or upper computation according to the boundary tag.
  cases hfacet : occurrence.1.facet with
  | inl top =>
      simpa only [EndpointBoundaryFaceOccurrence.exchangedActiveOccurrence,
        hfacet, BoundarySharedFacet.normalizedFacet_inl] using
        (SharedFacet.exchangedActiveFacet top.1 inner).1.lowerOccurrence_vertex
          (SharedFacet.exchangedActiveFacet_level_pos_of_top top inner) j
  | inr bottom =>
      simpa only [EndpointBoundaryFaceOccurrence.exchangedActiveOccurrence,
        hfacet, BoundarySharedFacet.normalizedFacet_inr] using
        (SharedFacet.exchangedActiveFacet bottom.1 inner).1.upperOccurrence_vertex
          (SharedFacet.exchangedActiveFacet_level_lt_of_bottom bottom inner) j

/-- Helper for Theorem 57.6: rebuild an ambient normalized facet with the
inner fixed coordinate as its new outer fixed coordinate. -/
def EndpointBoundaryFaceOccurrence.extremeCornerAmbientFacet
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (inner : NormalizedSharedFacet d m) : NormalizedSharedFacet (d + 1) m :=
  SharedFacet.fromActiveStaircase inner.1.meshRadius_pos
    (occurrence.1.facet.normalizedFacet.1.activeCoordinate inner.1.fixed)
    inner.1.level (occurrence.exchangedActiveOccurrence inner).simplex

/-- Helper for Theorem 57.6: active compression of the rebuilt corner facet
recovers the exchanged active staircase inserted by its constructor. -/
theorem EndpointBoundaryFaceOccurrence.extremeCornerAmbientFacet_activeStaircase
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (inner : NormalizedSharedFacet d m) :
    (occurrence.extremeCornerAmbientFacet inner).1.activeStaircase =
      (occurrence.exchangedActiveOccurrence inner).simplex := by
  -- Apply the computation rule for insertion followed by active compression.
  exact SharedFacet.activeStaircase_fromActiveStaircase
    inner.1.meshRadius_pos
    (occurrence.1.facet.normalizedFacet.1.activeCoordinate inner.1.fixed)
    inner.1.level (occurrence.exchangedActiveOccurrence inner).simplex

/-- Helper for Theorem 57.6: the rebuilt ambient facet fixes the old inner
fixed coordinate in ambient coordinates. -/
theorem EndpointBoundaryFaceOccurrence.extremeCornerAmbientFacet_fixed
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (inner : NormalizedSharedFacet d m) :
    (occurrence.extremeCornerAmbientFacet inner).1.fixed =
      occurrence.1.facet.normalizedFacet.1.activeCoordinate inner.1.fixed := by
  -- Apply the fixed-coordinate computation for active-staircase insertion.
  exact SharedFacet.fromActiveStaircase_fixed _ _ _ _

/-- Helper for Theorem 57.6: the rebuilt ambient facet has the old inner fixed
level. -/
theorem EndpointBoundaryFaceOccurrence.extremeCornerAmbientFacet_level
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (inner : NormalizedSharedFacet d m) :
    (occurrence.extremeCornerAmbientFacet inner).1.level = inner.1.level := by
  -- Apply the level computation for active-staircase insertion.
  exact SharedFacet.fromActiveStaircase_level _ _ _ _

/-- Helper for Theorem 57.6: every rebuilt vertex has the old inner level at
the new fixed coordinate. -/
theorem EndpointBoundaryFaceOccurrence.extremeCornerAmbientFacet_vertex_fixed
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (inner : NormalizedSharedFacet d m) (k : Fin (d + 2)) :
    (occurrence.extremeCornerAmbientFacet inner).1.vertex k
        (occurrence.1.facet.normalizedFacet.1.activeCoordinate inner.1.fixed) =
      inner.1.level := by
  -- Apply the fixed-coordinate vertex computation for active insertion.
  exact SharedFacet.fromActiveStaircase_vertex_fixed _ _ _ _ _

/-- Helper for Theorem 57.6: on every new active coordinate, the rebuilt
ambient facet uses the exchanged active occurrence's simplex. -/
theorem EndpointBoundaryFaceOccurrence.extremeCornerAmbientFacet_vertex_active
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (inner : NormalizedSharedFacet d m) (k : Fin (d + 2))
    (rank : Fin (d + 1)) :
    (occurrence.extremeCornerAmbientFacet inner).1.vertex k
        (SharedFacet.activeCoordinateEquivAt
          (occurrence.1.facet.normalizedFacet.1.activeCoordinate inner.1.fixed)
          rank).1 =
      (occurrence.exchangedActiveOccurrence inner).simplex.vertex k rank := by
  -- Apply the active-coordinate vertex computation for active insertion.
  exact SharedFacet.fromActiveStaircase_vertex_activeCoordinate _ _ _ _ _ _

/-- Helper for Theorem 57.6: at the old outer fixed coordinate, the rebuilt
corner facet and original ridge have the same retained value. -/
theorem EndpointBoundaryFaceOccurrence.extremeCornerAmbientFacet_oldFixed
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (inner : NormalizedSharedFacet d m) (j : Fin (d + 1)) :
    (occurrence.extremeCornerAmbientFacet inner).1.vertex
        ((occurrence.exchangedActiveOccurrence inner).omitted.succAbove j)
        occurrence.1.facet.normalizedFacet.1.fixed =
      occurrence.1.vertex j occurrence.1.facet.normalizedFacet.1.fixed := by
  -- Follow the exchanged fixed rank through the inserted active staircase.
  calc
    (occurrence.extremeCornerAmbientFacet inner).1.vertex
          ((occurrence.exchangedActiveOccurrence inner).omitted.succAbove j)
          occurrence.1.facet.normalizedFacet.1.fixed =
        (occurrence.exchangedActiveOccurrence inner).simplex.vertex
          ((occurrence.exchangedActiveOccurrence inner).omitted.succAbove j)
          (occurrence.1.facet.normalizedFacet.1.activeCoordinateExchangeEquiv
            inner.1.fixed inner.1.fixed) := by
      rw [← occurrence.1.facet.normalizedFacet.1
        |>.activeCoordinateExchangeEquiv_fixed_ambient inner.1.fixed]
      exact occurrence.extremeCornerAmbientFacet_vertex_active inner _ _
    _ = (occurrence.exchangedActiveOccurrence inner).vertex j
        (occurrence.1.facet.normalizedFacet.1.activeCoordinateExchangeEquiv
          inner.1.fixed inner.1.fixed) :=
      congrArg
        (fun vertex ↦ vertex
          (occurrence.1.facet.normalizedFacet.1.activeCoordinateExchangeEquiv
            inner.1.fixed inner.1.fixed))
        (StaircaseFaceOccurrence.vertex_eq_simplexVertex
          (occurrence.exchangedActiveOccurrence inner) j).symm
    _ = (SharedFacet.exchangedActiveFacet
          occurrence.1.facet.normalizedFacet inner).1.vertex j
        (occurrence.1.facet.normalizedFacet.1.activeCoordinateExchangeEquiv
          inner.1.fixed inner.1.fixed) :=
      congrArg
        (fun vertex ↦ vertex
          (occurrence.1.facet.normalizedFacet.1.activeCoordinateExchangeEquiv
            inner.1.fixed inner.1.fixed))
        (occurrence.exchangedActiveOccurrence_vertex inner j)
    _ = occurrence.1.facet.normalizedFacet.1.level :=
      SharedFacet.exchangedActiveFacet_vertex_fixed
        occurrence.1.facet.normalizedFacet inner j
    _ = occurrence.1.vertex j occurrence.1.facet.normalizedFacet.1.fixed :=
      (occurrence.1.vertex_fixed j).symm

/-- Helper for Theorem 57.6: at every residual active coordinate, the rebuilt
corner facet and the represented original ridge have the same retained value. -/
theorem EndpointBoundaryFaceOccurrence.extremeCornerAmbientFacet_residual
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (inner : NormalizedSharedFacet d m)
    (hvertex : ∀ j rank, inner.1.vertex j rank =
      occurrence.1.vertex j
        (occurrence.1.facet.normalizedFacet.1.activeCoordinate rank))
    (j rank : Fin (d + 1)) (hrank : rank ≠ inner.1.fixed) :
    (occurrence.extremeCornerAmbientFacet inner).1.vertex
        ((occurrence.exchangedActiveOccurrence inner).omitted.succAbove j)
        (occurrence.1.facet.normalizedFacet.1.activeCoordinate rank) =
      occurrence.1.vertex j
        (occurrence.1.facet.normalizedFacet.1.activeCoordinate rank) := by
  -- Follow the residual exchanged rank, then use the inner vertex specification.
  calc
    (occurrence.extremeCornerAmbientFacet inner).1.vertex
          ((occurrence.exchangedActiveOccurrence inner).omitted.succAbove j)
          (occurrence.1.facet.normalizedFacet.1.activeCoordinate rank) =
        (occurrence.exchangedActiveOccurrence inner).simplex.vertex
          ((occurrence.exchangedActiveOccurrence inner).omitted.succAbove j)
          (occurrence.1.facet.normalizedFacet.1.activeCoordinateExchangeEquiv
            inner.1.fixed rank) := by
      rw [← occurrence.1.facet.normalizedFacet.1
        |>.activeCoordinateExchangeEquiv_residual_ambient
          inner.1.fixed rank hrank]
      exact occurrence.extremeCornerAmbientFacet_vertex_active inner _ _
    _ = (occurrence.exchangedActiveOccurrence inner).vertex j
        (occurrence.1.facet.normalizedFacet.1.activeCoordinateExchangeEquiv
          inner.1.fixed rank) :=
      congrArg
        (fun vertex ↦ vertex
          (occurrence.1.facet.normalizedFacet.1.activeCoordinateExchangeEquiv
            inner.1.fixed rank))
        (StaircaseFaceOccurrence.vertex_eq_simplexVertex
          (occurrence.exchangedActiveOccurrence inner) j).symm
    _ = (SharedFacet.exchangedActiveFacet
          occurrence.1.facet.normalizedFacet inner).1.vertex j
        (occurrence.1.facet.normalizedFacet.1.activeCoordinateExchangeEquiv
          inner.1.fixed rank) :=
      congrArg
        (fun vertex ↦ vertex
          (occurrence.1.facet.normalizedFacet.1.activeCoordinateExchangeEquiv
            inner.1.fixed rank))
        (occurrence.exchangedActiveOccurrence_vertex inner j)
    _ = inner.1.vertex j rank :=
      SharedFacet.exchangedActiveFacet_vertex_exchange
        occurrence.1.facet.normalizedFacet inner j rank hrank
    _ = occurrence.1.vertex j
        (occurrence.1.facet.normalizedFacet.1.activeCoordinate rank) :=
      hvertex j rank

/-- Helper for Theorem 57.6: an inner normal form representing the active
ridge makes the rebuilt corner facet retain every original ridge vertex. -/
theorem EndpointBoundaryFaceOccurrence.extremeCornerAmbientFacet_retainedVertex
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (inner : NormalizedSharedFacet d m)
    (hvertex : ∀ j rank, inner.1.vertex j rank =
      occurrence.1.vertex j
        (occurrence.1.facet.normalizedFacet.1.activeCoordinate rank))
    (j : Fin (d + 1)) :
    (occurrence.extremeCornerAmbientFacet inner).1.vertex
        ((occurrence.exchangedActiveOccurrence inner).omitted.succAbove j) =
      occurrence.1.vertex j := by
  -- Split the ambient coordinates into the new fixed coordinate, the old
  -- fixed coordinate, and all residual active coordinates.
  funext i
  by_cases hi :
      i = occurrence.1.facet.normalizedFacet.1.activeCoordinate inner.1.fixed
  · subst i
    calc
      (occurrence.extremeCornerAmbientFacet inner).1.vertex
            ((occurrence.exchangedActiveOccurrence inner).omitted.succAbove j)
            (occurrence.1.facet.normalizedFacet.1.activeCoordinate
              inner.1.fixed) = inner.1.level :=
        occurrence.extremeCornerAmbientFacet_vertex_fixed inner _
      _ = inner.1.vertex j inner.1.fixed :=
        (inner.1.vertex_fixed j).symm
      _ = occurrence.1.vertex j
          (occurrence.1.facet.normalizedFacet.1.activeCoordinate inner.1.fixed) :=
        hvertex j inner.1.fixed
  · rcases occurrence.1.facet.normalizedFacet.1
        |>.exchangeCoordinate_eq_fixed_or_active inner.1.fixed hi with
      hiOuter | ⟨rank, hrank, hiResidual⟩
    · rw [hiOuter]
      exact occurrence.extremeCornerAmbientFacet_oldFixed inner j
    · rw [hiResidual]
      exact occurrence.extremeCornerAmbientFacet_residual inner hvertex j rank hrank

/-- Helper for Theorem 57.6: a lower endpoint normal form supplies the inner
vertex specification used by the corner exchange. -/
theorem EndpointBoundaryFaceOccurrence.normalForm_inl_vertex
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (lower : PositiveNormalizedSharedFacet d m)
    (hnormal : occurrence.normalForm = Sum.inl lower) (j rank : Fin (d + 1)) :
    lower.1.1.vertex j rank = occurrence.1.vertex j
      (occurrence.1.facet.normalizedFacet.1.activeCoordinate rank) := by
  -- Select the lower summand in the normal-form vertex computation.
  simpa only [hnormal, Sum.elim_inl] using occurrence.normalForm_vertex j rank

/-- Helper for Theorem 57.6: an upper endpoint normal form supplies the inner
vertex specification used by the corner exchange. -/
theorem EndpointBoundaryFaceOccurrence.normalForm_inr_vertex
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (upper : BelowTopNormalizedSharedFacet d m)
    (hnormal : occurrence.normalForm = Sum.inr upper) (j rank : Fin (d + 1)) :
    upper.1.1.vertex j rank = occurrence.1.vertex j
      (occurrence.1.facet.normalizedFacet.1.activeCoordinate rank) := by
  -- Select the upper summand in the normal-form vertex computation.
  simpa only [hnormal, Sum.elim_inr] using occurrence.normalForm_vertex j rank

/-- Helper for Theorem 57.6: a top extreme inner normal form makes the rebuilt
ambient facet a top boundary facet. -/
theorem EndpointBoundaryFaceOccurrence.extremeCornerAmbientFacet_top
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (lower : PositiveNormalizedSharedFacet d m)
    (htop : lower.1.1.level.1 = 2 * m) :
    (occurrence.extremeCornerAmbientFacet lower.1).1.level.1 = 2 * m := by
  -- The rebuilt ambient level is the inner normal-form level.
  rw [occurrence.extremeCornerAmbientFacet_level lower.1]
  exact htop

/-- Helper for Theorem 57.6: a bottom extreme inner normal form makes the
rebuilt ambient facet a bottom boundary facet. -/
theorem EndpointBoundaryFaceOccurrence.extremeCornerAmbientFacet_bottom
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (upper : BelowTopNormalizedSharedFacet d m)
    (hbottom : upper.1.1.level.1 = 0) :
    (occurrence.extremeCornerAmbientFacet upper.1).1.level.1 = 0 := by
  -- The rebuilt ambient level is the inner normal-form level.
  rw [occurrence.extremeCornerAmbientFacet_level upper.1]
  exact hbottom

/-- Helper for Theorem 57.6: build the alternate ambient occurrence at a top
extreme coordinate corner. -/
def EndpointBoundaryFaceOccurrence.extremeTopMate
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (lower : PositiveNormalizedSharedFacet d m)
    (htop : lower.1.1.level.1 = 2 * m) : BoundaryFaceOccurrence (d + 1) m :=
  { facet := Sum.inl
      ⟨occurrence.extremeCornerAmbientFacet lower.1,
        occurrence.extremeCornerAmbientFacet_top lower htop⟩
    omitted := (occurrence.exchangedActiveOccurrence lower.1).omitted }

/-- Helper for Theorem 57.6: build the alternate ambient occurrence at a
bottom extreme coordinate corner. -/
def EndpointBoundaryFaceOccurrence.extremeBottomMate
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (upper : BelowTopNormalizedSharedFacet d m)
    (hbottom : upper.1.1.level.1 = 0) : BoundaryFaceOccurrence (d + 1) m :=
  { facet := Sum.inr
      ⟨occurrence.extremeCornerAmbientFacet upper.1,
        occurrence.extremeCornerAmbientFacet_bottom upper hbottom⟩
    omitted := (occurrence.exchangedActiveOccurrence upper.1).omitted }

/-- Helper for Theorem 57.6: the top corner mate retains the exchanged
active occurrence's omitted endpoint. -/
theorem EndpointBoundaryFaceOccurrence.extremeTopMate_omitted
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (lower : PositiveNormalizedSharedFacet d m)
    (htop : lower.1.1.level.1 = 2 * m) :
    (occurrence.extremeTopMate lower htop).omitted =
      (occurrence.exchangedActiveOccurrence lower.1).omitted := by
  -- Project the omitted field of the corner constructor.
  rfl

/-- Helper for Theorem 57.6: the bottom corner mate retains the exchanged
active occurrence's omitted endpoint. -/
theorem EndpointBoundaryFaceOccurrence.extremeBottomMate_omitted
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (upper : BelowTopNormalizedSharedFacet d m)
    (hbottom : upper.1.1.level.1 = 0) :
    (occurrence.extremeBottomMate upper hbottom).omitted =
      (occurrence.exchangedActiveOccurrence upper.1).omitted := by
  -- Project the omitted field of the corner constructor.
  rfl

/-- Helper for Theorem 57.6: active compression of the top-corner mate
recovers its exchanged active staircase. -/
theorem EndpointBoundaryFaceOccurrence.extremeTopMate_activeStaircase
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (lower : PositiveNormalizedSharedFacet d m)
    (htop : lower.1.1.level.1 = 2 * m) :
    (occurrence.extremeTopMate lower htop).facet.normalizedFacet.1.activeStaircase =
      (occurrence.exchangedActiveOccurrence lower.1).simplex := by
  -- Forget the top tag and apply active compression of the rebuilt facet.
  rw [EndpointBoundaryFaceOccurrence.extremeTopMate,
    BoundarySharedFacet.normalizedFacet_inl]
  exact occurrence.extremeCornerAmbientFacet_activeStaircase lower.1

/-- Helper for Theorem 57.6: active compression of the bottom-corner mate
recovers its exchanged active staircase. -/
theorem EndpointBoundaryFaceOccurrence.extremeBottomMate_activeStaircase
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (upper : BelowTopNormalizedSharedFacet d m)
    (hbottom : upper.1.1.level.1 = 0) :
    (occurrence.extremeBottomMate upper hbottom).facet.normalizedFacet.1.activeStaircase =
      (occurrence.exchangedActiveOccurrence upper.1).simplex := by
  -- Forget the bottom tag and apply active compression of the rebuilt facet.
  rw [EndpointBoundaryFaceOccurrence.extremeBottomMate,
    BoundarySharedFacet.normalizedFacet_inr]
  exact occurrence.extremeCornerAmbientFacet_activeStaircase upper.1

/-- Helper for Theorem 57.6: the top corner mate fixes the ambient coordinate
represented by the old inner fixed rank. -/
theorem EndpointBoundaryFaceOccurrence.extremeTopMate_fixed
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (lower : PositiveNormalizedSharedFacet d m)
    (htop : lower.1.1.level.1 = 2 * m) :
    (occurrence.extremeTopMate lower htop).facet.normalizedFacet.1.fixed =
      occurrence.1.facet.normalizedFacet.1.activeCoordinate lower.1.1.fixed := by
  -- Forget the top tag and apply the rebuilt facet's fixed-coordinate formula.
  rw [EndpointBoundaryFaceOccurrence.extremeTopMate,
    BoundarySharedFacet.normalizedFacet_inl]
  exact occurrence.extremeCornerAmbientFacet_fixed lower.1

/-- Helper for Theorem 57.6: the bottom corner mate fixes the ambient
coordinate represented by the old inner fixed rank. -/
theorem EndpointBoundaryFaceOccurrence.extremeBottomMate_fixed
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (upper : BelowTopNormalizedSharedFacet d m)
    (hbottom : upper.1.1.level.1 = 0) :
    (occurrence.extremeBottomMate upper hbottom).facet.normalizedFacet.1.fixed =
      occurrence.1.facet.normalizedFacet.1.activeCoordinate upper.1.1.fixed := by
  -- Forget the bottom tag and apply the rebuilt facet's fixed-coordinate formula.
  rw [EndpointBoundaryFaceOccurrence.extremeBottomMate,
    BoundarySharedFacet.normalizedFacet_inr]
  exact occurrence.extremeCornerAmbientFacet_fixed upper.1

/-- Helper for Theorem 57.6: the top corner mate retains every original ridge
vertex pointwise. -/
theorem EndpointBoundaryFaceOccurrence.extremeTopMate_vertex
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (lower : PositiveNormalizedSharedFacet d m)
    (hnormal : occurrence.normalForm = Sum.inl lower)
    (htop : lower.1.1.level.1 = 2 * m) (j : Fin (d + 1)) :
    (occurrence.extremeTopMate lower htop).vertex j = occurrence.1.vertex j := by
  -- Remove the top tag and apply the coordinatewise retained-vertex theorem.
  rw [(occurrence.extremeTopMate lower htop).vertex_eq_facetVertex,
    EndpointBoundaryFaceOccurrence.extremeTopMate,
    BoundarySharedFacet.vertex_eq_normalizedFacet,
    BoundarySharedFacet.normalizedFacet_inl]
  exact occurrence.extremeCornerAmbientFacet_retainedVertex lower.1
    (occurrence.normalForm_inl_vertex lower hnormal) j

/-- Helper for Theorem 57.6: the bottom corner mate retains every original
ridge vertex pointwise. -/
theorem EndpointBoundaryFaceOccurrence.extremeBottomMate_vertex
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (upper : BelowTopNormalizedSharedFacet d m)
    (hnormal : occurrence.normalForm = Sum.inr upper)
    (hbottom : upper.1.1.level.1 = 0) (j : Fin (d + 1)) :
    (occurrence.extremeBottomMate upper hbottom).vertex j = occurrence.1.vertex j := by
  -- Remove the bottom tag and apply the coordinatewise retained-vertex theorem.
  rw [(occurrence.extremeBottomMate upper hbottom).vertex_eq_facetVertex,
    EndpointBoundaryFaceOccurrence.extremeBottomMate,
    BoundarySharedFacet.vertex_eq_normalizedFacet,
    BoundarySharedFacet.normalizedFacet_inr]
  exact occurrence.extremeCornerAmbientFacet_retainedVertex upper.1
    (occurrence.normalForm_inr_vertex upper hnormal) j

/-- Helper for Theorem 57.6: a top extreme endpoint occurrence has a distinct
ambient mate with the same unordered ridge. -/
theorem EndpointBoundaryFaceOccurrence.exists_distinct_mate_of_topCorner
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (lower : PositiveNormalizedSharedFacet d m)
    (hnormal : occurrence.normalForm = Sum.inl lower)
    (htop : lower.1.1.level.1 = 2 * m) :
    ∃ mate : BoundaryFaceOccurrence (d + 1) m,
      mate ≠ occurrence.1 ∧ mate.ridgeVertexSet = occurrence.1.ridgeVertexSet := by
  -- Distinguish the exchanged fixed coordinate, then lift pointwise equality
  -- to the unordered finite image.
  refine ⟨occurrence.extremeTopMate lower htop, ?_, ?_⟩
  · intro heq
    have hfixed := congrArg
      (fun mate : BoundaryFaceOccurrence (d + 1) m ↦
        mate.facet.normalizedFacet.1.fixed) heq
    rw [occurrence.extremeTopMate_fixed lower htop] at hfixed
    exact occurrence.1.facet.normalizedFacet.1
      |>.activeCoordinate_ne_fixed lower.1.1.fixed hfixed
  · rw [(occurrence.extremeTopMate lower htop).ridgeVertexSet_eq_vertexImage,
      occurrence.1.ridgeVertexSet_eq_vertexImage]
    apply Finset.image_congr
    intro j _
    exact occurrence.extremeTopMate_vertex lower hnormal htop j

/-- Helper for Theorem 57.6: a bottom extreme endpoint occurrence has a
distinct ambient mate with the same unordered ridge. -/
theorem EndpointBoundaryFaceOccurrence.exists_distinct_mate_of_bottomCorner
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (upper : BelowTopNormalizedSharedFacet d m)
    (hnormal : occurrence.normalForm = Sum.inr upper)
    (hbottom : upper.1.1.level.1 = 0) :
    ∃ mate : BoundaryFaceOccurrence (d + 1) m,
      mate ≠ occurrence.1 ∧ mate.ridgeVertexSet = occurrence.1.ridgeVertexSet := by
  -- Distinguish the exchanged fixed coordinate, then lift pointwise equality
  -- to the unordered finite image.
  refine ⟨occurrence.extremeBottomMate upper hbottom, ?_, ?_⟩
  · intro heq
    have hfixed := congrArg
      (fun mate : BoundaryFaceOccurrence (d + 1) m ↦
        mate.facet.normalizedFacet.1.fixed) heq
    rw [occurrence.extremeBottomMate_fixed upper hbottom] at hfixed
    exact occurrence.1.facet.normalizedFacet.1
      |>.activeCoordinate_ne_fixed upper.1.1.fixed hfixed
  · rw [(occurrence.extremeBottomMate upper hbottom).ridgeVertexSet_eq_vertexImage,
      occurrence.1.ridgeVertexSet_eq_vertexImage]
    apply Finset.image_congr
    intro j _
    exact occurrence.extremeBottomMate_vertex upper hnormal hbottom j

/-- Helper for Theorem 57.6: every endpoint boundary-ridge occurrence has a
distinct ambient presentation of the same unordered ridge. -/
theorem EndpointBoundaryFaceOccurrence.exists_distinct_mate
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m) :
    ∃ mate : BoundaryFaceOccurrence (d + 1) m,
      mate ≠ occurrence.1 ∧ mate.ridgeVertexSet = occurrence.1.ridgeVertexSet := by
  -- Use the adjacent opposite side in the two interior cases and the
  -- coordinate-exchange construction in the two extreme-corner cases.
  rcases occurrence.normalForm_interior_or_corner with
    ⟨lower, hnormal, hinterior⟩ |
    ⟨upper, hnormal, hinterior⟩ |
    ⟨lower, hnormal, htop⟩ |
    ⟨upper, hnormal, hbottom⟩
  · apply occurrence.exists_distinct_mate_of_interior
    simpa only [hnormal, Sum.elim_inl] using hinterior
  · apply occurrence.exists_distinct_mate_of_interior
    simpa only [hnormal, Sum.elim_inr] using hinterior
  · exact occurrence.exists_distinct_mate_of_topCorner lower hnormal htop
  · exact occurrence.exists_distinct_mate_of_bottomCorner upper hnormal hbottom

/-- Helper for Theorem 57.6: in every positive dimension, each endpoint
boundary-ridge occurrence has a distinct ambient presentation of its ridge. -/
theorem EndpointBoundaryFaceOccurrence.exists_distinct_mate_of_pos
    {d m : ℕ} (hd : 0 < d) (occurrence : EndpointBoundaryFaceOccurrence d m) :
    ∃ mate : BoundaryFaceOccurrence d m,
      mate ≠ occurrence.1 ∧ mate.ridgeVertexSet = occurrence.1.ridgeVertexSet := by
  -- Write the positive dimension as a successor and invoke the corner-complete API.
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  exact occurrence.exists_distinct_mate

end StandardSphere.CubicalTucker
