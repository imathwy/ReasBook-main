module

public import Topology_Munkres_2000.Book.Remark_50_3.FanParity
import Mathlib.Tactic.DeriveFintype

public section

noncomputable section

namespace StandardSphere.CubicalTucker

/-- Helper for Remark 50.3: a standard staircase simplex in an elementary
centered-grid cube is determined by its lower corner and coordinate order. -/
structure ElementaryStaircase (d m : ℕ) where
  corner : Fin d → Fin (2 * m)
  order : Equiv.Perm (Fin d)
deriving DecidableEq, Fintype

/-- Helper for Remark 50.3: the natural-number coordinate of a vertex in an
elementary staircase simplex. -/
def ElementaryStaircase.vertexValue {d m : ℕ} (σ : ElementaryStaircase d m)
    (k : Fin (d + 1)) (i : Fin d) : ℕ :=
  (σ.corner i).1 + if (σ.order.symm i).1 < k.1 then 1 else 0

/-- Helper for Remark 50.3: every staircase vertex coordinate remains in the
centered grid. -/
theorem ElementaryStaircase.vertexValue_lt {d m : ℕ}
    (σ : ElementaryStaircase d m) (k : Fin (d + 1)) (i : Fin d) :
    σ.vertexValue k i < 2 * m + 1 := by
  -- A staircase step adds at most one to a corner coordinate below `2m`.
  unfold vertexValue
  have hcorner := (σ.corner i).isLt
  split_ifs <;> omega

/-- Helper for Remark 50.3: a staircase simplex vertex as a centered-grid
vertex. -/
def ElementaryStaircase.vertex {d m : ℕ} (σ : ElementaryStaircase d m)
    (k : Fin (d + 1)) : CenteredGrid d m :=
  fun i ↦ ⟨σ.vertexValue k i, σ.vertexValue_lt k i⟩

/-- Helper for Remark 50.3: the stored staircase vertex has the expected
coordinate formula. -/
theorem ElementaryStaircase.vertex_value {d m : ℕ}
    (σ : ElementaryStaircase d m) (k : Fin (d + 1)) (i : Fin d) :
    (σ.vertex k i).1 =
      (σ.corner i).1 + if (σ.order.symm i).1 < k.1 then 1 else 0 := by
  -- The grid subtype stores exactly `vertexValue`.
  rfl

/-- Helper for Remark 50.3: any two vertices of one staircase simplex are
neighbors in the centered cubical grid. -/
theorem ElementaryStaircase.vertices_neighbor {d m : ℕ}
    (σ : ElementaryStaircase d m) (k l : Fin (d + 1)) :
    centeredGridNeighbor (σ.vertex k) (σ.vertex l) := by
  -- Each coordinate is the common corner value plus either zero or one.
  intro i
  rw [σ.vertex_value k i, σ.vertex_value l i]
  split_ifs <;> omega

/-- Helper for Remark 50.3: a codimension-one staircase-face occurrence is a
simplex together with its omitted vertex position. -/
structure StaircaseFaceOccurrence (d m : ℕ) where
  simplex : ElementaryStaircase d m
  omitted : Fin (d + 1)
deriving DecidableEq, Fintype

/-- Helper for Remark 50.3: rebuilding a staircase-face occurrence from its
two projections returns the original occurrence. -/
theorem StaircaseFaceOccurrence.mk_eq_self {d m : ℕ}
    (τ : StaircaseFaceOccurrence d m) :
    StaircaseFaceOccurrence.mk τ.simplex τ.omitted = τ := by
  -- Eliminate the two-field record; both projections then compute directly.
  cases τ
  rfl

/-- Helper for Remark 50.3: projecting a simplex-omission pair after building
its staircase-face occurrence returns the original pair. -/
theorem StaircaseFaceOccurrence.projections_mk_eq {d m : ℕ}
    (p : ElementaryStaircase d m × Fin (d + 1)) :
    ((StaircaseFaceOccurrence.mk p.1 p.2).simplex,
      (StaircaseFaceOccurrence.mk p.1 p.2).omitted) = p := by
  -- Eliminate the product; the constructor projections are definitionally equal.
  cases p
  rfl

/-- Helper for Remark 50.3: staircase-face occurrences are canonically the
product of a staircase simplex and an omitted vertex. -/
def staircaseFaceOccurrenceEquiv (d m : ℕ) :
    StaircaseFaceOccurrence d m ≃
      ElementaryStaircase d m × Fin (d + 1) :=
  { toFun := fun τ ↦ (τ.simplex, τ.omitted)
    invFun := fun p ↦ StaircaseFaceOccurrence.mk p.1 p.2
    left_inv := StaircaseFaceOccurrence.mk_eq_self
    right_inv := StaircaseFaceOccurrence.projections_mk_eq }

/-- Helper for Remark 50.3: summing over staircase-face occurrences is the
same as first summing over simplices and then over omitted vertices. -/
theorem sum_staircaseFaceOccurrence_eq_sum_simplex_omissions
    {d m : ℕ} {A : Type*} [AddCommMonoid A]
    (weight : StaircaseFaceOccurrence d m → A) :
    ∑ τ, weight τ =
      ∑ σ : ElementaryStaircase d m, ∑ k : Fin (d + 1), weight ⟨σ, k⟩ := by
  -- Reindex by the canonical product equivalence, then split the product sum.
  calc
    ∑ τ, weight τ =
        ∑ p : ElementaryStaircase d m × Fin (d + 1), weight ⟨p.1, p.2⟩ :=
      Fintype.sum_equiv (staircaseFaceOccurrenceEquiv d m) _ _ (fun _ ↦ rfl)
    _ = ∑ σ : ElementaryStaircase d m,
        ∑ k : Fin (d + 1), weight ⟨σ, k⟩ :=
      Fintype.sum_prod_type _

/-- Helper for Remark 50.3: enumerate the retained vertices of a staircase
face using `Fin.succAbove`. -/
def StaircaseFaceOccurrence.vertex {d m : ℕ} (τ : StaircaseFaceOccurrence d m)
    (j : Fin d) : CenteredGrid d m :=
  τ.simplex.vertex (τ.omitted.succAbove j)

/-- Helper for Theorem 57.6: the vertices of a freshly constructed face
occurrence are the corresponding retained simplex vertices. -/
theorem StaircaseFaceOccurrence.mk_vertex {d m : ℕ}
    (σ : ElementaryStaircase d m) (k : Fin (d + 1)) (j : Fin d) :
    (StaircaseFaceOccurrence.mk σ k).vertex j = σ.vertex (k.succAbove j) := by
  -- Expose the constructor computation once for clients of the opaque vertex API.
  rfl

/-- Helper for Theorem 57.6: the complete vertex enumeration of a constructed
face occurrence is simplex enumeration with the omitted position skipped. -/
theorem StaircaseFaceOccurrence.mk_vertex_eq {d m : ℕ}
    (σ : ElementaryStaircase d m) (k : Fin (d + 1)) :
    (StaircaseFaceOccurrence.mk σ k).vertex =
      fun j ↦ σ.vertex (k.succAbove j) := by
  -- Upgrade the owner computation rule to the function normal form used by weights.
  funext j
  exact StaircaseFaceOccurrence.mk_vertex σ k j

/-- Helper for Remark 50.3: all retained vertices of a staircase-face
occurrence lie in one elementary cube. -/
theorem StaircaseFaceOccurrence.vertices_neighbor {d m : ℕ}
    (τ : StaircaseFaceOccurrence d m) (j k : Fin d) :
    centeredGridNeighbor (τ.vertex j) (τ.vertex k) := by
  -- Both face vertices are vertices of the same stored staircase simplex.
  exact τ.simplex.vertices_neighbor _ _

/-- Helper for Remark 50.3: a staircase face is external when one coordinate
is constantly on the lower or upper boundary of the centered cube. -/
def StaircaseFaceOccurrence.IsExternal {d m : ℕ}
    (τ : StaircaseFaceOccurrence d m) : Prop :=
  ∃ i, (∀ j, (τ.vertex j i).1 = 0) ∨ ∀ j, (τ.vertex j i).1 = 2 * m

/-- Helper for Remark 50.3: every vertex of an external staircase face lies
on the centered-cube boundary. -/
theorem StaircaseFaceOccurrence.centeredGridBoundary_of_isExternal {d m : ℕ}
    {τ : StaircaseFaceOccurrence d m} (hτ : τ.IsExternal) (j : Fin d) :
    centeredGridBoundary (τ.vertex j) := by
  -- The coordinate constant on the face witnesses the boundary condition.
  obtain ⟨i, hlower | hupper⟩ := hτ
  · exact ⟨i, Or.inl (hlower j)⟩
  · exact ⟨i, Or.inr (hupper j)⟩

/-- Helper for Remark 50.3: swap the two staircase directions adjacent to an
internal omitted vertex. -/
def ElementaryStaircase.internalFaceMate {d m : ℕ}
    (σ : ElementaryStaircase d m) (k : Fin (d + 1))
    (hzero : k ≠ 0) (hlast : k ≠ Fin.last d) : ElementaryStaircase d m :=
  { corner := σ.corner
    order := σ.order * Equiv.swap (k.pred hzero) (k.castPred hlast) }

/-- Helper for Remark 50.3: swapping the two ranks adjacent to an omitted
internal rank does not change any retained threshold cut. -/
theorem internalFaceMate_rank_lt_succAbove_iff {d : ℕ}
    (k : Fin (d + 1)) (hzero : k ≠ 0) (hlast : k ≠ Fin.last d)
    (r j : Fin d) :
    ((Equiv.swap (k.pred hzero) (k.castPred hlast) r).1 <
        (k.succAbove j).1) ↔
      r.1 < (k.succAbove j).1 := by
  -- A retained rank is strictly below or strictly above the omitted rank, so
  -- exchanging its predecessor with the omitted rank preserves the cut.
  have hkpos : 0 < k.1 := Fin.pos_iff_ne_zero.mpr hzero
  have htne : (k.succAbove j).1 ≠ k.1 := by
    intro hval
    exact Fin.succAbove_ne k j (Fin.ext hval)
  by_cases hlower : r = k.pred hzero
  · subst r
    rw [Equiv.swap_apply_left]
    simp only [Fin.coe_castPred, Fin.val_pred]
    omega
  · by_cases hupper : r = k.castPred hlast
    · subst r
      rw [Equiv.swap_apply_right]
      simp only [Fin.coe_castPred, Fin.val_pred]
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne hlower hupper]

/-- Helper for Remark 50.3: the adjacent-order mate of an internal staircase
face enumerates exactly the same retained grid vertices. -/
theorem ElementaryStaircase.internalFaceMate_vertex {d m : ℕ}
    (σ : ElementaryStaircase d m) (k : Fin (d + 1))
    (hzero : k ≠ 0) (hlast : k ≠ Fin.last d) (j : Fin d) :
    (σ.internalFaceMate k hzero hlast).vertex (k.succAbove j) =
      σ.vertex (k.succAbove j) := by
  -- Reduce the vertex equality to the preceding rank-threshold invariance.
  have hrank (i : Fin d) :
      (σ.internalFaceMate k hzero hlast).order.symm i =
        Equiv.swap (k.pred hzero) (k.castPred hlast) (σ.order.symm i) := by
    -- Apply the swapped order; its two adjacent swaps cancel.
    apply (σ.order * Equiv.swap (k.pred hzero) (k.castPred hlast)).injective
    simp [internalFaceMate, Equiv.Perm.mul_apply]
  funext i
  apply Fin.ext
  simp only [ElementaryStaircase.vertex, ElementaryStaircase.vertexValue]
  simp only [hrank, internalFaceMate_rank_lt_succAbove_iff]
  rfl

/-- Helper for Remark 50.3: staircase-face occurrences whose omitted vertex
is neither endpoint of the staircase. -/
abbrev InternalStaircaseFace (d m : ℕ) :=
  {τ : StaircaseFaceOccurrence d m //
    τ.omitted ≠ 0 ∧ τ.omitted ≠ Fin.last d}

/-- Helper for Remark 50.3: pair an internal staircase face with its
adjacent-order presentation in the same elementary cube. -/
def internalStaircaseFaceMate {d m : ℕ}
    (τ : InternalStaircaseFace d m) : InternalStaircaseFace d m :=
  ⟨⟨τ.1.simplex.internalFaceMate τ.1.omitted τ.2.1 τ.2.2,
      τ.1.omitted⟩,
    τ.2⟩

/-- Helper for Remark 50.3: the internal staircase-face mate operation is an
involution. -/
theorem internalStaircaseFaceMate_involutive {d m : ℕ} :
    Function.Involutive
      (internalStaircaseFaceMate : InternalStaircaseFace d m →
        InternalStaircaseFace d m) := by
  rintro ⟨⟨σ, k⟩, hk⟩
  -- Swapping the same adjacent pair twice restores the original coordinate order.
  apply Subtype.ext
  simp [internalStaircaseFaceMate, ElementaryStaircase.internalFaceMate,
    mul_assoc]

/-- Helper for Remark 50.3: an internal staircase face and its mate enumerate
the same retained grid vertices. -/
theorem internalStaircaseFaceMate_vertex {d m : ℕ}
    (τ : InternalStaircaseFace d m) (j : Fin d) :
    (internalStaircaseFaceMate τ).1.vertex j = τ.1.vertex j := by
  -- Both occurrences omit the same rank, so use the mate-simplex vertex formula.
  exact τ.1.simplex.internalFaceMate_vertex τ.1.omitted τ.2.1 τ.2.2 j

/-- Helper for Remark 50.3: an internal staircase-face occurrence is distinct
from its adjacent-order mate. -/
theorem internalStaircaseFaceMate_ne {d m : ℕ}
    (τ : InternalStaircaseFace d m) : internalStaircaseFaceMate τ ≠ τ := by
  -- Equality would make the original permutation identify two adjacent ranks.
  intro hfixed
  have hoccurrence := congrArg Subtype.val hfixed
  have hsimplex := congrArg StaircaseFaceOccurrence.simplex hoccurrence
  have horder := congrArg ElementaryStaircase.order hsimplex
  have happly := congrArg
    (fun order : Equiv.Perm (Fin d) ↦ order (τ.1.omitted.pred τ.2.1)) horder
  have hadjacent : τ.1.omitted.castPred τ.2.2 = τ.1.omitted.pred τ.2.1 := by
    apply τ.1.simplex.order.injective
    simpa [internalStaircaseFaceMate, ElementaryStaircase.internalFaceMate,
      Equiv.Perm.mul_apply] using happly
  have hvalue := congrArg Fin.val hadjacent
  have hpositive : 0 < τ.1.omitted.1 := Fin.pos_iff_ne_zero.mpr τ.2.1
  simp only [Fin.coe_castPred, Fin.val_pred] at hvalue
  omega

/-- Helper for Remark 50.3: a canonical cubical facet records its fixed
coordinate and level, together with one staircase order on the active coordinates. -/
structure SharedFacet (d m : ℕ) where
  fixed : Fin (d + 1)
  level : Fin (2 * m + 1)
  corner : Fin (d + 1) → Fin (2 * m)
  activeOrder : Equiv.Perm (Fin d)
deriving DecidableEq, Fintype

/-- Helper for Remark 50.3: a shared facet with its irrelevant fixed-corner
entry chosen canonically to be zero. -/
abbrev NormalizedSharedFacet (d m : ℕ) :=
  {τ : SharedFacet d m // (τ.corner τ.fixed).1 = 0}

/-- Helper for Remark 50.3: replace the irrelevant fixed-coordinate corner
by the canonical zero value. -/
def SharedFacet.normalizedCorner {d m : ℕ} (hm : 0 < m)
    (τ : SharedFacet d m) (i : Fin (d + 1)) : Fin (2 * m) :=
  if i = τ.fixed then ⟨0, Nat.mul_pos (Nat.succ_pos 1) hm⟩ else τ.corner i

/-- Helper for Remark 50.3: the normalized corner is zero at the facet's
fixed coordinate. -/
theorem SharedFacet.normalizedCorner_fixed {d m : ℕ} (hm : 0 < m)
    (τ : SharedFacet d m) : (τ.normalizedCorner hm τ.fixed).1 = 0 := by
  -- The distinguished coordinate selects the canonical branch.
  simp only [normalizedCorner, if_pos]

/-- Helper for Remark 50.3: canonically normalize the redundant corner
coordinate of a shared facet. -/
def SharedFacet.normalize {d m : ℕ} (hm : 0 < m) (τ : SharedFacet d m) :
    NormalizedSharedFacet d m :=
  ⟨{τ with corner := τ.normalizedCorner hm}, τ.normalizedCorner_fixed hm⟩

/-- Helper for Remark 50.3: reflect every active corner coordinate while
keeping the normalized, geometrically irrelevant fixed corner unchanged. -/
def SharedFacet.reflectedCorner {d m : ℕ} (τ : NormalizedSharedFacet d m)
    (i : Fin (d + 1)) : Fin (2 * m) :=
  if i = τ.1.fixed then τ.1.corner i else Fin.rev (τ.1.corner i)

/-- Helper for Remark 50.3: the reflected corner remains normalized at the
fixed coordinate. -/
theorem SharedFacet.reflectedCorner_fixed {d m : ℕ}
    (τ : NormalizedSharedFacet d m) :
    (SharedFacet.reflectedCorner τ τ.1.fixed).1 = 0 := by
  -- Reflection deliberately leaves the redundant fixed entry unchanged.
  simp only [reflectedCorner, if_pos]
  exact τ.2

/-- Helper for Remark 50.3: centered reflection of a normalized shared facet
reverses its level, active corners, and active staircase order. -/
def SharedFacet.reflect {d m : ℕ} (τ : NormalizedSharedFacet d m) :
    NormalizedSharedFacet d m :=
  ⟨{ fixed := τ.1.fixed
     level := Fin.rev τ.1.level
     corner := SharedFacet.reflectedCorner τ
     activeOrder := τ.1.activeOrder * Fin.revPerm },
    SharedFacet.reflectedCorner_fixed τ⟩

/-- Helper for Remark 50.3: reflecting a normalized shared facet twice
returns the original facet. -/
theorem SharedFacet.reflect_involutive {d m : ℕ} :
    Function.Involutive
      (SharedFacet.reflect : NormalizedSharedFacet d m →
        NormalizedSharedFacet d m) := by
  -- Each reflected coordinate and the reversing permutation are involutions.
  intro τ
  rcases τ with ⟨⟨fixed, level, corner, activeOrder⟩, hnormalized⟩
  apply Subtype.ext
  simp only [reflect, Fin.rev_rev, SharedFacet.mk.injEq, true_and, mul_assoc]
  constructor
  · funext i
    by_cases hi : i = fixed
    · simp only [reflectedCorner, hi, if_pos]
    · simp only [reflectedCorner, hi, if_false, Fin.rev_rev]
  · apply Equiv.ext
    intro i
    simp [Equiv.Perm.mul_apply]

/-- Helper for Remark 50.3: the original and reflected fixed levels sum to
the top centered-grid level. -/
theorem SharedFacet.reflect_level_add {d m : ℕ}
    (τ : NormalizedSharedFacet d m) :
    (SharedFacet.reflect τ).1.level.1 + τ.1.level.1 = 2 * m := by
  -- The level component of reflection is exactly `Fin.rev`.
  exact Fin.rev_add_cast τ.1.level

/-- Helper for Remark 50.3: normalized shared facets on the top cubical
boundary. -/
abbrev TopBoundaryNormalizedSharedFacet (d m : ℕ) :=
  {τ : NormalizedSharedFacet d m // τ.1.level.1 = 2 * m}

/-- Helper for Remark 50.3: normalized shared facets on the lower cubical
boundary. -/
abbrev BottomBoundaryNormalizedSharedFacet (d m : ℕ) :=
  {τ : NormalizedSharedFacet d m // τ.1.level.1 = 0}

/-- Helper for Remark 50.3: reflection carries a top boundary facet to the
lower boundary. -/
theorem SharedFacet.reflect_level_eq_zero_of_level_eq_top {d m : ℕ}
    (τ : NormalizedSharedFacet d m) (hlevel : τ.1.level.1 = 2 * m) :
    (SharedFacet.reflect τ).1.level.1 = 0 := by
  -- Subtract the assumed top level from the reflection level sum.
  have hsum := SharedFacet.reflect_level_add τ
  omega

/-- Helper for Remark 50.3: reflection carries a lower boundary facet to the
top boundary. -/
theorem SharedFacet.reflect_level_eq_top_of_level_eq_zero {d m : ℕ}
    (τ : NormalizedSharedFacet d m) (hlevel : τ.1.level.1 = 0) :
    (SharedFacet.reflect τ).1.level.1 = 2 * m := by
  -- Remove the zero original level from the reflection level sum.
  have hsum := SharedFacet.reflect_level_add τ
  omega

/-- Helper for Remark 50.3: reflect a top normalized facet to the lower
boundary. -/
def SharedFacet.reflectTopBoundary {d m : ℕ}
    (τ : TopBoundaryNormalizedSharedFacet d m) :
    BottomBoundaryNormalizedSharedFacet d m :=
  ⟨SharedFacet.reflect τ.1,
    SharedFacet.reflect_level_eq_zero_of_level_eq_top τ.1 τ.2⟩

/-- Helper for Remark 50.3: reflect a lower normalized facet to the top
boundary. -/
def SharedFacet.reflectBottomBoundary {d m : ℕ}
    (τ : BottomBoundaryNormalizedSharedFacet d m) :
    TopBoundaryNormalizedSharedFacet d m :=
  ⟨SharedFacet.reflect τ.1,
    SharedFacet.reflect_level_eq_top_of_level_eq_zero τ.1 τ.2⟩

/-- Helper for Theorem 57.6: forgetting the boundary certificate after
top-to-bottom reflection leaves the normalized reflected facet. -/
theorem SharedFacet.reflectTopBoundary_val {d m : ℕ}
    (τ : TopBoundaryNormalizedSharedFacet d m) :
    (SharedFacet.reflectTopBoundary τ).1 = SharedFacet.reflect τ.1 := by
  -- Evaluate the data projection of the top-boundary reflection.
  rfl

/-- Helper for Theorem 57.6: forgetting the boundary certificate after
bottom-to-top reflection leaves the normalized reflected facet. -/
theorem SharedFacet.reflectBottomBoundary_val {d m : ℕ}
    (τ : BottomBoundaryNormalizedSharedFacet d m) :
    (SharedFacet.reflectBottomBoundary τ).1 = SharedFacet.reflect τ.1 := by
  -- Evaluate the data projection of the bottom-boundary reflection.
  rfl

/-- Helper for Remark 50.3: the top-to-bottom and bottom-to-top facet
reflections are inverse. -/
theorem SharedFacet.reflectBottomBoundary_reflectTopBoundary {d m : ℕ}
    (τ : TopBoundaryNormalizedSharedFacet d m) :
    SharedFacet.reflectBottomBoundary (SharedFacet.reflectTopBoundary τ) = τ := by
  -- Subtype certificates are irrelevant once the underlying reflection squares to one.
  apply Subtype.ext
  exact SharedFacet.reflect_involutive τ.1

/-- Helper for Remark 50.3: the bottom-to-top and top-to-bottom facet
reflections are inverse. -/
theorem SharedFacet.reflectTopBoundary_reflectBottomBoundary {d m : ℕ}
    (τ : BottomBoundaryNormalizedSharedFacet d m) :
    SharedFacet.reflectTopBoundary (SharedFacet.reflectBottomBoundary τ) = τ := by
  -- Use the same involutivity computation in the opposite boundary direction.
  apply Subtype.ext
  exact SharedFacet.reflect_involutive τ.1

/-- Helper for Remark 50.3: centered reflection gives the canonical
equivalence between top and lower normalized shared facets. -/
def SharedFacet.boundaryReflectEquiv (d m : ℕ) :
    TopBoundaryNormalizedSharedFacet d m ≃
      BottomBoundaryNormalizedSharedFacet d m :=
  { toFun := SharedFacet.reflectTopBoundary
    invFun := SharedFacet.reflectBottomBoundary
    left_inv := SharedFacet.reflectBottomBoundary_reflectTopBoundary
    right_inv := SharedFacet.reflectTopBoundary_reflectBottomBoundary }

/-- Helper for Theorem 57.6: the underlying normalized facet produced by the
boundary-reflection equivalence is the centered reflection. -/
theorem SharedFacet.boundaryReflectEquiv_apply {d m : ℕ}
    (τ : TopBoundaryNormalizedSharedFacet d m) :
    ((SharedFacet.boundaryReflectEquiv d m) τ).1 = SharedFacet.reflect τ.1 := by
  -- Unfold the equivalence application at its owner, avoiding downstream opacity.
  rfl

/-- Helper for Remark 50.3: order the fixed coordinate first and the active
coordinates according to the facet's stored permutation. -/
def SharedFacet.leadingOrder {d m : ℕ} (τ : SharedFacet d m) :
    Equiv.Perm (Fin (d + 1)) :=
  Equiv.Perm.decomposeFin.symm (τ.fixed, τ.activeOrder)

/-- Helper for Theorem 57.6: the full leading order sends a successor rank
according to the stored active-coordinate order. -/
theorem SharedFacet.leadingOrder_succ {d m : ℕ} (τ : SharedFacet d m)
    (x : Fin d) :
    τ.leadingOrder x.succ =
      Equiv.swap 0 τ.fixed (τ.activeOrder x).succ := by
  -- Expose the successor computation at the owner of `leadingOrder`.
  exact Equiv.Perm.decomposeFin_symm_apply_succ τ.activeOrder τ.fixed x

/-- Helper for Remark 50.3: rotate the leading order so that the fixed
coordinate is last. -/
def SharedFacet.trailingOrder {d m : ℕ} (τ : SharedFacet d m) :
    Equiv.Perm (Fin (d + 1)) :=
  τ.leadingOrder * finRotate (d + 1)

/-- Helper for Remark 50.3: enumerate the grid vertices of a canonical
cubical facet. -/
def SharedFacet.vertexValue {d m : ℕ} (τ : SharedFacet d m)
    (j : Fin (d + 1)) (i : Fin (d + 1)) : ℕ :=
  if i = τ.fixed then τ.level.1
  else (τ.corner i).1 + if (τ.leadingOrder.symm i).1 < j.1 + 1 then 1 else 0

/-- Helper for Remark 50.3: every canonical facet coordinate lies in the
centered grid. -/
theorem SharedFacet.vertexValue_lt {d m : ℕ} (τ : SharedFacet d m)
    (j : Fin (d + 1)) (i : Fin (d + 1)) :
    τ.vertexValue j i < 2 * m + 1 := by
  -- The fixed coordinate is a grid level; every active coordinate adds at most one.
  unfold vertexValue
  split_ifs
  · exact τ.level.isLt
  · have hcorner := (τ.corner i).isLt
    omega
  · have hcorner := (τ.corner i).isLt
    omega

/-- Helper for Remark 50.3: the centered-grid vertex represented by a
canonical cubical facet. -/
def SharedFacet.vertex {d m : ℕ} (τ : SharedFacet d m)
    (j : Fin (d + 1)) : CenteredGrid (d + 1) m :=
  fun i ↦ ⟨τ.vertexValue j i, τ.vertexValue_lt j i⟩

/-- Helper for Remark 50.3: a canonical facet vertex has the stored
fixed-level and active-staircase coordinate formula. -/
theorem SharedFacet.vertex_value {d m : ℕ} (τ : SharedFacet d m)
    (j : Fin (d + 1)) (i : Fin (d + 1)) :
    (τ.vertex j i).1 =
      if i = τ.fixed then τ.level.1
      else (τ.corner i).1 + if (τ.leadingOrder.symm i).1 < j.1 + 1 then 1 else 0 := by
  -- The grid subtype stores `vertexValue` without changing its natural-number value.
  rfl

/-- Helper for Remark 50.3: normalizing the redundant corner coordinate
does not change any vertex represented by a shared facet. -/
theorem SharedFacet.normalize_vertex {d m : ℕ} (hm : 0 < m)
    (τ : SharedFacet d m) (j : Fin (d + 1)) :
    (normalize hm τ).1.vertex j = τ.vertex j := by
  -- The vertex formula ignores the corner at `fixed`; all other entries agree.
  funext i
  apply Fin.ext
  rw [(normalize hm τ).1.vertex_value j i, τ.vertex_value j i]
  by_cases hi : i = τ.fixed
  · simp only [normalize, hi, if_pos]
  · simp only [normalize, leadingOrder, hi, if_false, normalizedCorner]
    rfl

/-- Helper for Remark 50.3: all vertices of one canonical shared facet are
neighbors in the centered cubical grid. -/
theorem SharedFacet.vertices_neighbor {d m : ℕ} (τ : SharedFacet d m)
    (j k : Fin (d + 1)) : centeredGridNeighbor (τ.vertex j) (τ.vertex k) := by
  -- The fixed coordinate agrees, and each active coordinate differs by at most one.
  intro i
  rw [τ.vertex_value j i, τ.vertex_value k i]
  by_cases hi : i = τ.fixed
  · simp [hi]
  · simp only [hi, if_false]
    split_ifs <;> omega

/-- Helper for Theorem 57.6: the canonical staircase enumeration of a shared
cubical facet has no repeated vertices. -/
theorem SharedFacet.vertex_injective {d m : ℕ} (τ : SharedFacet d m) :
    Function.Injective τ.vertex := by
  -- A later vertex has crossed the active coordinate at its rank, while an
  -- earlier vertex has not yet crossed that coordinate.
  have hseparate (j k : Fin (d + 1)) (hjk : j.1 < k.1) :
      τ.vertex j ≠ τ.vertex k := by
    have hkzero : k ≠ 0 := by
      intro hk
      subst k
      simp at hjk
    have hactive : τ.leadingOrder k ≠ τ.fixed := by
      intro hfixed
      apply hkzero
      apply τ.leadingOrder.injective
      exact hfixed.trans
        (Equiv.Perm.decomposeFin_symm_apply_zero τ.fixed τ.activeOrder).symm
    intro heq
    have hcoordinate := congrArg
      (fun v : CenteredGrid (d + 1) m ↦ (v (τ.leadingOrder k)).1) heq
    rw [τ.vertex_value j, τ.vertex_value k] at hcoordinate
    simp only [hactive, if_false, τ.leadingOrder.symm_apply_apply] at hcoordinate
    have hbefore : ¬k.1 < j.1 + 1 := by omega
    have hafter : k.1 < k.1 + 1 := by omega
    rw [if_neg hbefore, if_pos hafter] at hcoordinate
    omega
  intro j k heq
  apply Fin.ext
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hjk | hkj
  · exact hseparate j k hjk heq
  · exact hseparate k j hkj heq.symm

/-- Helper for Theorem 57.6: deleting one index from an injective enumeration
of `d + 1` vertices leaves exactly `d` distinct vertices. -/
theorem finsetImage_succAbove_card_of_injective {V : Type*} [DecidableEq V]
    {d : ℕ} (vertex : Fin (d + 1) → V) (hvertex : Function.Injective vertex)
    (omitted : Fin (d + 1)) :
    (Finset.univ.image (fun j ↦ vertex (omitted.succAbove j))).card = d := by
  -- The deletion embedding and the original enumeration remain injective.
  have hinjective : Function.Injective
      (fun j ↦ vertex (omitted.succAbove j)) :=
    hvertex.comp Fin.succAbove_right_injective
  calc
    (Finset.univ.image (fun j ↦ vertex (omitted.succAbove j))).card =
        (Finset.univ : Finset (Fin d)).card :=
      Finset.card_image_of_injective Finset.univ hinjective
    _ = d := Fintype.card_fin d

/-- Helper for Theorem 57.6: for an injective vertex enumeration, the
unordered deletion image uniquely determines the omitted position. -/
theorem finsetImage_succAbove_injective_of_injective
    {V : Type*} [DecidableEq V] {d : ℕ} (vertex : Fin (d + 1) → V)
    (hvertex : Function.Injective vertex) :
    Function.Injective (fun omitted : Fin (d + 1) ↦
      Finset.univ.image (fun j ↦ vertex (omitted.succAbove j))) := by
  -- If two omissions differ, the first omitted vertex occurs in the second
  -- deletion image but cannot occur in its own deletion image.
  intro omitted₁ omitted₂ himage
  by_contra hne
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hne
  have hmem₂ : vertex omitted₁ ∈
      Finset.univ.image (fun k ↦ vertex (omitted₂.succAbove k)) := by
    apply Finset.mem_image.mpr
    exact ⟨j, Finset.mem_univ j, congrArg vertex hj⟩
  have himage' :
      Finset.univ.image (fun k ↦ vertex (omitted₁.succAbove k)) =
        Finset.univ.image (fun k ↦ vertex (omitted₂.succAbove k)) :=
    himage
  have hmem₁ : vertex omitted₁ ∈
      Finset.univ.image (fun k ↦ vertex (omitted₁.succAbove k)) := by
    rw [himage']
    exact hmem₂
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hmem₁
  exact Fin.succAbove_ne omitted₁ k (hvertex hk)

/-- Helper for Remark 50.3: the lower adjacent cube has a valid corner when
the shared facet is not at level zero. -/
theorem SharedFacet.lowerCornerValue_lt {d m : ℕ} (τ : SharedFacet d m)
    (hlevel : 0 < τ.level.1) (i : Fin (d + 1)) :
    (if i = τ.fixed then τ.level.1 - 1 else (τ.corner i).1) < 2 * m := by
  -- At the fixed coordinate subtract one; elsewhere use the stored active corner.
  split_ifs
  · have hlevel_lt := τ.level.isLt
    omega
  · exact (τ.corner i).isLt

/-- Helper for Remark 50.3: the elementary cube immediately below an
internal canonical facet. -/
def SharedFacet.lowerSimplex {d m : ℕ} (τ : SharedFacet d m)
    (hlevel : 0 < τ.level.1) : ElementaryStaircase (d + 1) m :=
  { corner := fun i ↦
      ⟨if i = τ.fixed then τ.level.1 - 1 else (τ.corner i).1,
        τ.lowerCornerValue_lt hlevel i⟩
    order := τ.leadingOrder }

/-- Helper for Remark 50.3: the lower cube presents the shared facet by
deleting its initial staircase vertex. -/
def SharedFacet.lowerOccurrence {d m : ℕ} (τ : SharedFacet d m)
    (hlevel : 0 < τ.level.1) : StaircaseFaceOccurrence (d + 1) m :=
  ⟨τ.lowerSimplex hlevel, 0⟩

/-- Helper for Remark 50.3: the upper adjacent cube has a valid corner when
the shared facet is below the top grid level. -/
theorem SharedFacet.upperCornerValue_lt {d m : ℕ} (τ : SharedFacet d m)
    (hlevel : τ.level.1 < 2 * m) (i : Fin (d + 1)) :
    (if i = τ.fixed then τ.level.1 else (τ.corner i).1) < 2 * m := by
  -- At the fixed coordinate use the assumed internal level; elsewhere use the stored corner.
  split_ifs
  · exact hlevel
  · exact (τ.corner i).isLt

/-- Helper for Remark 50.3: the elementary cube immediately above an
internal canonical facet. -/
def SharedFacet.upperSimplex {d m : ℕ} (τ : SharedFacet d m)
    (hlevel : τ.level.1 < 2 * m) : ElementaryStaircase (d + 1) m :=
  { corner := fun i ↦
      ⟨if i = τ.fixed then τ.level.1 else (τ.corner i).1,
        τ.upperCornerValue_lt hlevel i⟩
    order := τ.trailingOrder }

/-- Helper for Remark 50.3: the upper cube presents the shared facet by
deleting its final staircase vertex. -/
def SharedFacet.upperOccurrence {d m : ℕ} (τ : SharedFacet d m)
    (hlevel : τ.level.1 < 2 * m) : StaircaseFaceOccurrence (d + 1) m :=
  ⟨τ.upperSimplex hlevel, Fin.last (d + 1)⟩

/-- Helper for Remark 50.3: the leading full order sends its initial position
to the facet's fixed coordinate. -/
theorem SharedFacet.leadingOrder_zero {d m : ℕ} (τ : SharedFacet d m) :
    τ.leadingOrder 0 = τ.fixed := by
  -- This is the distinguished-coordinate computation for `decomposeFin`.
  exact Equiv.Perm.decomposeFin_symm_apply_zero τ.fixed τ.activeOrder

/-- Helper for Remark 50.3: the fixed coordinate occupies position zero in
the leading full order. -/
theorem SharedFacet.leadingOrder_symm_fixed {d m : ℕ} (τ : SharedFacet d m) :
    τ.leadingOrder.symm τ.fixed = 0 := by
  -- Apply the inverse order to the preceding distinguished-coordinate formula.
  calc
    τ.leadingOrder.symm τ.fixed =
        τ.leadingOrder.symm (τ.leadingOrder 0) := by rw [τ.leadingOrder_zero]
    _ = 0 := τ.leadingOrder.symm_apply_apply 0

/-- Helper for Remark 50.3: a non-fixed coordinate has nonzero position in
the leading full order. -/
theorem SharedFacet.leadingOrder_symm_ne_zero {d m : ℕ} (τ : SharedFacet d m)
    {i : Fin (d + 1)} (hi : i ≠ τ.fixed) : τ.leadingOrder.symm i ≠ 0 := by
  -- Position zero is occupied by the fixed coordinate.
  intro hzero
  apply hi
  calc
    i = τ.leadingOrder (τ.leadingOrder.symm i) := (τ.leadingOrder.apply_symm_apply i).symm
    _ = τ.leadingOrder 0 := by rw [hzero]
    _ = τ.fixed := τ.leadingOrder_zero

/-- Helper for Remark 50.3: after rotating the full order, every active
coordinate's position decreases by one. -/
theorem SharedFacet.trailingOrder_symm_value {d m : ℕ} (τ : SharedFacet d m)
    {i : Fin (d + 1)} (hi : i ≠ τ.fixed) :
    (τ.trailingOrder.symm i).1 + 1 = (τ.leadingOrder.symm i).1 := by
  -- Inverting the rotation subtracts one from the nonzero leading position.
  have hnonzero := τ.leadingOrder_symm_ne_zero hi
  have hposition :
      τ.trailingOrder.symm i =
        (finRotate (d + 1)).symm (τ.leadingOrder.symm i) := by
    apply τ.trailingOrder.injective
    simp [trailingOrder, Equiv.Perm.mul_apply]
  rw [hposition]
  rw [coe_finRotate_symm_of_ne_zero hnonzero]
  have hpositive : 0 < (τ.leadingOrder.symm i).1 :=
    Nat.pos_of_ne_zero (Fin.val_ne_zero_iff.mpr hnonzero)
  omega

/-- Helper for Remark 50.3: after rotation the fixed coordinate occupies the
last position of the full order. -/
theorem SharedFacet.trailingOrder_symm_fixed {d m : ℕ} (τ : SharedFacet d m) :
    τ.trailingOrder.symm τ.fixed = Fin.last d := by
  -- Applying the trailing order sends the last position through the rotation to zero.
  apply τ.trailingOrder.injective
  simp [trailingOrder, Equiv.Perm.mul_apply, τ.leadingOrder_zero]

/-- Helper for Remark 50.3: reflection reverses every active coordinate's
rank in the leading order. -/
theorem SharedFacet.reflect_leadingOrder_symm_value {d m : ℕ}
    (τ : NormalizedSharedFacet d m) {i : Fin (d + 1)}
    (hi : i ≠ τ.1.fixed) :
    ((SharedFacet.reflect τ).1.leadingOrder.symm i).1 +
        (τ.1.leadingOrder.symm i).1 = d + 1 := by
  -- Write the old nonzero rank as a successor, then reverse its active index.
  obtain ⟨x, hx⟩ := Fin.exists_succ_eq_of_ne_zero
    (τ.1.leadingOrder_symm_ne_zero hi)
  have hnewApply :
      (SharedFacet.reflect τ).1.leadingOrder (Fin.succ (Fin.rev x)) = i := by
    calc
      (SharedFacet.reflect τ).1.leadingOrder (Fin.succ (Fin.rev x)) =
          Equiv.swap 0 τ.1.fixed
            (((τ.1.activeOrder * (Fin.revPerm : Equiv.Perm (Fin d)))
              (Fin.rev x)).succ) := by
        simp only [leadingOrder, reflect,
          Equiv.Perm.decomposeFin_symm_apply_succ]
      _ = Equiv.swap 0 τ.1.fixed (τ.1.activeOrder x).succ := by
        simp only [Equiv.Perm.mul_apply, Fin.revPerm_apply, Fin.rev_rev]
      _ = τ.1.leadingOrder (Fin.succ x) := by
        rw [leadingOrder, Equiv.Perm.decomposeFin_symm_apply_succ]
      _ = τ.1.leadingOrder (τ.1.leadingOrder.symm i) := by rw [hx]
      _ = i := τ.1.leadingOrder.apply_symm_apply i
  have hnewRank :
      (SharedFacet.reflect τ).1.leadingOrder.symm i = Fin.succ (Fin.rev x) := by
    apply (SharedFacet.reflect τ).1.leadingOrder.injective
    exact ((SharedFacet.reflect τ).1.leadingOrder.apply_symm_apply i).trans
      hnewApply.symm
  -- The two successor ranks sum to `d + 1` by the value formula for `Fin.rev`.
  rw [hnewRank, ← hx]
  simp only [Fin.val_succ, Fin.val_rev]
  omega

/-- Helper for Remark 50.3: reflected shared-facet vertices are the centered
reflections of the original vertices in reverse enumeration order. -/
theorem SharedFacet.reflect_vertex {d m : ℕ}
    (τ : NormalizedSharedFacet d m) (j : Fin (d + 1)) :
    (SharedFacet.reflect τ).1.vertex j =
      centeredGridNeg (τ.1.vertex (Fin.rev j)) := by
  -- Both vertices have coordinate sums `2m`; the rank reversal makes the two
  -- active-coordinate increment indicators complementary.
  funext i
  apply Fin.ext
  have hneg := centeredGridNeg_value (τ.1.vertex (Fin.rev j)) i
  have hsum :
      ((SharedFacet.reflect τ).1.vertex j i).1 +
          (τ.1.vertex (Fin.rev j) i).1 = 2 * m := by
    rw [(SharedFacet.reflect τ).1.vertex_value j i,
      τ.1.vertex_value (Fin.rev j) i]
    by_cases hi : i = τ.1.fixed
    · simp only [reflect, hi, if_pos]
      exact Fin.rev_add_cast τ.1.level
    · have hrank := SharedFacet.reflect_leadingOrder_symm_value τ hi
      have hjrank := Fin.rev_add_cast j
      have hcorner := (τ.1.corner i).isLt
      by_cases hold :
          (τ.1.leadingOrder.symm i).1 < (Fin.rev j).1 + 1
      · have hnew :
            ¬((SharedFacet.reflect τ).1.leadingOrder.symm i).1 < j.1 + 1 := by
          omega
        rw [if_neg hnew, if_pos hold]
        simp only [reflect, reflectedCorner, hi, if_false, Fin.val_rev]
        omega
      · have hnew :
            ((SharedFacet.reflect τ).1.leadingOrder.symm i).1 < j.1 + 1 := by
          omega
        rw [if_pos hnew, if_neg hold]
        simp only [reflect, reflectedCorner, hi, if_false, Fin.val_rev]
        omega
  omega

/-- Helper for Remark 50.3: every vertex of a shared facet at an extreme
fixed-coordinate level lies on the centered cubical boundary. -/
theorem SharedFacet.vertex_boundary_of_level_extreme {d m : ℕ}
    (τ : SharedFacet d m)
    (hlevel : τ.level.1 = 0 ∨ τ.level.1 = 2 * m) (j : Fin (d + 1)) :
    centeredGridBoundary (τ.vertex j) := by
  -- The facet's fixed coordinate supplies the extremal boundary coordinate.
  refine ⟨τ.fixed, ?_⟩
  rw [τ.vertex_value j τ.fixed, if_pos rfl]
  exact hlevel

/-- Helper for Remark 50.3: the lower adjacent cube's face enumeration is
the canonical shared-facet enumeration. -/
theorem SharedFacet.lowerOccurrence_vertex {d m : ℕ} (τ : SharedFacet d m)
    (hlevel : 0 < τ.level.1) (j : Fin (d + 1)) :
    (τ.lowerOccurrence hlevel).vertex j = τ.vertex j := by
  -- The initial deleted vertex increments the fixed coordinate and preserves active ranks.
  funext i
  apply Fin.ext
  by_cases hi : i = τ.fixed
  · subst i
    simp [StaircaseFaceOccurrence.vertex, lowerOccurrence, lowerSimplex,
      ElementaryStaircase.vertex, ElementaryStaircase.vertexValue, vertex,
      vertexValue, τ.leadingOrder_symm_fixed]
    omega
  · simp [StaircaseFaceOccurrence.vertex, lowerOccurrence, lowerSimplex,
      ElementaryStaircase.vertex, ElementaryStaircase.vertexValue, vertex,
      vertexValue, Fin.zero_succAbove, hi]

/-- Helper for Remark 50.3: the upper adjacent cube's face enumeration is
the canonical shared-facet enumeration. -/
theorem SharedFacet.upperOccurrence_vertex {d m : ℕ} (τ : SharedFacet d m)
    (hlevel : τ.level.1 < 2 * m) (j : Fin (d + 1)) :
    (τ.upperOccurrence hlevel).vertex j = τ.vertex j := by
  -- The final deleted vertex leaves the fixed level unchanged and shifts active ranks once.
  funext i
  apply Fin.ext
  by_cases hi : i = τ.fixed
  · subst i
    have hj : ¬d < j.1 := by omega
    simp [StaircaseFaceOccurrence.vertex, upperOccurrence, upperSimplex,
      ElementaryStaircase.vertex, ElementaryStaircase.vertexValue, vertex,
      vertexValue, τ.trailingOrder_symm_fixed,
      Fin.succAbove_last_apply, hj]
  · have hrank := τ.trailingOrder_symm_value hi
    simp only [StaircaseFaceOccurrence.vertex, upperOccurrence, upperSimplex,
      ElementaryStaircase.vertex, ElementaryStaircase.vertexValue, vertex,
      vertexValue, Fin.succAbove_last_apply, Fin.val_castSucc, hi, if_false]
    split_ifs <;> omega

/-- Helper for Remark 50.3: the two adjacent cube occurrences enumerate a
canonical shared facet by literally equal centered-grid vertices. -/
theorem StaircaseFaceOccurrence.sharedFacet_vertex {d m : ℕ}
    (τ : SharedFacet d m) (hlower : 0 < τ.level.1)
    (hupper : τ.level.1 < 2 * m) (j : Fin (d + 1)) :
    (τ.lowerOccurrence hlower).vertex j = (τ.upperOccurrence hupper).vertex j := by
  -- Normalize both adjacent presentations to the canonical facet key.
  exact (τ.lowerOccurrence_vertex hlower j).trans
    (τ.upperOccurrence_vertex hupper j).symm

/-- Helper for Remark 50.3: the coordinate first traversed by a staircase
whose initial vertex is omitted. -/
def StaircaseFaceOccurrence.lowerEndpointFixed {d m : ℕ}
    (τ : StaircaseFaceOccurrence (d + 1) m) : Fin (d + 1) :=
  (Equiv.Perm.decomposeFin τ.simplex.order).1

/-- Helper for Remark 50.3: canonically erase the irrelevant fixed-coordinate
corner of an initial-endpoint occurrence. -/
def StaircaseFaceOccurrence.lowerEndpointCorner {d m : ℕ}
    (τ : StaircaseFaceOccurrence (d + 1) m) (i : Fin (d + 1)) : Fin (2 * m) :=
  if i = τ.lowerEndpointFixed then
    ⟨0, Nat.zero_lt_of_lt (τ.simplex.corner τ.lowerEndpointFixed).isLt⟩
  else τ.simplex.corner i

/-- Helper for Remark 50.3: the level exposed after deleting the initial
vertex is a valid centered-grid level. -/
theorem StaircaseFaceOccurrence.lowerEndpointLevel_lt {d m : ℕ}
    (τ : StaircaseFaceOccurrence (d + 1) m) :
    (τ.simplex.corner τ.lowerEndpointFixed).1 + 1 < 2 * m + 1 := by
  -- The simplex corner lies strictly below `2m`, so its successor is at most `2m`.
  exact Nat.succ_lt_succ (τ.simplex.corner τ.lowerEndpointFixed).isLt

/-- Helper for Remark 50.3: the shared-facet level exposed by deleting the
initial staircase vertex. -/
def StaircaseFaceOccurrence.lowerEndpointLevel {d m : ℕ}
    (τ : StaircaseFaceOccurrence (d + 1) m) : Fin (2 * m + 1) :=
  ⟨(τ.simplex.corner τ.lowerEndpointFixed).1 + 1, τ.lowerEndpointLevel_lt⟩

/-- Helper for Remark 50.3: an initial-endpoint occurrence determines a
canonical shared facet. -/
def StaircaseFaceOccurrence.lowerEndpointFacetRaw {d m : ℕ}
    (τ : StaircaseFaceOccurrence (d + 1) m) : SharedFacet d m :=
  { fixed := τ.lowerEndpointFixed
    level := τ.lowerEndpointLevel
    corner := τ.lowerEndpointCorner
    activeOrder := (Equiv.Perm.decomposeFin τ.simplex.order).2 }

/-- Helper for Remark 50.3: the extracted lower endpoint facet has its
irrelevant corner normalized to zero. -/
theorem StaircaseFaceOccurrence.lowerEndpointFacetRaw_normalized {d m : ℕ}
    (τ : StaircaseFaceOccurrence (d + 1) m) :
    (τ.lowerEndpointFacetRaw.corner τ.lowerEndpointFacetRaw.fixed).1 = 0 := by
  -- The fixed-coordinate branch of `lowerEndpointCorner` is the canonical zero.
  simp [lowerEndpointFacetRaw, lowerEndpointCorner]

/-- Helper for Remark 50.3: extract the normalized shared facet represented
by an initial-endpoint occurrence. -/
def StaircaseFaceOccurrence.lowerEndpointFacet {d m : ℕ}
    (τ : StaircaseFaceOccurrence (d + 1) m) : NormalizedSharedFacet d m :=
  ⟨τ.lowerEndpointFacetRaw, τ.lowerEndpointFacetRaw_normalized⟩

/-- Helper for Remark 50.3: every extracted lower endpoint facet has positive
level, as it lies one step above its simplex corner. -/
theorem StaircaseFaceOccurrence.lowerEndpointFacet_level_pos {d m : ℕ}
    (τ : StaircaseFaceOccurrence (d + 1) m) :
    0 < τ.lowerEndpointFacet.1.level.1 := by
  -- The extracted level is the successor of a natural-number corner coordinate.
  exact Nat.succ_pos _

/-- Helper for Remark 50.3: extracting the facet of an occurrence omitting
its initial vertex and rebuilding its lower presentation returns the occurrence. -/
theorem StaircaseFaceOccurrence.lowerEndpointFacet_lowerOccurrence {d m : ℕ}
    (τ : StaircaseFaceOccurrence (d + 1) m) (homitted : τ.omitted = 0) :
    τ.lowerEndpointFacet.1.lowerOccurrence τ.lowerEndpointFacet_level_pos = τ := by
  -- The facet remembers the first coordinate, the remaining order, and every
  -- relevant corner coordinate; these reconstruct both fields of the occurrence.
  rw [← τ.mk_eq_self, homitted]
  apply congrArg (fun σ : ElementaryStaircase (d + 1) m ↦
    StaircaseFaceOccurrence.mk σ 0)
  apply congrArg₂ ElementaryStaircase.mk
  · funext i
    apply Fin.ext
    by_cases hi : i = τ.lowerEndpointFixed
    · simp [SharedFacet.lowerOccurrence, SharedFacet.lowerSimplex,
        lowerEndpointFacet, lowerEndpointFacetRaw, lowerEndpointLevel,
        lowerEndpointCorner, lowerEndpointFixed, hi]
    · have hi' : i ≠ (Equiv.Perm.decomposeFin τ.simplex.order).1 := by
        simpa only [lowerEndpointFixed] using hi
      simp [SharedFacet.lowerOccurrence, SharedFacet.lowerSimplex,
        lowerEndpointFacet, lowerEndpointFacetRaw, lowerEndpointCorner,
        lowerEndpointFixed, hi']
  · simp [SharedFacet.lowerOccurrence, SharedFacet.lowerSimplex,
      lowerEndpointFacet, lowerEndpointFacetRaw, SharedFacet.leadingOrder,
      lowerEndpointFixed]

/-- Helper for Remark 50.3: extracting the normalized facet from its lower
presentation recovers the original normalized facet. -/
theorem SharedFacet.lowerOccurrence_lowerEndpointFacet {d m : ℕ}
    (τ : NormalizedSharedFacet d m) (hlevel : 0 < τ.1.level.1) :
    (τ.1.lowerOccurrence hlevel).lowerEndpointFacet = τ := by
  -- Normalize the reconstructed fields; positivity cancels the predecessor in
  -- the lower corner, while the subtype hypothesis identifies the fixed corner.
  apply Subtype.ext
  rcases τ with ⟨⟨fixed, level, corner, activeOrder⟩, hnormalized⟩
  have hlevel' : 0 < level.1 := hlevel
  simp only [StaircaseFaceOccurrence.lowerEndpointFacet,
    StaircaseFaceOccurrence.lowerEndpointFacetRaw,
    StaircaseFaceOccurrence.lowerEndpointFixed,
    StaircaseFaceOccurrence.lowerEndpointLevel,
    StaircaseFaceOccurrence.lowerEndpointCorner, lowerOccurrence, lowerSimplex,
    leadingOrder, Equiv.apply_symm_apply, Prod.fst, Prod.snd]
  congr 1
  · apply Fin.ext
    simp only [Fin.val_mk, if_pos]
    omega
  · funext i
    apply Fin.ext
    by_cases hi : i = fixed
    · subst i
      simpa [StaircaseFaceOccurrence.lowerEndpointCorner,
        StaircaseFaceOccurrence.lowerEndpointFixed,
        Equiv.apply_symm_apply] using hnormalized.symm
    · simp [StaircaseFaceOccurrence.lowerEndpointCorner,
        StaircaseFaceOccurrence.lowerEndpointFixed,
        Equiv.apply_symm_apply, hi]

/-- Helper for Remark 50.3: staircase-face occurrences deleting the initial
staircase vertex. -/
abbrev LowerEndpointOccurrence (d m : ℕ) :=
  {τ : StaircaseFaceOccurrence (d + 1) m // τ.omitted = 0}

/-- Helper for Remark 50.3: normalized shared facets that have a lower
adjacent elementary cube. -/
abbrev PositiveNormalizedSharedFacet (d m : ℕ) :=
  {τ : NormalizedSharedFacet d m // 0 < τ.1.level.1}

/-- Helper for Remark 50.3: extract a positive normalized facet from an
initial-endpoint occurrence. -/
def lowerEndpointOccurrenceToFacet {d m : ℕ}
    (τ : LowerEndpointOccurrence d m) : PositiveNormalizedSharedFacet d m :=
  ⟨τ.1.lowerEndpointFacet, τ.1.lowerEndpointFacet_level_pos⟩

/-- Helper for Remark 50.3: a lower shared-facet presentation omits the
initial staircase vertex. -/
theorem SharedFacet.lowerOccurrence_omitted {d m : ℕ}
    (τ : SharedFacet d m) (hlevel : 0 < τ.level.1) :
    (τ.lowerOccurrence hlevel).omitted = 0 := by
  -- This is the omission stored by the lower-occurrence constructor.
  rfl

/-- Helper for Remark 50.3: present a positive normalized facet as its lower
endpoint occurrence. -/
def positiveNormalizedSharedFacetToLowerOccurrence {d m : ℕ}
    (τ : PositiveNormalizedSharedFacet d m) : LowerEndpointOccurrence d m :=
  ⟨τ.1.1.lowerOccurrence τ.2, τ.1.1.lowerOccurrence_omitted τ.2⟩

/-- Helper for Remark 50.3: lower endpoint normalization followed by lower
presentation is the identity. -/
theorem lowerEndpointOccurrenceToFacet_leftInverse {d m : ℕ}
    (τ : LowerEndpointOccurrence d m) :
    positiveNormalizedSharedFacetToLowerOccurrence
        (lowerEndpointOccurrenceToFacet τ) = τ := by
  -- Compare underlying occurrences using the established reconstruction theorem.
  apply Subtype.ext
  exact τ.1.lowerEndpointFacet_lowerOccurrence τ.2

/-- Helper for Remark 50.3: lower presentation followed by endpoint
normalization is the identity on positive normalized facets. -/
theorem lowerEndpointOccurrenceToFacet_rightInverse {d m : ℕ}
    (τ : PositiveNormalizedSharedFacet d m) :
    lowerEndpointOccurrenceToFacet
        (positiveNormalizedSharedFacetToLowerOccurrence τ) = τ := by
  -- Compare underlying normalized facets using the converse reconstruction theorem.
  apply Subtype.ext
  exact SharedFacet.lowerOccurrence_lowerEndpointFacet τ.1 τ.2

/-- Helper for Remark 50.3: initial-endpoint staircase occurrences are
canonically equivalent to positive normalized shared facets. -/
def lowerEndpointStaircaseFaceEquiv (d m : ℕ) :
    LowerEndpointOccurrence d m ≃ PositiveNormalizedSharedFacet d m :=
  { toFun := lowerEndpointOccurrenceToFacet
    invFun := positiveNormalizedSharedFacetToLowerOccurrence
    left_inv := lowerEndpointOccurrenceToFacet_leftInverse
    right_inv := lowerEndpointOccurrenceToFacet_rightInverse }

/-- Helper for Remark 50.3: the lower endpoint equivalence preserves every
enumerated centered-grid vertex. -/
theorem lowerEndpointStaircaseFaceEquiv_vertex {d m : ℕ}
    (τ : LowerEndpointOccurrence d m) (j : Fin (d + 1)) :
    τ.1.vertex j = ((lowerEndpointStaircaseFaceEquiv d m τ).1.1.vertex j) := by
  -- Rebuild the occurrence from its facet, then use the lower-occurrence
  -- computation rule to reach the canonical facet vertex.
  calc
    τ.1.vertex j =
        (τ.1.lowerEndpointFacet.1.lowerOccurrence
          τ.1.lowerEndpointFacet_level_pos).vertex j :=
      congrArg (fun occurrence ↦ occurrence.vertex j)
        (τ.1.lowerEndpointFacet_lowerOccurrence τ.2).symm
    _ = τ.1.lowerEndpointFacet.1.vertex j :=
      τ.1.lowerEndpointFacet.1.lowerOccurrence_vertex
        τ.1.lowerEndpointFacet_level_pos j

/-- Helper for Remark 50.3: rotate an endpoint occurrence's full order so
that its final traversed coordinate becomes the distinguished first one. -/
def StaircaseFaceOccurrence.upperEndpointLeadingOrder {d m : ℕ}
    (τ : StaircaseFaceOccurrence (d + 1) m) : Equiv.Perm (Fin (d + 1)) :=
  τ.simplex.order * (finRotate (d + 1)).symm

/-- Helper for Remark 50.3: the coordinate last traversed by a staircase
whose final vertex is omitted. -/
def StaircaseFaceOccurrence.upperEndpointFixed {d m : ℕ}
    (τ : StaircaseFaceOccurrence (d + 1) m) : Fin (d + 1) :=
  (Equiv.Perm.decomposeFin τ.upperEndpointLeadingOrder).1

/-- Helper for Remark 50.3: canonically erase the irrelevant fixed-coordinate
corner of a final-endpoint occurrence. -/
def StaircaseFaceOccurrence.upperEndpointCorner {d m : ℕ}
    (τ : StaircaseFaceOccurrence (d + 1) m) (i : Fin (d + 1)) : Fin (2 * m) :=
  if i = τ.upperEndpointFixed then
    ⟨0, Nat.zero_lt_of_lt (τ.simplex.corner τ.upperEndpointFixed).isLt⟩
  else τ.simplex.corner i

/-- Helper for Remark 50.3: the shared-facet level exposed by deleting the
final staircase vertex. -/
def StaircaseFaceOccurrence.upperEndpointLevel {d m : ℕ}
    (τ : StaircaseFaceOccurrence (d + 1) m) : Fin (2 * m + 1) :=
  Fin.castLE (Nat.le_add_right (2 * m) 1) (τ.simplex.corner τ.upperEndpointFixed)

/-- Helper for Remark 50.3: a final-endpoint occurrence determines a
canonical shared facet. -/
def StaircaseFaceOccurrence.upperEndpointFacetRaw {d m : ℕ}
    (τ : StaircaseFaceOccurrence (d + 1) m) : SharedFacet d m :=
  { fixed := τ.upperEndpointFixed
    level := τ.upperEndpointLevel
    corner := τ.upperEndpointCorner
    activeOrder := (Equiv.Perm.decomposeFin τ.upperEndpointLeadingOrder).2 }

/-- Helper for Remark 50.3: the extracted upper endpoint facet has its
irrelevant corner normalized to zero. -/
theorem StaircaseFaceOccurrence.upperEndpointFacetRaw_normalized {d m : ℕ}
    (τ : StaircaseFaceOccurrence (d + 1) m) :
    (τ.upperEndpointFacetRaw.corner τ.upperEndpointFacetRaw.fixed).1 = 0 := by
  -- The fixed-coordinate branch of `upperEndpointCorner` is canonical zero.
  simp [upperEndpointFacetRaw, upperEndpointCorner]

/-- Helper for Remark 50.3: extract the normalized shared facet represented
by a final-endpoint occurrence. -/
def StaircaseFaceOccurrence.upperEndpointFacet {d m : ℕ}
    (τ : StaircaseFaceOccurrence (d + 1) m) : NormalizedSharedFacet d m :=
  ⟨τ.upperEndpointFacetRaw, τ.upperEndpointFacetRaw_normalized⟩

/-- Helper for Remark 50.3: every extracted upper endpoint facet lies below
the top grid level. -/
theorem StaircaseFaceOccurrence.upperEndpointFacet_level_lt {d m : ℕ}
    (τ : StaircaseFaceOccurrence (d + 1) m) :
    τ.upperEndpointFacet.1.level.1 < 2 * m := by
  -- Its level is the original elementary-cube corner coordinate.
  exact (τ.simplex.corner τ.upperEndpointFixed).isLt

/-- Helper for Remark 50.3: extracting the facet of an occurrence omitting
its final vertex and rebuilding its upper presentation returns the occurrence. -/
theorem StaircaseFaceOccurrence.upperEndpointFacet_upperOccurrence {d m : ℕ}
    (τ : StaircaseFaceOccurrence (d + 1) m)
    (homitted : τ.omitted = Fin.last (d + 1)) :
    τ.upperEndpointFacet.1.upperOccurrence τ.upperEndpointFacet_level_lt = τ := by
  -- The rotated decomposition remembers the last coordinate, the remaining
  -- order, and every relevant corner coordinate.
  rw [← τ.mk_eq_self]
  apply congrArg₂ StaircaseFaceOccurrence.mk
  apply congrArg₂ ElementaryStaircase.mk
  · funext i
    apply Fin.ext
    by_cases hi : i = τ.upperEndpointFixed
    · simp [SharedFacet.upperOccurrence, SharedFacet.upperSimplex,
        upperEndpointFacet, upperEndpointFacetRaw, upperEndpointLevel,
        upperEndpointCorner, upperEndpointFixed, hi]
    · have hi' : i ≠
          (Equiv.Perm.decomposeFin τ.upperEndpointLeadingOrder).1 := by
        simpa only [upperEndpointFixed] using hi
      simp [SharedFacet.upperOccurrence, SharedFacet.upperSimplex,
        upperEndpointFacet, upperEndpointFacetRaw, upperEndpointCorner,
        upperEndpointFixed, hi']
  · change Equiv.Perm.decomposeFin.symm
        (Equiv.Perm.decomposeFin τ.upperEndpointLeadingOrder) *
          finRotate (d + 1) = τ.simplex.order
    rw [Equiv.symm_apply_apply]
    change (τ.simplex.order * (finRotate (d + 1)).symm) *
      finRotate (d + 1) = τ.simplex.order
    have hinverse :
        (finRotate (d + 1)).symm * finRotate (d + 1) = 1 := by
      apply Equiv.ext
      intro i
      simp [Equiv.Perm.mul_apply]
    rw [mul_assoc, hinverse, mul_one]
  · exact homitted.symm

/-- Helper for Remark 50.3: extracting the normalized facet from its upper
presentation recovers the original normalized facet. -/
theorem SharedFacet.upperOccurrence_upperEndpointFacet {d m : ℕ}
    (τ : NormalizedSharedFacet d m) (hlevel : τ.1.level.1 < 2 * m) :
    (τ.1.upperOccurrence hlevel).upperEndpointFacet = τ := by
  -- Rotation cancellation reduces the extracted order to the facet's leading
  -- order; normalization then changes only the irrelevant fixed corner.
  let occurrence := τ.1.upperOccurrence hlevel
  have hrotate :
      finRotate (d + 1) * (finRotate (d + 1)).symm = 1 := by
    apply Equiv.ext
    intro i
    simp [Equiv.Perm.mul_apply]
  have hleading :
      occurrence.upperEndpointLeadingOrder = τ.1.leadingOrder := by
    change (τ.1.leadingOrder * finRotate (d + 1)) *
      (finRotate (d + 1)).symm = τ.1.leadingOrder
    rw [mul_assoc, hrotate, mul_one]
  have hdecompose :
      Equiv.Perm.decomposeFin occurrence.upperEndpointLeadingOrder =
        (τ.1.fixed, τ.1.activeOrder) := by
    calc
      Equiv.Perm.decomposeFin occurrence.upperEndpointLeadingOrder =
          Equiv.Perm.decomposeFin τ.1.leadingOrder := congrArg _ hleading
      _ = (τ.1.fixed, τ.1.activeOrder) :=
        Equiv.apply_symm_apply Equiv.Perm.decomposeFin _
  have hfixed : occurrence.upperEndpointFixed = τ.1.fixed :=
    congrArg Prod.fst hdecompose
  have hactive :
      (Equiv.Perm.decomposeFin occurrence.upperEndpointLeadingOrder).2 =
        τ.1.activeOrder :=
    congrArg Prod.snd hdecompose
  have hlevelEq : occurrence.upperEndpointLevel = τ.1.level := by
    unfold StaircaseFaceOccurrence.upperEndpointLevel
    rw [hfixed]
    apply Fin.ext
    simp [occurrence, upperOccurrence, upperSimplex]
  have hcornerEq : occurrence.upperEndpointCorner = τ.1.corner := by
    funext i
    unfold StaircaseFaceOccurrence.upperEndpointCorner
    rw [hfixed]
    apply Fin.ext
    by_cases hi : i = τ.1.fixed
    · subst i
      simpa [occurrence, upperOccurrence, upperSimplex] using τ.2.symm
    · simp [occurrence, upperOccurrence, upperSimplex, hi]
  apply Subtype.ext
  change SharedFacet.mk occurrence.upperEndpointFixed occurrence.upperEndpointLevel
      occurrence.upperEndpointCorner
        (Equiv.Perm.decomposeFin occurrence.upperEndpointLeadingOrder).2 = τ.1
  rcases τ with ⟨⟨fixed, level, corner, activeOrder⟩, hnormalized⟩
  rw [hfixed, hlevelEq, hcornerEq, hactive]

/-- Helper for Remark 50.3: staircase-face occurrences deleting the final
staircase vertex. -/
abbrev UpperEndpointOccurrence (d m : ℕ) :=
  {τ : StaircaseFaceOccurrence (d + 1) m // τ.omitted = Fin.last (d + 1)}

/-- Helper for Remark 50.3: normalized shared facets that have an upper
adjacent elementary cube. -/
abbrev BelowTopNormalizedSharedFacet (d m : ℕ) :=
  {τ : NormalizedSharedFacet d m // τ.1.level.1 < 2 * m}

/-- Helper for Remark 50.3: extract a below-top normalized facet from a
final-endpoint occurrence. -/
def upperEndpointOccurrenceToFacet {d m : ℕ}
    (τ : UpperEndpointOccurrence d m) : BelowTopNormalizedSharedFacet d m :=
  ⟨τ.1.upperEndpointFacet, τ.1.upperEndpointFacet_level_lt⟩

/-- Helper for Remark 50.3: an upper shared-facet presentation omits the
final staircase vertex. -/
theorem SharedFacet.upperOccurrence_omitted {d m : ℕ}
    (τ : SharedFacet d m) (hlevel : τ.level.1 < 2 * m) :
    (τ.upperOccurrence hlevel).omitted = Fin.last (d + 1) := by
  -- This is the omission stored by the upper-occurrence constructor.
  rfl

/-- Helper for Remark 50.3: present a below-top normalized facet as its upper
endpoint occurrence. -/
def belowTopNormalizedSharedFacetToUpperOccurrence {d m : ℕ}
    (τ : BelowTopNormalizedSharedFacet d m) : UpperEndpointOccurrence d m :=
  ⟨τ.1.1.upperOccurrence τ.2, τ.1.1.upperOccurrence_omitted τ.2⟩

/-- Helper for Remark 50.3: upper endpoint normalization followed by upper
presentation is the identity. -/
theorem upperEndpointOccurrenceToFacet_leftInverse {d m : ℕ}
    (τ : UpperEndpointOccurrence d m) :
    belowTopNormalizedSharedFacetToUpperOccurrence
        (upperEndpointOccurrenceToFacet τ) = τ := by
  -- Compare underlying occurrences using the upper reconstruction theorem.
  apply Subtype.ext
  exact τ.1.upperEndpointFacet_upperOccurrence τ.2

/-- Helper for Remark 50.3: upper presentation followed by endpoint
normalization is the identity on below-top normalized facets. -/
theorem upperEndpointOccurrenceToFacet_rightInverse {d m : ℕ}
    (τ : BelowTopNormalizedSharedFacet d m) :
    upperEndpointOccurrenceToFacet
        (belowTopNormalizedSharedFacetToUpperOccurrence τ) = τ := by
  -- Compare normalized facets using the converse upper reconstruction theorem.
  apply Subtype.ext
  exact SharedFacet.upperOccurrence_upperEndpointFacet τ.1 τ.2

/-- Helper for Remark 50.3: final-endpoint staircase occurrences are
canonically equivalent to below-top normalized shared facets. -/
def upperEndpointStaircaseFaceEquiv (d m : ℕ) :
    UpperEndpointOccurrence d m ≃ BelowTopNormalizedSharedFacet d m :=
  { toFun := upperEndpointOccurrenceToFacet
    invFun := belowTopNormalizedSharedFacetToUpperOccurrence
    left_inv := upperEndpointOccurrenceToFacet_leftInverse
    right_inv := upperEndpointOccurrenceToFacet_rightInverse }

/-- Helper for Remark 50.3: the upper endpoint equivalence preserves every
enumerated centered-grid vertex. -/
theorem upperEndpointStaircaseFaceEquiv_vertex {d m : ℕ}
    (τ : UpperEndpointOccurrence d m) (j : Fin (d + 1)) :
    τ.1.vertex j = ((upperEndpointStaircaseFaceEquiv d m τ).1.1.vertex j) := by
  -- Rebuild the occurrence from its facet, then use the upper-occurrence
  -- computation rule to reach the canonical facet vertex.
  calc
    τ.1.vertex j =
        (τ.1.upperEndpointFacet.1.upperOccurrence
          τ.1.upperEndpointFacet_level_lt).vertex j :=
      congrArg (fun occurrence ↦ occurrence.vertex j)
        (τ.1.upperEndpointFacet_upperOccurrence τ.2).symm
    _ = τ.1.upperEndpointFacet.1.vertex j :=
      τ.1.upperEndpointFacet.1.upperOccurrence_vertex
        τ.1.upperEndpointFacet_level_lt j

/-- Helper for Remark 50.3: staircase-face occurrences deleting either
endpoint of the staircase. -/
abbrev EndpointStaircaseFaceOccurrence (d m : ℕ) :=
  {τ : StaircaseFaceOccurrence (d + 1) m //
    ¬(τ.omitted ≠ 0 ∧ τ.omitted ≠ Fin.last (d + 1))}

/-- Helper for Remark 50.3: an endpoint omission is either the initial or
the final staircase vertex. -/
theorem EndpointStaircaseFaceOccurrence.omitted_eq_zero_or_last {d m : ℕ}
    (τ : EndpointStaircaseFaceOccurrence d m) :
    τ.1.omitted = 0 ∨ τ.1.omitted = Fin.last (d + 1) := by
  -- Negating the internal-omission condition gives the two endpoint cases.
  by_cases hzero : τ.1.omitted = 0
  · exact Or.inl hzero
  · right
    by_contra hlast
    exact τ.2 ⟨hzero, hlast⟩

/-- Helper for Remark 50.3: a noninitial endpoint omission is the final
staircase vertex. -/
theorem EndpointStaircaseFaceOccurrence.omitted_eq_last_of_ne_zero {d m : ℕ}
    (τ : EndpointStaircaseFaceOccurrence d m) (hzero : τ.1.omitted ≠ 0) :
    τ.1.omitted = Fin.last (d + 1) := by
  -- Eliminate the initial endpoint from the canonical endpoint dichotomy.
  exact (τ.omitted_eq_zero_or_last.resolve_left hzero)

/-- Helper for Remark 50.3: every lower endpoint occurrence satisfies the
endpoint-omission predicate. -/
theorem LowerEndpointOccurrence.isEndpoint {d m : ℕ}
    (τ : LowerEndpointOccurrence d m) :
    ¬(τ.1.omitted ≠ 0 ∧ τ.1.omitted ≠ Fin.last (d + 1)) := by
  -- Its stored omitted vertex is zero.
  exact fun h ↦ h.1 τ.2

/-- Helper for Remark 50.3: every upper endpoint occurrence satisfies the
endpoint-omission predicate. -/
theorem UpperEndpointOccurrence.isEndpoint {d m : ℕ}
    (τ : UpperEndpointOccurrence d m) :
    ¬(τ.1.omitted ≠ 0 ∧ τ.1.omitted ≠ Fin.last (d + 1)) := by
  -- Its stored omitted vertex is the final one.
  exact fun h ↦ h.2 τ.2

/-- Helper for Remark 50.3: normalize an endpoint occurrence into its lower
or upper shared-facet presentation. -/
def endpointOccurrenceToSharedFacetSum {d m : ℕ}
    (τ : EndpointStaircaseFaceOccurrence d m) :
    PositiveNormalizedSharedFacet d m ⊕ BelowTopNormalizedSharedFacet d m :=
  if hzero : τ.1.omitted = 0 then
    Sum.inl (lowerEndpointStaircaseFaceEquiv d m ⟨τ.1, hzero⟩)
  else
    Sum.inr (upperEndpointStaircaseFaceEquiv d m
      ⟨τ.1, τ.omitted_eq_last_of_ne_zero hzero⟩)

/-- Helper for Remark 50.3: rebuild an endpoint occurrence from either
normalized shared-facet presentation. -/
def sharedFacetSumToEndpointOccurrence {d m : ℕ} :
    PositiveNormalizedSharedFacet d m ⊕ BelowTopNormalizedSharedFacet d m →
      EndpointStaircaseFaceOccurrence d m :=
  fun
  | Sum.inl τ =>
      ⟨((lowerEndpointStaircaseFaceEquiv d m).symm τ).1,
        ((lowerEndpointStaircaseFaceEquiv d m).symm τ).isEndpoint⟩
  | Sum.inr τ =>
      ⟨((upperEndpointStaircaseFaceEquiv d m).symm τ).1,
        ((upperEndpointStaircaseFaceEquiv d m).symm τ).isEndpoint⟩

/-- Helper for Remark 50.3: rebuilding after endpoint normalization returns
the original endpoint occurrence. -/
theorem endpointOccurrenceToSharedFacetSum_leftInverse {d m : ℕ}
    (τ : EndpointStaircaseFaceOccurrence d m) :
    sharedFacetSumToEndpointOccurrence (endpointOccurrenceToSharedFacetSum τ) = τ := by
  -- Split at the initial endpoint; the noninitial branch is forced to be final.
  by_cases hzero : τ.1.omitted = 0
  · apply Subtype.ext
    simp [endpointOccurrenceToSharedFacetSum, sharedFacetSumToEndpointOccurrence,
      hzero]
  · have hlast := τ.omitted_eq_last_of_ne_zero hzero
    apply Subtype.ext
    simp [endpointOccurrenceToSharedFacetSum, sharedFacetSumToEndpointOccurrence,
      hzero, hlast]

/-- Helper for Remark 50.3: endpoint normalization after rebuilding returns
the original sum of normalized shared facets. -/
theorem endpointOccurrenceToSharedFacetSum_rightInverse {d m : ℕ}
    (τ : PositiveNormalizedSharedFacet d m ⊕
      BelowTopNormalizedSharedFacet d m) :
    endpointOccurrenceToSharedFacetSum (sharedFacetSumToEndpointOccurrence τ) = τ := by
  -- Each summand rebuilds an occurrence with its defining endpoint omission.
  cases τ with
  | inl τ =>
      simp [endpointOccurrenceToSharedFacetSum, sharedFacetSumToEndpointOccurrence,
        ((lowerEndpointStaircaseFaceEquiv d m).symm τ).2]
  | inr τ =>
      have hlast :
          ((upperEndpointStaircaseFaceEquiv d m).symm τ).1.omitted =
            Fin.last (d + 1) :=
        ((upperEndpointStaircaseFaceEquiv d m).symm τ).2
      have hzero :
          ((upperEndpointStaircaseFaceEquiv d m).symm τ).1.omitted ≠ 0 := by
        rw [hlast]
        intro heq
        have hval := congrArg Fin.val heq
        simp at hval
      simp [endpointOccurrenceToSharedFacetSum, sharedFacetSumToEndpointOccurrence,
        hzero]

/-- Helper for Remark 50.3: endpoint staircase-face occurrences are
canonically the disjoint union of the two normalized shared-facet sides. -/
def endpointStaircaseFaceEquiv (d m : ℕ) :
    EndpointStaircaseFaceOccurrence d m ≃
      PositiveNormalizedSharedFacet d m ⊕ BelowTopNormalizedSharedFacet d m :=
  { toFun := endpointOccurrenceToSharedFacetSum
    invFun := sharedFacetSumToEndpointOccurrence
    left_inv := endpointOccurrenceToSharedFacetSum_leftInverse
    right_inv := endpointOccurrenceToSharedFacetSum_rightInverse }

/-- Helper for Remark 50.3: the combined endpoint equivalence preserves
every enumerated centered-grid vertex. -/
theorem endpointStaircaseFaceEquiv_vertex {d m : ℕ}
    (τ : EndpointStaircaseFaceOccurrence d m) :
    τ.1.vertex = Sum.elim
      (fun facet ↦ facet.1.1.vertex)
      (fun facet ↦ facet.1.1.vertex)
      (endpointStaircaseFaceEquiv d m τ) := by
  -- Use the corresponding lower or upper computation rule in each endpoint case.
  funext j
  by_cases hzero : τ.1.omitted = 0
  · simpa [endpointStaircaseFaceEquiv, endpointOccurrenceToSharedFacetSum,
      hzero] using lowerEndpointStaircaseFaceEquiv_vertex
        (τ := (⟨τ.1, hzero⟩ : LowerEndpointOccurrence d m)) j
  · have hlast := τ.omitted_eq_last_of_ne_zero hzero
    simpa [endpointStaircaseFaceEquiv, endpointOccurrenceToSharedFacetSum,
      hzero] using upperEndpointStaircaseFaceEquiv_vertex
        (τ := (⟨τ.1, hlast⟩ : UpperEndpointOccurrence d m)) j

/-- Helper for Remark 50.3: a normalized shared facet on either extreme level
of the centered cube. -/
abbrev BoundarySharedFacet (d m : ℕ) :=
  TopBoundaryNormalizedSharedFacet d m ⊕
    BottomBoundaryNormalizedSharedFacet d m

/-- Helper for Remark 50.3: forget which extreme side presents a boundary
shared facet. -/
def BoundarySharedFacet.normalizedFacet {d m : ℕ}
    (facet : BoundarySharedFacet d m) : NormalizedSharedFacet d m :=
  Sum.elim Subtype.val Subtype.val facet

/-- Helper for Remark 50.3: enumerate the vertices of a boundary shared
facet in its canonical staircase order. -/
def BoundarySharedFacet.vertex {d m : ℕ} (facet : BoundarySharedFacet d m)
    (j : Fin (d + 1)) : CenteredGrid (d + 1) m :=
  facet.normalizedFacet.1.vertex j

/-- Helper for Theorem 57.6: the vertex of a tagged boundary facet is the
vertex of its underlying normalized shared facet. -/
theorem BoundarySharedFacet.vertex_eq_normalizedFacet {d m : ℕ}
    (facet : BoundarySharedFacet d m) (j : Fin (d + 1)) :
    facet.vertex j = facet.normalizedFacet.1.vertex j := by
  -- Expose the boundary vertex projection once at its construction owner.
  rfl

/-- Helper for Theorem 57.6: the normalized facet underlying a top boundary
tag is the stored normalized facet. -/
theorem BoundarySharedFacet.normalizedFacet_inl {d m : ℕ}
    (facet : TopBoundaryNormalizedSharedFacet d m) :
    BoundarySharedFacet.normalizedFacet
      (Sum.inl facet : BoundarySharedFacet d m) = facet.1 := by
  -- Evaluate the top branch of the tagged-facet projection.
  rfl

/-- Helper for Theorem 57.6: the normalized facet underlying a bottom boundary
tag is the stored normalized facet. -/
theorem BoundarySharedFacet.normalizedFacet_inr {d m : ℕ}
    (facet : BottomBoundaryNormalizedSharedFacet d m) :
    BoundarySharedFacet.normalizedFacet
      (Sum.inr facet : BoundarySharedFacet d m) = facet.1 := by
  -- Evaluate the bottom branch of the tagged-facet projection.
  rfl

/-- Helper for Theorem 57.6: the canonical vertex enumeration of a boundary
shared facet has no repetitions. -/
theorem BoundarySharedFacet.vertex_injective {d m : ℕ}
    (facet : BoundarySharedFacet d m) : Function.Injective facet.vertex := by
  -- Forgetting the extreme-side tag exposes the injective shared-facet enumeration.
  exact facet.normalizedFacet.1.vertex_injective

/-- Helper for Theorem 57.6: within one boundary facet, its unordered ridge
vertex set uniquely determines the omitted vertex. -/
theorem BoundarySharedFacet.ridgeVertexSet_injective {d m : ℕ}
    (facet : BoundarySharedFacet d m) :
    Function.Injective (fun omitted : Fin (d + 1) ↦
      Finset.univ.image (fun j : Fin d ↦ facet.vertex (omitted.succAbove j))) := by
  -- Apply the generic deletion-image theorem to the facet's injective enumeration.
  exact finsetImage_succAbove_injective_of_injective facet.vertex
    facet.vertex_injective

/-- Helper for Remark 50.3: every vertex of a boundary shared facet lies on
the boundary of the centered cube. -/
theorem BoundarySharedFacet.vertex_boundary {d m : ℕ}
    (facet : BoundarySharedFacet d m) (j : Fin (d + 1)) :
    centeredGridBoundary (facet.vertex j) := by
  -- The chosen summand supplies the appropriate extreme fixed-coordinate level.
  cases facet with
  | inl top =>
      exact top.1.1.vertex_boundary_of_level_extreme (Or.inr top.2) j
  | inr bottom =>
      exact bottom.1.1.vertex_boundary_of_level_extreme (Or.inl bottom.2) j

/-- Helper for Remark 50.3: boundary shared facets whose complete vertex set
lies in the positive closed hemisphere. -/
abbrev PositiveHemisphereBoundaryFacet (d m : ℕ) :=
  {facet : BoundarySharedFacet d m //
    ∀ j, centeredGridPositiveHemisphere (facet.vertex j)}

/-- Helper for Remark 50.3: positive-hemisphere boundary facets form a finite
type because they are a subtype of the finite boundary-facet type. -/
noncomputable instance positiveHemisphereBoundaryFacetFintype (d m : ℕ) :
    Fintype (PositiveHemisphereBoundaryFacet d m) :=
  Fintype.ofFinite _

/-- Helper for Remark 50.3: an occurrence of a codimension-one ridge in a
positive-hemisphere boundary facet. -/
structure PositiveHemisphereFaceOccurrence (d m : ℕ) where
  facet : PositiveHemisphereBoundaryFacet d m
  omitted : Fin (d + 1)
deriving DecidableEq, Fintype

/-- Helper for Remark 50.3: enumerate the retained ridge vertices of a
positive-hemisphere face occurrence. -/
def PositiveHemisphereFaceOccurrence.vertex {d m : ℕ}
    (occurrence : PositiveHemisphereFaceOccurrence d m) (j : Fin d) :
    CenteredGrid (d + 1) m :=
  occurrence.facet.1.vertex (occurrence.omitted.succAbove j)

/-- Helper for Remark 50.3: the retained occurrence vertex is the facet
vertex at the corresponding `succAbove` index. -/
theorem PositiveHemisphereFaceOccurrence.vertex_eq_facetVertex {d m : ℕ}
    (occurrence : PositiveHemisphereFaceOccurrence d m) (j : Fin d) :
    occurrence.vertex j =
      occurrence.facet.1.vertex (occurrence.omitted.succAbove j) := by
  -- Expose the owner computation rule for clients of the occurrence API.
  rfl

/-- Helper for Remark 50.3: every retained ridge vertex remains in the
positive closed hemisphere. -/
theorem PositiveHemisphereFaceOccurrence.vertex_positive {d m : ℕ}
    (occurrence : PositiveHemisphereFaceOccurrence d m) (j : Fin d) :
    centeredGridPositiveHemisphere (occurrence.vertex j) := by
  -- Apply the positivity certificate of the stored boundary facet.
  exact occurrence.facet.2 (occurrence.omitted.succAbove j)

/-- Helper for Remark 50.3: every retained ridge vertex remains on the
boundary of the centered cube. -/
theorem PositiveHemisphereFaceOccurrence.vertex_boundary {d m : ℕ}
    (occurrence : PositiveHemisphereFaceOccurrence d m) (j : Fin d) :
    centeredGridBoundary (occurrence.vertex j) := by
  -- Apply the boundary computation for the stored extreme shared facet.
  exact occurrence.facet.1.vertex_boundary (occurrence.omitted.succAbove j)

/-- Helper for Remark 50.3: the unordered finite set of retained vertices of
a positive-hemisphere ridge occurrence. -/
def PositiveHemisphereFaceOccurrence.ridgeVertexSet {d m : ℕ}
    (occurrence : PositiveHemisphereFaceOccurrence d m) :
    Finset (CenteredGrid (d + 1) m) :=
  Finset.univ.image occurrence.vertex

/-- Helper for Remark 50.3: the unordered ridge set is the image of the
facet vertices whose indices survive the stored omission. -/
theorem PositiveHemisphereFaceOccurrence.ridgeVertexSet_eq_facetImage {d m : ℕ}
    (occurrence : PositiveHemisphereFaceOccurrence d m) :
    occurrence.ridgeVertexSet =
      Finset.univ.image (fun j ↦
        occurrence.facet.1.vertex (occurrence.omitted.succAbove j)) := by
  -- Expand the ridge image and use the retained-vertex computation rule.
  apply Finset.image_congr
  intro j _
  exact occurrence.vertex_eq_facetVertex j

/-- Helper for Theorem 57.6: every positive-hemisphere ridge occurrence has
exactly `d` distinct retained vertices. -/
theorem PositiveHemisphereFaceOccurrence.ridgeVertexSet_card {d m : ℕ}
    (occurrence : PositiveHemisphereFaceOccurrence d m) :
    occurrence.ridgeVertexSet.card = d := by
  -- Delete one position from the injective boundary-facet enumeration.
  exact finsetImage_succAbove_card_of_injective occurrence.facet.1.vertex
    occurrence.facet.1.vertex_injective occurrence.omitted

/-- Helper for Remark 50.3: a positive-hemisphere ridge is equatorial when
all of its retained vertices have central first coordinate. -/
def PositiveHemisphereFaceOccurrence.IsEquatorial {d m : ℕ}
    (occurrence : PositiveHemisphereFaceOccurrence d m) : Prop :=
  ∀ j, centeredGridOnEquator (occurrence.vertex j)

/-- Helper for Remark 50.3: an equatorial ridge has central first coordinate
at every retained vertex. -/
theorem PositiveHemisphereFaceOccurrence.vertex_onEquator {d m : ℕ}
    {occurrence : PositiveHemisphereFaceOccurrence d m}
    (hequator : occurrence.IsEquatorial) (j : Fin d) :
    (occurrence.vertex j 0).1 = m := by
  -- Project the stored equator condition to its first-coordinate equation.
  exact (centeredGridOnEquator_iff (occurrence.vertex j)).mp (hequator j)


end StandardSphere.CubicalTucker
