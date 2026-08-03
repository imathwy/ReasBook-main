module

public import Topology_Munkres_2000.Book.Definition_76_1.Cut

public section

open Set

namespace CyclicPolygon

noncomputable section

/-- Helper for Definition 76.3: a pre-wrap cyclic vertex index remains below the
number of vertices. -/
theorem rotatedBeforeVertexIndex_lt {n : ℕ} (start i : Fin n)
    (h : i.val < n - start.val) : start.val + i.val < n := by
  omega

/-- Helper for Definition 76.3: a post-wrap cyclic vertex index remains below the
number of vertices. -/
theorem rotatedAfterVertexIndex_lt {n : ℕ} (start i : Fin n) :
    i.val - (n - start.val) < n := by
  omega

/-- Helper for Definition 76.3: the cyclic index obtained by starting the presentation
at `start` and then advancing by `i`. -/
def rotatedIndex {n : ℕ} (start i : Fin n) : Fin n :=
  if h : i.val < n - start.val then
    ⟨start.val + i.val, rotatedBeforeVertexIndex_lt start i h⟩
  else
    ⟨i.val - (n - start.val), rotatedAfterVertexIndex_lt start i⟩

/-- Helper for Definition 76.3: cyclic reindexing is addition in `Fin n`. -/
theorem rotatedIndex_eq_add {n : ℕ} (start i : Fin n) :
    rotatedIndex start i = start + i := by
  -- Compare the wrapped and unwrapped branches with modular addition.
  apply Fin.ext
  unfold rotatedIndex
  split
  next hbefore =>
    simp only [Fin.val_add]
    rw [Nat.mod_eq_of_lt (rotatedBeforeVertexIndex_lt start i hbefore)]
  next hafter =>
    simp only [Fin.val_add]
    have hwrap : n ≤ start.val + i.val := by
      omega
    have hreduced : start.val + i.val - n < n := by
      omega
    rw [Nat.mod_eq_sub_mod hwrap, Nat.mod_eq_of_lt hreduced]
    omega

/-- Helper for Definition 76.3: cyclic reindexing commutes with cyclic successor. -/
theorem rotatedIndex_finRotate {n : ℕ} (start i : Fin n) :
    rotatedIndex start (finRotate n i) = finRotate n (rotatedIndex start i) := by
  -- Local instance justification (finite cyclic arithmetic): `i : Fin n` proves
  -- the nonzero modulus required only to use the additive-group successor formula.
  letI : NeZero n := i.neZero
  rw [rotatedIndex_eq_add, rotatedIndex_eq_add, finRotate_apply, finRotate_apply]
  exact (add_assoc start i 1).symm

/-- Helper for Definition 76.3: an unwrapped pre-wrap rotated index lies in the
lifted angle domain. -/
theorem rotatedBeforeIndex_lt {n : ℕ} (start : Fin n) (i : Fin (n + 1))
    (h : i.val < n - start.val) : start.val + i.val < n + 1 := by
  omega

/-- Helper for Definition 76.3: an unwrapped post-wrap rotated index lies in the
lifted angle domain. -/
theorem rotatedAfterIndex_lt {n : ℕ} (start : Fin n) (i : Fin (n + 1)) :
    i.val - (n - start.val) < n + 1 := by
  omega

/-- Helper for Definition 76.3: the lifted angle sequence after cyclically moving
`start` to index zero. -/
def rotatedAngles {n : ℕ} (poly : CyclicPolygon n) (start : Fin n) :
    Fin (n + 1) → ℝ :=
  fun i ↦
    if h : i.val < n - start.val then
      poly.angles ⟨start.val + i.val, rotatedBeforeIndex_lt start i h⟩
    else
      poly.angles ⟨i.val - (n - start.val), rotatedAfterIndex_lt start i⟩ +
        2 * Real.pi

/-- Helper for Definition 76.3: cyclic rotation preserves strict increase of the
unwrapped angle presentation. -/
theorem rotatedAngles_strictMono {n : ℕ} (poly : CyclicPolygon n) (start : Fin n) :
    StrictMono (rotatedAngles poly start) := by
  intro i j hij
  rw [Fin.lt_def] at hij
  unfold rotatedAngles
  split
  next hi =>
    split
    next hj =>
      -- Before wrapping, both old indices increase by the same offset.
      exact poly.angles_strictMono (by simp only [Fin.lt_def]; omega)
    next hj =>
      -- Crossing the wrap passes through the old closing angle.
      calc
        poly.angles ⟨start.val + i.val, by omega⟩ <
            poly.angles (Fin.last n) :=
          poly.angles_strictMono (by simp only [Fin.lt_def, Fin.val_last]; omega)
        _ = poly.angles 0 + 2 * Real.pi := poly.angles_last
        _ ≤ poly.angles ⟨j.val - (n - start.val), by omega⟩ + 2 * Real.pi :=
          by simpa only [add_comm] using
            add_le_add_right (poly.angles_strictMono.monotone (Fin.zero_le _))
              (2 * Real.pi)
  next hi =>
    split
    next hj =>
      omega
    next hj =>
      -- After wrapping, subtracting the fixed threshold preserves order.
      simpa only [add_comm] using add_lt_add_right
        (poly.angles_strictMono (by simp only [Fin.lt_def]; omega)) (2 * Real.pi)

/-- Helper for Definition 76.3: the rotated lifted sequence still closes after one turn. -/
theorem rotatedAngles_last {n : ℕ} (poly : CyclicPolygon n) (start : Fin n) :
    rotatedAngles poly start (Fin.last n) =
      rotatedAngles poly start 0 + 2 * Real.pi := by
  unfold rotatedAngles
  rw [dif_neg (by simp only [Fin.val_last]; omega)]
  rw [dif_pos (by simp only [Fin.val_zero]; omega)]
  congr 1
  apply congrArg poly.angles
  apply Fin.ext
  simp only [Fin.val_mk, Fin.val_last, Fin.val_zero]
  omega

/-- Helper for Definition 76.3: cyclically rotate the indexed presentation of a
cyclic polygon without changing its geometric region. -/
def rotateFrom {n : ℕ} (poly : CyclicPolygon n) (start : Fin n) : CyclicPolygon n :=
  { three_le := poly.three_le
    center := poly.center
    radius := poly.radius
    radius_pos := poly.radius_pos
    angles := rotatedAngles poly start
    angles_strictMono := rotatedAngles_strictMono poly start
    angles_last := rotatedAngles_last poly start }

/-- Helper for Definition 76.3: cyclic rotation preserves the circle center. -/
theorem rotateFrom_center {n : ℕ} (poly : CyclicPolygon n) (start : Fin n) :
    (rotateFrom poly start).center = poly.center := by
  -- The rotated presentation changes only its angular indexing.
  rfl

/-- Helper for Definition 76.3: cyclic rotation preserves the circle radius. -/
theorem rotateFrom_radius {n : ℕ} (poly : CyclicPolygon n) (start : Fin n) :
    (rotateFrom poly start).radius = poly.radius := by
  -- The rotated presentation changes only its angular indexing.
  rfl

/-- Helper for Definition 76.3: a rotated polygon's `i`th vertex is the original
vertex at the corresponding cyclic index. -/
theorem rotateFrom_vertices {n : ℕ} (poly : CyclicPolygon n) (start i : Fin n) :
    (rotateFrom poly start).toPolygon.vertices i =
      poly.toPolygon.vertices (rotatedIndex start i) := by
  rw [toPolygon_vertices, toPolygon_vertices]
  unfold vertex rotateFrom rotatedAngles rotatedIndex
  split
  next h =>
    simp only [Fin.val_castSucc, h, ↓reduceDIte]
    have hindex :
        (⟨start.val + i.val, rotatedBeforeIndex_lt start i.castSucc h⟩ :
          Fin (n + 1)) =
          (⟨start.val + i.val, rotatedBeforeVertexIndex_lt start i h⟩ : Fin n).castSucc :=
      Fin.ext rfl
    rw [hindex]
  next h =>
    simp only [Fin.val_castSucc, h, ↓reduceDIte, Real.cos_add_two_pi,
      Real.sin_add_two_pi]
    have hindex :
        (⟨i.val - (n - start.val), rotatedAfterIndex_lt start i.castSucc⟩ :
          Fin (n + 1)) =
          (⟨i.val - (n - start.val), rotatedAfterVertexIndex_lt start i⟩ : Fin n).castSucc :=
      Fin.ext rfl
    rw [hindex]

/-- Helper for Definition 76.3: cyclic index rotation is injective. -/
theorem rotatedIndex_injective {n : ℕ} (start : Fin n) :
    Function.Injective (rotatedIndex start) := by
  intro i j hij
  unfold rotatedIndex at hij
  split at hij
  next hi =>
    split at hij
    next hj =>
      apply Fin.ext
      have hval := congrArg Fin.val hij
      simp only [Fin.val_mk] at hval
      omega
    next hj =>
      have hval := congrArg Fin.val hij
      simp only [Fin.val_mk] at hval
      omega
  next hi =>
    split at hij
    next hj =>
      have hval := congrArg Fin.val hij
      simp only [Fin.val_mk] at hval
      omega
    next hj =>
      apply Fin.ext
      have hval := congrArg Fin.val hij
      simp only [Fin.val_mk] at hval
      omega

/-- Helper for Definition 76.3: cyclic index rotation is surjective. -/
theorem rotatedIndex_surjective {n : ℕ} (start : Fin n) :
    Function.Surjective (rotatedIndex start) :=
  Finite.surjective_of_injective (rotatedIndex_injective start)

/-- Helper for Definition 76.3: cyclic rotation of the presentation preserves the
filled polygonal region. -/
theorem rotateFrom_region {n : ℕ} (poly : CyclicPolygon n) (start : Fin n) :
    (rotateFrom poly start).region = poly.region := by
  have hrange : Set.range (rotateFrom poly start).toPolygon.vertices =
      Set.range poly.toPolygon.vertices := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨rotatedIndex start i, (rotateFrom_vertices poly start i).symm⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨i, hi⟩ := rotatedIndex_surjective start j
      refine ⟨i, ?_⟩
      rw [rotateFrom_vertices, hi]
  rw [(rotateFrom poly start).region_eq_convexHull, poly.region_eq_convexHull,
    hrange]

/-- Helper for Definition 76.3: a cyclic polygon can be transported across an
equality of its vertex counts. -/
def castVertexCount {first second : ℕ} (h : first = second)
    (poly : CyclicPolygon first) : CyclicPolygon second :=
  h ▸ poly

/-- Helper for Definition 76.3: transporting the vertex count preserves each
indexed vertex after casting its index. -/
theorem castVertexCount_vertices {first second : ℕ} (h : first = second)
    (poly : CyclicPolygon first) (i : Fin first) :
    (castVertexCount h poly).toPolygon.vertices (Fin.cast h i) =
      poly.toPolygon.vertices i := by
  -- Equality elimination reduces both the polygon and its index to their originals.
  subst second
  rfl

/-- Helper for Definition 76.3: transporting the vertex count preserves the
filled region as a subset of the plane. -/
theorem castVertexCount_region {first second : ℕ} (h : first = second)
    (poly : CyclicPolygon first) : (castVertexCount h poly).region = poly.region := by
  -- The transport is definitionally the identity once the count equality is eliminated.
  subst second
  rfl

/-- Helper for Definition 76.3: transporting the vertex count preserves the
circle center. -/
theorem castVertexCount_center {first second : ℕ} (h : first = second)
    (poly : CyclicPolygon first) : (castVertexCount h poly).center = poly.center := by
  -- Eliminate the count equality before comparing the record projection.
  subst second
  rfl

/-- Helper for Definition 76.3: transporting the vertex count preserves the
circle radius. -/
theorem castVertexCount_radius {first second : ℕ} (h : first = second)
    (poly : CyclicPolygon first) : (castVertexCount h poly).radius = poly.radius := by
  -- Eliminate the count equality before comparing the record projection.
  subst second
  rfl

/-- Helper for Definition 76.3: casting a finite index commutes with cyclic
successor rotation. -/
theorem finCast_finRotate {first second : ℕ} (h : first = second) (i : Fin first) :
    Fin.cast h (finRotate first i) = finRotate second (Fin.cast h i) := by
  -- With equal bounds, both rotations and both casts are literally the same map.
  subst second
  rfl

/-- Helper for Definition 76.3: index one belongs to every cyclic polygon's lifted
angle domain. -/
theorem firstSuccessorIndex_lt {n : ℕ} (poly : CyclicPolygon n) : 1 < n + 1 := by
  have hn := poly.three_le
  omega

/-- Helper for Definition 76.3: the first successor in a cyclic polygon's lifted
angle domain. -/
def firstSuccessorIndex {n : ℕ} (poly : CyclicPolygon n) : Fin (n + 1) :=
  ⟨1, firstSuccessorIndex_lt poly⟩

/-- Helper for Definition 76.3: the first successor retains value one. -/
theorem firstSuccessorIndex_val {n : ℕ} (poly : CyclicPolygon n) :
    (firstSuccessorIndex poly).val = 1 := by
  rfl

/-- Helper for Definition 76.3: the positive angular step used to insert `m - 2`
vertices into the first gap of a cyclic polygon. -/
def insertionStep {m n : ℕ} (hm : 3 ≤ m) (poly : CyclicPolygon n) : ℝ :=
  (poly.angles (firstSuccessorIndex poly) - poly.angles 0) / ((m : ℝ) - 1)

/-- Helper for Definition 76.3: the tail index of the combined presentation lies
in the original lifted angle domain. -/
theorem insertedTailIndex_lt {m n : ℕ} (hm : 3 ≤ m) (poly : CyclicPolygon n)
    (i : Fin (m + n - 2 + 1)) : i.val - (m - 2) < n + 1 := by
  omega

/-- Helper for Definition 76.3: insert `m - 2` equally spaced angles into the
first angular gap, retaining the remaining lifted angles. -/
def insertedAngles {m n : ℕ} (hm : 3 ≤ m) (poly : CyclicPolygon n) :
    Fin (m + n - 2 + 1) → ℝ :=
  fun i ↦
    if i.val < m then
      poly.angles 0 + (i.val : ℝ) * insertionStep hm poly
    else
      poly.angles ⟨i.val - (m - 2), insertedTailIndex_lt hm poly i⟩

/-- Helper for Definition 76.3: the inserted angle presentation is strictly increasing. -/
theorem insertedAngles_strictMono {m n : ℕ} (hm : 3 ≤ m)
    (poly : CyclicPolygon n) : StrictMono (insertedAngles hm poly) := by
  have hn : 3 ≤ n := poly.three_le
  have hgap : poly.angles 0 < poly.angles (firstSuccessorIndex poly) := by
    apply poly.angles_strictMono
    rw [Fin.lt_def, firstSuccessorIndex_val]
    simp only [Fin.val_zero]
    omega
  have hmReal : (1 : ℝ) < m := by
    exact_mod_cast (show 1 < m by omega)
  have hstep : 0 < insertionStep hm poly := by
    unfold insertionStep
    exact div_pos (sub_pos.mpr hgap) (sub_pos.mpr hmReal)
  have hstepTotal : ((m : ℝ) - 1) * insertionStep hm poly =
      poly.angles (firstSuccessorIndex poly) - poly.angles 0 := by
    unfold insertionStep
    exact mul_div_cancel₀ _ (sub_ne_zero.mpr hmReal.ne')
  intro i j hij
  rw [Fin.lt_def] at hij
  unfold insertedAngles
  split
  next hi =>
    split
    next hj =>
      -- Within the inserted block, positive step size preserves index order.
      have hcast : (i.val : ℝ) < j.val := by exact_mod_cast hij
      simpa only [add_comm] using
        add_lt_add_left (mul_lt_mul_of_pos_right hcast hstep) (poly.angles 0)
    next hj =>
      -- Every inserted point is at most the old second angle, while the tail starts later.
      have hicast : (i.val : ℝ) ≤ (m : ℝ) - 1 := by
        calc
          (i.val : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by
            exact_mod_cast (show i.val ≤ m - 1 by omega)
          _ = (m : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega)]
            norm_num
      have hinterp :
          poly.angles 0 + (i.val : ℝ) * insertionStep hm poly ≤
            poly.angles (firstSuccessorIndex poly) := by
        calc
          poly.angles 0 + (i.val : ℝ) * insertionStep hm poly ≤
              poly.angles 0 + ((m : ℝ) - 1) * insertionStep hm poly :=
            by simpa only [add_comm] using
              add_le_add_left (mul_le_mul_of_nonneg_right hicast hstep.le)
                (poly.angles 0)
          _ = poly.angles (firstSuccessorIndex poly) := by rw [hstepTotal]; ring
      have htailVal : 1 < j.val - (m - 2) := by
        have hjBound := j.isLt
        omega
      have htail : poly.angles (firstSuccessorIndex poly) <
          poly.angles ⟨j.val - (m - 2), insertedTailIndex_lt hm poly j⟩ :=
        poly.angles_strictMono (by
          rw [Fin.lt_def, firstSuccessorIndex_val]
          exact htailVal)
      exact lt_of_le_of_lt hinterp htail
  next hi =>
    split
    next hj =>
      omega
    next hj =>
      -- In the retained tail, subtracting the insertion offset preserves order.
      exact poly.angles_strictMono (by simp only [Fin.lt_def]; omega)

/-- Helper for Definition 76.3: the inserted lifted sequence closes after one turn. -/
theorem insertedAngles_last {m n : ℕ} (hm : 3 ≤ m) (poly : CyclicPolygon n) :
    insertedAngles hm poly (Fin.last (m + n - 2)) =
      insertedAngles hm poly 0 + 2 * Real.pi := by
  have hn : 3 ≤ n := poly.three_le
  unfold insertedAngles
  rw [if_neg (by simp only [Fin.val_last]; omega)]
  rw [if_pos (by simp only [Fin.val_zero]; omega)]
  have hindex :
      (⟨(Fin.last (m + n - 2)).val - (m - 2),
        insertedTailIndex_lt hm poly (Fin.last (m + n - 2))⟩ : Fin (n + 1)) =
        Fin.last n := by
    apply Fin.ext
    simp only [Fin.val_mk, Fin.val_last]
    omega
  rw [hindex, poly.angles_last]
  simp only [Fin.val_zero, Nat.cast_zero, zero_mul, add_zero]

/-- Helper for Definition 76.3: the combined polygon has at least three vertices. -/
theorem insertedVertexCount_three_le {m n : ℕ} (hm : 3 ≤ m)
    (poly : CyclicPolygon n) : 3 ≤ m + n - 2 := by
  have hn : 3 ≤ n := poly.three_le
  omega

/-- Helper for Definition 76.3: the cyclic polygon obtained by inserting `m - 2`
vertices into the first angular gap of `poly`. -/
def insertInFirstGap {m n : ℕ} (hm : 3 ≤ m) (poly : CyclicPolygon n) :
    CyclicPolygon (m + n - 2) :=
  { three_le := insertedVertexCount_three_le hm poly
    center := poly.center
    radius := poly.radius
    radius_pos := poly.radius_pos
    angles := insertedAngles hm poly
    angles_strictMono := insertedAngles_strictMono hm poly
    angles_last := insertedAngles_last hm poly }

/-- Helper for Definition 76.3: first-gap insertion preserves the circle center. -/
theorem insertInFirstGap_center {m n : ℕ} (hm : 3 ≤ m) (poly : CyclicPolygon n) :
    (insertInFirstGap hm poly).center = poly.center := by
  rfl

/-- Helper for Definition 76.3: first-gap insertion preserves the circle radius. -/
theorem insertInFirstGap_radius {m n : ℕ} (hm : 3 ≤ m) (poly : CyclicPolygon n) :
    (insertInFirstGap hm poly).radius = poly.radius := by
  rfl

/-- Helper for Definition 76.3: first-gap insertion uses the inserted angle sequence. -/
theorem insertInFirstGap_angles {m n : ℕ} (hm : 3 ≤ m)
    (poly : CyclicPolygon n) (i : Fin (m + n - 2 + 1)) :
    (insertInFirstGap hm poly).angles i = insertedAngles hm poly i := by
  rfl

/-- Helper for Definition 76.3: the last inserted-gap index belongs to the combined
polygon. -/
theorem sharedIndex_lt {m n : ℕ} (hm : 3 ≤ m) (poly : CyclicPolygon n) :
    m - 1 < m + n - 2 := by
  have hn := poly.three_le
  omega

/-- Helper for Definition 76.3: the combined index of the old first successor. -/
def sharedIndex {m n : ℕ} (hm : 3 ≤ m) (poly : CyclicPolygon n) :
    Fin (m + n - 2) :=
  ⟨m - 1, sharedIndex_lt hm poly⟩

/-- Helper for Definition 76.3: the shared cut index has value `m - 1`. -/
theorem sharedIndex_val {m n : ℕ} (hm : 3 ≤ m) (poly : CyclicPolygon n) :
    (sharedIndex hm poly).val = m - 1 := by
  rfl

/-- Helper for Definition 76.3: the shared cut index leaves at least two vertices
on its left. -/
theorem sharedIndex_one_lt {m n : ℕ} (hm : 3 ≤ m) (poly : CyclicPolygon n) :
    1 < (sharedIndex hm poly).val := by
  rw [sharedIndex_val]
  omega

/-- Helper for Definition 76.3: the shared cut index leaves at least two vertices
on its right. -/
theorem sharedIndex_lt_last {m n : ℕ} (hm : 3 ≤ m) (poly : CyclicPolygon n) :
    (sharedIndex hm poly).val < m + n - 2 - 1 := by
  have hn := poly.three_le
  rw [sharedIndex_val]
  omega

/-- Helper for Definition 76.3: the right cut of the inserted polygon has the
original number of vertices. -/
theorem insertedRightCount {m n : ℕ} (hm : 3 ≤ m) (poly : CyclicPolygon n) :
    m + n - 2 - (sharedIndex hm poly).val + 1 = n := by
  have hn := poly.three_le
  rw [sharedIndex_val]
  omega

/-- Helper for Definition 76.3: index one belongs to the polygon vertex domain. -/
theorem firstVertexIndex_lt {n : ℕ} (poly : CyclicPolygon n) : 1 < n := by
  have hn := poly.three_le
  omega

/-- Helper for Definition 76.3: the first successor vertex index. -/
def firstVertexIndex {n : ℕ} (poly : CyclicPolygon n) : Fin n :=
  ⟨1, firstVertexIndex_lt poly⟩

/-- Helper for Definition 76.3: the first successor vertex retains value one. -/
theorem firstVertexIndex_val {n : ℕ} (poly : CyclicPolygon n) :
    (firstVertexIndex poly).val = 1 := by
  rfl

/-- Helper for Definition 76.3: the first vertex index is the cyclic successor of zero. -/
theorem firstVertexIndex_eq_finRotate_indexZero {n : ℕ} (poly : CyclicPolygon n) :
    firstVertexIndex poly = finRotate n (CyclicPolygon.Cut.indexZero poly) := by
  -- Local instance justification (finite cyclic arithmetic): `poly.three_le`
  -- supplies the nonzero modulus needed only to evaluate the numeral successor.
  have hthree : 3 ≤ n := poly.three_le
  have hpos : 0 < n := by
    omega
  have hn : n ≠ 0 := by
    exact Nat.ne_of_gt hpos
  letI : NeZero n := ⟨hn⟩
  rw [finRotate_apply]
  apply Fin.ext
  simp only [firstVertexIndex_val, Fin.val_add,
    CyclicPolygon.Cut.indexZero_val, Fin.val_one' n, zero_add, Nat.mod_mod]
  have hone : 1 < n := by
    omega
  rw [Nat.mod_eq_of_lt hone]

/-- Helper for Definition 76.3: every positive old vertex has a retained combined index. -/
theorem retainedPositiveIndex_lt {m n : ℕ} (hm : 3 ≤ m)
    (poly : CyclicPolygon n) (i : Fin n) (hi : 0 < i.val) :
    i.val + (m - 2) < m + n - 2 := by
  have hn := poly.three_le
  omega

/-- Helper for Definition 76.3: the combined index retaining a positive old vertex. -/
def retainedPositiveIndex {m n : ℕ} (hm : 3 ≤ m)
    (poly : CyclicPolygon n) (i : Fin n) (hi : 0 < i.val) :
    Fin (m + n - 2) :=
  ⟨i.val + (m - 2), retainedPositiveIndex_lt hm poly i hi⟩

/-- Helper for Definition 76.3: a retained positive index has the expected offset value. -/
theorem retainedPositiveIndex_val {m n : ℕ} (hm : 3 ≤ m)
    (poly : CyclicPolygon n) (i : Fin n) (hi : 0 < i.val) :
    (retainedPositiveIndex hm poly i hi).val = i.val + (m - 2) := by
  rfl

/-- Helper for Definition 76.3: index zero is unchanged by first-gap insertion. -/
theorem insertInFirstGap_vertex_zero {m n : ℕ} (hm : 3 ≤ m)
    (poly : CyclicPolygon n) :
    (insertInFirstGap hm poly).toPolygon.vertices
        (CyclicPolygon.Cut.indexZero (insertInFirstGap hm poly)) =
      poly.toPolygon.vertices (CyclicPolygon.Cut.indexZero poly) := by
  rw [toPolygon_vertices, toPolygon_vertices]
  unfold vertex
  rw [insertInFirstGap_center, insertInFirstGap_radius, insertInFirstGap_angles]
  unfold insertedAngles
  rw [if_pos (by simp only [Fin.val_castSucc, CyclicPolygon.Cut.indexZero_val]; omega)]
  simp only [Fin.val_castSucc, CyclicPolygon.Cut.indexZero_val, Nat.cast_zero,
    zero_mul, add_zero]
  have hindex :
      (CyclicPolygon.Cut.indexZero poly).castSucc = (0 : Fin (n + 1)) := by
    apply Fin.ext
    simp only [Fin.val_castSucc, CyclicPolygon.Cut.indexZero_val, Fin.val_zero]
  rw [hindex]

/-- Helper for Definition 76.3: the end of the inserted block is the old first
successor vertex. -/
theorem insertInFirstGap_vertex_shared {m n : ℕ} (hm : 3 ≤ m)
    (poly : CyclicPolygon n) :
    (insertInFirstGap hm poly).toPolygon.vertices (sharedIndex hm poly) =
      poly.toPolygon.vertices (firstVertexIndex poly) := by
  rw [toPolygon_vertices, toPolygon_vertices]
  unfold vertex
  rw [insertInFirstGap_center, insertInFirstGap_radius, insertInFirstGap_angles]
  unfold insertedAngles sharedIndex
  simp only [Fin.val_castSucc, Fin.val_mk, if_pos (by omega)]
  have htotal : ((m : ℝ) - 1) * insertionStep hm poly =
      poly.angles (firstSuccessorIndex poly) - poly.angles 0 := by
    unfold insertionStep
    have hmReal : (1 : ℝ) < m := by
      exact_mod_cast (show 1 < m by omega)
    exact mul_div_cancel₀ _ (sub_ne_zero.mpr hmReal.ne')
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hcast, htotal]
  have hindex : firstSuccessorIndex poly = (firstVertexIndex poly).castSucc := by
    apply Fin.ext
    rw [firstSuccessorIndex_val, Fin.val_castSucc, firstVertexIndex_val]
  rw [hindex]
  rw [if_pos (by omega)]
  ring

/-- Helper for Definition 76.3: every old vertex after the first successor is retained
at its offset combined index. -/
theorem insertInFirstGap_vertex_tail {m n : ℕ} (hm : 3 ≤ m)
    (poly : CyclicPolygon n) (i : Fin n) (hi : 1 < i.val) :
    (insertInFirstGap hm poly).toPolygon.vertices
        (retainedPositiveIndex hm poly i (lt_trans Nat.zero_lt_one hi)) =
      poly.toPolygon.vertices i := by
  have hnot : ¬ i.val + (m - 2) < m := by
    omega
  rw [toPolygon_vertices, toPolygon_vertices]
  unfold vertex
  rw [insertInFirstGap_center, insertInFirstGap_radius, insertInFirstGap_angles]
  unfold insertedAngles
  rw [if_neg (by
    rw [Fin.val_castSucc, retainedPositiveIndex_val]
    exact hnot)]
  have hindex :
      (⟨(retainedPositiveIndex hm poly i
            (lt_trans Nat.zero_lt_one hi)).castSucc.val - (m - 2),
        insertedTailIndex_lt hm poly
          (retainedPositiveIndex hm poly i (lt_trans Nat.zero_lt_one hi)).castSucc⟩ :
          Fin (n + 1)) =
        i.castSucc := by
    apply Fin.ext
    simp only [Fin.val_castSucc, retainedPositiveIndex, Fin.val_mk]
    omega
  rw [hindex]

/-- Helper for Definition 76.3: each vertex of the right cut of the inserted polygon
is the corresponding vertex of the original polygon. -/
theorem insertedRightCut_vertices {m n : ℕ} (hm : 3 ≤ m)
    (poly : CyclicPolygon n)
    (i : Fin (m + n - 2 - (sharedIndex hm poly).val + 1)) :
    (CyclicPolygon.Cut.right (insertInFirstGap hm poly) (sharedIndex hm poly)
        (sharedIndex_one_lt hm poly) (sharedIndex_lt_last hm poly)).toPolygon.vertices i =
      poly.toPolygon.vertices (Fin.cast (insertedRightCount hm poly) i) := by
  let combined := insertInFirstGap hm poly
  let k := sharedIndex hm poly
  let j : Fin n := Fin.cast (insertedRightCount hm poly) i
  have hkval : (sharedIndex hm poly).val = m - 1 := sharedIndex_val hm poly
  rw [CyclicPolygon.Cut.right_apply]
  by_cases hi0 : i.val = 0
  · have hcombinedIndex : CyclicPolygon.Cut.rightIndex k i =
        CyclicPolygon.Cut.indexZero combined := by
      apply Fin.ext
      rw [CyclicPolygon.Cut.rightIndex_val, CyclicPolygon.Cut.indexZero_val]
      simp only [hi0, if_pos]
    have hjzero : j = CyclicPolygon.Cut.indexZero poly := by
      apply Fin.ext
      simp only [j, Fin.coe_cast, hi0, CyclicPolygon.Cut.indexZero_val]
    calc
      combined.toPolygon.vertices (CyclicPolygon.Cut.rightIndex k i) =
          combined.toPolygon.vertices (CyclicPolygon.Cut.indexZero combined) :=
        congrArg combined.toPolygon.vertices hcombinedIndex
      _ = poly.toPolygon.vertices (CyclicPolygon.Cut.indexZero poly) :=
        insertInFirstGap_vertex_zero hm poly
      _ = poly.toPolygon.vertices j := congrArg poly.toPolygon.vertices hjzero.symm
  · by_cases hi1 : i.val = 1
    · have hcombinedIndex : CyclicPolygon.Cut.rightIndex k i = k := by
        apply Fin.ext
        rw [CyclicPolygon.Cut.rightIndex_val]
        simp only [hi0, if_false]
        dsimp only [k]
        omega
      have hjone : j = firstVertexIndex poly := by
        apply Fin.ext
        simp only [j, Fin.coe_cast, hi1, firstVertexIndex_val]
      calc
        combined.toPolygon.vertices (CyclicPolygon.Cut.rightIndex k i) =
            combined.toPolygon.vertices k := congrArg combined.toPolygon.vertices hcombinedIndex
        _ = poly.toPolygon.vertices (firstVertexIndex poly) :=
          insertInFirstGap_vertex_shared hm poly
        _ = poly.toPolygon.vertices j := congrArg poly.toPolygon.vertices hjone.symm
    · have hj : 1 < j.val := by
        simp only [j, Fin.coe_cast]
        omega
      have hcombinedIndex : CyclicPolygon.Cut.rightIndex k i =
          retainedPositiveIndex hm poly j (lt_trans Nat.zero_lt_one hj) := by
        apply Fin.ext
        rw [CyclicPolygon.Cut.rightIndex_val]
        simp only [hi0, if_false, retainedPositiveIndex_val, j, Fin.coe_cast]
        dsimp only [k]
        omega
      calc
        combined.toPolygon.vertices (CyclicPolygon.Cut.rightIndex k i) =
            combined.toPolygon.vertices
              (retainedPositiveIndex hm poly j (lt_trans Nat.zero_lt_one hj)) :=
          congrArg combined.toPolygon.vertices hcombinedIndex
        _ = poly.toPolygon.vertices j := insertInFirstGap_vertex_tail hm poly j hj

/-- Helper for Definition 76.3: the right cut of a first-gap insertion has the same
filled region as the original polygon. -/
theorem insertedRightCut_region {m n : ℕ} (hm : 3 ≤ m)
    (poly : CyclicPolygon n) :
    (CyclicPolygon.Cut.right (insertInFirstGap hm poly) (sharedIndex hm poly)
      (sharedIndex_one_lt hm poly) (sharedIndex_lt_last hm poly)).region = poly.region := by
  have hrange : Set.range
      (CyclicPolygon.Cut.right (insertInFirstGap hm poly) (sharedIndex hm poly)
        (sharedIndex_one_lt hm poly)
        (sharedIndex_lt_last hm poly)).toPolygon.vertices =
      Set.range poly.toPolygon.vertices := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.cast (insertedRightCount hm poly) i,
        (insertedRightCut_vertices hm poly i).symm⟩
    · rintro ⟨j, rfl⟩
      let i := Fin.cast (insertedRightCount hm poly).symm j
      refine ⟨i, ?_⟩
      rw [insertedRightCut_vertices]
      apply congrArg poly.toPolygon.vertices
      apply Fin.ext
      rfl
  rw [(CyclicPolygon.Cut.right (insertInFirstGap hm poly) (sharedIndex hm poly)
      (sharedIndex_one_lt hm poly) (sharedIndex_lt_last hm poly)).region_eq_convexHull,
    poly.region_eq_convexHull, hrange]

end


end CyclicPolygon
