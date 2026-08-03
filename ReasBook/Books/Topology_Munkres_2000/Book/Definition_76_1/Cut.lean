module

public import Topology_Munkres_2000.Book.Definition_74_1.CyclicPolygon

public section

namespace CyclicPolygon.Cut

noncomputable section

variable {n : ℕ}

/-- The index map for the vertices `p₀, p₁, …, pₖ` of the left cut polygon. -/
def leftIndex (k : Fin n) (i : Fin (k.val + 1)) : Fin n :=
  Fin.castLE (Nat.succ_le_iff.mpr k.isLt) i

/-- The left index map preserves the underlying natural-number index. -/
theorem leftIndex_val (k : Fin n) (i : Fin (k.val + 1)) :
    (leftIndex k i).val = i.val := by
  -- `Fin.castLE` changes only the bound, not the underlying index.
  rfl

/-- The index map for the vertices `p₀, pₖ, pₖ₊₁, …, pₙ₋₁` of the right cut polygon. -/
def rightIndex (k : Fin n) (i : Fin (n - k.val + 1)) : Fin n :=
  Fin.cases (Fin.castLE (Nat.succ_le_iff.mpr k.isLt) 0)
    (fun j ↦ Fin.castLE (Nat.le_of_eq (Nat.add_sub_of_le (Nat.le_of_lt k.isLt)))
      (Fin.natAdd k.val j)) i

/-- The initial right-hand vertex is `p₀`. -/
theorem rightIndex_zero (k : Fin n) : (rightIndex k 0).val = 0 := by
  -- The exceptional first branch of `rightIndex` is the original index zero.
  rfl

/-- After its initial vertex, the right index map lists the vertices starting at `pₖ`. -/
theorem rightIndex_succ (k : Fin n) (i : Fin (n - k.val)) :
    (rightIndex k i.succ).val = k.val + i.val := by
  -- Successor indices use the translated tail beginning at `k`.
  rfl

/-- Helper for Definition 76.1: the value of a right-cut index is zero initially and
is translated by `k - 1` afterward. -/
theorem rightIndex_val (k : Fin n) (i : Fin (n - k.val + 1)) :
    (rightIndex k i).val = if i.val = 0 then 0 else k.val + i.val - 1 := by
  -- Eliminate the exceptional zero branch once, leaving a stable value formula.
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp only [rightIndex_zero, Fin.val_zero, ↓reduceIte]
  · rw [rightIndex_succ]
    simp only [Fin.val_succ, Nat.succ_ne_zero, ↓reduceIte]
    omega

/-- Helper for Definition 76.1: the final inherited right-cut index is `n - 1`. -/
theorem rightIndex_last (k : Fin n) :
    (rightIndex k (Fin.last (n - k.val))).val = n - 1 := by
  -- The final value follows directly from the arbitrary-index normal form.
  rw [rightIndex_val]
  simp only [Fin.val_last]
  split
  · omega
  · omega

/-- Helper for Definition 76.1: the left cut index map is strictly increasing. -/
theorem leftIndex_strictMono (k : Fin n) : StrictMono (leftIndex k) := by
  -- Comparing values reduces strict monotonicity to the unchanged natural indices.
  intro i j hij
  exact hij

/-- Helper for Definition 76.1: the right cut index map is strictly increasing after `k > 0`. -/
theorem rightIndex_strictMono (k : Fin n) (hk : 0 < k.val) : StrictMono (rightIndex k) := by
  -- Compare the stable natural-number formulas for the two indices.
  intro i j hij
  rw [Fin.lt_iff_val_lt_val] at hij ⊢
  rw [rightIndex_val, rightIndex_val]
  split
  · split
    · omega
    · omega
  · split
    · omega
    · omega

/-- The lifted angle sequence for the left cut polygon. -/
def leftAngles (P : CyclicPolygon n) (k : Fin n) : Fin (k.val + 2) → ℝ :=
  Fin.lastCases (P.angles 0 + 2 * Real.pi)
    (fun i ↦ P.angles (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt k.isLt)) i))

/-- The left lifted angle sequence agrees with the original sequence before its closing angle. -/
theorem leftAngles_apply (P : CyclicPolygon n) (k : Fin n) (i : Fin (k.val + 1)) :
    leftAngles P k i.castSucc = P.angles (leftIndex k i).castSucc := by
  -- Before the closing entry, `lastCases` selects the inherited angle branch.
  simp only [leftAngles, Fin.lastCases_castSucc]
  rfl

/-- Helper for Definition 76.1: the left cut starts with the original initial angle. -/
theorem leftAngles_zero (P : CyclicPolygon n) (k : Fin n) :
    leftAngles P k 0 = P.angles 0 := by
  -- Rewrite literal zero into the inherited `castSucc` spelling.
  rw [← Fin.castSucc_zero]
  rw [leftAngles_apply]
  rfl

/-- The lifted angle sequence for the right cut polygon. -/
def rightAngles (P : CyclicPolygon n) (k : Fin n) : Fin (n - k.val + 2) → ℝ :=
  Fin.lastCases (P.angles 0 + 2 * Real.pi)
    (fun i ↦ P.angles (rightIndex k i).castSucc)

/-- The right lifted angle sequence agrees with the original sequence before its closing angle. -/
theorem rightAngles_apply (P : CyclicPolygon n) (k : Fin n)
    (i : Fin (n - k.val + 1)) :
    rightAngles P k i.castSucc = P.angles (rightIndex k i).castSucc := by
  -- Before the closing entry, `lastCases` selects the inherited angle branch.
  simp only [rightAngles, Fin.lastCases_castSucc]

/-- Helper for Definition 76.1: the right cut starts with the original initial angle. -/
theorem rightAngles_zero (P : CyclicPolygon n) (k : Fin n) :
    rightAngles P k 0 = P.angles 0 := by
  -- Rewrite literal zero into the inherited spelling and normalize its index.
  rw [← Fin.castSucc_zero]
  rw [rightAngles_apply]
  congr 2

/-- The left lifted angle sequence is strictly increasing. -/
theorem leftAngles_strictMono (P : CyclicPolygon n) (k : Fin n) :
    StrictMono (leftAngles P k) := by
  -- It suffices to compare each inherited angle with its immediate successor.
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · rw [leftAngles_apply, Fin.succ_last, leftAngles, Fin.lastCases_last]
    have hangle := P.angles_strictMono (show (leftIndex k (Fin.last k.val)).castSucc <
        Fin.last n by
      rw [Fin.lt_iff_val_lt_val]
      simp only [Fin.val_castSucc, leftIndex_val, Fin.val_last]
      exact k.isLt)
    rw [P.angles_last] at hangle
    exact hangle
  · have hsucc : j.castSucc.succ = j.succ.castSucc := by
      exact Fin.ext rfl
    rw [hsucc, leftAngles_apply, leftAngles_apply]
    exact P.angles_strictMono (Fin.castSucc_lt_castSucc_iff.mpr
      (leftIndex_strictMono k Fin.castSucc_lt_succ))

/-- The final left lifted angle closes one full turn after its initial angle. -/
theorem leftAngles_last (P : CyclicPolygon n) (k : Fin n) :
    leftAngles P k (Fin.last (k.val + 1)) = leftAngles P k 0 + 2 * Real.pi := by
  -- Normalize the closing and initial branches of the lifted sequence.
  rw [leftAngles, Fin.lastCases_last, leftAngles_zero]

/-- The right lifted angle sequence is strictly increasing. -/
theorem rightAngles_strictMono (P : CyclicPolygon n) (k : Fin n) (hk₁ : 1 < k.val) :
    StrictMono (rightAngles P k) := by
  -- It suffices to compare each inherited angle with its immediate successor.
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · rw [rightAngles_apply, Fin.succ_last, rightAngles, Fin.lastCases_last]
    have hangle := P.angles_strictMono (show
        (rightIndex k (Fin.last (n - k.val))).castSucc < Fin.last n by
      rw [Fin.lt_iff_val_lt_val]
      simp only [Fin.val_castSucc, rightIndex_last, Fin.val_last]
      omega)
    rw [P.angles_last] at hangle
    exact hangle
  · have hsucc : j.castSucc.succ = j.succ.castSucc := by
      exact Fin.ext rfl
    rw [hsucc, rightAngles_apply, rightAngles_apply]
    exact P.angles_strictMono (Fin.castSucc_lt_castSucc_iff.mpr
      (rightIndex_strictMono k (by omega) Fin.castSucc_lt_succ))

/-- The final right lifted angle closes one full turn after its initial angle. -/
theorem rightAngles_last (P : CyclicPolygon n) (k : Fin n) :
    rightAngles P k (Fin.last (n - k.val + 1)) = rightAngles P k 0 + 2 * Real.pi := by
  -- Normalize the closing and initial branches of the lifted sequence.
  rw [rightAngles, Fin.lastCases_last, rightAngles_zero]

/-- The left cut polygon has at least three vertices. -/
theorem leftThreeLe (k : Fin n) (hk₁ : 1 < k.val) : 3 ≤ k.val + 1 := by
  -- The cut contains vertices `0`, `1`, and `k` because `k > 1`.
  omega

/-- The right cut polygon has at least three vertices. -/
theorem rightThreeLe (k : Fin n) (hk₂ : k.val < n - 1) : 3 ≤ n - k.val + 1 := by
  -- There are at least two vertices from `k` through `n - 1`, plus the initial zero.
  omega

/-- The cyclic polygon with successive vertices `p₀, p₁, …, pₖ, p₀`. -/
def left (P : CyclicPolygon n) (k : Fin n) (hk₁ : 1 < k.val) :
    CyclicPolygon (k.val + 1) where
  three_le := leftThreeLe k hk₁
  center := P.center
  radius := P.radius
  radius_pos := P.radius_pos
  angles := leftAngles P k
  angles_strictMono := leftAngles_strictMono P k
  angles_last := leftAngles_last P k

/-- Helper for Definition 76.3: the left cut preserves the ambient circle center. -/
theorem left_center (P : CyclicPolygon n) (k : Fin n) (hk₁ : 1 < k.val) :
    (left P k hk₁).center = P.center := by
  -- Cutting changes the angular presentation but not its circle.
  rfl

/-- Helper for Definition 76.3: the left cut preserves the ambient circle radius. -/
theorem left_radius (P : CyclicPolygon n) (k : Fin n) (hk₁ : 1 < k.val) :
    (left P k hk₁).radius = P.radius := by
  -- Cutting changes the angular presentation but not its circle.
  rfl

/-- The cyclic polygon with successive vertices `p₀, pₖ, …, pₙ₋₁, p₀`. -/
def right (P : CyclicPolygon n) (k : Fin n) (hk₁ : 1 < k.val)
    (hk₂ : k.val < n - 1) :
    CyclicPolygon (n - k.val + 1) where
  three_le := rightThreeLe k hk₂
  center := P.center
  radius := P.radius
  radius_pos := P.radius_pos
  angles := rightAngles P k
  angles_strictMono := rightAngles_strictMono P k hk₁
  angles_last := rightAngles_last P k

/-- The vertices of the left cut polygon are the corresponding original vertices. -/
theorem left_apply (P : CyclicPolygon n) (k : Fin n) (hk₁ : 1 < k.val)
    (i : Fin (k.val + 1)) :
    (left P k hk₁).toPolygon.vertices i = P.toPolygon.vertices (leftIndex k i) := by
  -- Expand vertices once, then use the inherited angle computation rule.
  rw [CyclicPolygon.toPolygon_vertices, CyclicPolygon.toPolygon_vertices]
  unfold CyclicPolygon.vertex
  simp only [left]
  rw [leftAngles_apply]

/-- The vertices of the right cut polygon are the corresponding original vertices. -/
theorem right_apply (P : CyclicPolygon n) (k : Fin n) (hk₁ : 1 < k.val)
    (hk₂ : k.val < n - 1)
    (i : Fin (n - k.val + 1)) :
    (right P k hk₁ hk₂).toPolygon.vertices i =
      P.toPolygon.vertices (rightIndex k i) := by
  -- Expand vertices once, then use the inherited angle computation rule.
  rw [CyclicPolygon.toPolygon_vertices, CyclicPolygon.toPolygon_vertices]
  unfold CyclicPolygon.vertex
  simp only [right]
  rw [rightAngles_apply]

/-- The closing edge of the left cut polygon and the initial edge of the right cut polygon
are the same diagonal joining `p₀` and `pₖ`. -/
theorem commonEdge (P : CyclicPolygon n) (k : Fin n) (hk₁ : 1 < k.val)
    (hk₂ : k.val < n - 1) :
    (left P k hk₁).edgeSet (Fin.last k.val) = (right P k hk₁ hk₂).edgeSet 0 := by
  -- Normalize both edge sets to the two orientations of the shared diagonal.
  unfold CyclicPolygon.edgeSet Polygon.edgeSet
  rw [finRotate_last, finRotate_apply_zero]
  rw [left_apply, left_apply, right_apply, right_apply]
  have hn : 0 < n := by
    omega
  have htail : 0 < n - k.val := by
    omega
  have hleftLast : leftIndex k (Fin.last k.val) = k := by
    apply Fin.ext
    simp only [leftIndex_val, Fin.val_last]
  have hleftZero : leftIndex k 0 = ⟨0, hn⟩ := by
    apply Fin.ext
    simp only [leftIndex_val, Fin.val_zero]
  have hrightZero : rightIndex k 0 = ⟨0, hn⟩ := by
    apply Fin.ext
    simpa only using rightIndex_zero k
  have hrightOne : rightIndex k 1 = k := by
    have hsucc : (⟨0, htail⟩ : Fin (n - k.val)).succ = 1 := by
      apply Fin.ext
      rw [Fin.val_succ]
      have honeLt : 1 < n - k.val + 1 := by
        omega
      have honeVal : (1 : Fin (n - k.val + 1)).val = 1 := by
        exact Nat.mod_eq_of_lt honeLt
      rw [honeVal]
    rw [← hsucc]
    apply Fin.ext
    simpa only [Nat.add_zero] using rightIndex_succ k ⟨0, htail⟩
  rw [hleftLast, hleftZero, hrightZero, hrightOne]
  exact affineSegment_comm ℝ _ _

/-- Helper for Definition 76.1: rotation commutes with the left index map away from
the closing diagonal. -/
theorem leftIndex_finRotate (k : Fin n) (i : Fin (k.val + 1))
    (hi : i ≠ Fin.last k.val) :
    leftIndex k (finRotate (k.val + 1) i) = finRotate n (leftIndex k i) := by
  -- Route correction: compare the two rotations through their total value formulas,
  -- rather than representing the index by a transported successor.
  cases n with
  | zero => exact k.elim0
  | succ n =>
      have hleftIndex_ne_last : leftIndex k i ≠ Fin.last n := by
        intro h
        have hval := congrArg Fin.val h
        rw [leftIndex_val, Fin.val_last] at hval
        have hiLt := i.isLt
        have hkLt := k.isLt
        exact hi (Fin.ext (by
          simp only [Fin.val_last]
          omega))
      apply Fin.ext
      rw [leftIndex_val, coe_finRotate, coe_finRotate]
      simp only [hi, hleftIndex_ne_last, ↓reduceIte, leftIndex_val]

/-- Helper for Definition 76.1: rotation commutes with the right index map away from
the initial diagonal. -/
theorem rightIndex_finRotate (k : Fin n) (i : Fin (n - k.val + 1)) (hi : i ≠ 0) :
    rightIndex k (finRotate (n - k.val + 1) i) = finRotate n (rightIndex k i) := by
  -- Route correction: isolate the unique wrapping endpoint, then keep the ordinary
  -- branch entirely in the natural-number value normal form.
  cases n with
  | zero => exact k.elim0
  | succ n =>
      by_cases hlast : i = Fin.last (n + 1 - k.val)
      · subst i
        have hrightLast : rightIndex k (Fin.last (n + 1 - k.val)) = Fin.last n := by
          apply Fin.ext
          rw [rightIndex_last, Fin.val_last]
          omega
        rw [finRotate_last, hrightLast, finRotate_last]
        apply Fin.ext
        simpa only [Fin.val_zero] using rightIndex_zero k
      · have hrightIndex_ne_last : rightIndex k i ≠ Fin.last n := by
          intro h
          have hval := congrArg Fin.val h
          rw [rightIndex_val, Fin.val_last] at hval
          have hiVal : i.val ≠ 0 := by
            intro hiZero
            exact hi (Fin.ext hiZero)
          simp only [hiVal, ↓reduceIte] at hval
          have hiLtLast := Fin.lt_last_iff_ne_last.mpr hlast
          rw [Fin.lt_def, Fin.val_last] at hiLtLast
          exact hlast (Fin.ext (by
            simp only [Fin.val_last]
            omega))
        apply Fin.ext
        rw [rightIndex_val k (finRotate (n + 1 - k.val + 1) i)]
        rw [coe_finRotate i, coe_finRotate (rightIndex k i), rightIndex_val k i]
        have hiVal : i.val ≠ 0 := by
          intro hiZero
          exact hi (Fin.ext hiZero)
        simp only [hlast, hrightIndex_ne_last, hiVal, ↓reduceIte]
        rw [if_neg (by omega)]
        omega

/-- Helper for Definition 76.1: every nonclosing left edge inherits its original
supporting half-plane. -/
theorem left_inherited_supportingHalfspace (P : CyclicPolygon n) (k : Fin n)
    (hk₁ : 1 < k.val) (i : Fin (k.val + 1)) (hi : i ≠ Fin.last k.val) :
    (left P k hk₁).supportingHalfspace i = P.supportingHalfspace (leftIndex k i) := by
  -- Rewrite the two cut vertices through the index bridge to recover the original edge.
  ext x
  rw [CyclicPolygon.mem_supportingHalfspace_iff,
    CyclicPolygon.mem_supportingHalfspace_iff]
  rw [left_apply, left_apply, leftIndex_finRotate k i hi]

/-- Helper for Definition 76.1: every noninitial right edge inherits its original
supporting half-plane. -/
theorem right_inherited_supportingHalfspace (P : CyclicPolygon n) (k : Fin n)
    (hk₁ : 1 < k.val) (hk₂ : k.val < n - 1) (i : Fin (n - k.val + 1)) (hi : i ≠ 0) :
    (right P k hk₁ hk₂).supportingHalfspace i = P.supportingHalfspace (rightIndex k i) := by
  -- Rewrite the two cut vertices through the index bridge to recover the original edge.
  ext x
  rw [CyclicPolygon.mem_supportingHalfspace_iff,
    CyclicPolygon.mem_supportingHalfspace_iff]
  rw [right_apply, right_apply, rightIndex_finRotate k i hi]

/-- Helper for Definition 76.1: reversing a based directed segment negates its
signed-area test. -/
theorem signedArea_sub_swap (a b x : EuclideanSpace ℝ (Fin 2)) :
    CyclicPolygon.signedArea (a - b) (x - b) =
      -CyclicPolygon.signedArea (b - a) (x - a) := by
  -- Use the determinant identity supplied by the signed-area owner API.
  exact CyclicPolygon.signedArea_sub_swap a b x

/-- Helper for Definition 76.1: a cyclic polygon has a valid initial vertex index. -/
theorem indexZero_isLt (P : CyclicPolygon n) : 0 < n := by
  -- At least three vertices in particular gives a nonempty index type.
  exact lt_of_lt_of_le (by decide) P.three_le

/-- Helper for Definition 76.1: the canonical index of the initial vertex. -/
def indexZero (P : CyclicPolygon n) : Fin n :=
  ⟨0, indexZero_isLt P⟩

/-- Helper for Proposition 76.2: the canonical initial cyclic index has value zero. -/
theorem indexZero_val (P : CyclicPolygon n) : (indexZero P).val = 0 := by
  -- The proof-carrying index retains its literal natural-number value.
  rfl

/-- Helper for Definition 76.1: the left closing half-plane is the nonpositive
side of the diagonal oriented from `p₀` to `pₖ`. -/
theorem mem_left_diagonal_supportingHalfspace_iff (P : CyclicPolygon n) (k : Fin n)
    (hk₁ : 1 < k.val) (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ (left P k hk₁).supportingHalfspace (Fin.last k.val) ↔
      CyclicPolygon.signedArea
        (P.toPolygon.vertices k - P.toPolygon.vertices (indexZero P))
        (x - P.toPolygon.vertices (indexZero P)) ≤ 0 := by
  -- Normalize the closing edge to `pₖ → p₀`, then reverse its signed-area test.
  rw [CyclicPolygon.mem_supportingHalfspace_iff, finRotate_last]
  rw [left_apply, left_apply]
  have hleftLast : leftIndex k (Fin.last k.val) = k := by
    apply Fin.ext
    simp only [leftIndex_val, Fin.val_last]
  have hleftZero : leftIndex k 0 = indexZero P := by
    apply Fin.ext
    simp only [leftIndex_val, Fin.val_zero, indexZero]
  rw [hleftLast, hleftZero, signedArea_sub_swap]
  exact neg_nonneg

/-- Helper for Definition 76.1: the right initial half-plane is the nonnegative
side of the diagonal oriented from `p₀` to `pₖ`. -/
theorem mem_right_diagonal_supportingHalfspace_iff (P : CyclicPolygon n) (k : Fin n)
    (hk₁ : 1 < k.val) (hk₂ : k.val < n - 1) (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ (right P k hk₁ hk₂).supportingHalfspace 0 ↔
      0 ≤ CyclicPolygon.signedArea
        (P.toPolygon.vertices k - P.toPolygon.vertices (indexZero P))
        (x - P.toPolygon.vertices (indexZero P)) := by
  -- Normalize the initial edge directly to the diagonal `p₀ → pₖ`.
  rw [CyclicPolygon.mem_supportingHalfspace_iff, finRotate_apply_zero]
  rw [right_apply, right_apply]
  have htail : 0 < n - k.val := by
    omega
  have hrightZero : rightIndex k 0 = indexZero P := by
    apply Fin.ext
    simpa only [indexZero] using rightIndex_zero k
  have hrightOne : rightIndex k 1 = k := by
    have hsucc : (⟨0, htail⟩ : Fin (n - k.val)).succ = 1 := by
      apply Fin.ext
      simp only [Fin.val_succ]
      have honeLt : 1 < n - k.val + 1 := by
        omega
      exact (Nat.mod_eq_of_lt honeLt).symm
    rw [← hsucc]
    apply Fin.ext
    simpa only [Nat.add_zero] using rightIndex_succ k ⟨0, htail⟩
  rw [hrightZero, hrightOne]

/-- Helper for Definition 76.1: the left cut region is contained in the original
polygonal region. -/
theorem left_region_subset (P : CyclicPolygon n) (k : Fin n) (hk₁ : 1 < k.val) :
    (left P k hk₁).region ⊆ P.region := by
  -- Compare the convex hulls using the inclusion of cut vertices in the original range.
  rw [(left P k hk₁).region_eq_convexHull, P.region_eq_convexHull]
  apply convexHull_mono
  rintro x ⟨i, rfl⟩
  exact ⟨leftIndex k i, (left_apply P k hk₁ i).symm⟩

/-- Helper for Definition 76.1: the right cut region is contained in the original
polygonal region. -/
theorem right_region_subset (P : CyclicPolygon n) (k : Fin n) (hk₁ : 1 < k.val)
    (hk₂ : k.val < n - 1) :
    (right P k hk₁ hk₂).region ⊆ P.region := by
  -- Compare the convex hulls using the inclusion of cut vertices in the original range.
  rw [(right P k hk₁ hk₂).region_eq_convexHull, P.region_eq_convexHull]
  apply convexHull_mono
  rintro x ⟨i, rfl⟩
  exact ⟨rightIndex k i, (right_apply P k hk₁ hk₂ i).symm⟩

/-- Helper for Definition 76.1: an original-region point on the nonpositive side
of the diagonal belongs to the left cut region. -/
theorem mem_left_region_of_mem_region_of_diagonal_nonpos (P : CyclicPolygon n)
    (k : Fin n) (hk₁ : 1 < k.val) (x : EuclideanSpace ℝ (Fin 2))
    (hx : x ∈ P.region)
    (hdiag : CyclicPolygon.signedArea
      (P.toPolygon.vertices k - P.toPolygon.vertices (indexZero P))
      (x - P.toPolygon.vertices (indexZero P)) ≤ 0) :
    x ∈ (left P k hk₁).region := by
  -- Check the exceptional diagonal separately; every other half-plane is inherited.
  rw [(left P k hk₁).region_eq_iInter_supportingHalfspace]
  refine Set.mem_iInter.mpr (fun i ↦ ?_)
  by_cases hi : i = Fin.last k.val
  · subst i
    exact (mem_left_diagonal_supportingHalfspace_iff P k hk₁ x).mpr hdiag
  · rw [left_inherited_supportingHalfspace P k hk₁ i hi]
    rw [P.region_eq_iInter_supportingHalfspace] at hx
    exact Set.mem_iInter.mp hx (leftIndex k i)

/-- Helper for Definition 76.1: an original-region point on the nonnegative side
of the diagonal belongs to the right cut region. -/
theorem mem_right_region_of_mem_region_of_diagonal_nonneg (P : CyclicPolygon n)
    (k : Fin n) (hk₁ : 1 < k.val) (hk₂ : k.val < n - 1)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ P.region)
    (hdiag : 0 ≤ CyclicPolygon.signedArea
      (P.toPolygon.vertices k - P.toPolygon.vertices (indexZero P))
      (x - P.toPolygon.vertices (indexZero P))) :
    x ∈ (right P k hk₁ hk₂).region := by
  -- Check the exceptional diagonal separately; every other half-plane is inherited.
  rw [(right P k hk₁ hk₂).region_eq_iInter_supportingHalfspace]
  refine Set.mem_iInter.mpr (fun i ↦ ?_)
  by_cases hi : i = 0
  · subst i
    exact (mem_right_diagonal_supportingHalfspace_iff P k hk₁ hk₂ x).mpr hdiag
  · rw [right_inherited_supportingHalfspace P k hk₁ hk₂ i hi]
    rw [P.region_eq_iInter_supportingHalfspace] at hx
    exact Set.mem_iInter.mp hx (rightIndex k i)

/-- The original filled polygonal region is the union of the two regions cut along the
diagonal joining `p₀` and `pₖ`. -/
theorem region_eq_union (P : CyclicPolygon n) (k : Fin n) (hk₁ : 1 < k.val)
    (hk₂ : k.val < n - 1) :
    P.region = (left P k hk₁).region ∪ (right P k hk₁ hk₂).region := by
  -- The cut regions lie in the original convex hull; conversely the diagonal sign
  -- places every original-region point on at least one side of the cut.
  ext x
  constructor
  · intro hx
    have hsign := le_total 0 (CyclicPolygon.signedArea
      (P.toPolygon.vertices k - P.toPolygon.vertices (indexZero P))
      (x - P.toPolygon.vertices (indexZero P)))
    cases hsign with
    | inl hnonneg =>
        exact Set.mem_union_right _
          (mem_right_region_of_mem_region_of_diagonal_nonneg P k hk₁ hk₂ x hx hnonneg)
    | inr hnonpos =>
        exact Set.mem_union_left _
          (mem_left_region_of_mem_region_of_diagonal_nonpos P k hk₁ x hx hnonpos)
  · intro hx
    rcases hx with hx | hx
    · exact left_region_subset P k hk₁ hx
    · exact right_region_subset P k hk₁ hk₂ hx


end

end CyclicPolygon.Cut
