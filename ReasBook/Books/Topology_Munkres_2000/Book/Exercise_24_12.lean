module

public import Topology_Munkres_2000.Book.Exercise_24_12.LongLine
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.SetTheory.Ordinal.FundamentalSequence

public section

open Set

universe u v

/-- Helper for Exercise 24.12: an order isomorphism restricts to predicates that it
matches pointwise. -/
lemma OrderIso.nonemptySubtypeEquiv {α : Type u} {β : Type v} [LE α] [LE β]
    (e : α ≃o β) (p : α → Prop) (q : β → Prop) (h : ∀ x, p x ↔ q (e x)) :
    Nonempty (Subtype p ≃o Subtype q) := by
  -- Restrict the underlying equivalence; order reflection is inherited from `e`.
  exact ⟨{ toEquiv := e.toEquiv.subtypeEquiv h, map_rel_iff' := e.map_rel_iff }⟩

/-- Helper for Exercise 24.12: the part below an interior point of a half-open
interval is the corresponding smaller half-open interval. -/
lemma icoIioOrderIsoNonempty {X : Type u} [LinearOrder X] (a b c : X)
    (hab : a < b) (hbc : b < c) :
    Nonempty (Set.Iio (⟨b, hab.le, hbc⟩ : Set.Ico a c) ≃o Set.Ico a b) := by
  -- Flatten the nested subtype while retaining the two endpoint inequalities.
  refine ⟨{
      toFun := fun x ↦ ⟨x.1.1, x.1.2.1, x.2⟩
      invFun := fun x ↦ ⟨⟨x.1, x.2.1, x.2.2.trans hbc⟩, x.2.2⟩
      left_inv := ?_
      right_inv := ?_
      map_rel_iff' := ?_ }⟩
  · intro x
    ext
    rfl
  · intro x
    ext
    rfl
  · intro x y
    rfl

/-- Helper for Exercise 24.12: the part at or above an interior point of a
half-open interval is the corresponding terminal half-open interval. -/
lemma icoIciOrderIsoNonempty {X : Type u} [LinearOrder X] (a b c : X)
    (hab : a < b) (hbc : b < c) :
    Nonempty (Set.Ici (⟨b, hab.le, hbc⟩ : Set.Ico a c) ≃o Set.Ico b c) := by
  -- Flatten the nested subtype while retaining the two endpoint inequalities.
  refine ⟨{
      toFun := fun x ↦ ⟨x.1.1, x.2, x.1.2.2⟩
      invFun := fun x ↦ ⟨⟨x.1, hab.le.trans x.2.1, x.2.2⟩, x.2.1⟩
      left_inv := ?_
      right_inv := ?_
      map_rel_iff' := ?_ }⟩
  · intro x
    ext
    rfl
  · intro x
    ext
    rfl
  · intro x y
    rfl

/-- Helper for Exercise 24.12: an interval splits at an interior point as the
lexicographic sum of its two adjacent half-open subintervals. -/
lemma icoOrderIsoSumLexNonempty {X : Type u} [LinearOrder X] (a b c : X)
    (hab : a < b) (hbc : b < c) :
    Nonempty (Set.Ico a c ≃o (Set.Ico a b ⊕ₗ Set.Ico b c)) := by
  -- Split inside the bounded subtype, then flatten both resulting pieces.
  let midpoint : Set.Ico a c := ⟨b, hab.le, hbc⟩
  rcases icoIioOrderIsoNonempty a b c hab hbc with ⟨eleft⟩
  rcases icoIciOrderIsoNonempty a b c hab hbc with ⟨eright⟩
  exact ⟨(OrderIso.sumLexIioIci midpoint).symm.trans
    (OrderIso.sumLexCongr eleft eright)⟩

/-- Helper for Exercise 24.12: positive affine interpolation stays below the right endpoint. -/
lemma affineInterpolation_lt_right (p q t : ℝ) (hpq : p < q) (ht : t < 1) :
    p + (q - p) * t < q := by
  nlinarith

/-- Helper for Exercise 24.12: every nondegenerate real half-open interval is
order-isomorphic to the unit half-open interval. -/
lemma realIcoOrderIsoUnitNonempty (p q : ℝ) (hpq : p < q) :
    Nonempty (Set.Ico p q ≃o Set.Ico (0 : ℝ) 1) := by
  -- Normalize by translation and positive scaling; the inverse reverses them.
  have hspan : 0 < q - p := sub_pos.mpr hpq
  refine ⟨{
      toFun := fun x ↦
        ⟨(x.1 - p) / (q - p),
          (div_nonneg (sub_nonneg.mpr x.2.1) hspan.le),
          (div_lt_one hspan).mpr (sub_lt_sub_right x.2.2 p)⟩
      invFun := fun x ↦
        ⟨p + (q - p) * x.1,
          le_add_of_nonneg_right (mul_nonneg hspan.le x.2.1),
          affineInterpolation_lt_right p q x.1 hpq x.2.2⟩
      left_inv := ?_
      right_inv := ?_
      map_rel_iff' := ?_ }⟩
  · intro x
    ext
    field_simp
    ring
  · intro x
    ext
    field_simp [hspan.ne']
    ring
  · intro x y
    constructor
    · intro hxy
      exact (sub_le_sub_iff_right p).mp ((div_le_div_iff_of_pos_right hspan).mp hxy)
    · intro hxy
      exact (div_le_div_iff_of_pos_right hspan).mpr ((sub_le_sub_iff_right p).mpr hxy)

/-- Part (1) of Exercise 24.12: for `a < b < c`, the interval `Set.Ico a c` has the
order type of `Set.Ico (0 : ℝ) 1` exactly when both subintervals do. -/
theorem icoOrderTypeSplit {X : Type u} [LinearOrder X] (a b c : X)
    (hab : a < b) (hbc : b < c) :
    Nonempty (Set.Ico a c ≃o Set.Ico (0 : ℝ) 1) ↔
      Nonempty (Set.Ico a b ≃o Set.Ico (0 : ℝ) 1) ∧
        Nonempty (Set.Ico b c ≃o Set.Ico (0 : ℝ) 1) := by
  constructor
  · rintro ⟨e⟩
    -- Restrict at the image of `b`, then affinely normalize both image pieces.
    let midpoint : Set.Ico a c := ⟨b, hab.le, hbc⟩
    let d : ℝ := e midpoint
    have hd_pos : 0 < d :=
      lt_of_le_of_lt (e (⟨a, le_rfl, hab.trans hbc⟩ : Set.Ico a c)).2.1
        (e.strictMono (show (⟨a, le_rfl, hab.trans hbc⟩ : Set.Ico a c) < midpoint from hab))
    have hd_one : d < 1 := (e midpoint).2.2
    have hleft := OrderIso.nonemptySubtypeEquiv e (fun x ↦ x < midpoint)
      (fun y ↦ y < e midpoint) (fun x ↦ (e.lt_iff_lt).symm)
    have hright := OrderIso.nonemptySubtypeEquiv e (fun x ↦ midpoint ≤ x)
      (fun y ↦ e midpoint ≤ y) (fun x ↦ (e.le_iff_le).symm)
    rcases hleft with ⟨eleft⟩
    rcases hright with ⟨eright⟩
    rcases icoIioOrderIsoNonempty a b c hab hbc with ⟨sourceLeft⟩
    rcases icoIciOrderIsoNonempty a b c hab hbc with ⟨sourceRight⟩
    rcases icoIioOrderIsoNonempty 0 d 1 hd_pos hd_one with ⟨targetLeft⟩
    rcases icoIciOrderIsoNonempty 0 d 1 hd_pos hd_one with ⟨targetRight⟩
    rcases realIcoOrderIsoUnitNonempty 0 d hd_pos with ⟨normalizeLeft⟩
    rcases realIcoOrderIsoUnitNonempty d 1 hd_one with ⟨normalizeRight⟩
    refine ⟨?_, ?_⟩
    · exact ⟨sourceLeft.symm.trans <| eleft.trans <| targetLeft.trans normalizeLeft⟩
    · exact ⟨sourceRight.symm.trans <| eright.trans <| targetRight.trans normalizeRight⟩
  · rintro ⟨⟨eleft⟩, ⟨eright⟩⟩
    -- Concatenate the two normalized blocks and fold two half-units back to one unit.
    have hzeroHalf : (0 : ℝ) < 1 / 2 := by norm_num
    have hhalfOne : (1 / 2 : ℝ) < 1 := by norm_num
    rcases icoOrderIsoSumLexNonempty a b c hab hbc with ⟨sourceSplit⟩
    rcases realIcoOrderIsoUnitNonempty 0 (1 / 2) hzeroHalf with ⟨leftHalf⟩
    rcases realIcoOrderIsoUnitNonempty (1 / 2) 1 hhalfOne with ⟨rightHalf⟩
    rcases icoOrderIsoSumLexNonempty 0 (1 / 2) 1 hzeroHalf hhalfOne with ⟨targetSplit⟩
    exact ⟨sourceSplit.trans <| (OrderIso.sumLexCongr eleft eright).trans <|
      (OrderIso.sumLexCongr leftHalf.symm rightHalf.symm).trans targetSplit.symm⟩

/-- Helper for Exercise 24.12: every point below the supremum of a strictly
increasing sequence lies below a later sequence term. -/
lemma exists_sequenceTerm_gt {X : Type u} [LinearOrder X] (x : ℕ → X) (b : X)
    (hx : StrictMono x) (hb : IsLUB (Set.range x) b) (y : Set.Ico (x 0) b) :
    ∃ n, y.1 < x (n + 1) := by
  -- Otherwise `y` is an upper bound of the whole sequence, contradicting `y < b`.
  by_contra h
  simp only [not_exists, not_lt] at h
  have hyUpper : y.1 ∈ upperBounds (Set.range x) := by
    rintro z ⟨n, rfl⟩
    exact (hx (Nat.lt_succ_self n)).le.trans (h n)
  exact (not_lt_of_ge (hb.2 hyUpper)) y.2.2

/-- Helper for Exercise 24.12: the least consecutive block whose right endpoint
lies above a point below the sequential supremum. -/
noncomputable def natSupBlockIndex {X : Type u} [LinearOrder X] (x : ℕ → X) (b : X)
    (hx : StrictMono x) (hb : IsLUB (Set.range x) b) (y : Set.Ico (x 0) b) : ℕ :=
  Nat.find (exists_sequenceTerm_gt x b hx hb y)

/-- Helper for Exercise 24.12: the least block index places the point below its
right endpoint. -/
lemma natSupBlockIndex_upper {X : Type u} [LinearOrder X] (x : ℕ → X) (b : X)
    (hx : StrictMono x) (hb : IsLUB (Set.range x) b) (y : Set.Ico (x 0) b) :
    y.1 < x (natSupBlockIndex x b hx hb y + 1) := by
  -- This is the defining property of the least witness.
  exact Nat.find_spec (exists_sequenceTerm_gt x b hx hb y)

/-- Helper for Exercise 24.12: the least block index places the point at or
above its left endpoint. -/
lemma natSupBlockIndex_lower {X : Type u} [LinearOrder X] (x : ℕ → X) (b : X)
    (hx : StrictMono x) (hb : IsLUB (Set.range x) b) (y : Set.Ico (x 0) b) :
    x (natSupBlockIndex x b hx hb y) ≤ y.1 := by
  -- At index zero use interval membership; otherwise use minimality one step earlier.
  unfold natSupBlockIndex
  generalize hindex : Nat.find (exists_sequenceTerm_gt x b hx hb y) = n
  cases n with
  | zero => exact y.2.1
  | succ k =>
      have hminimal := Nat.find_min (exists_sequenceTerm_gt x b hx hb y)
        (show k < Nat.find (exists_sequenceTerm_gt x b hx hb y) by omega)
      exact le_of_not_gt hminimal

/-- Helper for Exercise 24.12: consecutive block bounds uniquely determine the
least block index of a point below the sequential supremum. -/
lemma natSupBlockIndex_eq_of_bounds {X : Type u} [LinearOrder X] (x : ℕ → X) (b : X)
    (hx : StrictMono x) (hb : IsLUB (Set.range x) b) (y : Set.Ico (x 0) b) (n : ℕ)
    (hlower : x n ≤ y.1) (hupper : y.1 < x (n + 1)) :
    natSupBlockIndex x b hx hb y = n := by
  -- Compare the chosen index with the proposed block and rule out both strict inequalities.
  apply le_antisymm
  · by_contra h
    have hn : n < natSupBlockIndex x b hx hb y := by omega
    have hsequence : x (n + 1) ≤ x (natSupBlockIndex x b hx hb y) :=
      hx.monotone (by omega)
    exact (not_lt_of_ge (hsequence.trans (natSupBlockIndex_lower x b hx hb y))) hupper
  · by_contra h
    have hn : natSupBlockIndex x b hx hb y < n := by omega
    have hsequence : x (natSupBlockIndex x b hx hb y + 1) ≤ x n :=
      hx.monotone (by omega)
    exact (not_lt_of_ge (hsequence.trans hlower)) (natSupBlockIndex_upper x b hx hb y)

/-- Helper for Exercise 24.12: the least block index is monotone along the
sequential half-open interval. -/
lemma natSupBlockIndex_mono {X : Type u} [LinearOrder X] (x : ℕ → X) (b : X)
    (hx : StrictMono x) (hb : IsLUB (Set.range x) b) :
    Monotone (natSupBlockIndex x b hx hb) := by
  intro y z hyz
  -- A reversed index inequality would put `z` below the left endpoint of `y`'s block.
  by_contra h
  have hindices : natSupBlockIndex x b hx hb z + 1 ≤ natSupBlockIndex x b hx hb y := by
    omega
  have hsequence : x (natSupBlockIndex x b hx hb z + 1) ≤
      x (natSupBlockIndex x b hx hb y) := hx.monotone hindices
  have hzUpper := natSupBlockIndex_upper x b hx hb z
  have hyLower := natSupBlockIndex_lower x b hx hb y
  exact (not_lt_of_ge (hyLower.trans hyz)) (hzUpper.trans_le hsequence)

/-- Helper for Exercise 24.12: a point viewed inside the consecutive block
selected by its least block index. -/
def natSupBlockPoint {X : Type u} [LinearOrder X] (x : ℕ → X) (b : X)
    (hx : StrictMono x) (hb : IsLUB (Set.range x) b) (y : Set.Ico (x 0) b) :
    Set.Ico (x (natSupBlockIndex x b hx hb y))
      (x (natSupBlockIndex x b hx hb y + 1)) :=
  ⟨y.1, natSupBlockIndex_lower x b hx hb y, natSupBlockIndex_upper x b hx hb y⟩

/-- Helper for Exercise 24.12: transport a selected block point to an
extensionally equal block index. -/
def natSupBlockPointCast {X : Type u} [LinearOrder X] (x : ℕ → X) (b : X)
    (hx : StrictMono x) (hb : IsLUB (Set.range x) b) (y : Set.Ico (x 0) b) (n : ℕ)
    (hindex : natSupBlockIndex x b hx hb y = n) : Set.Ico (x n) (x (n + 1)) :=
  hindex ▸ natSupBlockPoint x b hx hb y

/-- Helper for Exercise 24.12: the transported selected block point has the
same underlying point. -/
lemma natSupBlockPointCast_val {X : Type u} [LinearOrder X] (x : ℕ → X) (b : X)
    (hx : StrictMono x) (hb : IsLUB (Set.range x) b) (y : Set.Ico (x 0) b) (n : ℕ)
    (hindex : natSupBlockIndex x b hx hb y = n) :
    (natSupBlockPointCast x b hx hb y n hindex).1 = y.1 := by
  -- Transport changes only the block-indexed membership proof.
  subst n
  rfl

/-- Helper for Exercise 24.12: evaluating a block map commutes with
transporting a selected point to an equal block index. -/
lemma natSupBlockMap_eq_cast {X : Type u} [LinearOrder X] (x : ℕ → X) (b : X)
    (hx : StrictMono x) (hb : IsLUB (Set.range x) b)
    (e : ∀ n, Set.Ico (x n) (x (n + 1)) ≃o Set.Ico (0 : ℝ) 1)
    (y : Set.Ico (x 0) b) (n : ℕ) (hindex : natSupBlockIndex x b hx hb y = n) :
    e (natSupBlockIndex x b hx hb y) (natSupBlockPoint x b hx hb y) =
      e n (natSupBlockPointCast x b hx hb y n hindex) := by
  -- The equality is reflexive once the block indices are identified.
  subst n
  rfl

/-- Helper for Exercise 24.12: the canonical block-coordinate encoding of a
sequential half-open interval. -/
noncomputable def natSupBlockCode {X : Type u} [LinearOrder X] (x : ℕ → X) (b : X)
    (hx : StrictMono x) (hb : IsLUB (Set.range x) b)
    (e : ∀ n, Set.Ico (x n) (x (n + 1)) ≃o Set.Ico (0 : ℝ) 1) :
    Set.Ico (x 0) b → ℕ ×ₗ Set.Ico (0 : ℝ) 1 :=
  fun y ↦ toLex
    (natSupBlockIndex x b hx hb y,
      e (natSupBlockIndex x b hx hb y) (natSupBlockPoint x b hx hb y))

/-- Helper for Exercise 24.12: the canonical block-coordinate encoding is
strictly increasing. -/
lemma natSupBlockCode_strictMono {X : Type u} [LinearOrder X] (x : ℕ → X) (b : X)
    (hx : StrictMono x) (hb : IsLUB (Set.range x) b)
    (e : ∀ n, Set.Ico (x n) (x (n + 1)) ≃o Set.Ico (0 : ℝ) 1) :
    StrictMono (natSupBlockCode x b hx hb e) := by
  intro y z hyz
  -- Compare block indices first; equality leaves only the within-block comparison.
  rw [Prod.Lex.lt_iff']
  refine ⟨?_, ?_⟩
  · simpa [natSupBlockCode] using natSupBlockIndex_mono x b hx hb hyz.le
  · intro hindex
    simp only [natSupBlockCode, ofLex_toLex] at hindex ⊢
    have hpoint : natSupBlockPointCast x b hx hb y _ hindex <
        natSupBlockPoint x b hx hb z := by
      change (natSupBlockPointCast x b hx hb y _ hindex).1 <
        (natSupBlockPoint x b hx hb z).1
      rw [natSupBlockPointCast_val]
      exact hyz
    calc
      e (natSupBlockIndex x b hx hb y) (natSupBlockPoint x b hx hb y) =
          e (natSupBlockIndex x b hx hb z)
            (natSupBlockPointCast x b hx hb y _ hindex) :=
        natSupBlockMap_eq_cast x b hx hb e y _ hindex
      _ < e (natSupBlockIndex x b hx hb z) (natSupBlockPoint x b hx hb z) :=
        (e _).strictMono hpoint

/-- Helper for Exercise 24.12: the canonical block-coordinate encoding reaches
every point of the natural lexicographic staircase. -/
lemma natSupBlockCode_surjective {X : Type u} [LinearOrder X] (x : ℕ → X) (b : X)
    (hx : StrictMono x) (hb : IsLUB (Set.range x) b)
    (e : ∀ n, Set.Ico (x n) (x (n + 1)) ≃o Set.Ico (0 : ℝ) 1) :
    Function.Surjective (natSupBlockCode x b hx hb e) := by
  rintro target
  rcases htarget : ofLex target with ⟨n, t⟩
  let blockPoint : Set.Ico (x n) (x (n + 1)) := (e n).symm t
  have hglobalLower : x 0 ≤ blockPoint.1 :=
    (hx.monotone (Nat.zero_le n)).trans blockPoint.2.1
  have hendpointUpper : x (n + 1) ≤ b := hb.1 ⟨n + 1, rfl⟩
  have hglobalUpper : blockPoint.1 < b := blockPoint.2.2.trans_le hendpointUpper
  let y : Set.Ico (x 0) b := ⟨blockPoint.1, hglobalLower, hglobalUpper⟩
  have hindex : natSupBlockIndex x b hx hb y = n :=
    natSupBlockIndex_eq_of_bounds x b hx hb y n blockPoint.2.1 blockPoint.2.2
  refine ⟨y, ?_⟩
  -- Recover the selected block and then cancel the chosen block isomorphism.
  apply ofLex.injective
  rw [htarget]
  ext
  · simpa [natSupBlockCode] using hindex
  · have hpoint : natSupBlockPointCast x b hx hb y n hindex = blockPoint := by
      ext
      exact natSupBlockPointCast_val x b hx hb y n hindex
    calc
      (e (natSupBlockIndex x b hx hb y) (natSupBlockPoint x b hx hb y)).1 =
          (e n (natSupBlockPointCast x b hx hb y n hindex)).1 :=
        congrArg Subtype.val (natSupBlockMap_eq_cast x b hx hb e y n hindex)
      _ = (e n blockPoint).1 := congrArg (fun point ↦ (e n point).1) hpoint
      _ = t.1 := congrArg Subtype.val ((e n).apply_symm_apply t)

/-- Helper for Exercise 24.12: a sequential interval with normalized consecutive
blocks is order-isomorphic to the natural lexicographic staircase. -/
lemma icoNatSupOrderIsoLexNonempty {X : Type u} [LinearOrder X] (x : ℕ → X) (b : X)
    (hx : StrictMono x) (hb : IsLUB (Set.range x) b)
    (e : ∀ n, Set.Ico (x n) (x (n + 1)) ≃o Set.Ico (0 : ℝ) 1) :
    Nonempty (Set.Ico (x 0) b ≃o (ℕ ×ₗ Set.Ico (0 : ℝ) 1)) := by
  -- Assemble the certified encoding through the canonical monotone-surjective constructor.
  exact ⟨StrictMono.orderIsoOfSurjective (natSupBlockCode x b hx hb e)
    (natSupBlockCode_strictMono x b hx hb e) (natSupBlockCode_surjective x b hx hb e)⟩

/-- Helper for Exercise 24.12: the sum of a natural block index and a unit
coordinate is nonnegative. -/
lemma natAddUnit_nonneg (n : ℕ) (t : Set.Ico (0 : ℝ) 1) : 0 ≤ (n : ℝ) + t.1 := by
  exact add_nonneg (Nat.cast_nonneg n) t.2.1

/-- Helper for Exercise 24.12: the natural lexicographic staircase maps to the
nonnegative reals by adding the block index and within-block coordinate. -/
def natLexUnitToNonnegative : (ℕ ×ₗ Set.Ico (0 : ℝ) 1) → Set.Ici (0 : ℝ) :=
  fun point ↦ ⟨((ofLex point).1 : ℝ) + (ofLex point).2.1,
    natAddUnit_nonneg (ofLex point).1 (ofLex point).2⟩

/-- Helper for Exercise 24.12: addition of block index and unit coordinate is
strictly increasing in lexicographic order. -/
lemma natLexUnitToNonnegative_strictMono : StrictMono natLexUnitToNonnegative := by
  intro p q hpq
  rw [Prod.Lex.lt_iff] at hpq
  rcases hpq with hpq | hpq
  · have hindex : (ofLex p).1 + 1 ≤ (ofLex q).1 := by omega
    have hleft : ((ofLex p).1 : ℝ) + (ofLex p).2.1 < ((ofLex p).1 : ℝ) + 1 := by
      linarith [(ofLex p).2.2.2]
    have hcast : (((ofLex p).1 + 1 : ℕ) : ℝ) ≤ ((ofLex q).1 : ℝ) :=
      Nat.cast_le.mpr hindex
    have hcast' : ((ofLex p).1 : ℝ) + 1 ≤ ((ofLex q).1 : ℝ) := by
      simpa using hcast
    have hright : ((ofLex p).1 : ℝ) + 1 ≤
        ((ofLex q).1 : ℝ) + (ofLex q).2.1 :=
      hcast'.trans (le_add_of_nonneg_right (ofLex q).2.2.1)
    exact hleft.trans_le hright
  · have hcoordinate : (ofLex p).2.1 < (ofLex q).2.1 := hpq.2
    change ((ofLex p).1 : ℝ) + (ofLex p).2.1 <
      ((ofLex q).1 : ℝ) + (ofLex q).2.1
    rw [hpq.1]
    linarith

/-- Helper for Exercise 24.12: every nonnegative real has a floor block index
and a fractional unit coordinate. -/
lemma natLexUnitToNonnegative_surjective :
    Function.Surjective natLexUnitToNonnegative := by
  intro y
  have hfloor : 0 ≤ ⌊y.1⌋ := Int.floor_nonneg.mpr y.2
  let n : ℕ := ⌊y.1⌋.toNat
  let t : Set.Ico (0 : ℝ) 1 := ⟨Int.fract y.1, Int.fract_nonneg y.1, Int.fract_lt_one y.1⟩
  refine ⟨toLex (n, t), ?_⟩
  ext
  have hnInt : (n : ℤ) = ⌊y.1⌋ := by
    exact Int.toNat_of_nonneg hfloor
  have hn : (n : ℝ) = (⌊y.1⌋ : ℝ) := by
    exact_mod_cast hnInt
  rw [natLexUnitToNonnegative]
  simp only [ofLex_toLex]
  rw [hn]
  exact Int.floor_add_fract y.1

/-- Helper for Exercise 24.12: the natural lexicographic staircase is
order-isomorphic to the nonnegative real half-line. -/
lemma natLexUnitOrderIsoNonnegativeNonempty :
    Nonempty ((ℕ ×ₗ Set.Ico (0 : ℝ) 1) ≃o Set.Ici (0 : ℝ)) := by
  exact ⟨StrictMono.orderIsoOfSurjective natLexUnitToNonnegative
    natLexUnitToNonnegative_strictMono natLexUnitToNonnegative_surjective⟩

/-- Helper for Exercise 24.12: the rational compression of a nonnegative real
belongs to the unit half-open interval. -/
lemma nonnegativeRatio_mem (y : Set.Ici (0 : ℝ)) : y.1 / (y.1 + 1) ∈ Set.Ico (0 : ℝ) 1 := by
  have hdenom : 0 < y.1 + 1 := add_pos_of_nonneg_of_pos y.2 zero_lt_one
  exact ⟨div_nonneg y.2 hdenom.le, (div_lt_one hdenom).mpr (by linarith)⟩

/-- Helper for Exercise 24.12: rational compression maps nonnegative reals to
the unit half-open interval. -/
noncomputable def nonnegativeToUnit : Set.Ici (0 : ℝ) → Set.Ico (0 : ℝ) 1 :=
  fun y ↦ ⟨y.1 / (y.1 + 1), nonnegativeRatio_mem y⟩

/-- Helper for Exercise 24.12: rational compression is strictly increasing on
nonnegative reals. -/
lemma nonnegativeToUnit_strictMono : StrictMono nonnegativeToUnit := by
  intro y z hyz
  have hydenom : 0 < y.1 + 1 := add_pos_of_nonneg_of_pos y.2 zero_lt_one
  have hzdenom : 0 < z.1 + 1 := add_pos_of_nonneg_of_pos z.2 zero_lt_one
  change y.1 / (y.1 + 1) < z.1 / (z.1 + 1)
  rw [div_lt_div_iff₀ hydenom hzdenom]
  have hyzReal : y.1 < z.1 := hyz
  nlinarith

/-- Helper for Exercise 24.12: rational compression reaches every point of the
unit half-open interval. -/
lemma nonnegativeToUnit_surjective : Function.Surjective nonnegativeToUnit := by
  intro t
  have hdenom : 0 < 1 - t.1 := sub_pos.mpr t.2.2
  let y : Set.Ici (0 : ℝ) := ⟨t.1 / (1 - t.1), div_nonneg t.2.1 hdenom.le⟩
  refine ⟨y, ?_⟩
  ext
  simp [nonnegativeToUnit, y]
  field_simp
  ring

/-- Helper for Exercise 24.12: the nonnegative real half-line is
order-isomorphic to the unit half-open interval. -/
lemma nonnegativeOrderIsoUnitNonempty :
    Nonempty (Set.Ici (0 : ℝ) ≃o Set.Ico (0 : ℝ) 1) := by
  exact ⟨StrictMono.orderIsoOfSurjective nonnegativeToUnit
    nonnegativeToUnit_strictMono nonnegativeToUnit_surjective⟩

/-- Helper for Exercise 24.12: the natural lexicographic staircase has the
order type of the unit half-open interval. -/
lemma natLexUnitIcoOrderIsoNonempty :
    Nonempty ((ℕ ×ₗ Set.Ico (0 : ℝ) 1) ≃o Set.Ico (0 : ℝ) 1) := by
  rcases natLexUnitOrderIsoNonnegativeNonempty with ⟨staircase⟩
  rcases nonnegativeOrderIsoUnitNonempty with ⟨compress⟩
  exact ⟨staircase.trans compress⟩

/-- Helper for Exercise 24.12: an order isomorphism restricts to a
half-open interval between two endpoints. -/
lemma OrderIso.nonemptyIcoCongr {α : Type u} {β : Type v} [LinearOrder α] [LinearOrder β]
    (e : α ≃o β) (a b : α) : Nonempty (Set.Ico a b ≃o Set.Ico (e a) (e b)) := by
  -- Restrict `e` using its endpoint order reflection laws.
  have hmembership (x : α) : x ∈ Set.Ico a b ↔ e x ∈ Set.Ico (e a) (e b) := by
    exact ⟨fun hx ↦ ⟨e.monotone hx.1, e.strictMono hx.2⟩,
      fun hx ↦ ⟨e.le_iff_le.mp hx.1, e.lt_iff_lt.mp hx.2⟩⟩
  exact OrderIso.nonemptySubtypeEquiv e (fun x ↦ x ∈ Set.Ico a b)
    (fun y ↦ y ∈ Set.Ico (e a) (e b)) hmembership

/-- Helper for Exercise 24.12: a half-open interval inside a half-open ambient
interval has the same order type as the corresponding ambient interval. -/
lemma nestedIcoOrderIsoNonempty {X : Type u} [LinearOrder X] {l r : X}
    (a b : Set.Ico l r) : Nonempty (Set.Ico a b ≃o Set.Ico a.1 b.1) := by
  -- Forget and restore the ambient membership proofs without changing values.
  refine ⟨{
      toFun := fun x ↦ ⟨x.1.1, x.2.1, x.2.2⟩
      invFun := fun x ↦
        ⟨⟨x.1, a.2.1.trans x.2.1, x.2.2.trans b.2.2⟩, x.2.1, x.2.2⟩
      left_inv := ?_
      right_inv := ?_
      map_rel_iff' := ?_ }⟩
  · intro x
    ext
    rfl
  · intro x
    ext
    rfl
  · intro x y
    rfl

/-- Part (2) of Exercise 24.12: an interval ending at the supremum of a strictly
increasing sequence has the order type of `Set.Ico (0 : ℝ) 1` exactly when
each consecutive interval does. -/
theorem icoOrderTypeNatSup {X : Type u} [LinearOrder X] (x : ℕ → X) (b : X)
    (hx : StrictMono x) (hb : IsLUB (Set.range x) b) :
    Nonempty (Set.Ico (x 0) b ≃o Set.Ico (0 : ℝ) 1) ↔
      ∀ i, Nonempty (Set.Ico (x i) (x (i + 1)) ≃o Set.Ico (0 : ℝ) 1) := by
  constructor
  · rintro ⟨global⟩ i
    -- Restrict the global isomorphism to the `i`th block, then normalize its real image.
    have hterm (n : ℕ) : x n < b :=
      (hx (Nat.lt_succ_self n)).trans_le (hb.1 ⟨n + 1, rfl⟩)
    let left : Set.Ico (x 0) b :=
      ⟨x i, hx.monotone (Nat.zero_le i), hterm i⟩
    let right : Set.Ico (x 0) b :=
      ⟨x (i + 1), hx.monotone (Nat.zero_le (i + 1)), hterm (i + 1)⟩
    have hleftRight : left < right := hx (Nat.lt_succ_self i)
    rcases nestedIcoOrderIsoNonempty left right with ⟨sourceNested⟩
    rcases OrderIso.nonemptyIcoCongr global left right with ⟨restricted⟩
    rcases nestedIcoOrderIsoNonempty (global left) (global right) with ⟨targetNested⟩
    rcases realIcoOrderIsoUnitNonempty (global left).1 (global right).1
      (global.strictMono hleftRight) with ⟨normalize⟩
    exact ⟨sourceNested.symm.trans <| restricted.trans <| targetNested.trans normalize⟩
  · intro blocks
    classical
    -- Choose one normalization per block, assemble the staircase, and then compress it
    -- to the unit interval.
    let chosen : ∀ n, Set.Ico (x n) (x (n + 1)) ≃o Set.Ico (0 : ℝ) 1 :=
      fun n ↦ Classical.choice (blocks n)
    rcases icoNatSupOrderIsoLexNonempty x b hx hb chosen with ⟨staircase⟩
    rcases natLexUnitIcoOrderIsoNonempty with ⟨normalize⟩
    exact ⟨staircase.trans normalize⟩

/-- Helper for Exercise 24.12: a lexicographic block between consecutive axis
points consists exactly of the points on the lower vertical fiber. -/
lemma OpenOmegaOne.mem_axisSuccessorBlock_iff (a b : OpenOmegaOne)
    (hab : (b : Ordinal) = (a : Ordinal) + 1)
    (z : OpenOmegaOne ×ₗ Set.Ico (0 : ℝ) 1) :
    z ∈ Set.Ico (LongLine.axisPoint a) (LongLine.axisPoint b) ↔ z.1 = a := by
  constructor
  · intro hz
    -- The lower endpoint gives `a ≤ z.1`, while the successor upper endpoint
    -- forces `z.1 ≤ a`.
    have halower : a ≤ z.1 := by
      rcases Prod.Lex.le_iff.mp hz.1 with hfirst | hfiber
      · exact hfirst.le
      · exact hfiber.1.le
    have hzupper : (z.1 : Ordinal) < b := by
      rcases Prod.Lex.lt_iff.mp hz.2 with hfirst | hfiber
      · exact hfirst
      · exfalso
        exact (not_lt_of_ge z.2.2.1) hfiber.2
    have hupper : z.1 ≤ a := by
      change (z.1 : Ordinal) ≤ a
      rw [hab, ← Order.succ_eq_add_one, Order.lt_succ_iff] at hzupper
      exact hzupper
    exact le_antisymm hupper halower
  · intro hz
    -- On the fixed fiber, the lower inequality is vertical and the upper
    -- inequality is supplied by the successor relation.
    constructor
    · rw [Prod.Lex.le_iff]
      right
      exact ⟨hz.symm, z.2.2.1⟩
    · rw [Prod.Lex.lt_iff]
      left
      change (z.1 : Ordinal) < b
      rw [hz, hab]
      exact Order.lt_succ _

/-- Helper for Exercise 24.12: a single vertical successor block has the order
type of the real unit half-open interval. -/
lemma OpenOmegaOne.axisSuccessorBlockOrderIso (a b : OpenOmegaOne)
    (hab : (b : Ordinal) = (a : Ordinal) + 1) :
    Nonempty
      (Set.Ico (LongLine.axisPoint a) (LongLine.axisPoint b) ≃o
        Set.Ico (0 : ℝ) 1) := by
  -- Project to the second coordinate; the membership characterization restores
  -- the unique point on the fiber for the inverse.
  refine ⟨{
      toFun := fun z ↦ z.1.2
      invFun := fun t ↦
        ⟨(a, t), (OpenOmegaOne.mem_axisSuccessorBlock_iff a b hab (a, t)).2 rfl⟩
      left_inv := ?_
      right_inv := ?_
      map_rel_iff' := ?_ }⟩
  · intro z
    apply Subtype.ext
    apply ofLex.injective
    exact Prod.ext
      ((OpenOmegaOne.mem_axisSuccessorBlock_iff a b hab z).1 z.2).symm
      rfl
  · intro t
    rfl
  · intro z w
    have hz : (ofLex z.1).1 = a :=
      (OpenOmegaOne.mem_axisSuccessorBlock_iff a b hab z).1 z.2
    have hw : (ofLex w.1).1 = a :=
      (OpenOmegaOne.mem_axisSuccessorBlock_iff a b hab w).1 w.2
    change z.1.2 ≤ w.1.2 ↔ z.1 ≤ w.1
    rw [Prod.Lex.le_iff, hz, hw]
    simp only [lt_self_iff_false, false_or, true_and]
    rfl

/-- Helper for Exercise 24.12: a countable limit ordinal admits a strictly
increasing axis sequence starting at the least ordinal and converging to its
axis point in the lexicographic order. -/
lemma OpenOmegaOne.exists_axisSequence_isLUB (a : OpenOmegaOne)
    (ha : Order.IsSuccLimit (a : Ordinal)) :
    ∃ x : ℕ → OpenOmegaOne,
      x 0 = LongLine.leastOrdinal ∧ StrictMono x ∧
      (∀ n, x (n + 1) < a) ∧
      IsLUB (Set.range (fun n ↦ LongLine.axisPoint (x n)))
        (LongLine.axisPoint a) := by
  -- Countability identifies the cofinality index with `ω`, providing a
  -- fundamental sequence below `a`.
  have hcof : (a : Ordinal).cof.ord = Ordinal.omega0 := by
    rw [Ordinal.cof_eq_aleph0_of_isSuccLimit ha a.2, Cardinal.ord_aleph0]
  obtain ⟨f, hf⟩ := Ordinal.exists_isFundamentalSeq hcof
  have hfcountable (i : Set.Iio Ordinal.omega0) : (f i).1 ∈ OpenOmegaOne :=
    by
      change (f i).1 < Ordinal.omega 1
      exact lt_trans (f i).2 a.2
  let x : ℕ → OpenOmegaOne := fun n ↦
    match n with
    | 0 => LongLine.leastOrdinal
    | m + 1 => ⟨(f ⟨(m + 1 : ℕ), Ordinal.natCast_lt_omega0 _⟩).1,
        hfcountable ⟨(m + 1 : ℕ), Ordinal.natCast_lt_omega0 _⟩⟩
  have hxzero : x 0 = LongLine.leastOrdinal := rfl
  have hxtail (n : ℕ) : (x (n + 1) : Ordinal) =
      f ⟨(n + 1 : ℕ), Ordinal.natCast_lt_omega0 _⟩ := rfl
  have hxtail_lt (n : ℕ) : x (n + 1) < a := by
    exact (f ⟨(n + 1 : ℕ), Ordinal.natCast_lt_omega0 _⟩).2
  have htailCofinal : ∀ c : Ordinal, c < a → ∃ n, c < x (n + 1) := by
    intro c hc
    obtain ⟨i, ⟨j, hj⟩, hcj⟩ := hf.isCofinal_range ⟨c, hc⟩
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp j.2
    rw [← hj] at hcj
    have hindex : j < (⟨(n + 1 : ℕ), Ordinal.natCast_lt_omega0 _⟩ :
        Set.Iio Ordinal.omega0) := by
      change (j : Ordinal) < (n + 1 : ℕ)
      rw [hn]
      simp
    refine ⟨n, hcj.trans_lt (hf.strictMono hindex)⟩
  have hxmono : StrictMono x := by
    intro m n hmn
    cases m with
    | zero =>
        cases n with
        | zero => omega
        | succ n =>
            change (0 : Ordinal) < f ⟨(n + 1 : ℕ), Ordinal.natCast_lt_omega0 _⟩
            exact (bot_le : (0 : Ordinal) ≤ _).trans_lt
              (hf.strictMono (show (⟨0, Ordinal.natCast_lt_omega0 0⟩ : Set.Iio Ordinal.omega0) <
                ⟨(n + 1 : ℕ), Ordinal.natCast_lt_omega0 _⟩ by simp))
    | succ m =>
        cases n with
        | zero => omega
        | succ n =>
            change (x (m + 1) : Ordinal) < x (n + 1)
            rw [hxtail, hxtail]
            exact hf.strictMono (by simpa using hmn)
  refine ⟨x, hxzero, hxmono, hxtail_lt, ?_⟩
  constructor
  · rintro _ ⟨n, rfl⟩
    -- Every sequence point is below the limiting axis point by its first
    -- coordinate.
    rw [Prod.Lex.le_iff]
    left
    cases n with
    | zero =>
        change (x 0 : Ordinal) < a
        rw [hxzero]
        change (0 : Ordinal) < a
        exact ha.bot_lt
    | succ n => exact hxtail_lt n
  · intro y hy
    -- Cofinality of the shifted tail forces the first coordinate of every
    -- upper bound above `a`, which gives the desired lexicographic inequality.
    rw [Prod.Lex.le_iff]
    by_cases hfirst : a < y.1
    · exact Or.inl hfirst
    · right
      have hay : a = y.1 := by
        apply le_antisymm
        · by_contra hnot
          have hylt : y.1 < a := lt_of_not_ge hnot
          obtain ⟨n, hn⟩ := htailCofinal y.1 hylt
          have haxis := hy ⟨n + 1, rfl⟩
          exact (not_lt_of_ge haxis) (Prod.Lex.lt_iff.2 (Or.inl hn))
        · exact le_of_not_gt hfirst
      refine ⟨hay, ?_⟩
      exact y.2.2.1

/-- Part (3) of Exercise 24.12: every nontrivial initial lexicographic segment of
`OpenOmegaOne ×ₗ Set.Ico (0 : ℝ) 1` ending at an axis point has the order type
of `Set.Ico (0 : ℝ) 1`. -/
theorem OpenOmegaOne.initialLexSegmentOrderType (a : OpenOmegaOne)
    (ha : a ≠ LongLine.leastOrdinal) :
    Nonempty
      (Set.Ico LongLine.origin (LongLine.axisPoint a) ≃o Set.Ico (0 : ℝ) 1) :=
  by
    -- Route correction: induct on the countable-ordinal subtype itself, so
    -- predecessor and sequence terms feed directly into the induction hypothesis.
    have hordinalWellFounded :
        WellFounded (fun x y : OpenOmegaOne ↦ (x : Ordinal) < y) :=
      InvImage.wf Subtype.val wellFounded_lt
    induction a using hordinalWellFounded.induction with
    | h a ih =>
        rcases Ordinal.zero_or_succ_or_isSuccLimit (a : Ordinal) with hzero | hrest
        · exfalso
          apply ha
          apply Subtype.ext
          simpa [LongLine.leastOrdinal] using hzero
        · rcases hrest with hsuccessor | hlimit
          · obtain ⟨predecessor, hsuccessor⟩ := hsuccessor
            have hpredecessorCountable : predecessor ∈ OpenOmegaOne := by
              change predecessor < Ordinal.omega 1
              exact (Order.lt_succ predecessor).trans (hsuccessor ▸ a.2)
            let p : OpenOmegaOne := ⟨predecessor, hpredecessorCountable⟩
            have hap : (a : Ordinal) = (p : Ordinal) + 1 := by
              simpa [p, Order.succ_eq_add_one] using hsuccessor.symm
            have hpa : p < a := by
              change (p : Ordinal) < a
              rw [hap]
              exact Order.lt_succ _
            have hblock := OpenOmegaOne.axisSuccessorBlockOrderIso p a hap
            by_cases hpzero : p = LongLine.leastOrdinal
            · rw [hpzero] at hblock
              exact hblock
            · have horiginP := ih p (show (p : Ordinal) < a from hpa) hpzero
              have horiginLtP : LongLine.origin < LongLine.axisPoint p := by
                rw [Prod.Lex.lt_iff]
                left
                change LongLine.leastOrdinal < p
                exact lt_of_le_of_ne
                  (CountableOrdinal.zero_isLeast.2 (Set.mem_univ p))
                  (fun h ↦ hpzero h.symm)
              have hpLtA : LongLine.axisPoint p < LongLine.axisPoint a := by
                rw [Prod.Lex.lt_iff]
                exact Or.inl hpa
              exact (icoOrderTypeSplit LongLine.origin (LongLine.axisPoint p)
                (LongLine.axisPoint a) horiginLtP hpLtA).2 ⟨horiginP, hblock⟩
          · obtain ⟨x, hxzero, hxmono, hxlt, hxLUB⟩ :=
              OpenOmegaOne.exists_axisSequence_isLUB a hlimit
            have haxisMono : StrictMono (fun n ↦ LongLine.axisPoint (x n)) := by
              intro m n hmn
              rw [Prod.Lex.lt_iff]
              exact Or.inl (hxmono hmn)
            have hsequenceSegment := (icoOrderTypeNatSup
              (fun n ↦ LongLine.axisPoint (x n)) (LongLine.axisPoint a)
              haxisMono hxLUB).2
            rw [hxzero] at hsequenceSegment
            exact hsequenceSegment fun n ↦ by
              cases n with
              | zero =>
              have hxoneNe : x 1 ≠ LongLine.leastOrdinal := by
                intro h
                exact (hxmono Nat.zero_lt_one).ne (hxzero.trans h.symm)
              have hsegment := ih (x 1)
                (show (x 1 : Ordinal) < a from hxlt 0) hxoneNe
              rw [hxzero]
              exact hsegment
              | succ n =>
              have hleftNe : x (n + 1) ≠ LongLine.leastOrdinal := by
                exact ne_of_gt (hxzero ▸ hxmono (Nat.zero_lt_succ _))
              have hrightNe : x (n + 2) ≠ LongLine.leastOrdinal := by
                exact ne_of_gt (hxzero ▸ hxmono (Nat.zero_lt_succ _))
              have hrightSegment := ih (x (n + 2))
                (show (x (n + 2) : Ordinal) < a from hxlt (n + 1)) hrightNe
              have horiginLeft : LongLine.origin < LongLine.axisPoint (x (n + 1)) := by
                rw [Prod.Lex.lt_iff]
                left
                change LongLine.leastOrdinal < x (n + 1)
                exact lt_of_le_of_ne
                  (CountableOrdinal.zero_isLeast.2 (Set.mem_univ _))
                  (fun h ↦ hleftNe h.symm)
              have hleftRight : LongLine.axisPoint (x (n + 1)) <
                  LongLine.axisPoint (x (n + 2)) := by
                rw [Prod.Lex.lt_iff]
                exact Or.inl (hxmono (Nat.lt_succ_self _))
              exact (icoOrderTypeSplit LongLine.origin
                (LongLine.axisPoint (x (n + 1)))
                (LongLine.axisPoint (x (n + 2))) horiginLeft hleftRight).1
                hrightSegment |>.2

/-- Helper for Exercise 24.12: deleting the least endpoint from isomorphic
half-open intervals gives isomorphic open intervals. -/
lemma icoInteriorOrderIsoNonempty {X : Type u} {Y : Type v}
    [LinearOrder X] [LinearOrder Y] (a c : X) (p q : Y) (hac : a < c)
    (hpq : p < q) (e : Set.Ico a c ≃o Set.Ico p q) :
    Nonempty (Set.Ioo a c ≃o Set.Ioo p q) := by
  -- First record that the order isomorphism preserves the least endpoints.
  have hbot : e ⟨a, le_rfl, hac⟩ = ⟨p, le_rfl, hpq⟩ :=
    e.map_bot' (fun x ↦ x.2.1) (fun y ↦ y.2.1)
  -- Restrict `e` and its inverse to the points strictly above those endpoints.
  refine ⟨{
      toFun := fun x ↦ ⟨(e ⟨x.1, x.2.1.le, x.2.2⟩).1, ?_,
        (e ⟨x.1, x.2.1.le, x.2.2⟩).2.2⟩
      invFun := fun y ↦ ⟨(e.symm ⟨y.1, y.2.1.le, y.2.2⟩).1, ?_,
        (e.symm ⟨y.1, y.2.1.le, y.2.2⟩).2.2⟩
      left_inv := ?_
      right_inv := ?_
      map_rel_iff' := ?_ }⟩
  · have hstrict := e.strictMono
        (show (⟨a, le_rfl, hac⟩ : Set.Ico a c) < ⟨x.1, x.2.1.le, x.2.2⟩ from x.2.1)
    rw [hbot] at hstrict
    exact hstrict
  · have hstrict := e.symm.strictMono
        (show (⟨p, le_rfl, hpq⟩ : Set.Ico p q) < ⟨y.1, y.2.1.le, y.2.2⟩ from y.2.1)
    rw [← hbot] at hstrict
    change (e.symm (e ⟨a, le_rfl, hac⟩)).1 <
      (e.symm ⟨y.1, y.2.1.le, y.2.2⟩).1 at hstrict
    rw [e.symm_apply_apply] at hstrict
    exact hstrict
  · intro x
    ext
    change (e.symm (e ⟨x.1, x.2.1.le, x.2.2⟩)).1 = x.1
    exact congrArg Subtype.val (e.symm_apply_apply ⟨x.1, x.2.1.le, x.2.2⟩)
  · intro y
    ext
    change (e (e.symm ⟨y.1, y.2.1.le, y.2.2⟩)).1 = y.1
    exact congrArg Subtype.val (e.apply_symm_apply ⟨y.1, y.2.1.le, y.2.2⟩)
  · intro x y
    exact e.le_iff_le

/-- Helper for Exercise 24.12: a nonleast axis point lies above the deleted
origin. -/
lemma LongLine.origin_lt_axisPoint (a : OpenOmegaOne)
    (ha : a ≠ LongLine.leastOrdinal) :
    LongLine.origin < LongLine.axisPoint a := by
  -- The least ordinal is below `a`, so the first lexicographic coordinate increases.
  rw [Prod.Lex.lt_iff]
  left
  change LongLine.leastOrdinal < a
  exact lt_of_le_of_ne (CountableOrdinal.zero_isLeast.2 (Set.mem_univ a))
    (fun h ↦ ha h.symm)

/-- Helper for Exercise 24.12: a nonleast axis point regarded as a point of the
long line. -/
def LongLine.axisPointInLongLine (a : OpenOmegaOne)
    (ha : a ≠ LongLine.leastOrdinal) : LongLine :=
  ⟨LongLine.axisPoint a, LongLine.origin_lt_axisPoint a ha⟩

/-- Helper for Exercise 24.12: every nontrivial open initial segment of the
long line has the order type of a real open interval. -/
lemma LongLine.openInitialSegmentOrderIso (a : OpenOmegaOne)
    (ha : a ≠ LongLine.leastOrdinal) :
    Nonempty
      (Set.Iio (LongLine.axisPointInLongLine a ha) ≃o Set.Ioo (0 : ℝ) 1) := by
  -- Delete the least point from the completed half-open initial-segment chart.
  obtain ⟨e⟩ := OpenOmegaOne.initialLexSegmentOrderType a ha
  obtain ⟨eInterior⟩ := icoInteriorOrderIsoNonempty LongLine.origin
    (LongLine.axisPoint a) (0 : ℝ) 1 (LongLine.origin_lt_axisPoint a ha)
    zero_lt_one e
  -- Flatten the nested subtype `Iio` inside `LongLine` to the ambient open interval.
  let flatten : Set.Iio (LongLine.axisPointInLongLine a ha) ≃o
      Set.Ioo LongLine.origin (LongLine.axisPoint a) :=
    { toFun := fun x ↦ ⟨x.1.1, x.1.2, x.2⟩
      invFun := fun x ↦ ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      left_inv := fun x ↦ by ext; rfl
      right_inv := fun x ↦ by ext; rfl
      map_rel_iff' := by
        intro x y
        rfl }
  exact ⟨flatten.trans eInterior⟩

/-- Helper for Exercise 24.12: two long-line points lie below a common
nonleast successor axis point. -/
lemma LongLine.existsCommonAxisBound (x y : LongLine) :
    ∃ (a : OpenOmegaOne) (ha : a ≠ LongLine.leastOrdinal),
      x < LongLine.axisPointInLongLine a ha ∧
        y < LongLine.axisPointInLongLine a ha := by
  -- The successor of the maximum first coordinate is still countable.
  let m : Ordinal := max (x.1.1 : Ordinal) y.1.1
  have hm : m < Ordinal.omega 1 :=
    max_lt x.1.1.2 y.1.1.2
  have hsucc : Order.succ m < Ordinal.omega 1 :=
    Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) hm
  let a : OpenOmegaOne := ⟨Order.succ m, hsucc⟩
  have ha : a ≠ LongLine.leastOrdinal := by
    intro h
    have hzero : Order.succ m = 0 := congrArg Subtype.val h
    exact (Order.succ_ne_bot m) hzero
  refine ⟨a, ha, ?_, ?_⟩
  · -- The first coordinate of `x` is at most the chosen maximum.
    change x.1 < LongLine.axisPoint a
    rw [Prod.Lex.lt_iff]
    left
    change (x.1.1 : Ordinal) < Order.succ m
    exact lt_of_le_of_lt (le_max_left _ _) (Order.lt_succ _)
  · -- The same maximum also bounds the first coordinate of `y`.
    change y.1 < LongLine.axisPoint a
    rw [Prod.Lex.lt_iff]
    left
    change (y.1.1 : Ordinal) < Order.succ m
    exact lt_of_le_of_lt (le_max_right _ _) (Order.lt_succ _)

/-- Exercise 24.12: The long line is path connected. -/
instance LongLine.instPathConnectedSpace : PathConnectedSpace LongLine :=
  { nonempty := ⟨⟨(LongLine.leastOrdinal,
        (⟨1 / 2, by norm_num, by norm_num⟩ : Set.Ico (0 : ℝ) 1)), by
          rw [LongLine.mem_iff, Prod.Lex.lt_iff]
          exact Or.inr ⟨rfl, by
            change (0 : ℝ) < 1 / 2
            norm_num⟩⟩⟩
    joined := by
      intro x y
      -- Put both points in one initial segment and transport a real interval path.
      obtain ⟨a, ha, hx, hy⟩ := LongLine.existsCommonAxisBound x y
      obtain ⟨e⟩ := LongLine.openInitialSegmentOrderIso a ha
      let x' : Set.Iio (LongLine.axisPointInLongLine a ha) := ⟨x, hx⟩
      let y' : Set.Iio (LongLine.axisPointInLongLine a ha) := ⟨y, hy⟩
      have hreal : IsPathConnected (Set.Ioo (0 : ℝ) 1) :=
        (convex_Ioo (0 : ℝ) 1).isPathConnected ⟨1 / 2, by norm_num⟩
      have hjoinedReal : Joined (e x') (e y') :=
        (hreal.joinedIn (e x').1 (e x').2 (e y').1 (e y').2).joined_subtype
      let pathInitial := hjoinedReal.somePath.map e.toHomeomorph.symm.continuous
      have hsource : x' = e.toHomeomorph.symm (e x') := by simp
      have htarget : y' = e.toHomeomorph.symm (e y') := by simp
      let pathInitial' : Path x' y' := pathInitial.cast hsource htarget
      exact ⟨pathInitial'.map continuous_subtype_val⟩ }

/-- Helper for Exercise 24.12: an order chart on an open initial segment gives
an open real-interval neighborhood of every point in that segment. -/
lemma existsOpenIntervalNeighborhood_of_iioOrderIso
    {X : Type u} [LinearOrder X] [TopologicalSpace X] [OrderTopology X]
    (x c : X) (hx : x < c) (p q : ℝ) (_hpq : p < q)
    (e : Set.Iio c ≃o Set.Ioo p q) :
    ∃ (U : Set X) (a b : ℝ),
      IsOpen U ∧ x ∈ U ∧ a < b ∧ Nonempty (U ≃ₜ Set.Ioo a b) := by
  -- Choose real endpoints strictly around the coordinate of `x`.
  let x' : Set.Iio c := ⟨x, hx⟩
  let z : ℝ := (e x').1
  let a : ℝ := (p + z) / 2
  let b : ℝ := (z + q) / 2
  have hpz : p < z := (e x').2.1
  have hzq : z < q := (e x').2.2
  have hap : p < a := by dsimp [a]; linarith
  have haz : a < z := by dsimp [a]; linarith
  have hzb : z < b := by dsimp [b]; linarith
  have hbq : b < q := by dsimp [b]; linarith
  let left : Set.Iio c := e.symm ⟨a, hap, haz.trans hzq⟩
  let right : Set.Iio c := e.symm ⟨b, hpz.trans hzb, hbq⟩
  have hleftx : left.1 < x := by
    change left < x'
    rw [e.symm_apply_lt]
    exact haz
  have hxright : x < right.1 := by
    change x' < right
    rw [e.lt_symm_apply]
    exact hzb
  have hleftright : left.1 < right.1 := hleftx.trans hxright
  let U : Set X := Set.Ioo left.1 right.1
  -- Restrict the chart and flatten the nested source interval to `U`.
  let restrict : Set.Ioo left right ≃o Set.Ioo a b :=
    { toFun := fun y ↦ ⟨(e y.1).1, by
          constructor
          · have h := e.strictMono y.2.1
            change (e left).1 < (e y.1).1 at h
            change a < (e y.1).1
            rw [show e left = ⟨a, hap, haz.trans hzq⟩ from e.apply_symm_apply _] at h
            exact h
          · have h := e.strictMono y.2.2
            change (e y.1).1 < (e right).1 at h
            change (e y.1).1 < b
            rw [show e right = ⟨b, hpz.trans hzb, hbq⟩ from e.apply_symm_apply _] at h
            exact h⟩
      invFun := fun y ↦ ⟨e.symm ⟨y.1, hap.trans y.2.1, y.2.2.trans hbq⟩, by
          constructor
          · exact e.symm.strictMono y.2.1
          · exact e.symm.strictMono y.2.2⟩
      left_inv := by
        intro y
        ext
        change (e.symm (e y.1)).1 = y.1.1
        exact congrArg Subtype.val (e.symm_apply_apply y.1)
      right_inv := by
        intro y
        ext
        change (e (e.symm ⟨y.1, hap.trans y.2.1, y.2.2.trans hbq⟩)).1 = y.1
        exact congrArg Subtype.val (e.apply_symm_apply
          ⟨y.1, hap.trans y.2.1, y.2.2.trans hbq⟩)
      map_rel_iff' := by
        intro y₁ y₂
        exact e.le_iff_le }
  let flatten : U ≃o Set.Ioo left right :=
    { toFun := fun y ↦ ⟨⟨y.1, y.2.2.trans right.2⟩, y.2⟩
      invFun := fun y ↦ ⟨y.1.1, y.2⟩
      left_inv := fun y ↦ by ext; rfl
      right_inv := fun y ↦ by ext; rfl
      map_rel_iff' := by
        intro y₁ y₂
        rfl }
  refine ⟨U, a, b, isOpen_Ioo, ⟨hleftx, hxright⟩, haz.trans hzb, ?_⟩
  exact ⟨(flatten.trans restrict).toHomeomorph⟩

/-- Part (5) of Exercise 24.12: every point of the long line has an open neighborhood
homeomorphic to an open interval in `ℝ`. -/
theorem LongLine.existsIntervalNeighborhood (x : LongLine) :
    ∃ (U : Set LongLine) (a b : ℝ),
      IsOpen U ∧ x ∈ U ∧ a < b ∧ Nonempty (U ≃ₜ Set.Ioo a b) :=
  by
    -- Bound `x` by a successor axis point and apply the generic chart adapter.
    obtain ⟨a, ha, hx, _⟩ := LongLine.existsCommonAxisBound x x
    obtain ⟨e⟩ := LongLine.openInitialSegmentOrderIso a ha
    exact existsOpenIntervalNeighborhood_of_iioOrderIso x
      (LongLine.axisPointInLongLine a ha) hx (0 : ℝ) 1 zero_lt_one e

/-- Helper for Exercise 24.12: every point with positive second coordinate lies
strictly above the deleted origin. -/
lemma LongLine.lexPoint_mem (a : OpenOmegaOne) (t : Set.Ico (0 : ℝ) 1)
    (ht : 0 < t) :
    LongLine.origin < ((a, t) : OpenOmegaOne ×ₗ Set.Ico (0 : ℝ) 1) := by
  -- Compare first coordinates; equality leaves the positive vertical coordinate.
  rw [Prod.Lex.lt_iff]
  simp only [LongLine.origin, LongLine.axisPoint]
  by_cases h : LongLine.leastOrdinal = a
  · right
    exact ⟨h, ht⟩
  · left
    have hle : LongLine.leastOrdinal ≤ a :=
      CountableOrdinal.zero_isLeast.2 (Set.mem_univ a)
    exact lt_of_le_of_ne hle h

/-- Helper for Exercise 24.12: membership in a vertical open interval determines
its first coordinate. -/
lemma LongLine.first_eq_of_mem_verticalIoo (a : OpenOmegaOne)
    (p q : Set.Ico (0 : ℝ) 1) (hp : 0 < p) (hq : 0 < q) (z : LongLine)
    (hz : z ∈ Set.Ioo
      (⟨(a, p), LongLine.mem_iff.2 (LongLine.lexPoint_mem a p hp)⟩ : LongLine)
      (⟨(a, q), LongLine.mem_iff.2 (LongLine.lexPoint_mem a q hq)⟩ : LongLine)) :
    z.1.1 = a := by
  -- The two lexicographic inequalities bound the first coordinate by `a` on both sides.
  have hleft : a ≤ z.1.1 := by
    rcases (Prod.Lex.lt_iff.mp hz.1) with h | h
    · exact h.le
    · exact h.1.le
  have hright : z.1.1 ≤ a := by
    rcases (Prod.Lex.lt_iff.mp hz.2) with h | h
    · exact h.le
    · change (ofLex z.1).1 ≤ (ofLex ((a, q) :
        OpenOmegaOne ×ₗ Set.Ico (0 : ℝ) 1)).1
      exact h.1.le
  exact le_antisymm hright hleft

/-- The long line does not have a countable basis. -/
theorem LongLine.notSecondCountable : ¬ SecondCountableTopology LongLine := by
  -- Use one fixed nonempty vertical open interval above every countable ordinal.
  let lowerCoord : Set.Ico (0 : ℝ) 1 := ⟨1 / 3, by norm_num, by norm_num⟩
  let middleCoord : Set.Ico (0 : ℝ) 1 := ⟨1 / 2, by norm_num, by norm_num⟩
  let upperCoord : Set.Ico (0 : ℝ) 1 := ⟨2 / 3, by norm_num, by norm_num⟩
  have hlower : 0 < lowerCoord := by
    change (0 : ℝ) < 1 / 3
    norm_num
  have hmiddle : 0 < middleCoord := by
    change (0 : ℝ) < 1 / 2
    norm_num
  have hupper : 0 < upperCoord := by
    change (0 : ℝ) < 2 / 3
    norm_num
  have hlm : lowerCoord < middleCoord := by norm_num [lowerCoord, middleCoord]
  have hmu : middleCoord < upperCoord := by norm_num [middleCoord, upperCoord]
  let lowerPoint : OpenOmegaOne → LongLine := fun a ↦
    ⟨(a, lowerCoord), LongLine.mem_iff.2 (LongLine.lexPoint_mem a lowerCoord hlower)⟩
  let middlePoint : OpenOmegaOne → LongLine := fun a ↦
    ⟨(a, middleCoord), LongLine.mem_iff.2 (LongLine.lexPoint_mem a middleCoord hmiddle)⟩
  let upperPoint : OpenOmegaOne → LongLine := fun a ↦
    ⟨(a, upperCoord), LongLine.mem_iff.2 (LongLine.lexPoint_mem a upperCoord hupper)⟩
  let slice : OpenOmegaOne → Set LongLine := fun a ↦ Set.Ioo (lowerPoint a) (upperPoint a)
  intro secondCountable
  letI : SecondCountableTopology LongLine := secondCountable
  haveI : TopologicalSpace.SeparableSpace LongLine := inferInstance
  have hopen : ∀ a, IsOpen (slice a) := fun _ ↦ isOpen_Ioo
  have hnonempty : ∀ a, (slice a).Nonempty := by
    intro a
    refine ⟨middlePoint a, ?_⟩
    constructor
    · unfold lowerPoint middlePoint
      exact Prod.Lex.lt_iff.2 (Or.inr ⟨rfl, hlm⟩)
    · unfold middlePoint upperPoint
      exact Prod.Lex.lt_iff.2 (Or.inr ⟨rfl, hmu⟩)
  have hdisjoint : Pairwise (Function.onFun Disjoint slice) := by
    intro a b hab
    change Disjoint (slice a) (slice b)
    rw [Set.disjoint_left]
    intro z hza hzb
    have hzaFirst : z.1.1 = a :=
      LongLine.first_eq_of_mem_verticalIoo a lowerCoord upperCoord hlower hupper z hza
    have hzbFirst : z.1.1 = b :=
      LongLine.first_eq_of_mem_verticalIoo b lowerCoord upperCoord hlower hupper z hzb
    exact hab (hzaFirst.symm.trans hzbFirst)
  exact not_countable (hdisjoint.countable_of_isOpen_disjoint hopen hnonempty)

/-- The long line does not embed in any second-countable space. -/
theorem LongLine.noEmbeddingIntoSecondCountable {Y : Type v} [TopologicalSpace Y]
    [SecondCountableTopology Y] :
    ¬ ∃ f : LongLine → Y, Topology.IsEmbedding f := by
  rintro ⟨f, hf⟩
  exact LongLine.notSecondCountable hf.secondCountableTopology

/-- Part (6) of Exercise 24.12: the long line cannot be embedded in any
finite-dimensional Euclidean space. -/
theorem LongLine.notEmbeddableEuclidean (n : ℕ) :
    ¬ ∃ f : LongLine → EuclideanSpace ℝ (Fin n), Topology.IsEmbedding f :=
  LongLine.noEmbeddingIntoSecondCountable
