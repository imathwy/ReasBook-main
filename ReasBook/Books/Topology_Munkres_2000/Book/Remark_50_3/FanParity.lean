module

public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Perm.Fin

public section

namespace StandardSphere.CubicalTucker

/-- Helper for Remark 50.3: the sign obtained after alternating `n` times from an
initial Boolean sign. -/
def alternatingSignAt (initial : Bool) : ℕ → Bool
  | 0 => initial
  | n + 1 => !(alternatingSignAt initial n)

/-- Helper for Remark 50.3: shifting an alternating sign sequence toggles its
initial sign. -/
lemma alternatingSignAt_succ (initial : Bool) (n : ℕ) :
    alternatingSignAt initial (n + 1) = alternatingSignAt (!initial) n := by
  -- Induct through the two simultaneous sign toggles.
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa only [alternatingSignAt] using congrArg Bool.not ih

/-- Helper for Remark 50.3: a Boolean tuple alternates from the prescribed
initial sign. -/
def IsAlternatingSign {r : ℕ} (initial : Bool) (sign : Fin r → Bool) : Prop :=
  ∀ j, sign j = alternatingSignAt initial j.1

/-- Helper for Remark 50.3: the mod-two indicator of an alternating Boolean
tuple. -/
noncomputable def alternatingSignWeight {r : ℕ} (initial : Bool)
    (sign : Fin r → Bool) : ZMod 2 :=
  @ite (ZMod 2) (IsAlternatingSign initial sign) (Classical.dec _) 1 0

/-- Helper for Remark 50.3: adjoining a head sign gives an alternating tuple
exactly when the head is prescribed and the tail starts with the opposite sign. -/
lemma isAlternatingSign_cons_iff {r : ℕ} (initial head : Bool)
    (tail : Fin r → Bool) :
    IsAlternatingSign initial (Fin.cons head tail) ↔
      head = initial ∧ IsAlternatingSign (!initial) tail := by
  -- Read the head at index zero and shift the remaining parity pattern once.
  constructor
  · intro halternating
    constructor
    · have hhead := halternating (0 : Fin (r + 1))
      change head = initial at hhead
      exact hhead
    · intro j
      simpa only [Fin.cons_succ, Fin.val_succ, alternatingSignAt_succ] using
        halternating j.succ
  · rintro ⟨rfl, halternating⟩ j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · rfl
    · simpa only [Fin.cons_succ, Fin.val_succ, alternatingSignAt_succ] using
        halternating k

/-- Helper for Remark 50.3: the alternating indicator of a tuple with a head
reduces to the opposite-initial indicator of its tail. -/
lemma alternatingSignWeight_cons {r : ℕ} (initial head : Bool)
    (tail : Fin r → Bool) :
    alternatingSignWeight initial (Fin.cons head tail) =
      if head = initial then alternatingSignWeight (!initial) tail else 0 := by
  -- Expand both indicators using the head-and-tail characterization.
  by_cases hhead : head = initial
  · subst head
    have hiff := isAlternatingSign_cons_iff initial initial tail
    by_cases htail : IsAlternatingSign (!initial) tail
    · have hcons : IsAlternatingSign initial (Fin.cons initial tail) :=
        hiff.mpr ⟨rfl, htail⟩
      simp [alternatingSignWeight, htail, hcons]
    · have hcons : ¬IsAlternatingSign initial (Fin.cons initial tail) :=
        fun h ↦ htail (hiff.mp h).2
      simp [alternatingSignWeight, htail, hcons]
  · have hcons : ¬IsAlternatingSign initial (Fin.cons head tail) :=
      fun h ↦ hhead ((isAlternatingSign_cons_iff initial head tail).mp h).1
    simp [alternatingSignWeight, hhead, hcons]

/-- Helper for Remark 50.3: the mod-two sum of the alternating indicators of
all vertex deletions is the sum of the two alternating orientations. -/
lemma sum_alternatingSignWeight_omit (r : ℕ) (initial : Bool)
    (sign : Fin (r + 1) → Bool) :
    ∑ k : Fin (r + 1),
        alternatingSignWeight initial (fun j ↦ sign (k.succAbove j)) =
      alternatingSignWeight initial sign + alternatingSignWeight (!initial) sign := by
  -- Peel off the first vertex; the successor omissions are the boundary sum
  -- for the tail with the initial sign toggled.
  induction r generalizing initial with
  | zero =>
      cases initial <;> cases hsign : sign 0 <;>
        simp [alternatingSignWeight, IsAlternatingSign,
          alternatingSignAt, hsign]
  | succ r ih =>
      let head := sign 0
      let tail := Fin.tail sign
      have hsign : sign = Fin.cons head tail := by
        exact (Fin.cons_self_tail sign).symm
      rw [hsign, Fin.sum_univ_succ]
      have homitZero :
          (fun j : Fin (r + 1) ↦
            (Fin.cons head tail : Fin (r + 2) → Bool)
              ((0 : Fin (r + 2)).succAbove j)) =
            (tail : Fin (r + 1) → Bool) := by
        funext j
        simp only [Fin.zero_succAbove, Fin.cons_succ]
      have homitSucc (k : Fin (r + 1)) :
          (fun j : Fin (r + 1) ↦
            (Fin.cons head tail : Fin (r + 2) → Bool)
              (k.succ.succAbove j)) =
            (Fin.cons head (fun j ↦ tail (k.succAbove j)) :
              Fin (r + 1) → Bool) := by
        funext j
        refine Fin.cases ?_ (fun i ↦ ?_) j
        · simp only [Fin.succ_succAbove_zero, Fin.cons_zero]
        · simp only [Fin.succ_succAbove_succ, Fin.cons_succ]
      rw [homitZero]
      simp_rw [homitSucc, alternatingSignWeight_cons]
      have hcharTwo (a b : ZMod 2) : a + (b + a) = b := by
        calc
          a + (b + a) = (a + a) + b := by ac_rfl
          _ = 0 + b := by rw [CharTwo.add_self_eq_zero]
          _ = b := zero_add b
      cases initial <;> cases head <;>
        simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
          Bool.true_eq_false, ↓reduceIte, ih]
      all_goals
        simp only [Finset.sum_const_zero, add_zero, zero_add, hcharTwo]

end StandardSphere.CubicalTucker

namespace StandardSphere

/-- Helper for Remark 50.3: vertices of the centered cubical grid with radius
`m` in `d` coordinates. -/
abbrev CenteredGrid (d m : ℕ) := Fin d → Fin (2 * m + 1)

/-- Helper for Remark 50.3: reflection of a centered grid vertex through the
grid center. -/
@[expose] def centeredGridNeg {d m : ℕ} (v : CenteredGrid d m) :
    CenteredGrid d m :=
  fun i ↦ Fin.rev (v i)

/-- Helper for Remark 50.3: a centered grid vertex lies on the cubical boundary
when at least one coordinate is extremal. -/
@[expose] def centeredGridBoundary {d m : ℕ} (v : CenteredGrid d m) : Prop :=
  ∃ i, (v i).1 = 0 ∨ (v i).1 = 2 * m

/-- Helper for Remark 50.3: two centered grid vertices lie in a common
elementary cube when their coordinates differ by at most one. -/
@[expose] def centeredGridNeighbor {d m : ℕ}
    (v w : CenteredGrid d m) : Prop :=
  ∀ i, (v i).1 ≤ (w i).1 + 1 ∧ (w i).1 ≤ (v i).1 + 1

/-- Helper for Remark 50.3: centered-grid reflection is an involution. -/
lemma centeredGridNeg_neg {d m : ℕ} (v : CenteredGrid d m) :
    centeredGridNeg (centeredGridNeg v) = v := by
  -- Reduce the global reflection to the coordinatewise involution `Fin.rev`.
  funext i
  exact Fin.rev_rev (v i)

/-- Helper for Remark 50.3: a coordinate and its centered reflection sum to
`2 * m`. -/
lemma centeredGridNeg_value {d m : ℕ} (v : CenteredGrid d m) (i : Fin d) :
    (centeredGridNeg v i).1 + (v i).1 = 2 * m := by
  -- Use the standard value computation for reflection in a finite interval.
  exact Fin.rev_add_cast (v i)

/-- Helper for Remark 50.3: centered reflection preserves the cubical boundary. -/
lemma centeredGridBoundary_neg {d m : ℕ} (v : CenteredGrid d m) :
    centeredGridBoundary (centeredGridNeg v) ↔ centeredGridBoundary v := by
  -- Reflection exchanges the two extremal values in the witnessing coordinate.
  constructor
  · rintro ⟨i, hi | hi⟩
    · refine ⟨i, Or.inr ?_⟩
      have hsum := centeredGridNeg_value v i
      omega
    · refine ⟨i, Or.inl ?_⟩
      have hsum := centeredGridNeg_value v i
      omega
  · rintro ⟨i, hi | hi⟩
    · refine ⟨i, Or.inr ?_⟩
      have hsum := centeredGridNeg_value v i
      omega
    · refine ⟨i, Or.inl ?_⟩
      have hsum := centeredGridNeg_value v i
      omega

/-- Helper for Remark 50.3: simultaneous centered reflection preserves the
elementary-cube neighbor relation. -/
lemma centeredGridNeighbor_neg {d m : ℕ} (v w : CenteredGrid d m) :
    centeredGridNeighbor (centeredGridNeg v) (centeredGridNeg w) ↔
      centeredGridNeighbor v w := by
  -- Reflected coordinate differences are the original differences reversed.
  constructor
  · intro h i
    have hv := centeredGridNeg_value v i
    have hw := centeredGridNeg_value w i
    obtain ⟨hvw, hwv⟩ := h i
    constructor
    · omega
    · omega
  · intro h i
    have hv := centeredGridNeg_value v i
    have hw := centeredGridNeg_value w i
    obtain ⟨hvw, hwv⟩ := h i
    constructor
    · omega
    · omega

/-- Helper for Remark 50.3: at positive radius, centered reflection has no
fixed point on the cubical boundary. -/
lemma centeredGridNeg_ne_of_boundary {d m : ℕ} (hm : 0 < m)
    {v : CenteredGrid d m} (hv : centeredGridBoundary v) :
    centeredGridNeg v ≠ v := by
  -- An extremal coordinate is reflected to the opposite, distinct extremum.
  rintro hfixed
  obtain ⟨i, hi | hi⟩ := hv
  · have hcoordinate := congrFun hfixed i
    have hvalue := centeredGridNeg_value v i
    have heq := congrArg Fin.val hcoordinate
    omega
  · have hcoordinate := congrFun hfixed i
    have hvalue := centeredGridNeg_value v i
    have heq := congrArg Fin.val hcoordinate
    omega

/-- Helper for Remark 50.3: every centered-grid vertex is its own neighbor. -/
lemma centeredGridNeighbor_refl {d m : ℕ} (v : CenteredGrid d m) :
    centeredGridNeighbor v v := by
  -- Both coordinate inequalities are immediate after allowing one grid step.
  intro i
  omega

/-- Helper for Remark 50.3: centered-grid neighborhood is symmetric. -/
lemma centeredGridNeighbor_symm {d m : ℕ} {v w : CenteredGrid d m}
    (hvw : centeredGridNeighbor v w) : centeredGridNeighbor w v := by
  -- Swap the two coordinate inequalities supplied by the hypothesis.
  intro i
  exact (hvw i).symm

/-- Helper for Remark 50.3: the central grid value is a valid coordinate. -/
lemma centeredGridCenter_isLt (m : ℕ) : m < 2 * m + 1 := by
  -- The centered interval has one endpoint beyond twice its radius.
  omega

/-- Helper for Remark 50.3: the central coordinate of the interval
`Fin (2 * m + 1)`. -/
def centeredGridCenter (m : ℕ) : Fin (2 * m + 1) :=
  ⟨m, centeredGridCenter_isLt m⟩

/-- Helper for Remark 50.3: centered reflection fixes the central coordinate. -/
lemma centeredGridCenter_rev (m : ℕ) :
    Fin.rev (centeredGridCenter m) = centeredGridCenter m := by
  -- Compare values and use the reflection sum at the central value.
  apply Fin.ext
  have hsum := Fin.rev_add_cast (centeredGridCenter m)
  simp only [centeredGridCenter] at hsum ⊢
  omega

/-- Helper for Remark 50.3: insert the central coordinate to identify a
lower-dimensional grid with the central equator. -/
def centeredGridEquator {d m : ℕ} (v : CenteredGrid d m) :
    CenteredGrid (d + 1) m :=
  Fin.cons (centeredGridCenter m) v

/-- Helper for Remark 50.3: the inserted equator coordinate is central. -/
lemma centeredGridEquator_zero {d m : ℕ} (v : CenteredGrid d m) :
    centeredGridEquator v 0 = centeredGridCenter m := by
  -- Evaluate the head of the inserted coordinate tuple.
  rfl

/-- Helper for Remark 50.3: the remaining coordinates of an equator insertion
are the original lower-dimensional vertex. -/
lemma centeredGridEquator_succ {d m : ℕ} (v : CenteredGrid d m) (i : Fin d) :
    centeredGridEquator v i.succ = v i := by
  -- Evaluate the tail of the inserted coordinate tuple.
  rfl

/-- Helper for Remark 50.3: equator insertion commutes with centered reflection. -/
lemma centeredGridEquator_neg {d m : ℕ} (v : CenteredGrid d m) :
    centeredGridNeg (centeredGridEquator v) =
      centeredGridEquator (centeredGridNeg v) := by
  -- Compare the central coordinate and every retained coordinate separately.
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact centeredGridCenter_rev m
  · rfl

/-- Helper for Remark 50.3: at positive radius, equator insertion preserves
and reflects cubical-boundary membership. -/
lemma centeredGridEquator_boundary_iff {d m : ℕ} (hm : 0 < m)
    (v : CenteredGrid d m) :
    centeredGridBoundary (centeredGridEquator v) ↔ centeredGridBoundary v := by
  -- A positive-radius central coordinate is not extremal, so any witness lies in the tail.
  constructor
  · rintro ⟨i, hi⟩
    induction i using Fin.cases with
    | zero =>
      simp only [centeredGridEquator_zero, centeredGridCenter] at hi
      omega
    | succ j =>
      exact ⟨j, by simpa only [centeredGridEquator_succ] using hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i.succ, by simpa only [centeredGridEquator_succ] using hi⟩

/-- Helper for Remark 50.3: equator insertion preserves and reflects the
elementary-cube neighbor relation. -/
lemma centeredGridEquator_neighbor_iff {d m : ℕ} (v w : CenteredGrid d m) :
    centeredGridNeighbor (centeredGridEquator v) (centeredGridEquator w) ↔
      centeredGridNeighbor v w := by
  -- The common central coordinate contributes a trivial inequality pair.
  constructor
  · intro h i
    simpa only [centeredGridEquator_succ] using h i.succ
  · intro h i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [centeredGridEquator_zero]
      omega
    · simpa only [centeredGridEquator_succ] using h j

/-- Helper for Remark 50.3: the positive closed hemisphere is selected by the
first coordinate lying at or above the center. -/
def centeredGridPositiveHemisphere {d m : ℕ}
    (v : CenteredGrid (d + 1) m) : Prop :=
  m ≤ (v 0).1

/-- Helper for Remark 50.3: the negative closed hemisphere is selected by the
first coordinate lying at or below the center. -/
def centeredGridNegativeHemisphere {d m : ℕ}
    (v : CenteredGrid (d + 1) m) : Prop :=
  (v 0).1 ≤ m

/-- Helper for Remark 50.3: the central equator consists of vertices whose
first coordinate is the center. -/
def centeredGridOnEquator {d m : ℕ} (v : CenteredGrid (d + 1) m) : Prop :=
  (v 0).1 = m

/-- Helper for Remark 50.3: positive-hemisphere membership is exactly the
first-coordinate lower bound. -/
lemma centeredGridPositiveHemisphere_iff {d m : ℕ}
    (v : CenteredGrid (d + 1) m) :
    centeredGridPositiveHemisphere v ↔ m ≤ (v 0).1 := by
  -- Expose the defining coordinate inequality through a stable proposition.
  rfl

/-- Helper for Remark 50.3: negative-hemisphere membership is exactly the
first-coordinate upper bound. -/
lemma centeredGridNegativeHemisphere_iff {d m : ℕ}
    (v : CenteredGrid (d + 1) m) :
    centeredGridNegativeHemisphere v ↔ (v 0).1 ≤ m := by
  -- Expose the defining coordinate inequality through a stable proposition.
  rfl

/-- Helper for Remark 50.3: equator membership is exactly equality of the
first coordinate with the grid center. -/
lemma centeredGridOnEquator_iff {d m : ℕ} (v : CenteredGrid (d + 1) m) :
    centeredGridOnEquator v ↔ (v 0).1 = m := by
  -- Expose the defining coordinate equality through a stable proposition.
  rfl

/-- Helper for Remark 50.3: reflection exchanges the positive and negative
closed hemispheres. -/
lemma centeredGridNeg_positiveHemisphere_iff {d m : ℕ}
    (v : CenteredGrid (d + 1) m) :
    centeredGridPositiveHemisphere (centeredGridNeg v) ↔
      centeredGridNegativeHemisphere v := by
  -- The first reflected value is `2 * m` minus the original first value.
  have hsum := centeredGridNeg_value v (0 : Fin (d + 1))
  unfold centeredGridPositiveHemisphere centeredGridNegativeHemisphere
  omega

/-- Helper for Remark 50.3: reflection exchanges the negative and positive
closed hemispheres. -/
lemma centeredGridNeg_negativeHemisphere_iff {d m : ℕ}
    (v : CenteredGrid (d + 1) m) :
    centeredGridNegativeHemisphere (centeredGridNeg v) ↔
      centeredGridPositiveHemisphere v := by
  -- Use the same first-coordinate reflection equation with the inequalities reversed.
  have hsum := centeredGridNeg_value v (0 : Fin (d + 1))
  unfold centeredGridPositiveHemisphere centeredGridNegativeHemisphere
  omega

/-- Helper for Remark 50.3: reflection preserves the central equator. -/
lemma centeredGridNeg_onEquator_iff {d m : ℕ}
    (v : CenteredGrid (d + 1) m) :
    centeredGridOnEquator (centeredGridNeg v) ↔ centeredGridOnEquator v := by
  -- A reflected first coordinate equals the center exactly when the original does.
  have hsum := centeredGridNeg_value v (0 : Fin (d + 1))
  unfold centeredGridOnEquator
  omega

/-- Helper for Remark 50.3: every equator insertion lies on the central equator. -/
lemma centeredGridEquator_onEquator {d m : ℕ} (v : CenteredGrid d m) :
    centeredGridOnEquator (centeredGridEquator v) := by
  -- Evaluate the inserted first coordinate.
  simp only [centeredGridOnEquator, centeredGridEquator_zero, centeredGridCenter]

/-- Helper for Remark 50.3: an equatorial vertex is reconstructed by inserting
the center before its tail coordinates. -/
lemma centeredGridEquator_tail {d m : ℕ} (v : CenteredGrid (d + 1) m)
    (hv : centeredGridOnEquator v) :
    centeredGridEquator (Fin.tail v) = v := by
  -- Compare the central head using `hv` and retain all tail coordinates verbatim.
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · apply Fin.ext
    simpa only [centeredGridEquator_zero, centeredGridCenter,
      centeredGridOnEquator] using hv.symm
  · rfl

end StandardSphere
