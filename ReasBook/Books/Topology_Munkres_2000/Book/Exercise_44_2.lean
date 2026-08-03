module

public import Topology_Munkres_2000.Book.Exercise_44_1
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.Topology.Order.AtTopBotIxx

public section

open Set Function Topology Filter
open scoped unitInterval

/-- Helper for Exercise 44.2: a coordinate in `[-R, R]`, normalized affinely,
lies in the unit interval. -/
lemma normalizedCoordinate_mem_unitInterval {x R : ℝ} (hR : 0 < R) (hx : |x| ≤ R) :
    (x / R + 1) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
  -- The two absolute-value inequalities become the lower and upper endpoint bounds.
  constructor
  · have hx_lower : -R ≤ x := (abs_le.mp hx).1
    have hquotient : (-1 : ℝ) ≤ x / R := by
      apply (le_div_iff₀ hR).2
      simpa using hx_lower
    apply div_nonneg
    · linarith
    · norm_num
  · have hx_upper : x ≤ R := (abs_le.mp hx).2
    apply (div_le_one (by norm_num : (0 : ℝ) < 2)).2
    have hquotient : x / R ≤ 1 := (div_le_one hR).2 hx_upper
    linarith

/-- Helper for Exercise 44.2: a continuous surjection onto a unit cube yields a
based loop whose range contains a prescribed centered coordinate box. -/
lemma existsBasedLoop_range_contains_coordinateBox {n : ℕ}
    (g : C(unitInterval, Fin n → unitInterval)) (hg : Function.Surjective g) (r : ℕ) :
    ∃ γ : Path (0 : EuclideanSpace ℝ (Fin n)) 0,
      ∀ y, (∀ i, |y i| ≤ (r : ℝ) + 1) → y ∈ Set.range γ := by
  -- Affinely send the unit cube onto the box of radius `r + 1`.
  let boxFun : (Fin n → unitInterval) → EuclideanSpace ℝ (Fin n) := fun x =>
    WithLp.toLp 2 (fun i => ((r : ℝ) + 1) * (2 * (x i : ℝ) - 1))
  have boxFun_continuous : Continuous boxFun := by
    fun_prop
  let box : C(Fin n → unitInterval, EuclideanSpace ℝ (Fin n)) :=
    ⟨boxFun, boxFun_continuous⟩
  let curve : C(unitInterval, EuclideanSpace ℝ (Fin n)) := box.comp g
  have curve_source : curve 0 = curve 0 := rfl
  have curve_target : curve 1 = curve 1 := rfl
  let middle : Path (curve 0) (curve 1) := Path.mk curve curve_source curve_target
  let γ : Path (0 : EuclideanSpace ℝ (Fin n)) 0 :=
    (Path.segment 0 (curve 0)).trans (middle.trans (Path.segment (curve 1) 0))
  refine ⟨γ, ?_⟩
  intro y hy
  -- Normalize the target point back to the unit cube and use surjectivity of `g`.
  have radius_pos : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have coordinate_mem (i : Fin n) :
      (y i / ((r : ℝ) + 1) + 1) / 2 ∈ Set.Icc (0 : ℝ) 1 :=
    normalizedCoordinate_mem_unitInterval radius_pos (hy i)
  let x : Fin n → unitInterval := fun i =>
    ⟨(y i / ((r : ℝ) + 1) + 1) / 2, coordinate_mem i⟩
  obtain ⟨t, ht⟩ := hg x
  have curve_hits : curve t = y := by
    ext i
    simp [curve, box, boxFun, ht, x, PiLp.toLp_apply]
    field_simp [ne_of_gt radius_pos]
    ring
  have middle_hits : y ∈ Set.range middle := ⟨t, curve_hits⟩
  -- The middle part of the based loop contains the entire affine box curve.
  rw [show γ = (Path.segment 0 (curve 0)).trans
      (middle.trans (Path.segment (curve 1) 0)) by rfl, Path.trans_range, Path.trans_range]
  exact Or.inr (Or.inl middle_hits)

/-- Helper for Exercise 44.2: translation identifies an integer unit interval with
the standard unit interval. -/
lemma integerIntervalParameter_mem (k : ℤ)
    (x : Set.Icc (k : ℝ) ((k : ℝ) + 1)) :
    (x.1 - (k : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
  -- Subtracting the left endpoint transports both interval inequalities.
  constructor
  · linarith [x.2.1]
  · linarith [x.2.2]

/-- Helper for Exercise 44.2: the affine parameter on an integer unit interval. -/
def integerIntervalParameter (k : ℤ)
    (x : Set.Icc (k : ℝ) ((k : ℝ) + 1)) : unitInterval :=
  ⟨x.1 - (k : ℝ), integerIntervalParameter_mem k x⟩

/-- Helper for Exercise 44.2: the integer-interval parameter depends continuously
on the point of the interval. -/
lemma continuous_integerIntervalParameter (k : ℤ) :
    Continuous (integerIntervalParameter k) := by
  -- Continuity follows from the affine formula on the underlying real coordinate.
  apply Continuous.subtype_mk
  fun_prop

/-- Helper for Exercise 44.2: a based loop restricted to an integer unit interval
is a continuous local piece. -/
def integerLoopPiece {E : Type*} [TopologicalSpace E] {base : E}
    (γ : ℤ → Path base base) (k : ℤ) :
    C(Set.Icc (k : ℝ) ((k : ℝ) + 1), E) :=
  ⟨fun x => γ k (integerIntervalParameter k x),
    (γ k).continuous.comp (continuous_integerIntervalParameter k)⟩

/-- Helper for Exercise 44.2: two integer-loop pieces agree wherever their
closed unit intervals overlap. -/
lemma integerLoopPiece_eq_of_mem {E : Type*} [TopologicalSpace E] {base : E}
    (γ : ℤ → Path base base) (k l : ℤ) (x : ℝ)
    (hxk : x ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1))
    (hxl : x ∈ Set.Icc (l : ℝ) ((l : ℝ) + 1)) :
    integerLoopPiece γ k ⟨x, hxk⟩ = integerLoopPiece γ l ⟨x, hxl⟩ := by
  -- Distinct integer unit intervals can intersect only at a common endpoint.
  rcases lt_trichotomy k l with hkl | hkl | hkl
  · have hsucc : k + 1 ≤ l := Int.add_one_le_iff.mpr hkl
    have hleft : x = (k : ℝ) + 1 := by
      have hcast : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast hsucc
      linarith [hxk.2, hxl.1]
    have hright : x = (l : ℝ) := by
      have hcast : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast hsucc
      linarith [hxk.2, hxl.1]
    have hadjacent : k + 1 = l := by
      exact_mod_cast hleft.symm.trans hright
    subst l
    simp [integerLoopPiece, integerIntervalParameter, hleft]
  · subst l
    rfl
  · have hsucc : l + 1 ≤ k := Int.add_one_le_iff.mpr hkl
    have hleft : x = (l : ℝ) + 1 := by
      have hcast : (l : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hsucc
      linarith [hxl.2, hxk.1]
    have hright : x = (k : ℝ) := by
      have hcast : (l : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hsucc
      linarith [hxl.2, hxk.1]
    have hadjacent : l + 1 = k := by
      exact_mod_cast hleft.symm.trans hright
    subst k
    simp [integerLoopPiece, integerIntervalParameter, hleft]

/-- Helper for Exercise 44.2: the integer unit intervals form a locally finite
closed cover of the real line. -/
lemma locallyFinite_integerUnitIntervals :
    LocallyFinite (fun k : ℤ => Set.Icc (k : ℝ) ((k : ℝ) + 1)) := by
  -- Both endpoints escape to the appropriate infinities with the integer index.
  apply locallyFinite_Icc_of_tendsto
  · exact tendsto_intCast_atTop_atTop
  · apply Filter.tendsto_atBot_add_const_right atBot 1
    exact (tendsto_intCast_atBot_iff).2 tendsto_id

/-- Helper for Exercise 44.2: glue based loops along consecutive integer intervals. -/
noncomputable def gluedIntegerLoops {E : Type*} [TopologicalSpace E] {base : E}
    (γ : ℤ → Path base base) : ℝ → E :=
  Set.liftCover (fun k : ℤ => Set.Icc (k : ℝ) ((k : ℝ) + 1))
    (fun k x => integerLoopPiece γ k x) (integerLoopPiece_eq_of_mem γ)
    (iUnion_Icc_intCast ℝ)

/-- Helper for Exercise 44.2: the glued integer-loop function agrees with each
local loop piece on its defining interval. -/
lemma gluedIntegerLoops_of_mem {E : Type*} [TopologicalSpace E] {base : E}
    (γ : ℤ → Path base base) (k : ℤ) {x : ℝ}
    (hx : x ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1)) :
    gluedIntegerLoops γ x = integerLoopPiece γ k ⟨x, hx⟩ := by
  -- This is the computation rule supplied by the cover-lifting construction.
  simpa only [gluedIntegerLoops] using
    (Set.liftCover_of_mem
      (S := fun l : ℤ => Set.Icc (l : ℝ) ((l : ℝ) + 1))
      (f := fun l x => integerLoopPiece γ l x) hx)

/-- Helper for Exercise 44.2: a family of based loops can be pasted into one
continuous real-parameterized map containing every loop range. -/
lemma existsContinuousMap_range_contains_integerLoops
    {E : Type*} [TopologicalSpace E] {base : E} (γ : ℤ → Path base base) :
    ∃ F : C(ℝ, E), ∀ k, Set.range (γ k) ⊆ Set.range F := by
  -- Closed locally finite pasting proves continuity of the raw glued function.
  have glued_continuous : Continuous (gluedIntegerLoops γ) := by
    apply locallyFinite_integerUnitIntervals.continuous (iUnion_Icc_intCast ℝ)
    · intro k
      exact isClosed_Icc
    · intro k
      rw [continuousOn_iff_continuous_restrict]
      apply Continuous.congr (integerLoopPiece γ k).continuous
      intro x
      exact (gluedIntegerLoops_of_mem γ k x.2).symm
  let F : C(ℝ, E) := ⟨gluedIntegerLoops γ, glued_continuous⟩
  refine ⟨F, ?_⟩
  intro k y hy
  obtain ⟨t, rfl⟩ := hy
  -- The parameter `t` is realized on the interval starting at `k`.
  let x : ℝ := (k : ℝ) + t
  have hx : x ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1) := by
    constructor
    · linarith [t.2.1]
    · linarith [t.2.2]
  refine ⟨x, ?_⟩
  rw [show F x = gluedIntegerLoops γ x by rfl, gluedIntegerLoops_of_mem γ k hx]
  have hparameter : integerIntervalParameter k ⟨x, hx⟩ = t := by
    apply Subtype.ext
    simp [integerIntervalParameter, x]
  exact congrArg (γ k) hparameter

/-- Helper for Exercise 44.2: every finite Euclidean vector has all coordinates
bounded in absolute value by one natural number. -/
lemma exists_nat_coordinatewise_abs_le {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) :
    ∃ r : ℕ, ∀ i, |y i| ≤ r := by
  -- Bound the norm Archimedeanly, then use each coordinate projection's norm bound.
  obtain ⟨r, hr⟩ := exists_nat_ge ‖y‖
  refine ⟨r, ?_⟩
  intro i
  rw [← Real.norm_eq_abs]
  exact (PiLp.norm_apply_le y i).trans hr

/-- Exercise 44.2: For every finite dimension `n`, there is a continuous surjection
from `ℝ` onto `EuclideanSpace ℝ (Fin n)`. -/
theorem existsContinuousSurjectiveRealEuclideanSpace (n : ℕ) :
    ∃ f : C(ℝ, EuclideanSpace ℝ (Fin n)), Function.Surjective f := by
  -- Start with one cube-filling curve and turn it into loops covering larger boxes.
  obtain ⟨g, hg⟩ := existsContinuousSurjectiveUnitCube n
  choose γ hγ using fun k : ℤ =>
    existsBasedLoop_range_contains_coordinateBox g hg k.natAbs
  obtain ⟨F, hF⟩ := existsContinuousMap_range_contains_integerLoops γ
  refine ⟨F, ?_⟩
  intro y
  -- Choose a box containing `y`; the correspondingly indexed loop hits it.
  obtain ⟨r, hr⟩ := exists_nat_coordinatewise_abs_le y
  have hy_loop : y ∈ Set.range (γ (r : ℤ)) := by
    apply hγ
    intro i
    have hr_real : |y i| ≤ (r : ℝ) := by exact_mod_cast hr i
    simpa using hr_real.trans (by linarith : (r : ℝ) ≤ (r : ℝ) + 1)
  exact hF (r : ℤ) hy_loop
