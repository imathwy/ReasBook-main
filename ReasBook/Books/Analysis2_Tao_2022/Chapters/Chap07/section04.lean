/-
  Copyright (c) 2026 Zichen Wang. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
-/

import Mathlib

section Chap07
section Section04

/-- Definition 7.5 (Lebesgue measurability): a set `E ⊆ ℝ^n` is Lebesgue measurable iff
for every set `A ⊆ ℝ^n`, one has
`m*(A) = m*(A ∩ E) + m*(A \ E)`, where `m*` is Lebesgue outer measure. -/
def isLebesgueMeasurable (n : ℕ) (E : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  (MeasureTheory.volume.toOuterMeasure).IsCaratheodory E

/-- The Lebesgue measure `m(E)` as a function defined on Lebesgue measurable sets. -/
noncomputable def lebesgueMeasureOfSet (n : ℕ) :
    {E : Set (EuclideanSpace ℝ (Fin n)) // isLebesgueMeasurable n E} → ENNReal :=
  fun E => (MeasureTheory.volume.toOuterMeasure) E.1

/-- The index of the last coordinate in `Fin n` when `n ≥ 1`. -/
lemma lastCoordinateIndex_lt (n : ℕ) (hn : 1 ≤ n) : n - 1 < n := by
  have hn0 : 0 < n := Nat.succ_le_iff.mp hn
  exact Nat.sub_lt hn0 Nat.one_pos

/-- The `Fin n` index corresponding to the last coordinate when `n ≥ 1`. -/
def lastCoordinateIndex (n : ℕ) (hn : 1 ≤ n) : Fin n :=
  ⟨n - 1, lastCoordinateIndex_lt n hn⟩

/-- Helper for Lemma 7.2: continuity of the last-coordinate projection on `ℝ^n`. -/
lemma helperForLemma_7_2_lastCoordinateProjectionContinuous (n : ℕ) (hn : 1 ≤ n) :
    Continuous (fun x : EuclideanSpace ℝ (Fin n) => x (lastCoordinateIndex n hn)) := by
  simpa [EuclideanSpace] using
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin n => ℝ)
      (i := lastCoordinateIndex n hn))

/-- Helper for Lemma 7.2: the positivity half-space is open in `ℝ^n`. -/
lemma helperForLemma_7_2_halfSpaceIsOpen (n : ℕ) (hn : 1 ≤ n) :
    IsOpen ({x : EuclideanSpace ℝ (Fin n) | 0 < x (lastCoordinateIndex n hn)} :
      Set (EuclideanSpace ℝ (Fin n))) := by
  simpa [Set.preimage] using
    (isOpen_Ioi.preimage (helperForLemma_7_2_lastCoordinateProjectionContinuous n hn))

/-- Helper for Lemma 7.2: every open subset of `ℝ^n` is Lebesgue measurable. -/
lemma helperForLemma_7_2_isLebesgueMeasurable_of_isOpen (n : ℕ)
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : IsOpen E) : isLebesgueMeasurable n E := by
  unfold isLebesgueMeasurable
  exact (MeasureTheory.le_toOuterMeasure_caratheodory MeasureTheory.volume) E hE.measurableSet

/-- Lemma 7.2 (Half-spaces are measurable): in `ℝ^n` with `n ≥ 1`, the open half-space
`{(x_1, …, x_n) : x_n > 0}` (encoded via the last coordinate index) is Lebesgue measurable. -/
lemma halfSpace_isLebesgueMeasurable (n : ℕ) (hn : 1 ≤ n) :
    isLebesgueMeasurable n
      {x : EuclideanSpace ℝ (Fin n) | 0 < x (lastCoordinateIndex n hn)} := by
  exact helperForLemma_7_2_isLebesgueMeasurable_of_isOpen n
    (helperForLemma_7_2_halfSpaceIsOpen n hn)

/-- Helper for Lemma 7.3: preimage of a translated image under the same translation. -/
lemma helperForLemma_7_3_preimage_add_image (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (E : Set (EuclideanSpace ℝ (Fin n))) :
    (fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹'
      ((fun y : EuclideanSpace ℝ (Fin n) => x + y) '' E) = E := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨z, hz, hzEq⟩
    have hyz : y = z := (add_left_cancel (a := x) hzEq).symm
    exact hyz ▸ hz
  · intro hy
    exact ⟨y, hy, rfl⟩

/-- Helper for Lemma 7.3: preimage of an intersection with a translated image. -/
lemma helperForLemma_7_3_preimage_add_inter (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (E t : Set (EuclideanSpace ℝ (Fin n))) :
    (fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹'
      (t ∩ ((fun y : EuclideanSpace ℝ (Fin n) => x + y) '' E)) =
        ((fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹' t) ∩ E := by
  calc
    (fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹'
        (t ∩ ((fun y : EuclideanSpace ℝ (Fin n) => x + y) '' E))
        = ((fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹' t) ∩
          ((fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹'
            ((fun y : EuclideanSpace ℝ (Fin n) => x + y) '' E)) := by
              rw [Set.preimage_inter]
    _ = ((fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹' t) ∩ E := by
          rw [helperForLemma_7_3_preimage_add_image n x E]

/-- Helper for Lemma 7.3: preimage of a set difference with a translated image. -/
lemma helperForLemma_7_3_preimage_add_diff (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (E t : Set (EuclideanSpace ℝ (Fin n))) :
    (fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹'
      (t \ ((fun y : EuclideanSpace ℝ (Fin n) => x + y) '' E)) =
        ((fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹' t) \ E := by
  calc
    (fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹'
        (t \ ((fun y : EuclideanSpace ℝ (Fin n) => x + y) '' E))
        = ((fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹' t) \
          ((fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹'
            ((fun y : EuclideanSpace ℝ (Fin n) => x + y) '' E)) := by
              rw [Set.preimage_diff]
    _ = ((fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹' t) \ E := by
          rw [helperForLemma_7_3_preimage_add_image n x E]

/-- Helper for Lemma 7.3: translation preserves Lebesgue measurability and volume. -/
lemma helperForLemma_7_3_translation_preserves_measurability_and_volume
    (n : ℕ) (E : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    (hE : isLebesgueMeasurable n E) :
    isLebesgueMeasurable n ((fun y : EuclideanSpace ℝ (Fin n) => x + y) '' E) ∧
      MeasureTheory.volume ((fun y : EuclideanSpace ℝ (Fin n) => x + y) '' E) =
        MeasureTheory.volume E := by
  constructor
  · unfold isLebesgueMeasurable at hE ⊢
    intro t
    have hPreimageEq :
        MeasureTheory.volume t =
          MeasureTheory.volume ((fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹' t) := by
      symm
      simpa using (MeasureTheory.measure_preimage_add MeasureTheory.volume x t)
    have hInterEq :
        MeasureTheory.volume (t ∩ ((fun y : EuclideanSpace ℝ (Fin n) => x + y) '' E)) =
          MeasureTheory.volume
            (((fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹' t) ∩ E) := by
      calc
        MeasureTheory.volume (t ∩ ((fun y : EuclideanSpace ℝ (Fin n) => x + y) '' E))
            = MeasureTheory.volume
                ((fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹'
                  (t ∩ ((fun y : EuclideanSpace ℝ (Fin n) => x + y) '' E))) := by
                symm
                exact MeasureTheory.measure_preimage_add MeasureTheory.volume x
                  (t ∩ ((fun y : EuclideanSpace ℝ (Fin n) => x + y) '' E))
        _ = MeasureTheory.volume (((fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹' t) ∩ E) := by
              rw [helperForLemma_7_3_preimage_add_inter n x E t]
    have hDiffEq :
        MeasureTheory.volume (t \ ((fun y : EuclideanSpace ℝ (Fin n) => x + y) '' E)) =
          MeasureTheory.volume
            (((fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹' t) \ E) := by
      calc
        MeasureTheory.volume (t \ ((fun y : EuclideanSpace ℝ (Fin n) => x + y) '' E))
            = MeasureTheory.volume
                ((fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹'
                  (t \ ((fun y : EuclideanSpace ℝ (Fin n) => x + y) '' E))) := by
                symm
                exact MeasureTheory.measure_preimage_add MeasureTheory.volume x
                  (t \ ((fun y : EuclideanSpace ℝ (Fin n) => x + y) '' E))
        _ = MeasureTheory.volume (((fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹' t) \ E) := by
              rw [helperForLemma_7_3_preimage_add_diff n x E t]
    calc
      MeasureTheory.volume t
          = MeasureTheory.volume ((fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹' t) :=
            hPreimageEq
      _ = MeasureTheory.volume (((fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹' t) ∩ E) +
            MeasureTheory.volume (((fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹' t) \ E) := by
              simpa [MeasureTheory.Measure.toOuterMeasure_apply] using
                hE ((fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹' t)
      _ = MeasureTheory.volume (t ∩ ((fun y : EuclideanSpace ℝ (Fin n) => x + y) '' E)) +
            MeasureTheory.volume (t \ ((fun y : EuclideanSpace ℝ (Fin n) => x + y) '' E)) := by
              rw [← hInterEq, ← hDiffEq]
  · calc
      MeasureTheory.volume ((fun y : EuclideanSpace ℝ (Fin n) => x + y) '' E)
          = MeasureTheory.volume
              ((fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹'
                ((fun y : EuclideanSpace ℝ (Fin n) => x + y) '' E)) := by
                symm
                exact MeasureTheory.measure_preimage_add MeasureTheory.volume x
                  (((fun y : EuclideanSpace ℝ (Fin n) => x + y) '' E))
      _ = MeasureTheory.volume E := by
            rw [helperForLemma_7_3_preimage_add_image n x E]

/-- Helper for Lemma 7.3: finite unions and finite intersections of measurable sets are measurable.
-/
lemma helperForLemma_7_3_finite_union_and_intersection (n N : ℕ)
    (E : Fin N → Set (EuclideanSpace ℝ (Fin n)))
    (hE : ∀ j : Fin N, isLebesgueMeasurable n (E j)) :
    isLebesgueMeasurable n (⋃ j, E j) ∧ isLebesgueMeasurable n (⋂ j, E j) := by
  have hUnion : isLebesgueMeasurable n (⋃ j, E j) := by
    unfold isLebesgueMeasurable
    simpa using
      (MeasureTheory.OuterMeasure.IsCaratheodory.biUnion_of_finite
        (m := MeasureTheory.volume.toOuterMeasure)
        (s := E)
        (t := (Set.univ : Set (Fin N)))
        (Set.toFinite (Set.univ : Set (Fin N)))
        (by
          intro i hi
          simpa [isLebesgueMeasurable] using hE i))
  have hUnionCompl : isLebesgueMeasurable n (⋃ j, (E j)ᶜ) := by
    unfold isLebesgueMeasurable
    simpa using
      (MeasureTheory.OuterMeasure.IsCaratheodory.biUnion_of_finite
        (m := MeasureTheory.volume.toOuterMeasure)
        (s := fun j : Fin N => (E j)ᶜ)
        (t := (Set.univ : Set (Fin N)))
        (Set.toFinite (Set.univ : Set (Fin N)))
        (by
          intro i hi
          have hiMeas : isLebesgueMeasurable n (E i) := hE i
          exact MeasureTheory.OuterMeasure.isCaratheodory_compl
            (MeasureTheory.volume.toOuterMeasure)
            (by simpa [isLebesgueMeasurable] using hiMeas)))
  have hInter : isLebesgueMeasurable n (⋂ j, E j) := by
    have hEq : (⋂ j, E j) = (⋃ j, (E j)ᶜ)ᶜ := by
      ext x
      simp
    rw [hEq]
    unfold isLebesgueMeasurable at hUnionCompl ⊢
    exact MeasureTheory.OuterMeasure.isCaratheodory_compl
      (MeasureTheory.volume.toOuterMeasure) hUnionCompl
  exact ⟨hUnion, hInter⟩

/-- Helper for Lemma 7.3: continuity of each coordinate projection on `ℝ^n`. -/
lemma helperForLemma_7_3_coordinateProjectionContinuous (n : ℕ) (i : Fin n) :
    Continuous (fun x : EuclideanSpace ℝ (Fin n) => x i) := by
  simpa [EuclideanSpace] using
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin n => ℝ) (i := i))

/-- Helper for Lemma 7.3: coordinate open boxes and coordinate closed boxes are measurable. -/
lemma helperForLemma_7_3_coordinate_open_closed_boxes_measurable (n : ℕ)
    (a b : EuclideanSpace ℝ (Fin n)) :
    isLebesgueMeasurable n {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin n, a i < x i ∧ x i < b i} ∧
      isLebesgueMeasurable n
        {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin n, a i ≤ x i ∧ x i ≤ b i} := by
  have hOpenBox :
      IsOpen {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin n, a i < x i ∧ x i < b i} := by
    have hBiInterOpen :
        IsOpen (⋂ i ∈ (Set.univ : Set (Fin n)),
          {x : EuclideanSpace ℝ (Fin n) | a i < x i ∧ x i < b i}) := by
      exact (Set.toFinite (Set.univ : Set (Fin n))).isOpen_biInter (fun i hi =>
        by
          simpa [Set.setOf_and] using
            ((isOpen_lt continuous_const
              (helperForLemma_7_3_coordinateProjectionContinuous n i)).inter
              (isOpen_lt
                (helperForLemma_7_3_coordinateProjectionContinuous n i)
                continuous_const)))
    have hEq :
        {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin n, a i < x i ∧ x i < b i} =
          (⋂ i ∈ (Set.univ : Set (Fin n)),
            {x : EuclideanSpace ℝ (Fin n) | a i < x i ∧ x i < b i}) := by
      ext x
      simp
    rw [hEq]
    exact hBiInterOpen
  have hClosedBox :
      IsClosed {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin n, a i ≤ x i ∧ x i ≤ b i} := by
    have hBiInterClosed :
        IsClosed (⋂ i ∈ (Set.univ : Set (Fin n)),
          {x : EuclideanSpace ℝ (Fin n) | a i ≤ x i ∧ x i ≤ b i}) := by
      exact isClosed_biInter (fun i hi =>
        by
          simpa [Set.setOf_and] using
            ((isClosed_le continuous_const
              (helperForLemma_7_3_coordinateProjectionContinuous n i)).inter
              (isClosed_le
                (helperForLemma_7_3_coordinateProjectionContinuous n i)
                continuous_const)))
    have hEq :
        {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin n, a i ≤ x i ∧ x i ≤ b i} =
          (⋂ i ∈ (Set.univ : Set (Fin n)),
            {x : EuclideanSpace ℝ (Fin n) | a i ≤ x i ∧ x i ≤ b i}) := by
      ext x
      simp
    rw [hEq]
    exact hBiInterClosed
  constructor
  · unfold isLebesgueMeasurable
    exact (MeasureTheory.le_toOuterMeasure_caratheodory MeasureTheory.volume)
      _ hOpenBox.measurableSet
  · unfold isLebesgueMeasurable
    exact (MeasureTheory.le_toOuterMeasure_caratheodory MeasureTheory.volume)
      _ hClosedBox.measurableSet

/-- Helper for Lemma 7.3: a set of outer measure zero is Carathéodory-measurable. -/
lemma helperForLemma_7_3_outerMeasure_zero_implies_measurable (n : ℕ)
    (E : Set (EuclideanSpace ℝ (Fin n)))
    (hE0 : (MeasureTheory.volume.toOuterMeasure) E = 0) :
    isLebesgueMeasurable n E := by
  unfold isLebesgueMeasurable
  refine (MeasureTheory.OuterMeasure.isCaratheodory_iff_le (MeasureTheory.volume.toOuterMeasure)).2
    ?_
  intro t
  have hInterZero : (MeasureTheory.volume.toOuterMeasure) (t ∩ E) = 0 := by
    apply le_antisymm
    · exact le_trans
        ((MeasureTheory.volume.toOuterMeasure).mono (Set.inter_subset_right : t ∩ E ⊆ E))
        (by simpa [hE0])
    · simp
  calc
    (MeasureTheory.volume.toOuterMeasure) (t ∩ E) +
        (MeasureTheory.volume.toOuterMeasure) (t \ E)
        ≤ 0 + (MeasureTheory.volume.toOuterMeasure) (t \ E) := by
          gcongr
          exact le_of_eq hInterZero
    _ = (MeasureTheory.volume.toOuterMeasure) (t \ E) := by simp
    _ ≤ (MeasureTheory.volume.toOuterMeasure) t :=
      (MeasureTheory.volume.toOuterMeasure).mono (by
        intro y hy
        exact hy.1)

/-- Lemma 7.3 (Properties of measurable sets):
(a) complements of measurable sets are measurable;
(b) translation preserves measurability and volume;
(c) measurable sets are closed under finite unions and intersections of two sets;
(d) measurable sets are closed under finite unions and intersections over `Fin N`;
(e) every coordinate open box and coordinate closed box in `ℝ^n` is measurable;
(f) sets of outer measure zero are measurable. -/
theorem measurableSet_properties (n : ℕ) :
    (∀ E : Set (EuclideanSpace ℝ (Fin n)),
      isLebesgueMeasurable n E → isLebesgueMeasurable n Eᶜ) ∧
    (∀ (E : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)),
      isLebesgueMeasurable n E →
        isLebesgueMeasurable n ((fun y : EuclideanSpace ℝ (Fin n) => x + y) '' E) ∧
          MeasureTheory.volume ((fun y : EuclideanSpace ℝ (Fin n) => x + y) '' E) =
            MeasureTheory.volume E) ∧
    (∀ E₁ E₂ : Set (EuclideanSpace ℝ (Fin n)),
      isLebesgueMeasurable n E₁ →
        isLebesgueMeasurable n E₂ →
          isLebesgueMeasurable n (E₁ ∩ E₂) ∧ isLebesgueMeasurable n (E₁ ∪ E₂)) ∧
    (∀ (N : ℕ) (E : Fin N → Set (EuclideanSpace ℝ (Fin n))),
      (∀ j : Fin N, isLebesgueMeasurable n (E j)) →
        isLebesgueMeasurable n (⋃ j, E j) ∧ isLebesgueMeasurable n (⋂ j, E j)) ∧
    (∀ a b : EuclideanSpace ℝ (Fin n),
      isLebesgueMeasurable n {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin n, a i < x i ∧ x i < b i} ∧
        isLebesgueMeasurable n
          {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin n, a i ≤ x i ∧ x i ≤ b i}) ∧
    (∀ E : Set (EuclideanSpace ℝ (Fin n)),
      (MeasureTheory.volume.toOuterMeasure) E = 0 → isLebesgueMeasurable n E) := by
  constructor
  · intro E hE
    unfold isLebesgueMeasurable at hE ⊢
    exact MeasureTheory.OuterMeasure.isCaratheodory_compl (MeasureTheory.volume.toOuterMeasure) hE
  constructor
  · intro E x hE
    exact helperForLemma_7_3_translation_preserves_measurability_and_volume n E x hE
  constructor
  · intro E₁ E₂ hE₁ hE₂
    unfold isLebesgueMeasurable at hE₁ hE₂ ⊢
    constructor
    · exact (MeasureTheory.volume.toOuterMeasure).isCaratheodory_inter hE₁ hE₂
    · exact (MeasureTheory.volume.toOuterMeasure).isCaratheodory_union hE₁ hE₂
  constructor
  · intro N E hE
    exact helperForLemma_7_3_finite_union_and_intersection n N E hE
  constructor
  · intro a b
    exact helperForLemma_7_3_coordinate_open_closed_boxes_measurable n a b
  · intro E hE0
    exact helperForLemma_7_3_outerMeasure_zero_implies_measurable n E hE0

/-- The measure induced by an outer measure on its Carathéodory measurable sets. -/
noncomputable def outerMeasureRestrictedMeasure {α : Type*}
    (mStar : MeasureTheory.OuterMeasure α) : @MeasureTheory.Measure α mStar.caratheodory :=
  @MeasureTheory.OuterMeasure.toMeasure α mStar.caratheodory mStar (le_rfl)

/-- Helper for Lemma 7.4: one member of a pairwise disjoint family is disjoint from the finite
union of all other members indexed by a `Finset` that does not contain it. -/
lemma helperForLemma_7_4_disjoint_with_biUnion_of_finset {α J : Type*}
    (E : J → Set α) (hDisj : Pairwise (fun i j => Disjoint (E i) (E j)))
    (s : Finset J) (i : J) (hi : i ∉ s) :
    Disjoint (E i) (⋃ j ∈ (s : Set J), E j) := by
  rw [Set.disjoint_iUnion_right]
  intro j
  rw [Set.disjoint_iUnion_right]
  intro hj
  have hij : i ≠ j := by
    intro hEq
    apply hi
    simpa [hEq] using hj
  exact hDisj hij

/-- Helper for Lemma 7.4: finite additivity of an outer measure on intersections with a finite
pairwise disjoint family of Carathéodory measurable sets. -/
lemma helperForLemma_7_4_outerMeasure_inter_biUnion_finset_eq_sum {α J : Type*}
    (mStar : MeasureTheory.OuterMeasure α) (E : J → Set α)
    (hMeas : ∀ j, mStar.IsCaratheodory (E j))
    (hDisj : Pairwise (fun i j => Disjoint (E i) (E j))) (A : Set α)
    (s : Finset J) :
    mStar (A ∩ ⋃ j ∈ (s : Set J), E j) = Finset.sum s (fun j => mStar (A ∩ E j)) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp
  | @insert i s hi hs =>
      have hDisjUnion : Disjoint (E i) (⋃ j ∈ (s : Set J), E j) :=
        helperForLemma_7_4_disjoint_with_biUnion_of_finset E hDisj s i hi
      have hSplit :
          mStar (A ∩ (E i ∪ ⋃ j ∈ (s : Set J), E j)) =
            mStar (A ∩ E i) + mStar (A ∩ ⋃ j ∈ (s : Set J), E j) := by
        exact mStar.measure_inter_union hDisjUnion.le_bot (hMeas i)
      calc
        mStar (A ∩ ⋃ j ∈ ((insert i s : Finset J) : Set J), E j)
            = mStar (A ∩ (E i ∪ ⋃ j ∈ (s : Set J), E j)) := by
              simp
        _ = mStar (A ∩ E i) + mStar (A ∩ ⋃ j ∈ (s : Set J), E j) := hSplit
        _ = mStar (A ∩ E i) + Finset.sum s (fun j => mStar (A ∩ E j)) := by
              rw [hs]
        _ = Finset.sum (insert i s) (fun j => mStar (A ∩ E j)) := by
              simp [hi]

/-- Helper for Lemma 7.4: finite additivity for the measure induced from an outer measure on its
Carathéodory measurable sets. -/
lemma helperForLemma_7_4_restricted_measure_biUnion_univ_eq_sum {α J : Type*} [Fintype J]
    (mStar : MeasureTheory.OuterMeasure α) (E : J → Set α)
    (hMeas : ∀ j, mStar.IsCaratheodory (E j))
    (hDisj : Pairwise (fun i j => Disjoint (E i) (E j))) :
    outerMeasureRestrictedMeasure mStar (⋃ j, E j) =
      ∑ j, outerMeasureRestrictedMeasure mStar (E j) := by
  classical
  let μ : @MeasureTheory.Measure α mStar.caratheodory := outerMeasureRestrictedMeasure mStar
  have hPairwiseDisjoint : Set.PairwiseDisjoint (↑(Finset.univ : Finset J)) E := by
    intro i hi j hj hij
    exact hDisj hij
  have hMeasFinite : ∀ j ∈ (Finset.univ : Finset J), @MeasurableSet α mStar.caratheodory (E j) := by
    intro j hj
    exact hMeas j
  have hBiUnion :
      μ (⋃ j ∈ (Finset.univ : Finset J), E j) =
        ∑ p ∈ (Finset.univ : Finset J), μ (E p) := by
    exact MeasureTheory.measure_biUnion_finset (μ := μ) hPairwiseDisjoint hMeasFinite
  have hUnionEq : (⋃ j ∈ (Finset.univ : Finset J), E j) = ⋃ j, E j := by
    ext x
    simp
  calc
    outerMeasureRestrictedMeasure mStar (⋃ j, E j)
        = μ (⋃ j, E j) := by
          rfl
    _ = μ (⋃ j ∈ (Finset.univ : Finset J), E j) := by
          rw [hUnionEq]
    _ = ∑ p ∈ (Finset.univ : Finset J), μ (E p) := hBiUnion
    _ = ∑ j, μ (E j) := by
          simp
    _ = ∑ j, outerMeasureRestrictedMeasure mStar (E j) := by
          rfl

/-- Lemma 7.4 (Finite additivity): for a finite pairwise disjoint family `(E_j)_{j ∈ J}` of
`m*`-Carathéodory measurable sets, one has
`m*(A ∩ ⋃ j, E_j) = ∑ j, m*(A ∩ E_j)` for every `A` (equation (7.u101)); in particular, for
the restricted measure `m` induced by `m*` on `m*`-measurable sets,
`m(⋃ j, E_j) = ∑ j, m(E_j)` (equation (7.u102)). -/
theorem outerMeasure_finite_additivity {α J : Type*} [Fintype J]
    (mStar : MeasureTheory.OuterMeasure α) (E : J → Set α)
    (hMeas : ∀ j, mStar.IsCaratheodory (E j))
    (hDisj : Pairwise (fun i j => Disjoint (E i) (E j))) (A : Set α) :
    mStar (A ∩ ⋃ j, E j) = ∑ j, mStar (A ∩ E j) ∧
      outerMeasureRestrictedMeasure mStar (⋃ j, E j) =
        ∑ j, outerMeasureRestrictedMeasure mStar (E j) := by
  constructor
  · simpa using
      helperForLemma_7_4_outerMeasure_inter_biUnion_finset_eq_sum
        mStar E hMeas hDisj A Finset.univ
  · exact helperForLemma_7_4_restricted_measure_biUnion_univ_eq_sum mStar E hMeas hDisj

/-- Proposition 7.14: in a measure space `(X, 𝓜, m)`, if `A, B ∈ 𝓜` and `A ⊆ B`, then
`B \ A ∈ 𝓜` and `m(B \ A) + m(A) = m(B)` (equation (7.u109)). -/
theorem measurableSet_diff_and_measure_add_eq_of_subset {α : Type*} [MeasurableSpace α]
    (m : MeasureTheory.Measure α) (A B : Set α) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : A ⊆ B) :
    MeasurableSet (B \ A) ∧ m (B \ A) + m A = m B := by
  constructor
  · exact hB.diff hA
  · simpa [Set.inter_eq_right.mpr hAB] using
      (MeasureTheory.measure_diff_add_inter (μ := m) hA (s := B) (t := A))

/-- Helper for Lemma 7.5: a countable union of Carathéodory-measurable sets is Carathéodory
measurable. -/
lemma helperForLemma_7_5_iUnion_isCaratheodory {α J : Type*} [Countable J]
    (mStar : MeasureTheory.OuterMeasure α) (E : J → Set α)
    (hMeas : ∀ j, mStar.IsCaratheodory (E j)) :
    mStar.IsCaratheodory (⋃ j, E j) := by
  have hMeasurable : ∀ j, @MeasurableSet α mStar.caratheodory (E j) := by
    intro j
    exact hMeas j
  simpa using MeasurableSet.iUnion hMeasurable

/-- Helper for Lemma 7.5: convert pairwise disjointness into the `Disjoint on` form used by
`measure_iUnion`. -/
lemma helperForLemma_7_5_pairwise_disjoint_on {α J : Type*}
    (E : J → Set α) (hDisj : Pairwise (fun i j => Disjoint (E i) (E j))) :
    Pairwise (Function.onFun Disjoint E) := by
  simpa [Function.onFun] using hDisj

/-- Helper for Lemma 7.5: the restricted measure of a countable pairwise disjoint union is the
sum of the restricted measures. -/
lemma helperForLemma_7_5_restrictedMeasure_iUnion_eq_tsum {α J : Type*} [Countable J]
    (mStar : MeasureTheory.OuterMeasure α) (E : J → Set α)
    (hMeas : ∀ j, mStar.IsCaratheodory (E j))
    (hDisj : Pairwise (fun i j => Disjoint (E i) (E j))) :
    outerMeasureRestrictedMeasure mStar (⋃ j, E j) =
      ∑' j, outerMeasureRestrictedMeasure mStar (E j) := by
  let μ : @MeasureTheory.Measure α mStar.caratheodory := outerMeasureRestrictedMeasure mStar
  have hMeasurable : ∀ j, @MeasurableSet α mStar.caratheodory (E j) := by
    intro j
    exact hMeas j
  have hPairwise : Pairwise (Function.onFun Disjoint E) :=
    helperForLemma_7_5_pairwise_disjoint_on E hDisj
  calc
    outerMeasureRestrictedMeasure mStar (⋃ j, E j)
        = μ (⋃ j, E j) := by
          rfl
    _ = ∑' j, μ (E j) := by
          exact MeasureTheory.measure_iUnion hPairwise hMeasurable
    _ = ∑' j, outerMeasureRestrictedMeasure mStar (E j) := by
          rfl

/-- Lemma 7.5 (Countable additivity): for the measure obtained by restricting an outer measure
`m*` to its Carathéodory measurable sets, if `(E_j)_{j ∈ J}` is a countable pairwise disjoint
family of measurable sets, then `⋃ j, E_j` is measurable and
`m(⋃ j, E_j) = ∑' j, m(E_j)` (equation (7.u112), independent of enumeration). -/
theorem outerMeasure_countable_additivity {α J : Type*} [Countable J]
    (mStar : MeasureTheory.OuterMeasure α) (E : J → Set α)
    (hMeas : ∀ j, mStar.IsCaratheodory (E j))
    (hDisj : Pairwise (fun i j => Disjoint (E i) (E j))) :
    mStar.IsCaratheodory (⋃ j, E j) ∧
      outerMeasureRestrictedMeasure mStar (⋃ j, E j) =
        ∑' j, outerMeasureRestrictedMeasure mStar (E j) := by
  constructor
  · exact helperForLemma_7_5_iUnion_isCaratheodory mStar E hMeas
  · exact helperForLemma_7_5_restrictedMeasure_iUnion_eq_tsum mStar E hMeas hDisj

/-- Lemma 7.6 (countable disjoint union measurable): if `m*` is an outer measure on `X`,
`m` is its restriction to `m*`-measurable sets, and `(E_j)_{j ∈ J}` is a countable pairwise
disjoint family of `m*`-measurable sets, then `E := ⋃ j, E_j` is `m*`-measurable and
`m(E) = ∑' j, m(E_j)` (equation (7.u124)). -/
lemma outerMeasure_countable_disjoint_union_measurable {α J : Type*} [Countable J]
    (mStar : MeasureTheory.OuterMeasure α) (E : J → Set α)
    (hMeas : ∀ j, mStar.IsCaratheodory (E j))
    (hDisj : Pairwise (fun i j => Disjoint (E i) (E j))) :
    mStar.IsCaratheodory (⋃ j, E j) ∧
      outerMeasureRestrictedMeasure mStar (⋃ j, E j) =
        ∑' j, outerMeasureRestrictedMeasure mStar (E j) := by
  simpa using outerMeasure_countable_additivity mStar E hMeas hDisj

/-- Lemma 7.7 ($\sigma$-algebra property): in a measurable space `(Ω, 𝓕)`, for a countable
family `(Ω_j)_{j ∈ J}` with each `Ω_j ∈ 𝓕`, both `⋃ j, Ω_j` and `⋂ j, Ω_j` belong to `𝓕`. -/
theorem measurableSet_iUnion_iInter_of_countable {α J : Type*} [MeasurableSpace α] [Countable J]
    (Ω : J → Set α) (hΩ : ∀ j : J, MeasurableSet (Ω j)) :
    MeasurableSet (⋃ j, Ω j) ∧ MeasurableSet (⋂ j, Ω j) := by
  constructor
  · simpa using MeasurableSet.iUnion hΩ
  · simpa using MeasurableSet.iInter hΩ

/-- Helper for Lemma 7.8: coordinate open boxes in `Fin n → ℝ` are open. -/
lemma helperForLemma_7_8_coordinateOpenBox_isOpen_fun (n : ℕ) (a b : Fin n → ℝ) :
    IsOpen {x : Fin n → ℝ | ∀ i : Fin n, a i < x i ∧ x i < b i} := by
  have hOpenIoo : ∀ i ∈ (Set.univ : Set (Fin n)), IsOpen (Set.Ioo (a i) (b i)) := by
    intro i hi
    exact isOpen_Ioo
  have hPi :
      IsOpen ((Set.univ : Set (Fin n)).pi (fun i => Set.Ioo (a i) (b i))) := by
    exact isOpen_set_pi (Set.toFinite (Set.univ : Set (Fin n))) hOpenIoo
  have hEq :
      {x : Fin n → ℝ | ∀ i : Fin n, a i < x i ∧ x i < b i} =
        ((Set.univ : Set (Fin n)).pi (fun i => Set.Ioo (a i) (b i))) := by
    ext x
    simp [Set.mem_pi]
  rw [hEq]
  exact hPi

/-- Helper for Lemma 7.8: every point of an open subset of `Fin n → ℝ` lies in a coordinate open
box contained in that open set. -/
lemma helperForLemma_7_8_exists_coordinateOpenBox_subset_of_mem_fun (n : ℕ)
    (E : Set (Fin n → ℝ)) (hE : IsOpen E) {x : Fin n → ℝ} (hx : x ∈ E) :
    ∃ a b : Fin n → ℝ,
      x ∈ {y : Fin n → ℝ | ∀ i : Fin n, a i < y i ∧ y i < b i} ∧
      {y : Fin n → ℝ | ∀ i : Fin n, a i < y i ∧ y i < b i} ⊆ E := by
  rcases (Metric.isOpen_iff.mp hE) x hx with ⟨ε, hεpos, hBall⟩
  refine ⟨fun i => x i - ε / 2, fun i => x i + ε / 2, ?_, ?_⟩
  · intro i
    constructor <;> linarith
  · intro y hy
    have hεhalfPos : 0 < ε / 2 := by
      linarith
    have hyCoord : ∀ i : Fin n, dist (y i) (x i) < ε / 2 := by
      intro i
      rcases hy i with ⟨hleft, hright⟩
      have hAbs : |y i - x i| < ε / 2 := by
        rw [abs_lt]
        constructor <;> linarith
      simpa [Real.dist_eq] using hAbs
    have hyDistHalf : dist y x < ε / 2 := by
      exact (dist_pi_lt_iff hεhalfPos).2 hyCoord
    have hHalfLt : ε / 2 < ε := by
      linarith
    have hyDist : dist y x < ε := lt_trans hyDistHalf hHalfLt
    have hyBall : y ∈ Metric.ball x ε := Metric.mem_ball.mpr hyDist
    exact hBall hyBall

/-- Helper for Lemma 7.8: an open set in `Fin n → ℝ` is the union of all coordinate open boxes
contained in it. -/
lemma helperForLemma_7_8_eq_iUnion_all_boxes_subset_fun (n : ℕ)
    (E : Set (Fin n → ℝ)) (hE : IsOpen E) :
    let I0 := {ab : (Fin n → ℝ) × (Fin n → ℝ) |
      {x : Fin n → ℝ | ∀ i : Fin n, ab.1 i < x i ∧ x i < ab.2 i} ⊆ E}
    E = ⋃ k : I0, {x : Fin n → ℝ | ∀ i : Fin n, k.1.1 i < x i ∧ x i < k.1.2 i} := by
  ext x
  constructor
  · intro hx
    rcases helperForLemma_7_8_exists_coordinateOpenBox_subset_of_mem_fun n E hE hx with
      ⟨a, b, hxBox, hBoxSubset⟩
    refine Set.mem_iUnion.mpr ?_
    refine ⟨⟨(a, b), hBoxSubset⟩, ?_⟩
    exact hxBox
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨k, hxk⟩
    exact k.2 hxk

/-- Helper for Lemma 7.8: from the full coordinate-box cover of an open set in `Fin n → ℝ`,
extract a countable subcover. -/
lemma helperForLemma_7_8_countable_subcover_of_all_boxes_fun (n : ℕ)
    (E : Set (Fin n → ℝ)) (hE : IsOpen E) :
    ∃ T : Set {ab : (Fin n → ℝ) × (Fin n → ℝ) |
          {x : Fin n → ℝ | ∀ i : Fin n, ab.1 i < x i ∧ x i < ab.2 i} ⊆ E},
      T.Countable ∧
      E = ⋃ k ∈ T, {x : Fin n → ℝ | ∀ i : Fin n, k.1.1 i < x i ∧ x i < k.1.2 i} := by
  let I0 := {ab : (Fin n → ℝ) × (Fin n → ℝ) |
      {x : Fin n → ℝ | ∀ i : Fin n, ab.1 i < x i ∧ x i < ab.2 i} ⊆ E}
  let s : I0 → Set (Fin n → ℝ) :=
    fun k => {x : Fin n → ℝ | ∀ i : Fin n, k.1.1 i < x i ∧ x i < k.1.2 i}
  have hsOpen : ∀ k : I0, IsOpen (s k) := by
    intro k
    exact helperForLemma_7_8_coordinateOpenBox_isOpen_fun n k.1.1 k.1.2
  rcases TopologicalSpace.isOpen_iUnion_countable s hsOpen with ⟨T, hTCount, hTUnion⟩
  have hAll : E = ⋃ k : I0, s k := by
    simpa [I0, s] using helperForLemma_7_8_eq_iUnion_all_boxes_subset_fun n E hE
  refine ⟨T, hTCount, ?_⟩
  calc
    E = ⋃ k : I0, s k := hAll
    _ = ⋃ k ∈ T, s k := hTUnion.symm
    _ = ⋃ k ∈ T, {x : Fin n → ℝ | ∀ i : Fin n, k.1.1 i < x i ∧ x i < k.1.2 i} := by
          rfl

/-- Helper for Lemma 7.8: every open subset of `Fin n → ℝ` is a union of countably many
coordinate open boxes. -/
lemma helperForLemma_7_8_isOpen_eq_iUnion_countable_coordinateOpenBoxes_fun (n : ℕ)
    (E : Set (Fin n → ℝ)) (hE : IsOpen E) :
    ∃ (I : Type) (_hI : Countable I) (a b : I → Fin n → ℝ),
      E = ⋃ k : I, {x : Fin n → ℝ | ∀ i : Fin n, a k i < x i ∧ x i < b k i} := by
  rcases helperForLemma_7_8_countable_subcover_of_all_boxes_fun n E hE with ⟨T, hTCount, hCover⟩
  refine ⟨T, hTCount.to_subtype, fun k => k.1.1.1, fun k => k.1.1.2, ?_⟩
  calc
    E = ⋃ k ∈ T, {x : Fin n → ℝ | ∀ i : Fin n, k.1.1 i < x i ∧ x i < k.1.2 i} := hCover
    _ = ⋃ k : T, {x : Fin n → ℝ | ∀ i : Fin n, k.1.1.1 i < x i ∧ x i < k.1.1.2 i} := by
          simp [Set.iUnion_subtype]

/-- Lemma 7.8: if `E ⊆ ℝ^n` is open in the Euclidean topology, then `E` is the union of a
finite or countable family of coordinate open boxes
`∏_{i=1}^n (a_{k,i}, b_{k,i})` (encoded as a countable index type). -/
theorem isOpen_eq_iUnion_countable_coordinateOpenBoxes (n : ℕ)
    (E : Set (EuclideanSpace ℝ (Fin n))) (hE : IsOpen E) :
    ∃ (I : Type) (_hI : Countable I) (a b : I → Fin n → ℝ),
      E = ⋃ k : I, {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin n, a k i < x i ∧ x i < b k i} := by
  let e : EuclideanSpace ℝ (Fin n) ≃ₜ (Fin n → ℝ) :=
    PiLp.homeomorph (p := (2 : ENNReal)) (β := fun _ : Fin n => ℝ)
  let Efun : Set (Fin n → ℝ) := e '' E
  have hEfun : IsOpen Efun := e.isOpenMap E hE
  rcases helperForLemma_7_8_isOpen_eq_iUnion_countable_coordinateOpenBoxes_fun n Efun hEfun with
    ⟨I, hICount, a, b, hCoverFun⟩
  refine ⟨I, hICount, a, b, ?_⟩
  ext x
  constructor
  · intro hx
    have hxFun : e x ∈ Efun := by
      exact ⟨x, hx, rfl⟩
    rw [hCoverFun] at hxFun
    rcases Set.mem_iUnion.mp hxFun with ⟨k, hk⟩
    exact Set.mem_iUnion.mpr ⟨k, hk⟩
  · intro hx
    have hxFun : e x ∈ Efun := by
      rw [hCoverFun]
      rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
      exact Set.mem_iUnion.mpr ⟨k, hk⟩
    rcases hxFun with ⟨y, hyE, hyx⟩
    have hxy : x = y := by
      exact e.injective hyx.symm
    exact hxy ▸ hyE

/-- Lemma 7.9 (Borel property): every open subset of `ℝ^n` and every closed subset of `ℝ^n`
is Lebesgue measurable. -/
lemma isLebesgueMeasurable_of_isOpen_or_isClosed (n : ℕ) :
    (∀ E : Set (EuclideanSpace ℝ (Fin n)), IsOpen E → isLebesgueMeasurable n E) ∧
      (∀ E : Set (EuclideanSpace ℝ (Fin n)), IsClosed E → isLebesgueMeasurable n E) := by
  constructor
  · intro E hE
    exact helperForLemma_7_2_isLebesgueMeasurable_of_isOpen n hE
  · intro E hE
    have hOpenCompl : IsOpen Eᶜ := hE.isOpen_compl
    have hMeasCompl : isLebesgueMeasurable n Eᶜ :=
      helperForLemma_7_2_isLebesgueMeasurable_of_isOpen n hOpenCompl
    have hCompl :
        ∀ A : Set (EuclideanSpace ℝ (Fin n)),
          isLebesgueMeasurable n A → isLebesgueMeasurable n Aᶜ :=
      (measurableSet_properties n).1
    have hMeasDoubleCompl : isLebesgueMeasurable n (Eᶜ)ᶜ := hCompl (Eᶜ) hMeasCompl
    simpa using hMeasDoubleCompl

/-- Proposition 7.15: if `A ⊆ B ⊆ ℝ^n`, `B` is Lebesgue measurable, and `m(B) = 0`,
then `A` is Lebesgue measurable and `m(A) = 0`. -/
theorem isLebesgueMeasurable_and_volume_eq_zero_of_subset_of_volume_eq_zero (n : ℕ)
    (A B : Set (EuclideanSpace ℝ (Fin n))) (hAB : A ⊆ B)
    (hBzero : MeasureTheory.volume B = 0) :
    isLebesgueMeasurable n A ∧ MeasureTheory.volume A = 0 := by
  have hAzero : MeasureTheory.volume A = 0 := MeasureTheory.measure_mono_null hAB hBzero
  have hAouter0 : (MeasureTheory.volume.toOuterMeasure) A = 0 := by
    simpa using hAzero
  have hAmeas : isLebesgueMeasurable n A :=
    helperForLemma_7_3_outerMeasure_zero_implies_measurable n A hAouter0
  exact ⟨hAmeas, hAzero⟩

/-- Helper for Proposition 7.16: the rational coordinate cube in `Fin 2 → ℝ` is countable and
dense. -/
lemma helperForProposition_7_16_rationalFunctionSet_countable_dense :
    let Qfun : Set (Fin 2 → ℝ) :=
      Set.univ.pi (fun _ : Fin 2 => Set.range (fun q : ℚ => (q : ℝ)))
    Qfun.Countable ∧ Dense Qfun := by
  let Qfun : Set (Fin 2 → ℝ) :=
    Set.univ.pi (fun _ : Fin 2 => Set.range (fun q : ℚ => (q : ℝ)))
  have hQfunCountable : Qfun.Countable := by
    classical
    dsimp [Qfun]
    exact Set.countable_univ_pi (fun _ => Set.countable_range (fun q : ℚ => (q : ℝ)))
  have hDenseRangeRat : Dense (Set.range (fun q : ℚ => (q : ℝ))) := by
    simpa using Rat.denseRange_cast
  have hQfunDense : Dense Qfun := by
    dsimp [Qfun]
    exact dense_pi Set.univ (fun _ _ => hDenseRangeRat)
  exact ⟨hQfunCountable, hQfunDense⟩

/-- Helper for Proposition 7.16: the rational grid in `ℝ^2` is countable, dense, null, and
Lebesgue measurable. -/
lemma helperForProposition_7_16_rationalGrid_countable_dense_zero_measurable :
    let Q : Set (EuclideanSpace ℝ (Fin 2)) :=
      {x | ∀ i : Fin 2, x i ∈ Set.range (fun q : ℚ => (q : ℝ))}
    Q.Countable ∧ Dense Q ∧ MeasureTheory.volume Q = 0 ∧ isLebesgueMeasurable 2 Q := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ₜ (Fin 2 → ℝ) :=
    PiLp.homeomorph (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ)
  let Qfun : Set (Fin 2 → ℝ) :=
    Set.univ.pi (fun _ : Fin 2 => Set.range (fun q : ℚ => (q : ℝ)))
  let Q : Set (EuclideanSpace ℝ (Fin 2)) :=
    {x | ∀ i : Fin 2, x i ∈ Set.range (fun q : ℚ => (q : ℝ))}
  have hQfun : Qfun.Countable ∧ Dense Qfun :=
    helperForProposition_7_16_rationalFunctionSet_countable_dense
  have hQpreimage : Q = e ⁻¹' Qfun := by
    ext x
    constructor
    · intro hx i hi
      exact hx i
    · intro hx i
      exact hx i (by simp)
  have hQCountable : Q.Countable := by
    rw [hQpreimage]
    exact hQfun.1.preimage e.injective
  have hQDense : Dense Q := by
    rw [hQpreimage]
    exact Dense.preimage hQfun.2 e.isOpenMap
  have hQVolumeZero : MeasureTheory.volume Q = 0 :=
    Set.Countable.measure_zero hQCountable MeasureTheory.volume
  have hQMeas : isLebesgueMeasurable 2 Q := by
    apply helperForLemma_7_3_outerMeasure_zero_implies_measurable 2 Q
    simpa using hQVolumeZero
  exact ⟨hQCountable, hQDense, hQVolumeZero, hQMeas⟩

/-- Helper for Proposition 7.16: the unit square in `ℝ^2` is Lebesgue measurable and has
volume `1`. -/
lemma helperForProposition_7_16_unitSquare_measurable_volume_one :
    let U : Set (EuclideanSpace ℝ (Fin 2)) :=
      {x | ∀ i : Fin 2, x i ∈ Set.Icc (0 : ℝ) 1}
    isLebesgueMeasurable 2 U ∧ MeasureTheory.volume U = 1 := by
  let U : Set (EuclideanSpace ℝ (Fin 2)) :=
    {x | ∀ i : Fin 2, x i ∈ Set.Icc (0 : ℝ) 1}
  let eMeas : EuclideanSpace ℝ (Fin 2) ≃ᵐ (Fin 2 → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm
  have hUClosed : IsClosed U := by
    have hUAsInter :
        U = ⋂ i : Fin 2, {x : EuclideanSpace ℝ (Fin 2) | x i ∈ Set.Icc (0 : ℝ) 1} := by
      ext x
      simp [U]
    rw [hUAsInter]
    refine isClosed_iInter ?_
    intro i
    exact isClosed_Icc.preimage (helperForLemma_7_3_coordinateProjectionContinuous 2 i)
  have hUMeas : isLebesgueMeasurable 2 U :=
    (isLebesgueMeasurable_of_isOpen_or_isClosed 2).2 U hUClosed
  have hUPreimage :
      U = eMeas ⁻¹' Set.Icc (fun _ : Fin 2 => (0 : ℝ)) (fun _ : Fin 2 => (1 : ℝ)) := by
    ext x
    constructor
    · intro hx
      constructor
      · intro i
        exact (hx i).1
      · intro i
        exact (hx i).2
    · intro hx i
      exact ⟨hx.1 i, hx.2 i⟩
  have hVolumePreimage :
      MeasureTheory.volume U =
        MeasureTheory.volume (Set.Icc (fun _ : Fin 2 => (0 : ℝ)) (fun _ : Fin 2 => (1 : ℝ))) := by
    rw [hUPreimage]
    exact (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (ι := Fin 2)).measure_preimage
      isClosed_Icc.nullMeasurableSet
  have hVolumeIcc :
      MeasureTheory.volume (Set.Icc (fun _ : Fin 2 => (0 : ℝ)) (fun _ : Fin 2 => (1 : ℝ))) = 1 := by
    simpa using (Real.volume_Icc_pi (a := fun _ : Fin 2 => (0 : ℝ)) (b := fun _ : Fin 2 => (1 : ℝ)))
  have hUVolumeOne : MeasureTheory.volume U = 1 := by
    calc
      MeasureTheory.volume U =
          MeasureTheory.volume (Set.Icc (fun _ : Fin 2 => (0 : ℝ)) (fun _ : Fin 2 => (1 : ℝ))) :=
        hVolumePreimage
      _ = 1 := hVolumeIcc
  exact ⟨hUMeas, hUVolumeOne⟩

/-- Helper for Proposition 7.16: if a dense set is contained in `Aᶜ`, then `A` has empty
interior. -/
lemma helperForProposition_7_16_emptyInterior_from_dense_complement
    (A Q : Set (EuclideanSpace ℝ (Fin 2))) (hQDense : Dense Q) (hQSubset : Q ⊆ Aᶜ) :
    interior A = ∅ := by
  have hDenseCompl : Dense Aᶜ := Dense.mono hQSubset hQDense
  simpa using hDenseCompl.interior_compl

/-- Proposition 7.16: for
`A := [0,1]^2 \ ℚ^2 = {x ∈ ℝ^2 : (∀ i, 0 ≤ x_i ≤ 1) ∧ (∃ i, x_i ∉ ℚ)}`,
the set `A` is Lebesgue measurable, has Lebesgue measure `1`, and has empty interior. -/
theorem unitSquare_diff_rationalPoints_isLebesgueMeasurable_volume_one_interior_empty :
    let A : Set (EuclideanSpace ℝ (Fin 2)) :=
      {x | (∀ i : Fin 2, x i ∈ Set.Icc (0 : ℝ) 1)} \
        {x | ∀ i : Fin 2, x i ∈ Set.range (fun q : ℚ => (q : ℝ))}
    isLebesgueMeasurable 2 A ∧ MeasureTheory.volume A = 1 ∧ interior A = ∅ := by
  let U : Set (EuclideanSpace ℝ (Fin 2)) :=
    {x | ∀ i : Fin 2, x i ∈ Set.Icc (0 : ℝ) 1}
  let Q : Set (EuclideanSpace ℝ (Fin 2)) :=
    {x | ∀ i : Fin 2, x i ∈ Set.range (fun q : ℚ => (q : ℝ))}
  let A : Set (EuclideanSpace ℝ (Fin 2)) := U \ Q
  have hQ :
      Q.Countable ∧ Dense Q ∧ MeasureTheory.volume Q = 0 ∧ isLebesgueMeasurable 2 Q := by
    simpa [Q] using helperForProposition_7_16_rationalGrid_countable_dense_zero_measurable
  have hU : isLebesgueMeasurable 2 U ∧ MeasureTheory.volume U = 1 := by
    simpa [U] using helperForProposition_7_16_unitSquare_measurable_volume_one
  have hQComplMeas : isLebesgueMeasurable 2 Qᶜ := (measurableSet_properties 2).1 Q hQ.2.2.2
  have hAAsInterMeas : isLebesgueMeasurable 2 (U ∩ Qᶜ) :=
    ((measurableSet_properties 2).2.2.1 U Qᶜ hU.1 hQComplMeas).1
  have hAAsInter : A = U ∩ Qᶜ := by
    ext x
    simp [A]
  have hAMeas : isLebesgueMeasurable 2 A := by
    rw [hAAsInter]
    exact hAAsInterMeas
  have hInterVolumeZero : MeasureTheory.volume (U ∩ Q) = 0 :=
    MeasureTheory.measure_mono_null (by intro x hx; exact hx.2) hQ.2.2.1
  have hAVolume : MeasureTheory.volume A = 1 := by
    have hDiffVolume :
        MeasureTheory.volume (U \ Q) = MeasureTheory.volume U :=
      MeasureTheory.measure_diff_null' (μ := MeasureTheory.volume) (s₁ := U) (s₂ := Q)
        hInterVolumeZero
    calc
      MeasureTheory.volume A = MeasureTheory.volume (U \ Q) := by rfl
      _ = MeasureTheory.volume U := hDiffVolume
      _ = 1 := hU.2
  have hQSubsetACompl : Q ⊆ Aᶜ := by
    intro x hxQ hxA
    exact hxA.2 hxQ
  have hAInterior : interior A = ∅ :=
    helperForProposition_7_16_emptyInterior_from_dense_complement A Q hQ.2.1 hQSubsetACompl
  exact ⟨hAMeas, hAVolume, hAInterior⟩

end Section04
end Chap07
