import Mathlib
import BauschkeLean.Chap09.Remark_9_37
import BauschkeLean.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators ERealFunction InnerProductSpace

universe u v

namespace ERealFunction

section Subdifferentials

variable {I : Type v} [Fintype I]
variable {H : I → Type u}
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]

attribute [local instance] Classical.decEq

/-- Helper for Proposition 16 9: freezing every coordinate except `i` and reinserting the base
value at `i` recovers the original point. -/
private theorem coordinateSlice_eq_base (x : lp H 2) (i : I) :
    coordinateSlice x i (x i) = x := by
  classical
  -- Compare the two `lp` points coordinatewise.
  ext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [coordinateSlice_apply_of_ne, hj]

/-- Helper for Proposition 16 9: the displacement from `x` to a coordinate slice is the
single-coordinate vector supported at the active index. -/
private theorem coordinateSlice_sub_eq_single (x : lp H 2) (i : I) (y : H i) :
    coordinateSlice x i y - x = lp.single 2 i (y - x i) := by
  classical
  -- Replace `x` by the slice obtained from reinserting its own `i`th coordinate.
  calc
    coordinateSlice x i y - x = coordinateSlice x i y - coordinateSlice x i (x i) := by
      rw [coordinateSlice_eq_base]
    _ = lp.single 2 i y - lp.single 2 i (x i) := by
      -- Compare the two normalized differences coordinatewise.
      ext j
      by_cases hj : j = i
      · subst hj
        change coordinateSlice x j y j - coordinateSlice x j (x j) j =
          (lp.single 2 j y) j - (lp.single 2 j (x j)) j
        simp [coordinateSlice]
      · change coordinateSlice x i y j - coordinateSlice x i (x i) j =
          (lp.single 2 i y) j - (lp.single 2 i (x i)) j
        simp [coordinateSlice, hj]
    _ = lp.single 2 i (y - x i) := by
      rw [← lp.single_sub]

/-- Helper for Proposition 16 9: the ambient inner product against the slice displacement reduces
to the active-coordinate inner product. -/
private theorem inner_coordinateSlice_sub_eq (x u : lp H 2) (i : I) (y : H i) :
    ⟪coordinateSlice x i y - x, u⟫_ℝ = ⟪y - x i, u i⟫_ℝ := by
  classical
  -- Rewrite the displacement as a single-coordinate vector and use the canonical `lp` formula.
  rw [coordinateSlice_sub_eq_single, lp.inner_single_left]

/-- Helper for Proposition 16 9: a global subgradient yields coordinatewise subgradients of the
slice functions obtained by freezing every other coordinate. -/
private theorem subdifferential_subset_coordinatewise_slice_subdifferential
    {g : lp H 2 → Set.Ioi (⊥ : EReal)} {x : lp H 2} :
    (∂ g) x ⊆ {u | ∀ i, u i ∈ (∂ (g ∘ coordinateSlice x i)) (x i)} := by
  classical
  intro u hu i
  have hu' := (mem_subdifferential_iff (f := g) (x := x) (u := u)).1 hu
  -- Test the ambient subgradient inequality on the `i`th slice through `x`.
  refine (mem_subdifferential_iff (f := g ∘ coordinateSlice x i) (x := x i) (u := u i)).2 ?_
  intro yi
  have hinner :
      (⟪coordinateSlice x i yi - x, u⟫_ℝ : EReal) = (⟪yi - x i, u i⟫_ℝ : EReal) := by
    -- Push the scalar inner-product identity through the real-to-`EReal` coercion.
    exact congrArg (fun t : ℝ ↦ (t : EReal))
      (inner_coordinateSlice_sub_eq (x := x) (u := u) (i := i) (y := yi))
  have hslice := hu' (coordinateSlice x i yi)
  -- Normalize the displacement and the frozen basepoint in the slice inequality.
  rw [hinner] at hslice
  simpa only [Function.comp_apply, coordinateSlice_eq_base] using hslice

/-- Helper for Proposition 16 9: over a finite index set, summing values in `]-∞,+∞]` never
produces `-∞`. -/
private theorem finset_sum_mem_Ioi_bot (s : Finset I) (a : I → Set.Ioi (⊥ : EReal)) :
    (∑ i ∈ s, (a i : EReal)) ∈ Set.Ioi (⊥ : EReal) := by
  classical
  -- Induct on the finite set and use that `EReal` addition preserves non-`⊥`.
  have hne : (∑ i ∈ s, (a i : EReal)) ≠ ⊥ := by
    induction s using Finset.induction_on with
    | empty =>
        simp
    | @insert i s hi ih =>
        simpa [Finset.sum_insert, hi] using
          (EReal.add_ne_bot_iff.2 ⟨ne_of_gt (a i).2, ih⟩)
  exact lt_of_le_of_ne bot_le hne.symm

/-- Helper for Proposition 16 9: a finite sum of values in `]-∞,+∞]` is finite exactly when each
summand is finite. -/
private theorem finset_sum_lt_top_iff (s : Finset I) (a : I → Set.Ioi (⊥ : EReal)) :
    (∑ i ∈ s, (a i : EReal)) < ⊤ ↔ ∀ i ∈ s, (a i : EReal) < ⊤ := by
  classical
  -- Split off one coordinate and use the two-term `EReal` finiteness criterion.
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      have hsum_ne_bot : (∑ j ∈ s, (a j : EReal)) ≠ ⊥ :=
        ne_of_gt (finset_sum_mem_Ioi_bot (s := s) a)
      have hai_ne_bot : (a i : EReal) ≠ ⊥ := ne_of_gt (a i).2
      have ih' : (∑ j ∈ s, (a j : EReal)) ≠ ⊤ ↔ ∀ j ∈ s, (a j : EReal) < ⊤ := by
        rw [← lt_top_iff_ne_top, ih]
      rw [Finset.sum_insert hi, lt_top_iff_ne_top,
        EReal.add_ne_top_iff_ne_top₂ hai_ne_bot hsum_ne_bot, ih']
      constructor
      · intro h j hj
        rcases Finset.mem_insert.mp hj with rfl | hj'
        · exact lt_top_iff_ne_top.mpr h.1
        · exact h.2 j hj'
      · intro h
        constructor
        · exact lt_top_iff_ne_top.mp (h i (Finset.mem_insert_self i s))
        · intro j hj
          exact h j (Finset.mem_insert_of_mem hj)

/-- Helper for Proposition 16 9: a subgradient at `x` forces `x` into the effective domain. -/
private theorem mem_effectiveDomain_of_mem_subdifferential
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (g : K → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain g).Nonempty) {x u : K}
    (hu : u ∈ (∂ g) x) :
    x ∈ effectiveDomain g := by
  rcases hdom with ⟨y, hy⟩
  -- Test the subgradient inequality at one finite-domain point.
  by_contra hx
  have hx_top : (g x : EReal) = ⊤ := by
    apply le_antisymm le_top
    exact not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx)
  have hy_top : (g y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hxy : (⊤ : EReal) ≤ (g y : EReal) := by
    have hxy' : (⟪y - x, u⟫_ℝ : EReal) + (g x : EReal) ≤ (g y : EReal) :=
      (mem_subdifferential_iff (f := g) (x := x) (u := u)).1 hu y
    rw [hx_top] at hxy'
    simpa using hxy'
  exact hy_top (le_antisymm le_top hxy)

/-- Helper for Proposition 16 9: finiteness of the direct-sum value is equivalent to coordinatewise
finiteness. -/
private theorem mem_effectiveDomain_directSumFunction_iff
    (f : ∀ i, H i → Set.Ioi (⊥ : EReal)) (x : lp H 2) :
    x ∈ effectiveDomain (directSumFunction f) ↔ ∀ i, x i ∈ effectiveDomain (f i) := by
  -- Route correction: rewrite the direct sum as the finite coordinate sum and use the finite-sum
  -- criterion proved above.
  rw [mem_effectiveDomain_iff, directSumFunction_apply,
    finset_sum_lt_top_iff (s := (Finset.univ : Finset I)) (a := fun i ↦ f i (x i))]
  constructor
  · intro hx i
    exact hx i (by simp)
  · intro hx i hi
    exact hx i

/-- Helper for Proposition 16 9: choosing one effective-domain point in every coordinate yields a
global effective-domain point for the direct-sum function. -/
private theorem directSumFunction_effectiveDomain_nonempty
    (f : ∀ i, H i → Set.Ioi (⊥ : EReal))
    (hdom : ∀ i, (effectiveDomain (f i)).Nonempty) :
    (effectiveDomain (directSumFunction f)).Nonempty := by
  classical
  let x₀ : ∀ i, H i := fun i ↦ Classical.choose (hdom i)
  have hx₀ : ∀ i, x₀ i ∈ effectiveDomain (f i) := by
    intro i
    exact Classical.choose_spec (hdom i)
  refine ⟨⟨x₀, Memℓp.all x₀⟩, ?_⟩
  exact (mem_effectiveDomain_directSumFunction_iff (f := f) (x := ⟨x₀, Memℓp.all x₀⟩)).2 hx₀

/-- Helper for Proposition 16 9: finite coordinate values sum to the corresponding real-cast
sum. -/
private theorem finset_sum_eq_coe_toReal
    (f : ∀ i, H i → Set.Ioi (⊥ : EReal)) (s : Finset I) (x : ∀ i, H i)
    (hx : ∀ i ∈ s, x i ∈ effectiveDomain (f i)) :
    (∑ i ∈ s, (f i (x i) : EReal)) =
      ((∑ i ∈ s, (f i (x i) : EReal).toReal : ℝ) : EReal) := by
  classical
  -- Induct over the finite set and convert the distinguished finite value by `EReal.coe_toReal`.
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      have hi_top : (f i (x i) : EReal) ≠ ⊤ := by
        exact ne_of_lt ((mem_effectiveDomain_iff).mp (hx i (Finset.mem_insert_self i s)))
      have hi_bot : (f i (x i) : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (f i (x i) : EReal) from (f i (x i)).2)
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ih]
      · conv_lhs => rw [← EReal.coe_toReal hi_top hi_bot]
        rw [← EReal.coe_add]
      · intro j hj
        exact hx j (Finset.mem_insert_of_mem hj)

/-- Helper for Proposition 16 9: a finite sum of real-cast `EReal` values is the cast of the real
sum. -/
private theorem finset_sum_coe_real (s : Finset I) (r : I → ℝ) :
    (∑ i ∈ s, (r i : EReal)) = ((∑ i ∈ s, r i : ℝ) : EReal) := by
  classical
  -- Induct on the finite set and combine the new term with the induction hypothesis by
  -- `EReal.coe_add`.
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ih, EReal.coe_add]

/-- Helper for Proposition 16 9: along a coordinate slice, the direct-sum function is the active
coordinate value plus the frozen finite tail. -/
private theorem directSumFunction_coordinateSlice_apply_eq
    (f : ∀ i, H i → Set.Ioi (⊥ : EReal)) (x₀ : lp H 2)
    (hx₀ : ∀ j, x₀ j ∈ effectiveDomain (f j)) (i : I) (z : H i) :
    (directSumFunction f (coordinateSlice x₀ i z) : EReal) =
      (f i z : EReal) +
        ((∑ j ∈ Finset.univ.erase i, (f j (x₀ j) : EReal).toReal : ℝ) : EReal) := by
  classical
  have htail :
      (∑ j ∈ Finset.univ.erase i, (f j (Function.update x₀ i z j) : EReal)) =
        ((∑ j ∈ Finset.univ.erase i, (f j (x₀ j) : EReal).toReal : ℝ) : EReal) := by
    have hx_tail : ∀ j ∈ Finset.univ.erase i, Function.update x₀ i z j ∈ effectiveDomain (f j) := by
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simpa [Function.update, hji] using hx₀ j
    have htail_raw :=
      finset_sum_eq_coe_toReal (f := f) (s := Finset.univ.erase i)
        (x := Function.update x₀ i z) hx_tail
    have htail_toReal :
        (∑ j ∈ Finset.univ.erase i, (f j (Function.update x₀ i z j) : EReal).toReal : ℝ) =
          ∑ j ∈ Finset.univ.erase i, (f j (x₀ j) : EReal).toReal := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [Function.update, hji]
    -- On the erased tail, the slice agrees with the frozen basepoint.
    calc
      (∑ j ∈ Finset.univ.erase i, (f j (Function.update x₀ i z j) : EReal))
          =
            ((
              ∑ j ∈ Finset.univ.erase i,
                (f j (Function.update x₀ i z j) : EReal).toReal : ℝ
            ) : EReal) := htail_raw
      _ = ((∑ j ∈ Finset.univ.erase i, (f j (x₀ j) : EReal).toReal : ℝ) : EReal) := by
            rw [htail_toReal]
  -- Split the finite direct sum into the active coordinate and the frozen tail.
  calc
    (directSumFunction f (coordinateSlice x₀ i z) : EReal)
        = ∑ j, (f j ((coordinateSlice x₀ i z) j) : EReal) := by
            rw [directSumFunction_apply]
    _ = (f i ((coordinateSlice x₀ i z) i) : EReal) +
          ∑ j ∈ Finset.univ.erase i, (f j ((coordinateSlice x₀ i z) j) : EReal) := by
            symm
            exact Finset.add_sum_erase (s := Finset.univ)
              (f := fun j ↦ (f j ((coordinateSlice x₀ i z) j) : EReal)) (by simp)
    _ = (f i z : EReal) +
          ∑ j ∈ Finset.univ.erase i, (f j (Function.update x₀ i z j) : EReal) := by
            simp [coordinateSlice]
    _ = (f i z : EReal) +
          ((∑ j ∈ Finset.univ.erase i, (f j (x₀ j) : EReal).toReal : ℝ) : EReal) := by
            rw [htail]

/-- Helper for Proposition 16 9: adding the same finite real constant to both sides preserves an
`EReal` inequality. -/
private theorem add_coe_real_le_add_coe_real_iff (a b : EReal) (c : ℝ) :
    a + (c : EReal) ≤ b + (c : EReal) ↔ a ≤ b := by
  -- This is the cancellation law for adding a finite real scalar in `EReal`.
  exact (EReal.addLECancellable_coe c).add_le_add_iff_right

/-- Helper for Proposition 16 9: the subgradient inequality for a coordinate slice is equivalent to
the subgradient inequality for the active summand alone. -/
private theorem mem_subdifferential_directSum_slice_iff
    (f : ∀ i, H i → Set.Ioi (⊥ : EReal)) (x : lp H 2)
    (hx : ∀ j, x j ∈ effectiveDomain (f j)) (i : I) (v : H i) :
    v ∈ (∂ (directSumFunction f ∘ coordinateSlice x i)) (x i) ↔
      v ∈ (∂ (f i)) (x i) := by
  classical
  let c : ℝ := ∑ j ∈ Finset.univ.erase i, (f j (x j) : EReal).toReal
  constructor
  · intro hv
    refine (mem_subdifferential_iff (f := f i) (x := x i) (u := v)).2 ?_
    intro z
    have hbase :
        (((directSumFunction f ∘ coordinateSlice x i) (x i)) : EReal) =
          (f i (x i) : EReal) + (c : EReal) := by
      rw [Function.comp_apply]
      simpa [c] using
        (directSumFunction_coordinateSlice_apply_eq
          (f := f) (x₀ := x) (hx₀ := hx) (i := i) (z := x i))
    have hz :
        (((directSumFunction f ∘ coordinateSlice x i) z) : EReal) =
          (f i z : EReal) + (c : EReal) := by
      rw [Function.comp_apply]
      simpa [c] using
        (directSumFunction_coordinateSlice_apply_eq
          (f := f) (x₀ := x) (hx₀ := hx) (i := i) (z := z))
    have hslice_raw :=
      (mem_subdifferential_iff (f := directSumFunction f ∘ coordinateSlice x i)
        (x := x i) (u := v)).1 hv z
    have hslice_raw' :
        (⟪z - x i, v⟫_ℝ : EReal) + (((directSumFunction f ∘ coordinateSlice x i) (x i)) : EReal) ≤
          (((directSumFunction f ∘ coordinateSlice x i) z) : EReal) := by
      simpa using hslice_raw
    have hslice :
        (⟪z - x i, v⟫_ℝ : EReal) + ((f i (x i) : EReal) + (c : EReal)) ≤
          (f i z : EReal) + (c : EReal) := by
      simpa only [hbase, hz] using hslice_raw'
    have hshift :
        ((⟪z - x i, v⟫_ℝ : EReal) + (f i (x i) : EReal)) + (c : EReal) ≤
          (f i z : EReal) + (c : EReal) := by
      simpa [add_assoc] using hslice
    -- Cancel the common finite tail to recover the active-coordinate inequality.
    exact (add_coe_real_le_add_coe_real_iff _ _ c).1 hshift
  · intro hv
    refine (mem_subdifferential_iff (f := directSumFunction f ∘ coordinateSlice x i)
      (x := x i) (u := v)).2 ?_
    intro z
    have hbase :
        (((directSumFunction f ∘ coordinateSlice x i) (x i)) : EReal) =
          (f i (x i) : EReal) + (c : EReal) := by
      rw [Function.comp_apply]
      simpa [c] using
        (directSumFunction_coordinateSlice_apply_eq
          (f := f) (x₀ := x) (hx₀ := hx) (i := i) (z := x i))
    have hz :
        (((directSumFunction f ∘ coordinateSlice x i) z) : EReal) =
          (f i z : EReal) + (c : EReal) := by
      rw [Function.comp_apply]
      simpa [c] using
        (directSumFunction_coordinateSlice_apply_eq
          (f := f) (x₀ := x) (hx₀ := hx) (i := i) (z := z))
    have hcoord :=
      (mem_subdifferential_iff (f := f i) (x := x i) (u := v)).1 hv z
    have hshift :
        ((⟪z - x i, v⟫_ℝ : EReal) + (f i (x i) : EReal)) + (c : EReal) ≤
          (f i z : EReal) + (c : EReal) := by
      exact (add_coe_real_le_add_coe_real_iff _ _ c).2 hcoord
    have hslice :
        (⟪z - x i, v⟫_ℝ : EReal) + ((f i (x i) : EReal) + (c : EReal)) ≤
          (f i z : EReal) + (c : EReal) := by
      simpa [add_assoc] using hshift
    -- Reinsert the common frozen tail and rewrite the slice values back to the direct-sum form.
    change
      (⟪z - x i, v⟫_ℝ : EReal) + (((directSumFunction f ∘ coordinateSlice x i) (x i)) : EReal) ≤
        (((directSumFunction f ∘ coordinateSlice x i) z) : EReal)
    simpa only [hbase, hz] using hslice

-- Proof sketch: for the forward inclusion, specialize Proposition 16.7 to the direct-sum
-- function and identify each coordinate slice with the corresponding summand up to an additive
-- constant. For the reverse inclusion, choose one effective-domain point in every frozen
-- coordinate, expand the coordinate subgradient inequalities, and sum them to obtain the global
-- subgradient inequality for `directSumFunction f`.
/-- Proposition 16 9: for a finite family of `]-∞,+∞]`-valued functions with nonempty effective
domains, the subdifferential of the direct-sum function is the coordinatewise Cartesian product of
the subdifferentials of the summands. -/
theorem subdifferential_directSumFunction_eq_coordinatewise
    (f : ∀ i, H i → Set.Ioi (⊥ : EReal))
    (hdom : ∀ i, (effectiveDomain (f i)).Nonempty)
    (x : lp H 2) :
    (∂ (directSumFunction f)) x = {u : lp H 2 | ∀ i, u i ∈ (∂ (f i)) (x i)} := by
  classical
  ext u
  constructor
  · intro hu i
    have hx :
        x ∈ effectiveDomain (directSumFunction f) :=
      mem_effectiveDomain_of_mem_subdifferential
        (g := directSumFunction f)
        (hdom := directSumFunction_effectiveDomain_nonempty (f := f) hdom) hu
    have hxcoord := (mem_effectiveDomain_directSumFunction_iff (f := f) (x := x)).1 hx
    have hslice :
        ∀ j, u j ∈ (∂ (directSumFunction f ∘ coordinateSlice x j)) (x j) :=
      subdifferential_subset_coordinatewise_slice_subdifferential
        (g := directSumFunction f) (x := x) hu
    -- The ambient subgradient restricts to every coordinate slice, then the frozen tail cancels.
    exact (mem_subdifferential_directSum_slice_iff
      (f := f) (x := x) (hx := hxcoord) (i := i) (v := u i)).1 (hslice i)
  · intro hu
    refine (mem_subdifferential_iff (f := directSumFunction f) (x := x) (u := u)).2 ?_
    intro y
    have hsum :
        ∑ i, (((⟪y i - x i, u i⟫_ℝ : ℝ) : EReal) + (f i (x i) : EReal)) ≤
          ∑ i, (f i (y i) : EReal) := by
      -- Sum the coordinate subgradient inequalities over the finite index set.
      exact Finset.sum_le_sum fun i _ ↦
        (mem_subdifferential_iff (f := f i) (x := x i) (u := u i)).1 (hu i) (y i)
    have hinner :
        (∑ i, ((⟪y i - x i, u i⟫_ℝ : ℝ) : EReal)) =
          ((⟪y - x, u⟫_ℝ : ℝ) : EReal) := by
      have hinner_real :
          (∑ i, ⟪y i - x i, u i⟫_ℝ : ℝ) = ⟪y - x, u⟫_ℝ := by
        calc
          (∑ i, ⟪y i - x i, u i⟫_ℝ : ℝ) = ∑ i, ⟪(y - x) i, u i⟫_ℝ := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [show (y - x) i = y i - x i by rfl]
          _ = ⟪y - x, u⟫_ℝ := by
            calc
              ∑ i, ⟪(y - x) i, u i⟫_ℝ
                  = ∑ i, ⟪(lpPiLpₗᵢ H ℝ (y - x)) i, (lpPiLpₗᵢ H ℝ u) i⟫_ℝ := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      rw [show (y - x) i = y i - x i by rfl]
                      simp [coe_lpPiLpₗᵢ]
              _ = ⟪lpPiLpₗᵢ H ℝ (y - x), lpPiLpₗᵢ H ℝ u⟫_ℝ := by
                    symm
                    rw [PiLp.inner_apply]
              _ = ⟪y - x, u⟫_ℝ := by
                    simpa using (lpPiLpₗᵢ H ℝ).inner_map_map (y - x) u
      -- Convert the real inner-product sum into the `EReal` sum used in the subgradient inequality.
      calc
        (∑ i, ((⟪y i - x i, u i⟫_ℝ : ℝ) : EReal))
            = ((∑ i, ⟪y i - x i, u i⟫_ℝ : ℝ) : EReal) := by
                simpa using
                  (finset_sum_coe_real (s := (Finset.univ : Finset I))
                    (r := fun i ↦ ⟪y i - x i, u i⟫_ℝ))
        _ = ((⟪y - x, u⟫_ℝ : ℝ) : EReal) := by
              exact congrArg (fun r : ℝ ↦ (r : EReal)) hinner_real
    -- Rewrite the global inequality into the summed coordinate form and apply `hsum`.
    have hdx : ((directSumFunction f x) : EReal) = ∑ i, (f i (x i) : EReal) := by
      rw [directSumFunction_apply]
    have hdy : ((directSumFunction f y) : EReal) = ∑ i, (f i (y i) : EReal) := by
      rw [directSumFunction_apply]
    have hglobal :
        ((⟪y - x, u⟫_ℝ : EReal) + ((directSumFunction f x : EReal))) ≤
          ((directSumFunction f y : EReal)) := by
      rw [hdx, hdy, ← hinner, ← Finset.sum_add_distrib]
      exact hsum
    simpa using hglobal

end Subdifferentials

end ERealFunction
