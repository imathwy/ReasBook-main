import Mathlib
import BauschkeLean.Chap09.Remark_9_37
import BauschkeLean.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

section Subdifferentials

variable {I : Type v} [Finite I]
variable {H : I → Type u}
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]

attribute [local instance] Classical.decEq

omit [∀ i, InnerProductSpace ℝ (H i)] in
/-- Helper for Proposition 16 7: freezing every coordinate except `i` and reinserting the base
value at `i` recovers the original point. -/
private theorem coordinateSlice_eq_base (x : lp H 2) (i : I) :
    coordinateSlice x i (x i) = x := by
  classical
  -- Compare the two `lp` vectors coordinatewise.
  ext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [coordinateSlice_apply_of_ne, hj]

omit [∀ i, InnerProductSpace ℝ (H i)] in
/-- Helper for Proposition 16 7: the displacement from `x` to a coordinate slice is the
single-coordinate vector supported at the active index. -/
private theorem coordinateSlice_sub_eq_single (x : lp H 2) (i : I) (y : H i) :
    coordinateSlice x i y - x = lp.single 2 i (y - x i) := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
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

/-- Helper for Proposition 16 7: the ambient inner product against the slice displacement reduces
to the inner product in the active coordinate. -/
private theorem inner_coordinateSlice_sub_eq (x u : lp H 2) (i : I) (y : H i) :
    ⟪coordinateSlice x i y - x, u⟫_ℝ = ⟪y - x i, u i⟫_ℝ := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  -- Rewrite the displacement as a single-coordinate vector and use the canonical `lp` formula.
  rw [coordinateSlice_sub_eq_single, lp.inner_single_left]

/-- Helper for Proposition 16 7: a global subgradient yields coordinatewise subgradients of the
slice functions obtained by freezing every other coordinate. -/
private theorem subdifferential_subset_coordinatewise_subdifferential_fintype
    {f : lp H 2 → Set.Ioi (⊥ : EReal)} {x : lp H 2} :
    (∂ f) x ⊆ {u | ∀ i, u i ∈ (∂ (f ∘ coordinateSlice x i)) (x i)} := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  intro u hu i
  have hu' := (mem_subdifferential_iff (f := f) (x := x) (u := u)).1 hu
  -- Test the ambient subgradient inequality on the `i`th slice through `x`.
  refine (mem_subdifferential_iff (f := f ∘ coordinateSlice x i) (x := x i) (u := u i)).2 ?_
  intro yi
  have hinner :
      (⟪coordinateSlice x i yi - x, u⟫_ℝ : EReal) = (⟪yi - x i, u i⟫_ℝ : EReal) := by
    -- Push the scalar inner-product identity through the real-to-`EReal` coercion.
    exact congrArg (fun t : ℝ ↦ (t : EReal))
      (inner_coordinateSlice_sub_eq (x := x) (u := u) (i := i) (y := yi))
  -- Normalize the displacement and the frozen basepoint in the slice inequality.
  have hslice := hu' (coordinateSlice x i yi)
  rw [hinner] at hslice
  simpa only [Function.comp_apply, coordinateSlice_eq_base] using hslice

-- Proof sketch: if `u ∈ ∂ f x`, then the subgradient inequality for `f` at `x` can be tested on
-- the slice `coordinateSlice x i yi`; this yields the subgradient inequality for the scalar slice
-- function `f ∘ coordinateSlice x i` at `x i` with slope `u i`, for every `i`.
/-- Proposition 16 7: every subgradient of a function on a finite Hilbert direct sum yields
coordinatewise subgradients of the slice functions obtained by freezing all but one coordinate. -/
theorem subdifferential_subset_coordinatewise_subdifferential
    {f : lp H 2 → Set.Ioi (⊥ : EReal)} {x : lp H 2} :
    (∂ f) x ⊆ {u | ∀ i, u i ∈ (∂ (f ∘ coordinateSlice x i)) (x i)} := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  simpa using
    (subdifferential_subset_coordinatewise_subdifferential_fintype
      (I := I) (H := H) (f := f) (x := x))

end Subdifferentials

end ERealFunction
