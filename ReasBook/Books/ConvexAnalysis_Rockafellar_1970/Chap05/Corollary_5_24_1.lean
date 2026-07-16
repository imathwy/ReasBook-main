import Mathlib

noncomputable section

open MeasureTheory

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 5.24.1 says that for a finite convex function on a real interval, the
  increment `f y - f x` is given by the interval integral of either one-sided derivative.
- `core/canonical`: in mathlib, the natural owner layer for this one-dimensional finite setting is
  `ConvexOn ℝ I f` together with the one-sided derivatives
  `derivWithin f (Set.Ioi t) t` and `derivWithin f (Set.Iio t) t`.
- `bridge/view`: the endpoint interior hypotheses are a derived way to guarantee the primitive
  segment-level condition `uIcc x y ⊆ interior I`; the canonical source theorem below is stated at
  this primitive layer, with endpoint-interior versions as wrappers.

Domain-style sampling used here:
- `ConvexOn.hasDerivWithinAt_rightDeriv_of_mem_interior` and
  `ConvexOn.hasDerivWithinAt_leftDeriv_of_mem_interior`;
- `ConvexOn.monotoneOn_rightDeriv` and `ConvexOn.monotoneOn_leftDeriv`;
- `intervalIntegral.integral_eq_sub_of_hasDeriv_right`;
- `MonotoneOn.intervalIntegrable`.
-/

namespace ConvexOn

-- Textbook one-sided derivative notation for the finite-valued scalar-line layer used here.
local notation:max f "′+" => fun t => derivWithin f (Set.Ioi t) t
local notation:max f "′-" => fun t => derivWithin f (Set.Iio t) t

-- Proof sketch: under the primitive segment hypothesis `uIcc x y ⊆ interior I`, continuity on
-- `uIcc x y`, one-sided differentiability on `Ioo (min x y) (max x y)`, and interval integrability
-- of the right derivative are all available from the convex one-dimensional API, so FTC-2 applies.
/-- Corollary 5.24.1 at the primitive segment layer (right-derivative form): for a finite convex
function, if the full segment between `x` and `y` lies in `interior I`, then the increment
`f y - f x` is the interval integral of the right one-sided derivative of `f`. -/
theorem sub_eq_intervalIntegral_rightDeriv_of_uIcc_subset_interior
    {I : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ I f)
    {x y : ℝ} (hxyI : Set.uIcc x y ⊆ interior I) :
    f y - f x = ∫ t in x..y, f′+ t := by
  symm
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right ?_ ?_ ?_
  · exact (hf.continuousOn_interior).mono hxyI
  · intro t ht
    exact hf.hasDerivWithinAt_rightDeriv_of_mem_interior (hxyI (Set.uIoo_subset_uIcc_self ht))
  · exact (hf.monotoneOn_rightDeriv.mono hxyI).intervalIntegrable

-- Proof sketch: same primitive segment hypothesis as above; now use the left one-sided derivative
-- and the left-derivative convex API.
/-- Corollary 5.24.1 at the primitive segment layer (left-derivative form): for a finite convex
function, if the full segment between `x` and `y` lies in `interior I`, then the increment
`f y - f x` is the interval integral of the left one-sided derivative of `f`. -/
theorem sub_eq_intervalIntegral_leftDeriv_of_uIcc_subset_interior
    {I : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ I f)
    {x y : ℝ} (hxyI : Set.uIcc x y ⊆ interior I) :
    f y - f x = ∫ t in x..y, f′- t := by
  let g : ℝ → ℝ := f′-
  let h : ℝ → ℝ := fun u => -f (-u)
  have hg_int_xy : IntervalIntegrable g volume x y :=
    (hf.monotoneOn_leftDeriv.mono hxyI).intervalIntegrable
  have hg_int_yx : IntervalIntegrable g volume y x := hg_int_xy.symm
  have hgneg_int : IntervalIntegrable (fun u => g (-u)) volume (-y) (-x) :=
    (IntervalIntegrable.iff_comp_neg (f := g) (a := y) (b := x)).1 hg_int_yx
  have hneg_uIcc : ∀ {u : ℝ}, u ∈ Set.uIcc (-y) (-x) → -u ∈ Set.uIcc x y := by
    intro u hu
    rcases hu with ⟨humin, humax⟩
    have humin' : -max x y ≤ u := by simpa [min_neg_neg, max_comm] using humin
    have humax' : u ≤ -min x y := by simpa [max_neg_neg, min_comm] using humax
    refine ⟨?_, ?_⟩ <;> linarith
  have hcont_h : ContinuousOn h (Set.uIcc (-y) (-x)) := by
    refine (hf.continuousOn_interior.comp continuous_neg.continuousOn ?_).neg
    intro u hu
    exact hxyI (hneg_uIcc hu)
  have hderiv_h :
      ∀ u ∈ Set.Ioo (min (-y) (-x)) (max (-y) (-x)),
        HasDerivWithinAt h (g (-u)) (Set.Ioi u) u := by
    intro u hu
    have hu_mem_uIoo : u ∈ Set.uIoo (-y) (-x) := by simpa [Set.uIoo] using hu
    have hu_neg_mem_uIoo : -u ∈ Set.uIoo x y := by
      rcases hu_mem_uIoo with ⟨humin, humax⟩
      have humin' : -max x y < u := by simpa [min_neg_neg, max_comm] using humin
      have humax' : u < -min x y := by simpa [max_neg_neg, min_comm] using humax
      exact ⟨by linarith, by linarith⟩
    have hu_neg_int : -u ∈ interior I := hxyI (Set.uIoo_subset_uIcc_self hu_neg_mem_uIoo)
    have hleft : HasDerivWithinAt f (g (-u)) (Set.Iio (-u)) (-u) := by
      simpa [g] using hf.hasDerivWithinAt_leftDeriv_of_mem_interior hu_neg_int
    have hneg : HasDerivWithinAt (fun v : ℝ => -v) (-1) (Set.Ioi u) u :=
      (hasDerivAt_neg u).hasDerivWithinAt
    have hmaps : Set.MapsTo (fun v : ℝ => -v) (Set.Ioi u) (Set.Iio (-u)) := by
      intro v hv
      have hv' : u < v := hv
      exact neg_lt_neg hv'
    have hcomp : HasDerivWithinAt (fun v : ℝ => f (-v)) ((g (-u)) * (-1)) (Set.Ioi u) u :=
      hleft.comp u hneg hmaps
    simpa [h, g, mul_comm, mul_left_comm, mul_assoc] using hcomp.neg
  have hFTC_h : h (-x) - h (-y) = ∫ u in -y..-x, g (-u) := by
    symm
    simpa [h] using
      (intervalIntegral.integral_eq_sub_of_hasDeriv_right (a := -y) (b := -x)
        hcont_h hderiv_h hgneg_int)
  have hFTC : f y - f x = ∫ u in -y..-x, g (-u) := by
    simpa [h, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hFTC_h
  calc
    f y - f x = ∫ u in -y..-x, g (-u) := hFTC
    _ = ∫ t in x..y, g t := by
      rw [intervalIntegral.integral_comp_neg (f := g) (a := -y) (b := -x)]
      simp
    _ = ∫ t in x..y, f′- t := by rfl

/-- Corollary 5.24.1, endpoint-interior wrapper (right-derivative form): if `x,y ∈ interior I`,
then the increment `f y - f x` is the interval integral of the right one-sided derivative of `f`. -/
theorem sub_eq_intervalIntegral_rightDeriv
    {I : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ I f)
    {x y : ℝ} (hx : x ∈ interior I) (hy : y ∈ interior I) :
    f y - f x = ∫ t in x..y, f′+ t := by
  refine hf.sub_eq_intervalIntegral_rightDeriv_of_uIcc_subset_interior ?_
  exact (hf.1.interior.ordConnected).uIcc_subset hx hy

/-- Corollary 5.24.1, endpoint-interior wrapper (left-derivative form): if `x,y ∈ interior I`,
then the increment `f y - f x` is the interval integral of the left one-sided derivative of `f`. -/
theorem sub_eq_intervalIntegral_leftDeriv
    {I : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ I f)
    {x y : ℝ} (hx : x ∈ interior I) (hy : y ∈ interior I) :
    f y - f x = ∫ t in x..y, f′- t := by
  refine hf.sub_eq_intervalIntegral_leftDeriv_of_uIcc_subset_interior ?_
  exact (hf.1.interior.ordConnected).uIcc_subset hx hy

end ConvexOn
