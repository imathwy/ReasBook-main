import Mathlib
import BauschkeLean.Chap02.Definition_2_54
import BauschkeLean.Chap16.Proposition_16_17
import BauschkeLean.Chap16.Proposition_16_7
import BauschkeLean.Chap17.Definition_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped InnerProductSpace

universe u v

namespace ERealFunction

section DifferentiabilityOfConvexFunctions

variable {I : Type v} [Finite I]
variable {H : I → Type u}
variable [∀ i, NormedAddCommGroup (H i)]

variable [∀ i, InnerProductSpace ℝ (H i)]

attribute [local instance] Classical.decEq

omit [∀ i, InnerProductSpace ℝ (H i)] in
/-- Helper for Proposition 17 34: reinserting the original active coordinate into a slice recovers
the base point. -/
private theorem coordinateSlice_eq_base (x : lp H 2) (i : I) :
    coordinateSlice x i (x i) = x := by
  -- Compare the slice and the base point coordinatewise.
  ext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [coordinateSlice_apply_of_ne, hj]

/-- Helper for Proposition 17 34: coordinate slices preserve convex combinations in the active
coordinate. -/
private theorem coordinateSlice_convexCombination
    (x : lp H 2) (i : I) (y z : H i) (α : ℝ) :
    α • coordinateSlice x i y + (1 - α) • coordinateSlice x i z =
      coordinateSlice x i (α • y + (1 - α) • z) := by
  -- Only the distinguished coordinate changes, so extensionality reduces the identity to two
  -- coordinate computations.
  ext j
  by_cases hj : j = i
  · subst hj
    change (α • Function.update x j y + (1 - α) • Function.update x j z) j =
      Function.update x j (α • y + (1 - α) • z) j
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
    simp
  · change (α • Function.update x i y + (1 - α) • Function.update x i z) j =
      Function.update x i (α • y + (1 - α) • z) j
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
    simp [Function.update, hj]

/-- Helper for Proposition 17 34: precomposing a convex function with a coordinate slice preserves
convexity on the effective domain of that slice. -/
lemma convexOn_coordinateSlice
    {f : lp H 2 → Set.Ioi (⊥ : EReal)} (hconv : ConvexOn f (effectiveDomain f))
    {x : lp H 2} (hx : x ∈ effectiveDomain f) (i : I) :
    ConvexOn (f ∘ coordinateSlice x i) (effectiveDomain (f ∘ coordinateSlice x i)) := by
  have hxslice : x i ∈ effectiveDomain (f ∘ coordinateSlice x i) := by
    -- The slice through `x` at its own active coordinate is exactly `x`.
    simpa [effectiveDomain, Function.comp_apply, coordinateSlice_eq_base] using hx
  refine ⟨⟨x i, hxslice⟩, ?_, ?_⟩
  · -- The chosen set is already the effective domain of the sliced function.
    intro y hy
    exact hy
  · intro y hy z hz α hα0 hα1
    have hy' : coordinateSlice x i y ∈ effectiveDomain f := by
      exact hy
    have hz' : coordinateSlice x i z ∈ effectiveDomain f := by
      exact hz
    -- Apply convexity to the two slice points and rewrite the resulting convex combination.
    simpa [Function.comp_apply, coordinateSlice_convexCombination] using
      hconv.ineq hy' hz' hα0 hα1

/-- Helper for Proposition 17 34: every ambient subgradient at `x` agrees coordinatewise with the
assembled slice gradients. -/
lemma subgradient_coordinate_eq_gradient
    {f : lp H 2 → Set.Ioi (⊥ : EReal)} (hconv : ConvexOn f (effectiveDomain f))
    {x : lp H 2} (hxsub : SubdifferentiableAt f x) (grad : lp H 2)
    (hgrad : ∀ i,
      HasGateauxDerivativeAt
        (fun y ↦ (f (coordinateSlice x i y) : EReal).toReal)
        (toDualMap ℝ (H i) (grad i)) (x i))
    {u : lp H 2} (hu : u ∈ (∂ f) x) (i : I) :
    u i = grad i := sorry

-- Proof sketch: Proposition 16.7 sends every `u ∈ ∂ f(x)` to a family of slice subgradients.
-- Since `hconv.nonempty` and `SubdifferentiableAt f x` imply `x ∈ effectiveDomain f`, Proposition
-- 17.31 (1) makes each slice subdifferential the singleton `{grad i}` and identifies `x i` with
-- an effective-domain point of the `i`-th slice. Thus every subgradient of `f` at `x` must agree
-- coordinatewise with `grad`, hence equal `grad` itself in `lp H 2`; `SubdifferentiableAt f x`
-- supplies the nonemptiness needed to conclude equality with that singleton.
/-- At a subdifferentiability point `x`, if every coordinate slice through `x` has Gâteaux
gradient `grad i`, then the subdifferential of `f` at `x` is the singleton consisting of the
assembled coordinatewise gradient. -/
theorem subdifferential_eq_singleton_of_coordinatewise_hasGateauxDerivativeAt
    {f : lp H 2 → Set.Ioi (⊥ : EReal)} (hconv : ConvexOn f (effectiveDomain f))
    {x : lp H 2} (hxsub : SubdifferentiableAt f x) (grad : lp H 2)
    (hgrad : ∀ i,
      HasGateauxDerivativeAt
        (fun y ↦ (f (coordinateSlice x i y) : EReal).toReal)
        (toDualMap ℝ (H i) (grad i)) (x i)) :
    (∂ f) x = ({grad} : Set (lp H 2)) := sorry

variable [∀ i, CompleteSpace (H i)]

omit [Finite I] in
/-- Helper for Proposition 17 34: source continuity in the effective domain yields a nonempty
subdifferential, hence subdifferentiability. -/
lemma subdifferentiableAt_of_continuousAtInEffectiveDomain
    {f : lp H 2 → Set.Ioi (⊥ : EReal)} (hconv : ConvexOn f (effectiveDomain f))
    {x : lp H 2} (hxcont : ContinuousAtInEffectiveDomain f x) :
    SubdifferentiableAt f x := by
  -- Proposition 16.17(2) gives a nonempty subdifferential, which is exactly subdifferentiability.
  rw [subdifferentiableAt_iff_mem_dom, SetValuedOperator.mem_dom_iff]
  exact
    (subdifferential_nonempty_and_weaklyCompact_of_continuousPoint
      f hconv hxcont).1

-- Proof sketch: continuity on the effective domain gives subdifferentiability at `x`. The slice
-- hypotheses already use the Chapter 17 owner `GateauxDifferentiableAt`, so each coordinate slice
-- carries a source Gâteaux derivative map. Passing to the corresponding coordinatewise real
-- Gâteaux gradients yields a candidate assembled gradient `grad`; the previous theorem identifies
-- `∂ f(x)` with `{grad}`, and the Chapter 17 directional-derivative characterization then gives
-- the global source-facing witness at `x`.
/-- Proposition 17.34: for a proper convex function on a finite Hilbert sum, if `x` is a
continuity point on the effective domain and every coordinate slice `f ∘ coordinateSlice x i` is
Gâteaux differentiable at `x i`, then `f` is Gâteaux differentiable at `x` in the Chapter 17
source sense. The assembled gradient formula `(17.46)` is recorded by the companion theorem
below. -/
theorem gateauxDifferentiableAt_of_coordinatewise_gateauxDifferentiableAt
    {f : lp H 2 → Set.Ioi (⊥ : EReal)} (hproper : IsProper f.asEReal)
    (hconv : ConvexOn f (effectiveDomain f))
    {x : lp H 2} (hxcont : ContinuousAtInEffectiveDomain f x)
    (hslice : ∀ i, ∃ A : H i →L[ℝ] ℝ,
      ∀ y : H i, HasDirectionalDerivativeAt (f ∘ coordinateSlice x i) (x i) y (A y : EReal)) :
    ∃ A : lp H 2 →L[ℝ] ℝ,
      ∀ y : lp H 2, HasDirectionalDerivativeAt f x y (A y : EReal) := sorry

/-- Companion for Proposition 17.34: under the source hypotheses there is an assembled
`grad : lp H 2` whose `i`-th coordinate is the Gâteaux gradient of
`f ∘ coordinateSlice x i` at `x i`; equivalently, `(17.46)` holds and `toDualMap ℝ (lp H 2) grad`
is the Gâteaux derivative of the finite-valued representative of `f` at `x`. -/
theorem exists_lpGradient_of_coordinatewise_gateauxDifferentiableAt
    {f : lp H 2 → Set.Ioi (⊥ : EReal)} (hproper : IsProper f.asEReal)
    (hconv : ConvexOn f (effectiveDomain f))
    {x : lp H 2} (hxcont : ContinuousAtInEffectiveDomain f x)
    (hslice : ∀ i, ∃ A : H i →L[ℝ] ℝ,
      ∀ y : H i, HasDirectionalDerivativeAt (f ∘ coordinateSlice x i) (x i) y (A y : EReal)) :
    ∃ grad : lp H 2,
      HasGateauxDerivativeAt
        (fun z ↦ (f z : EReal).toReal)
        (toDualMap ℝ (lp H 2) grad) x ∧
      ∀ i,
        HasGateauxDerivativeAt
          (fun y ↦ (f (coordinateSlice x i y) : EReal).toReal)
          (toDualMap ℝ (H i) (grad i)) (x i) := sorry

/-- Companion bridge for Proposition 17.34: if the slice Gâteaux derivatives are represented by
the coordinates of `grad`, then the finite-valued representative of `f` has Gâteaux derivative
`toDualMap ℝ (lp H 2) grad` at `x`, encoding the assembled gradient formula `(17.46)`. -/
theorem hasGateauxDerivativeAt_of_coordinatewise_hasGateauxDerivativeAt
    {f : lp H 2 → Set.Ioi (⊥ : EReal)} (hproper : IsProper f.asEReal)
    (hconv : ConvexOn f (effectiveDomain f))
    {x : lp H 2} (hxcont : ContinuousAtInEffectiveDomain f x)
    (grad : lp H 2)
    (hgrad : ∀ i,
      HasGateauxDerivativeAt
        (fun y ↦ (f (coordinateSlice x i y) : EReal).toReal)
        (toDualMap ℝ (H i) (grad i)) (x i)) :
    HasGateauxDerivativeAt
      (fun z ↦ (f z : EReal).toReal)
      (toDualMap ℝ (lp H 2) grad) x := sorry

end DifferentiabilityOfConvexFunctions

end ERealFunction
