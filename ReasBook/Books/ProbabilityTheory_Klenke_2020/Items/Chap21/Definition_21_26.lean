import ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_40
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped NNReal Topology ZeroAtInfty

noncomputable section

universe u

variable {E : Type u} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]

namespace ProbabilityTheory

/-- Definition 21.26: a Feller semigroup on a Borel topological state space is a Markov semigroup
of transition kernels whose kernel expectation operators preserve real-valued `C₀(E)` and
converge pointwise to the identity as `t → 0`. -/
class IsFellerSemigroup (κ : NNReal → Kernel E E) : Prop extends IsMarkovSemigroup κ where
  /-- For every `t` and `f : C₀(E, ℝ)`, the kernel expectation `x ↦ ∫ y, f y ∂ κ t x` is
  continuous. -/
  mapZeroAtInfty_continuous (t : NNReal) (f : C₀(E, ℝ)) :
    Continuous fun x ↦ ∫ y, f y ∂ κ t x
  /-- For every `t` and `f : C₀(E, ℝ)`, the kernel expectation `x ↦ ∫ y, f y ∂ κ t x` vanishes at
  infinity. -/
  mapZeroAtInfty_zeroAtInfty (t : NNReal) (f : C₀(E, ℝ)) :
    Tendsto (fun x ↦ ∫ y, f y ∂ κ t x) (cocompact E) (𝓝 0)
  /-- For every `f : C₀(E, ℝ)` and `x : E`, the kernel expectation converges to `f x` as
  `t → 0`. -/
  continuousAt_zero (f : C₀(E, ℝ)) (x : E) :
    Tendsto (fun t : NNReal ↦ ∫ y, f y ∂ κ t x) (𝓝 0) (𝓝 (f x))

namespace IsFellerSemigroup

variable {κ : NNReal → Kernel E E} [hκ : IsFellerSemigroup κ]

/-- The canonical action of a Feller semigroup on `C₀(E, ℝ)` is given by kernel expectation. -/
def mapZeroAtInfty (κ : NNReal → Kernel E E) [IsFellerSemigroup κ]
    (t : NNReal) (f : C₀(E, ℝ)) : C₀(E, ℝ) :=
  let hκ : IsFellerSemigroup κ := inferInstance
  { toFun := fun x ↦ ∫ y, f y ∂ κ t x
    continuous_toFun := hκ.mapZeroAtInfty_continuous t f
    zero_at_infty' := hκ.mapZeroAtInfty_zeroAtInfty t f }

omit [BorelSpace E] in
/-- Evaluating the Feller operator at `x` gives the kernel expectation against the row `κ t x`. -/
@[simp] theorem mapZeroAtInfty_apply (t : NNReal) (f : C₀(E, ℝ)) (x : E) :
    mapZeroAtInfty κ t f x = ∫ y, f y ∂ κ t x :=
  rfl

omit [BorelSpace E] in
/-- Evaluated at a fixed state `x`, the Feller operators converge to `f x` as `t → 0`. -/
theorem tendsto_mapZeroAtInfty_zero_apply (f : C₀(E, ℝ)) (x : E) :
    Tendsto (fun t : NNReal ↦ mapZeroAtInfty κ t f x) (𝓝 0) (𝓝 (f x)) := by
  simpa [mapZeroAtInfty_apply] using hκ.continuousAt_zero f x

end IsFellerSemigroup

-- Proof sketch: for the constant semigroup `κ t = Kernel.id`, the induced `C₀(E)` action is the
-- identity for every `t`, so the semigroup law and pointwise continuity at `0` are immediate.
/-- The constant identity-kernel family is a Feller semigroup. -/
instance instIsFellerSemigroupId :
    IsFellerSemigroup (fun _ : NNReal ↦ (Kernel.id : Kernel E E)) where
  isMarkovKernel _ := by infer_instance
  zero_eq := rfl
  comp_eq s t := by
    sorry
  mapZeroAtInfty_continuous _ f := by
    sorry
  mapZeroAtInfty_zeroAtInfty _ f := by
    sorry
  continuousAt_zero f x := by
    sorry

end ProbabilityTheory
