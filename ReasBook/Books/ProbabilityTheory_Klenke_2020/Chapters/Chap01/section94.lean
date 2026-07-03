import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_1_94 (from Items/Chap01) -/
open MeasureTheory

local infixr:25 " →ₛ " => MeasureTheory.SimpleFunc

universe u v

namespace MeasureTheory.SimpleFunc

variable {α : Type u} {β : Type v} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass β] {f : α → β}

/-- A measurable map with finite range defines a canonical simple function. -/
def ofMeasurable (hf : Measurable f) (hfin : (Set.range f).Finite) : α →ₛ β :=
  ⟨f, fun y ↦ MeasurableSet.preimage (measurableSet_singleton y) hf, hfin⟩

end MeasureTheory.SimpleFunc

/-- Remark 1.94: a measurable map with finite range can be regarded as a simple function. -/
-- Proof sketch: the canonical simple function is `SimpleFunc.ofMeasurable hf hfin`, whose fibers
-- are measurable because `f` is measurable and singletons in the codomain are measurable.
theorem measurable_exists_eq_simpleFunc_of_finite_range
    {α : Type u} {β : Type v} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] {f : α → β}
    (hf : Measurable f) (hfin : (Set.range f).Finite) :
    ((SimpleFunc.ofMeasurable hf hfin : α →ₛ β) : α → β) = f := by
  show ((SimpleFunc.mk f
      (fun y ↦ MeasurableSet.preimage (measurableSet_singleton y) hf) hfin : α →ₛ β) : α → β) = f
  exact SimpleFunc.coe_mk f
    (fun y ↦ MeasurableSet.preimage (measurableSet_singleton y) hf) hfin
