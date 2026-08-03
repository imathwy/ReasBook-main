module

public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.UniformSpace.AbstractCompletion

open Set

public section

namespace Isometry

universe u v

variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
variable {h : X → Y}

/-- The map from a metric space into the closure of the range of an isometry. -/
@[expose]
def toClosure (_ : Isometry h) : X → closure (range h) :=
  inclusion subset_closure ∘ rangeFactorization h

/-- The closure-valued map induced by an isometry evaluates to the original map. -/
theorem toClosure_apply (hh : Isometry h) (x : X) :
    hh.toClosure x = ⟨h x, subset_closure (mem_range_self x)⟩ := rfl

/-- The map into the closure of the range of an isometry is an isometry. -/
theorem toClosure_isometry (hh : Isometry h) : Isometry hh.toClosure := by
  intro x y
  exact hh.edist_eq x y

/-- The map into the closure of the range of an isometry has dense range. -/
theorem denseRange_toClosure (hh : Isometry h) : DenseRange hh.toClosure := by
  exact ((denseRange_inclusion_iff subset_closure).2 subset_rfl).comp
    rangeFactorization_surjective.denseRange (continuous_inclusion subset_closure)

/-- An isometry into a complete metric space realizes an abstract completion on the closure
of its range. -/
@[expose]
def abstractCompletion [CompleteSpace Y] (hh : Isometry h) : AbstractCompletion X where
  space := closure (range h)
  coe := hh.toClosure
  uniformStruct := inferInstance
  complete := isClosed_closure.completeSpace_coe
  separation := inferInstance
  isUniformInducing := hh.toClosure_isometry.isUniformInducing
  dense := hh.denseRange_toClosure

/-- The canonical map of the closure completion is the closure-valued map induced by the
original isometry. -/
theorem abstractCompletion_coe [CompleteSpace Y] (hh : Isometry h) (x : X) :
    hh.abstractCompletion.coe x = hh.toClosure x := rfl

end Isometry

end
