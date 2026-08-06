module

public import Mathlib.Data.Set.Prod
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.ContinuousMap.Defs

public section

universe u v w

variable {E : Type u} {A : Type v} {B : Type w}
variable [TopologicalSpace E] [TopologicalSpace A] [TopologicalSpace B]

/-- The projection from the pullback of `p` along `f` to the base `A`. -/
@[expose]
def pullbackSnd (p : E → B) (f : C(A, B)) : C(Function.Pullback p f, A) where
  toFun x := x.1.2
  continuous_toFun := continuous_snd.comp continuous_subtype_val

/-- Evaluating `pullbackSnd p f` returns the second coordinate of a pullback point. -/
@[simp] theorem pullbackSnd_apply (p : E → B) (f : C(A, B)) (x : Function.Pullback p f) :
    pullbackSnd p f x = x.1.2 := rfl
