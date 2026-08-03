module

public import Topology_Munkres_2000.Book.Definition_43_9.Evaluation
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

public section

open UniformConvergence

universe u v

namespace ContinuousMap

variable (X : Type u) (Y : Type v)
variable [TopologicalSpace X] [UniformSpace Y]

/-- The topology on `C(X, Y)` induced by the uniform-convergence topology on all functions
`X → Y`. -/
@[reducible, expose]
def uniformTopology : TopologicalSpace C(X, Y) :=
  TopologicalSpace.induced (fun f : C(X, Y) ↦ UniformFun.ofFun f)
    (UniformFun.topologicalSpace X Y)

/-- The uniform topology on `C(X, Y)` is induced by its inclusion into `UniformFun X Y`. -/
theorem uniformTopology_def :
    uniformTopology X Y =
      TopologicalSpace.induced (fun f : C(X, Y) ↦ UniformFun.ofFun f)
        (UniformFun.topologicalSpace X Y) := rfl

end ContinuousMap

/-- Continuous maps equipped with the topology of uniform convergence. -/
@[expose]
def UniformTopologyContinuousMap (X : Type u) (Y : Type v) [TopologicalSpace X]
    [UniformSpace Y] := C(X, Y)

namespace UniformTopologyContinuousMap

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [UniformSpace Y]

/-- The canonical equivalence with ordinary bundled continuous maps. -/
def equivContinuousMap : UniformTopologyContinuousMap X Y ≃ C(X, Y) :=
  Equiv.refl _

/-- The inclusion into the uniform-convergence function space. -/
def toUniformFun (f : UniformTopologyContinuousMap X Y) : UniformFun X Y :=
  UniformFun.ofFun (equivContinuousMap f)

/-- Helper for Corollary 8.0.1: the canonical inclusion is the ordinary continuous
map, reinterpreted as a uniform function. -/
theorem toUniformFun_eq (f : UniformTopologyContinuousMap X Y) :
    toUniformFun f = UniformFun.ofFun (equivContinuousMap f) := by
  -- At the construction site, the claimed computation is the defining equation.
  rfl

/-- The uniform structure inducing uniform convergence on continuous maps. -/
instance instUniformSpace : UniformSpace (UniformTopologyContinuousMap X Y) :=
  UniformSpace.comap toUniformFun (UniformFun.uniformSpace X Y)

/-- The underlying function of a continuous map in the uniform topology. -/
def toFun (f : UniformTopologyContinuousMap X Y) : X → Y :=
  equivContinuousMap f

/-- The underlying-function map is injective. -/
theorem toFun_injective : Function.Injective (toFun : UniformTopologyContinuousMap X Y → X → Y) :=
  fun f g h ↦ by
    apply equivContinuousMap.injective
    simpa [toFun] using h

/-- Continuous maps in the uniform topology coerce to their underlying functions. -/
instance instFunLike : FunLike (UniformTopologyContinuousMap X Y) X Y where
  coe := toFun
  coe_injective := toFun_injective

/-- A continuous map in the uniform topology is continuous as a function. -/
theorem continuous (f : UniformTopologyContinuousMap X Y) : Continuous f :=
  (equivContinuousMap f).continuous

/-- Continuous maps in the uniform topology are equal when they agree pointwise. -/
@[ext]
theorem ext {f g : UniformTopologyContinuousMap X Y} (h : ∀ x, f x = g x) : f = g :=
  toFun_injective (funext h)

/-- The topology on the named view agrees with `ContinuousMap.uniformTopology`. -/
theorem topologicalSpace_eq_uniformTopology :
    (inferInstance : TopologicalSpace (UniformTopologyContinuousMap X Y)) =
      ContinuousMap.uniformTopology X Y := by
  rw [ContinuousMap.uniformTopology_def]
  rfl

end UniformTopologyContinuousMap
