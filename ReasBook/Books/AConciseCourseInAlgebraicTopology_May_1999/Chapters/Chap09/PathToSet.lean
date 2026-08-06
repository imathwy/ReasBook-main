import Mathlib.Topology.Path

open scoped unitInterval

universe u

variable {X : Type u} [TopologicalSpace X]

-- Semantic recall: mathlib's `Path x y` is the canonical owner for fixed-endpoint paths, so the
-- textbook space of paths from a basepoint to `A` is modeled by `PathToSet A x`.

/-- A path in `X` beginning at `x` and ending at some point of `A`. -/
structure PathToSet (A : Set X) (x : X) : Type u where
  /-- The endpoint of the path, viewed as a point of `A`. -/
  endpoint : A
  /-- The underlying path from `x` to the chosen endpoint. -/
  path : Path x endpoint.1

namespace PathToSet

variable {A : Set X} {x : X}

/-- A `PathToSet` is evaluated by evaluating its underlying path. -/
instance : CoeFun (PathToSet A x) fun _ ↦ I → X where
  coe γ := γ.path

/-- The endpoint of a `PathToSet` lies in `A`. -/
theorem endpoint_mem (γ : PathToSet A x) : γ.path 1 ∈ A :=
  sorry

/-- The constant path at a basepoint of `A` defines an element of `PathToSet A x.1`. -/
def refl (x : A) : PathToSet A x.1 where
  endpoint := x
  path := Path.refl x.1

end PathToSet

namespace PathToSet

variable (A : Set X) (x : A)

/-- Record a path ending in `A` by its endpoint and underlying continuous map. -/
def endpointAndPath (γ : PathToSet A x.1) : A × C(I, X) :=
  (γ.endpoint, γ.path.toContinuousMap)

/-- `endpointAndPath` is injective. -/
theorem endpointAndPath_injective : Function.Injective (endpointAndPath A x) := by
  intro γ δ h
  rcases γ with ⟨γ_endpoint, γ_path⟩
  rcases δ with ⟨δ_endpoint, δ_path⟩
  have h_endpoint : γ_endpoint = δ_endpoint := congrArg Prod.fst h
  have h_path : γ_path.toContinuousMap = δ_path.toContinuousMap := congrArg Prod.snd h
  cases h_endpoint
  have h_path' : γ_path = δ_path := by
    apply Path.ext
    exact congrArg ContinuousMap.toFun h_path
  cases h_path'
  rfl

/-- `PathToSet A x.1` carries the topology induced from its endpoint and underlying path. -/
instance instTopologicalSpace : TopologicalSpace (PathToSet A x.1) :=
  TopologicalSpace.induced (endpointAndPath A x) inferInstance

end PathToSet
