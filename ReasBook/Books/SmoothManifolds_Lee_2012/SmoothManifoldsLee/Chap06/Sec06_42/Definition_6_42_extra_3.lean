import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

-- Domain sampling pass: this file lies in the general-topology / continuous-map-to-subtype domain.
-- Relevant owner declarations checked before refinement are:
-- `ContinuousMap`,
-- `Function.LeftInverse`,
-- `continuous_subtype_val`,
-- and `Continuous.subtype_mk`.
-- The best owner abstraction is a continuous map `X → M` into the subtype, with the retraction
-- property expressed canonically as a left inverse to the subtype inclusion. The only primitive
-- data is that continuous map; the identity-on-`M` law is derived API on that owner.

/-- Definition 6.42-extra-3. A retraction of a topological space `X` onto a subspace
`M ⊆ X` is a continuous map `X → M` whose restriction to `M` is the identity map of `M`. -/
def TopologicalRetraction {X : Type u} [TopologicalSpace X] (M : Set X) :=
  {r : ContinuousMap X M // Function.LeftInverse r ((↑) : M → X)}

namespace TopologicalRetraction

variable {X : Type u} [TopologicalSpace X] {M : Set X}

/-- A topological retraction can be used as its underlying function `X → M`. -/
instance : CoeFun (TopologicalRetraction M) (fun _ ↦ X → M) where
  coe r := r.1

/-- A topological retraction restricts to the identity on the subspace `M`. -/
theorem leftInverse (r : TopologicalRetraction M) :
    Function.LeftInverse r ((↑) : M → X) :=
  r.2

/-- A topological retraction is continuous. -/
theorem continuous (r : TopologicalRetraction M) : Continuous r :=
  r.1.continuous

/-- A topological retraction restricts to the identity on the subspace `M`. -/
@[simp] theorem eqOn_subspace_apply (r : TopologicalRetraction M) (x : M) : r x = x :=
  r.leftInverse x

end TopologicalRetraction
