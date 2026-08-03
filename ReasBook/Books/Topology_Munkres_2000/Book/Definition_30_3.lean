module

import Mathlib.Topology.Closure

universe u

variable {X : Type u} [TopologicalSpace X] (A : Set X)

/- Definition 30.3. A subset `A` of a space `X` is dense in `X` when
`closure A = Set.univ`; the canonical mathlib notion is `Dense A`. -/
#check Dense A
#check (dense_iff_closure_eq : Dense A ↔ closure A = Set.univ)
