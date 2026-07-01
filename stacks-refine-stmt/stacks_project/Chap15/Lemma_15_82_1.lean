import Mathlib
import stacks_project.Chap15.«15_60_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open Polynomial

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "ev0" => Polynomial.evalRingHom 0

/- Domain-style sampling for Lemma 15.82.1:
- primary domain: derived base change for the polynomial evaluation map `R[X] → R`;
- sampled owner declarations:
  `Polynomial.evalRingHom`,
  `derivedTensorWithAlgebra`,
  `(ModuleCat.restrictScalars f).mapDerivedCategory`,
  `CategoryTheory.IsIsomorphic`;
- best owner abstraction: the source-facing theorem should use the chapter owner
  `derivedTensorWithAlgebra (Polynomial.evalRingHom 0)`, with restriction of scalars along
  `Polynomial.evalRingHom 0` kept as the bridge/view that places `K` in `D(R[X])`; since the
  comparison is only needed as an object-level existence statement, the public surface should
  remain at the theorem-level `IsIsomorphic` API rather than expose a chosen concrete isomorphism;
- primitive data: the ring hom `R[X] →+* R`;
- derived API: the derived restriction functor, the owner functor
  `derivedTensorWithAlgebra (Polynomial.evalRingHom 0)`, and the theorem that the displayed
  object is isomorphic to `K ⊞ K⟦(1 : ℤ)⟧`.

Source/core/bridge triage:
- `source-facing`: the main isomorphism theorem below;
- `core/canonical`: `Polynomial.evalRingHom`, `derivedTensorWithAlgebra`,
  `ModuleCat.restrictScalars`;
- `bridge/view`: the derived restriction-of-scalars functor
  `(ModuleCat.restrictScalars (Polynomial.evalRingHom 0)).mapDerivedCategory` along
  `Polynomial.evalRingHom 0`. -/

-- Proof sketch: resolve `K` by an `R`-flat complex, view it over `R[X]` via the action with
-- `X = 0`, compute the derived tensor product using the two-term free resolution
-- `R[X] \xrightarrow{X} R[X]` of `R`, and identify the resulting total complex with the split
-- object `K ⊞ K[1]`.
/-- Lemma 15.82.1: if a derived `R`-complex is viewed as an `R[X]`-complex through the map
`R[X] → R` sending `X` to `0`, then derived tensoring back with `R` over `R[X]` is isomorphic to
`K^• ⊞ K^•[1]` in `D(R)`. -/
theorem derivedTensor_restrictScalars_evalAtZero_isomorphic_biprod_shift
    (K : DModR) :
    IsIsomorphic
      ((derivedTensorWithAlgebra ev0).obj
        (((ModuleCat.restrictScalars ev0).mapDerivedCategory).obj K))
      (K ⊞ K⟦(1 : ℤ)⟧) := by
  sorry

end

end CategoryTheory
