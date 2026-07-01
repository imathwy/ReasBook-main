import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap05.Lemma_23_0_1

noncomputable section

open Filter
open scoped Topology

universe u v

section

variable {𝕜 : Type*}
variable [Field 𝕜] [LinearOrder 𝕜]
variable {U : Type u} {X : Type v}

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.5.3 singles out the partial directional derivatives
  `K'(u, v; u', 0)` and `K'(u, v; 0, v')` of a saddle-function.
- `core/canonical`: the chapter owner for directional derivatives is already
  `Function.HasDirectionalDerivativeAt` / `Function.directionalDerivativeAt` from
  `Chap05.Lemma_23_0_1`.
- `bridge/view`: the first- and second-variable partial derivatives are exactly the directional
  derivatives of the uncurried bifunction in directions `(u', 0)` and `(0, v')`, equivalently the
  directional derivatives of the corresponding slices.

Domain-style sampling used here:
- `Function.directionalDifferenceQuotientAt`;
- `Function.HasDirectionalDerivativeAt`;
- `Function.directionalDerivativeAt`;
- the earlier Chapter 7 slice-bridge pattern from `Chap07.Text_35_5_1`, where the first-variable
  partial owner is likewise obtained by specializing an existing one-variable owner to a fixed
  slice.

Primitive data vs derived API:
- primitive owner data: the existing directional-derivative owners on functions;
- derived API: the slice-identification lemmas below for the two partial directions.

Layer target: `bridge/view`.
-/

/- Text 35.5.3 uses the existing Chapter 23 owner for directional derivatives, specialized to the
uncurried bifunction `Function.uncurry K`; no separate saddle-directional-derivative owner should
be introduced here. -/
recall Function.HasDirectionalDerivativeAt

/- The proof route also uses the Chapter 23 directional-difference-quotient owner directly. -/
recall Function.directionalDifferenceQuotientAt

/- The value-level owner is likewise the existing Chapter 23 directional derivative. -/
recall Function.directionalDerivativeAt

namespace Function

/-- Text 35.5.3, first-variable quotient bridge:
the mixed-direction quotient in direction `(u', 0)` is exactly the quotient of the first-variable
slice `K · v` in direction `u'`. -/
@[simp] theorem directionalDifferenceQuotientAt_uncurry_first_eq
    [AddCommMonoid U] [SMul 𝕜 U]
    [AddCommMonoid X] [SMulZeroClass 𝕜 X]
    (K : U → X → WithTopBot 𝕜) (u : U) (v : X) (u' : U) :
    directionalDifferenceQuotientAt (uncurry K) (u, v) (u', 0) =
      directionalDifferenceQuotientAt (K · v) u u' := by
  funext t
  simp [directionalDifferenceQuotientAt, uncurry]

/-- Text 35.5.3, second-variable quotient bridge:
the mixed-direction quotient in direction `(0, v')` is exactly the quotient of the second-variable
slice `K u` in direction `v'`. -/
@[simp] theorem directionalDifferenceQuotientAt_uncurry_second_eq
    [AddCommMonoid U] [SMulZeroClass 𝕜 U]
    [AddCommMonoid X] [SMul 𝕜 X]
    (K : U → X → WithTopBot 𝕜) (u : U) (v : X) (v' : X) :
    directionalDifferenceQuotientAt (uncurry K) (u, v) (0, v') =
      directionalDifferenceQuotientAt (K u) v v' := by
  funext t
  simp [directionalDifferenceQuotientAt, uncurry]

section Topology

variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]

/-- Text 35.5.3, first-variable owner bridge:
existence of `K'(u, v; u', 0)` is exactly existence of the directional derivative of `K · v` at
`u` in direction `u'`. -/
@[simp] theorem hasDirectionalDerivativeAt_uncurry_first_iff
    [AddCommMonoid U] [SMul 𝕜 U]
    [AddCommMonoid X] [SMulZeroClass 𝕜 X]
    (K : U → X → WithTopBot 𝕜) (u : U) (v : X) (u' : U) (L : WithTopBot 𝕜) :
    HasDirectionalDerivativeAt (uncurry K) (u, v) (u', 0) L ↔
      HasDirectionalDerivativeAt (K · v) u u' L := by
  simp [HasDirectionalDerivativeAt, directionalDifferenceQuotientAt_uncurry_first_eq]

/-- Text 35.5.3, second-variable owner bridge:
existence of `K'(u, v; 0, v')` is exactly existence of the directional derivative of `K u` at `v`
in direction `v'`. -/
@[simp] theorem hasDirectionalDerivativeAt_uncurry_second_iff
    [AddCommMonoid U] [SMulZeroClass 𝕜 U]
    [AddCommMonoid X] [SMul 𝕜 X]
    (K : U → X → WithTopBot 𝕜) (u : U) (v : X) (v' : X) (L : WithTopBot 𝕜) :
    HasDirectionalDerivativeAt (uncurry K) (u, v) (0, v') L ↔
      HasDirectionalDerivativeAt (K u) v v' L := by
  simp [HasDirectionalDerivativeAt, directionalDifferenceQuotientAt_uncurry_second_eq]

/-- Text 35.5.3, first-variable slice form: the partial directional derivative
`K'(u, v; u', 0)` is exactly the directional derivative of the slice `fun u'' ↦ K u'' v`
at `u` in the direction `u'`. -/
@[simp] theorem directionalDerivativeAt_uncurry_first_eq
    [AddCommMonoid U] [SMul 𝕜 U]
    [AddCommMonoid X] [SMulZeroClass 𝕜 X]
    (K : U → X → WithTopBot 𝕜) (u : U) (v : X) (u' : U) :
    directionalDerivativeAt (uncurry K) (u, v) (u', 0) =
      directionalDerivativeAt (K · v) u u' := by
  simp [directionalDerivativeAt, directionalDifferenceQuotientAt_uncurry_first_eq]

/-- Text 35.5.3, second-variable slice form: the partial directional derivative
`K'(u, v; 0, v')` is exactly the directional derivative of the slice `K u`
at `v` in the direction `v'`. -/
@[simp] theorem directionalDerivativeAt_uncurry_second_eq
    [AddCommMonoid U] [SMulZeroClass 𝕜 U]
    [AddCommMonoid X] [SMul 𝕜 X]
    (K : U → X → WithTopBot 𝕜) (u : U) (v : X) (v' : X) :
    directionalDerivativeAt (uncurry K) (u, v) (0, v') =
      directionalDerivativeAt (K u) v v' := by
  simp [directionalDerivativeAt, directionalDifferenceQuotientAt_uncurry_second_eq]

end Topology

end Function

end
