import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_5
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: this item names the condition that a bifunction is image-closed,
  meaning each second-variable slice `F u` is closed.
- `core/canonical`: this is already the Chapter 33 owner `Bifunction.IsConvexClosed`, i.e. the
  whole-space second-variable closedness.
- `bridge/view`: the slice-wise wording is already owned by `Bifunction.isConvexClosed_iff`, and
  the global graph-function route to this condition is the transfer theorem
  `Bifunction.lowerSemicontinuous_slice_of_closedb`.

Primary mathematical domain:
- slice-wise lower semicontinuity for bifunctions and its relation to lower semicontinuity of the
  uncurried graph function.

Domain-style sampling used here:
- `Bifunction.IsConvexClosed`;
- `Bifunction.isConvexClosed_iff`;
- `Bifunction.lowerSemicontinuous_slice_of_closedb`.

Primitive data vs derived API:
- primitive data: a bifunction `F : U → X → L`;
- primitive owner: `Bifunction.IsConvexClosed F`;
- derived bridge API: the slice-wise lower-semicontinuity characterization and the transfer from
  `closedᵇ(F)`.

Layer target: `bridge/view`. This item keeps the canonical Chapter 33 owner surface and the
primitive uncurry-to-slice lower-semicontinuity bridge at the same weak topological/preorder
layer, without importing downstream theorem files.
-/

section

open scoped Rockafellar

variable {U : Type u} {X : Type v} {L : Type w}
variable [TopologicalSpace U] [TopologicalSpace X]
variable [Preorder L]

-- Proof sketch: compose `Function.uncurry F` with the continuous map `x ↦ (u, x)`.
/-- Lower semicontinuity of the uncurried graph function transfers to each fixed-`u`
second-variable slice. -/
theorem lowerSemicontinuous_slice_of_uncurry
    {F : U → X → L} (hF : LowerSemicontinuous (Function.uncurry F)) (u : U) :
    LowerSemicontinuous (F u) := by
  let e : X → U × X := fun x => (u, x)
  have he : Continuous e := continuous_const.prodMk continuous_id
  simpa [Function.comp, Function.uncurry, e] using hF.comp he

-- Proof sketch: `closedᵇ(F)` is definitional notation for lower semicontinuity of
-- `Function.uncurry F`.
/-- Source-facing bridge: closedness of a bifunction graph implies lower semicontinuity of each
fixed-`u` second-variable slice. -/
theorem lowerSemicontinuous_slice_of_closedb
    {F : U → X → L} (hF : closedᵇ(F)) (u : U) :
    LowerSemicontinuous (F u) :=
  lowerSemicontinuous_slice_of_uncurry hF u

-- Proof sketch: apply `lowerSemicontinuous_slice_of_uncurry` pointwise in
-- `u` and rewrite the source-facing notation `closedᵇ`.
/-- Owner-level bridge: lower semicontinuity of the uncurried graph function implies
second-variable closedness in the Chapter 33 owner sense. -/
theorem IsConvexClosed.of_closedb
    {F : U → X → L} (hF : closedᵇ(F)) :
    IsConvexClosed F := by
  rw [isConvexClosed_iff]
  intro u
  exact lowerSemicontinuous_slice_of_uncurry hF u

end

/- Definition33.0.17: an image-closed bifunction is exactly a bifunction whose second-variable
slices are closed; in the Chapter 33 API this is the existing owner `Bifunction.IsConvexClosed`.
-/
recall Bifunction.IsConvexClosed

/- The slice-wise lower-semicontinuity formulation of this item is already the companion theorem
`Bifunction.isConvexClosed_iff`. -/
recall Bifunction.isConvexClosed_iff

end Bifunction
