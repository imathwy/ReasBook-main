import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.Definition_17_10_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Remark 17.10.3:
- primary domain: quasi-coherent `\mathcal O_X`-modules on ringed spaces and arbitrary direct
  sums/coproducts;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `SheafOfModules.IsQuasicoherent`,
  `SheafOfModules.isQuasicoherent`,
  `ringedSpaceModule_sigmaComparison_isIso_of_isCompact`;
- best owner abstraction: the ambient owner is `(RingedSpace.Modules X)` with the owner predicate
  `SheafOfModules.IsQuasicoherent`; the direct sum from the source is the categorical coproduct
  `∐ ℱ`;
- primitive data: a ringed space `X`, an index type `I`, and a family
  `ℱ : I → RingedSpace.Modules X`;
- derived API: the source-facing existence statement that even when every `ℱ i` is
  quasi-coherent, the coproduct `∐ ℱ` need not be.

Layer triage:
- `source-facing`: the warning that infinite direct sums of quasi-coherent modules need not remain
  quasi-coherent;
- `core/canonical`: `RingedSpace.Modules` and `SheafOfModules.IsQuasicoherent`;
- `bridge/view`: the categorical coproduct `∐ ℱ`, viewed as the direct sum from the source.
-/

-- Proof sketch: the source gives this as a warning rather than a construction. The canonical Lean
-- shape is therefore an existence statement over the owner category `(RingedSpace.Modules X)` and
-- its coproducts.
/-- Remark 17.10.3: in general, an infinite direct sum of quasi-coherent
`\mathcal O_X`-modules need not be quasi-coherent. -/
theorem exists_infinite_directSum_of_quasicoherent_not_quasicoherent :
    ∃ (X : RingedSpace.{u}) (I : Type u) (_ : Infinite I) (ℱ : I → RingedSpace.Modules X),
      (∀ i, (ℱ i).IsQuasicoherent) ∧ ¬ (∐ ℱ).IsQuasicoherent := by
  sorry

end AlgebraicGeometry
