import Mathlib
import stacks_project.Chap10.Lemma_10_97_3
import stacks_project.Chap10.Lemma_10_97_6
import stacks_project.Chap10.Lemma_10_163_8
import stacks_project.Chap15.Lemma_15_51_4

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open Algebra

universe u

namespace Algebra

/-- The canonical `FieldAlgebraProperty` bridge for ordinary normality. -/
abbrev IsNormalProperty : FieldAlgebraProperty :=
  fun k A ↦ fun [Field k] [CommRing A] [Algebra k A] ↦ IsNormalRing A

end Algebra

section

/-
Domain-style sampling:
- primary domain: normality of Noetherian local rings, formal fibers, and maximal-ideal
  completion;
- sampled owner declarations:
  `LocalFormalFibersHaveProperty`,
  `IsNormalProperty`,
  `adicCompletion_isNoetherianRing`,
  `maximalIdeal_adicCompletion_algebraMap_faithfullyFlat`,
  `isNormalRing_of_flat_of_fiber`;
- best owner abstraction: the source-facing extra hypothesis is the chapter owner
  `LocalFormalFibersHaveProperty`, while the conclusion is obtained from the canonical ascent
  theorem `isNormalRing_of_flat_of_fiber`;
- primitive data: `IsNormalRing A` and the fiberwise normality hypothesis for the completion map
  `A → A^∧`;
- derived API: the bridge `IsNormalProperty`, reusing the upstream specialization of
  `FieldAlgebraProperty` instead of a file-local alias.

Source/core/bridge triage:
- `source-facing`: the normality statement for the maximal-ideal completion;
- `core/canonical`: `LocalFormalFibersHaveProperty` and `isNormalRing_of_flat_of_fiber`;
- `bridge/view`: `IsNormalProperty`.
-/
variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

-- Proof sketch: the completion map `A → ACompletion` is flat for Noetherian local rings. Apply
-- `isNormalRing_of_flat_of_fiber` to this map, using the normality of `A` and the owner
-- hypothesis `LocalFormalFibersHaveProperty IsNormalProperty A`.
/-- Lemma 15.52.6: if a Noetherian local ring `A` is normal and has normal formal fibers, then its
maximal-ideal completion `AdicCompletion (maximalIdeal A) A` is normal; in particular this
applies when the formal fibers are normal because `A` is excellent or quasi-excellent. -/
theorem isNormalRing_maximalIdeal_adicCompletion_of_normal_formalFibers
    [IsNormalRing A]
    (hformal : LocalFormalFibersHaveProperty IsNormalProperty A) :
    IsNormalRing ACompletion := by
  let _ : IsNoetherianRing ACompletion :=
    adicCompletion_isNoetherianRing (maximalIdeal A)
  let _ : Module.Flat A ACompletion :=
    (maximalIdeal_adicCompletion_algebraMap_faithfullyFlat A).flat
  simpa using isNormalRing_of_flat_of_fiber hformal

end
