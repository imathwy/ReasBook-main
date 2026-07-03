import Mathlib
import StacksProject_2024.Chap13.Definition_13_34_1
import StacksProject_2024.Chap15.Situation_15_92_15
import StacksProject_2024.Chap15.Definition_15_59_13
import StacksProject_2024.Chap15.Definition_15_92_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ComplexShape
open Opposite
open scoped KoszulComplex

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A] {r : ℕ}

local notation "DMod" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.92.16:
- primary domain: derived-category realizations of the powered Koszul tower and sequential derived
  limits of its tensor image;
- sampled owner declarations:
  `koszulPowerInverseSystem`,
  `ComplexShape.embeddingDownNat.extendFunctor`,
  `DerivedCategory.Q`,
  `DerivedCategory.IsDerivedCompleteWithRespectTo`;
- best owner abstraction: the source-facing derived tower should be obtained from the chapter owner
  `koszulPowerInverseSystem` by the canonical extension-and-localization functor, rather than by a
  parallel stage alias in this file;
- primitive data: the powered Koszul inverse system from Situation `15.92.15`;
- derived API: the tensor tower and the derived-completeness statement for a chosen derived limit.

Source/core/bridge triage:
- `source-facing`: the powered Koszul tensor tower in `D(A)` and the derived-completeness theorem
  for its derived limit;
- `core/canonical`: `koszulPowerInverseSystem`, `ComplexShape.embeddingDownNat.extendFunctor`,
  `DerivedCategory.Q`, and `K.IsDerivedCompleteWithRespectTo I`;
- `bridge/view`: the canonical stage object
  `(derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n)`. -/

/-- The inverse system in `D(A)` whose `n`th stage is the derived tensor product of the `n`th
powered Koszul complex with the fixed object `K`. This is the library-facing model of the tower
`(K \otimes_A^{\mathbf L} K_n^\bullet)_n`. -/
abbrev derivedCompletionKoszulPowerTensorDerivedInverseSystem
    (K : DMod) (f : Fin r → A) : ℕᵒᵖ ⥤ DMod :=
  derivedCompletionKoszulPowersDerivedInverseSystem f ⋙ derivedTensorProduct K

-- Proof sketch: Lemma `15.28.6` makes each generator `f i` act null-homotopically on every
-- powered Koszul stage, so each tensor stage satisfies the stagewise annihilation hypothesis from
-- Lemma `15.92.14`. Applying that lemma to the chosen derived limit gives derived completeness.
/-- Lemma 15.92.16: in Situation `15.92.15`, if `K'` is a chosen derived limit of the inverse
system obtained by applying the derived tensor functor `- \otimes_A^{\mathbf L} K` to the powered
Koszul tower `(K_n^\bullet)_n`, then `K'` is derived complete with respect to the ideal
`I = (f_1, \ldots, f_r)`. This is the library-facing form of the textbook object
`R \!\varprojlim (K \otimes_A^{\mathbf L} K_n^\bullet)`. -/
theorem derivedLimitOfKoszulPowerTensor_isDerivedCompleteWithRespectTo_spanRange
    (f : Fin r → A) (K K' : DMod)
    (hlim : IsDerivedLimit (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) K') :
    K'.IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f)) := sorry

end

end CategoryTheory
