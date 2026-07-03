import Mathlib
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Definition_15_59_13
import StacksProject_2024.Chap15.«15_74_0_2»
import StacksProject_2024.Chap15.Lemma_15_59_14
import StacksProject_2024.Chap15.Lemma_15_102_Basic

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped DerivedTensorProduct IdealPowerSubmodule

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "single₀" => (ModuleCat.single0Functor : ModuleCat A ⥤ DMod)

/- Domain-style sampling for Lemma 15.102.7:
- primary domain: eventual factorization in `D(A)` of the ideal-power inclusion through the first
  stage of the derived ideal-power tensor tower;
- sampled owner declarations:
  `idealPowerStage`,
  `idealPowerSubtype`,
  `derivedTensorProduct`,
  `singleZeroDerivedTensorIso`;
- best owner abstraction: the source-facing factorization should reuse the chapter owner
  `singleZeroDerivedTensorIso` for the canonical tensor-unit identification
  `A[0] \otimes_A^{\mathbf L} M[0] ≅ M[0]`, rather than restating that bridge by an expanded
  whiskered composite;
- primitive data: the ideal `I`, the finite module `M`, and the canonical inclusion
  `idealPowerSubtype I n M`;
- derived API: the existence of a power `n` and a factorization of that inclusion through
  `I[0] \otimes_A^{\mathbf L} M[0]`.

Source/core/bridge triage:
- `source-facing`: the eventual factorization statement below;
- `core/canonical`: `idealPowerStage`, `idealPowerSubtype`, and `derivedTensorProduct`;
- `bridge/view`: `singleZeroDerivedTensorIso`, identifying `A[0] \otimes_A^{\mathbf L} -` with the
  identity on `D(A)`. -/

-- Proof sketch: view `M` as the complex `M[0]` and apply Lemma `15.102.6` to compare the tower
-- `(I^n \otimes_A^{\mathbf L} M[0])_n` with `(I^n M[0])_n`. For sufficiently large `n`, the map
-- `I^n M[0] → M[0]` is represented by the tensor-stage map coming from the inclusion
-- `I^n ⟶ I ⟶ A`, followed by the canonical tensor-unit identification
-- `A[0] \otimes_A^{\mathbf L} M[0] ≅ M[0]`.
/-- Lemma 15.102.7: if `A` is Noetherian, `I ⊆ A` is an ideal, and `M` is a finite `A`-module,
then for some integer `n > 0` the canonical map `I^n M[0] → M[0]` in `D(A)` factors through the
map induced by `I → A`,
`I[0] \otimes_A^{\mathbf L} M[0] → A[0] \otimes_A^{\mathbf L} M[0]`,
together with the canonical tensor-unit identification
`A[0] \otimes_A^{\mathbf L} M[0] ≅ M[0]`. -/
theorem exists_idealPower_inclusion_factorization_through_ideal_derivedTensor_map
    (I : Ideal A) (M : ModuleCat A) [Module.Finite A M] :
    ∃ n : ℕ, 0 < n ∧
      ∃ α : (single₀).obj (idealPowerStage I n M) ⟶
          (single₀).obj (ModuleCat.of A ↥I) ⊗[A]^L (single₀).obj M,
        α ≫
            (derivedTensorProduct ((single₀).obj M)).map
              ((single₀).map (ModuleCat.ofHom I.subtype)) ≫
            (singleZeroDerivedTensorIso ((single₀).obj M)).hom =
          (single₀).map (ModuleCat.ofHom (idealPowerSubtype I n M)) := sorry

end

end CategoryTheory
