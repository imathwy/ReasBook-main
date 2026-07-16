import StacksProject_2024.stacks_project.Chap20.«20_14_1_1»
import StacksProject_2024.stacks_project.Chap20.Lemma_20_36_1
import StacksProject_2024.stacks_project.Chap20.Lemma_20_39_2

open CategoryTheory
open CategoryTheory.SequentialInverseSystem
open AlgebraicGeometry
open OrderHom
open SequentialProObjectMorphismRep

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X
local notation "ModΓX" => ModuleCat (globalSectionsRing X)
local notation "RΓ" => moduleDerivedGlobalSections X
local notation "HΓ" => DerivedCategory.homologyFunctor ModΓX

/- Domain-style sampling for Example 20.39.3:
- primary domain: the quotient-tower replacement step in the inverse-system comparison for
  `RΓ(X, ℱ)`;
- sampled owner declarations:
  `globalSectionMul`,
  `endomorphismPowerCokernelTower`,
  `endomorphismPowerTwoTermTower`,
  `SequentialInverseSystem.IsProIsomorphic`,
  `SequentialProObjectMorphismRep.mapRep`,
  `exists_cokernel_to_endomorphismPowerTwoTerm_shiftedProIsomorphism`;
- best owner abstraction:
  `source-facing`: the replacement of the middle tower
    `H^p(X, E_n)` by `H^p(X, ℱ / f^(n + 1)ℱ)` under eventual stabilization of `ℱ[f^n]`;
  `core/canonical`: `globalSectionMul`, `endomorphismPowerCokernelTower`,
    `endomorphismPowerTwoTermTower`, `SequentialInverseSystem.IsProIsomorphic`, and
    `SequentialProObjectMorphismRep.mapRep`;
  `bridge/view`: postcomposing the ringed-space specialization of Lemma 20.39.2 with derived
    global sections and homology;
- primitive vs. derived:
  primitive data are the ringed space `X`, the global section `f`, the module `ℱ`, and the
  endomorphism `globalSectionMul f ℱ`;
  derived API is the induced cohomology-level pro-isomorphism between the quotient and two-term
  towers.

Source/core/bridge triage:
- `source-facing`: the quotient-tower replacement step used in Example 20.39.3;
- `core/canonical`: `globalSectionMul`, `endomorphismPowerCokernelTower`,
  `endomorphismPowerTwoTermTower`, `SequentialInverseSystem.IsProIsomorphic`, and
  `SequentialProObjectMorphismRep.mapRep`;
- `bridge/view`: the cohomology towers obtained by postcomposing with `RΓ` and `HΓ p`. -/

section

-- Proof sketch: specialize Lemma 20.39.2 to the endomorphism `globalSectionMul f ℱ` of the
-- module `ℱ`, then postcompose the resulting tower comparison by the derived global-
-- sections functor and the `p`th homology functor. This yields the cohomology-level quotient-
-- tower replacement used in Example 20.39.3.
/-- Example 20.39.3, stable quotient-tower replacement: if the kernels `ℱ[f^n]` stabilize, then
for every `p : ℤ` the inverse system `(H^p(X, ℱ / f^(n + 1)ℱ))_n` is pro-isomorphic to the
inverse system obtained from the two-term complexes `E_n = ℱ ⊗_{𝒪_X} (𝒪_X ⟶ 𝒪_X)`, where the
displayed arrow is multiplication by `f^(n + 1)`.
This is the source-facing bridge step used to replace the middle tower in the diagram of Lemma
20.39.1. -/
@[stacks 0H3E]
theorem exists_quotientCohomologyTower_shiftedProIsomorphism
    (f : globalSectionsRing X) (ℱ : ModX) (p : ℤ)
    (hstable : endomorphismPowerKernelStabilizes (globalSectionMul f ℱ)) :
    ∃ c : ℕ,
      ∃ comparison :
        shift ((endomorphismPowerCokernelTower (globalSectionMul f ℱ)) ⋙ RΓ ⋙ HΓ p) c ⟶
          ((endomorphismPowerTwoTermTower (globalSectionMul f ℱ)) ⋙ RΓ ⋙ HΓ p),
        (ofShiftNatTrans c comparison).IsProIsomorphism := by
  let G := RΓ ⋙ HΓ p
  obtain ⟨c, comparison, hcomparison⟩ :=
    exists_cokernel_to_endomorphismPowerTwoTerm_shiftedProIsomorphism
      (globalSectionMul f ℱ) hstable
  refine ⟨c, Functor.whiskerRight comparison G, ?_⟩
  simpa [G, shift] using isProIsomorphism_mapRep G hcomparison

/- The companion above exposes the actual shifted comparison morphism. The theorem below keeps the
bundled `IsProIsomorphic` surface used downstream in Example 20.39.3. -/
@[stacks 0H3E]
theorem quotientCohomologyTower_isProIsomorphic
    (f : globalSectionsRing X) (ℱ : ModX) (p : ℤ)
    (hstable : endomorphismPowerKernelStabilizes (globalSectionMul f ℱ)) :
    IsProIsomorphic
      ((endomorphismPowerCokernelTower (globalSectionMul f ℱ)) ⋙ RΓ ⋙ HΓ p)
      ((endomorphismPowerTwoTermTower (globalSectionMul f ℱ)) ⋙ RΓ ⋙ HΓ p) := by
  obtain ⟨c, comparison, hcomparison⟩ :=
    exists_quotientCohomologyTower_shiftedProIsomorphism f ℱ p hstable
  exact ⟨ofShiftNatTrans c comparison, hcomparison⟩

end

end AlgebraicGeometry.RingedSpace
