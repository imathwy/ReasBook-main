import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
import StacksProject_2024.Chap13.Definition_13_3_6
import StacksProject_2024.Chap13.Lemma_13_4_21
import StacksProject_2024.Chap13.Lemma_13_4_22
import StacksProject_2024.Chap13.Lemma_13_16_3
import StacksProject_2024.Chap13.Definition_13_34_1
import StacksProject_2024.Chap15.Lemma_15_87_14_Emmanouil
import StacksProject_2024.Chap15.Lemma_15_94_9
import StacksProject_2024.Chap15.Remark_15_94_7
import StacksProject_2024.Chap20.Global_sections_cohomology_delta_functor
import StacksProject_2024.Chap20.Lemma_20_11_2
import StacksProject_2024.Chap20.Lemma_20_36_1
import StacksProject_2024.Chap20.Lemma_20_36_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.CohomologicalDeltaFunctor
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open DerivedCategory.TStructure
open CategoryTheory.SequentialInverseSystem
open ShortComplex.ShortExact
open scoped IdealPowerTorsion PrincipalTateModule

noncomputable section

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow_isLocalization

universe u v

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "ModX" => X.Modules
local notation "ModΓX" => ModuleCat (globalSectionsRing X)

/- Domain-style sampling for Remark 20.36.6:
- primary domain: cohomology towers of principal-power quotient and torsion inverse systems in
  `ModuleCat (globalSectionsRing X)`, together with inverse limits and `R¹ lim`;
- sampled owner declarations:
  `ShortComplex.ShortExact.singleδ`,
  `DeltaFunctor.postcomposeExactFunctor`,
  `DeltaFunctor.toCohomologicalDeltaFunctor`,
  `CohomologicalDeltaFunctor.δ`,
  `globalSectionPowerQuotientTower`,
  `principalPowerQuotientTower`,
  `principalPowerTorsionTower`,
  `SequentialInverseSystem.firstDerivedLimit`;
- best owner abstraction: the ambient owner for the quotient tower of `ℱ` is the
  Chapter 20 owner `globalSectionPowerQuotientTower f ℱ`; the cohomology connecting morphism is
  owned canonically by the short-exact-sequence boundary `singleδ`, postcomposed with the derived
  global-sections owner and then converted to a cohomological `δ`-functor; the
  degree-one Milnor term plus its comparison morphism are owned by
  `SequentialInverseSystem.firstDerivedLimit` and
  `SequentialInverseSystem.firstDerivedLimitMap`; the source-facing content of this file is the
  geometric specialization to the cohomology towers built from
  `globalSectionPowerQuotientTower`, `principalPowerQuotientTower`, and
  `principalPowerTorsionTower`;
- primitive vs. derived:
  primitive data are the ringed space `X`, the global section `f`, the module `ℱ`, and the
  quotient/torsion towers together with the canonical short exact row
  `0 → ℱ ⟶ ℱ ⟶ ℱ / f^(n + 1)ℱ → 0`, where the first map is multiplication by `f^(n + 1)`;
  derived API is the short exact tower sequence, the induced completion sequence, and the induced
  comparison map on `R¹ lim`.

Source/core/bridge triage:
- `source-facing`: the four parts of Remark `20.36.6` for the geometric cohomology towers;
- `core/canonical`: `SequentialInverseSystem.firstDerivedLimit`,
  `SequentialInverseSystem.firstDerivedLimitMap`, `principalPowerQuotientTower`,
  `principalPowerTorsionTower`, `principalTateModule`, `ShortComplex.ShortExact.singleδ`, and the
  derived global-sections functor;
- `bridge/view`: the middle cohomology tower obtained by applying the canonical global-sections
  cohomology degree functor to `globalSectionPowerQuotientTower f ℱ`, with stagewise connecting
  maps induced by `CohomologicalDeltaFunctor.δ` on the canonical quotient short exact rows. -/

section

variable (f : globalSectionsRing X) (ℱ : X.Modules)
variable (p : ℕ)

/-- The inverse system `n ↦ H^p(X, ℱ / f^(n + 1)ℱ)` attached to a global section `f`. -/
abbrev globalSectionPowerQuotientCohomologyTower
    (f : globalSectionsRing X) (ℱ : ModX) (p : ℕ) :
    SequentialInverseSystem ModΓX :=
  globalSectionPowerQuotientTower f ℱ ⋙ (globalCohomologyDeltaFunctor X p).obj

/-- The inverse system `n ↦ H^p(X, ℱ)[f^(n + 1)]` attached to a global section `f`. -/
abbrev globalCohomologyPowerTorsionTower
    (f : globalSectionsRing X) (ℱ : ModX) (p : ℕ) :
    SequentialInverseSystem ModΓX :=
  principalPowerTorsionTower f (((globalCohomologyDeltaFunctor X p).obj).obj ℱ)

private abbrev cohomologyToQuotientStageMap
    (f : globalSectionsRing X) (ℱ : ModX) (p n : ℕ) :
    ((globalCohomologyDeltaFunctor X p).obj).obj ℱ ⟶
      (globalSectionPowerQuotientCohomologyTower f ℱ p).obj (op n) :=
  ((globalCohomologyDeltaFunctor X p).obj).map
    (cokernel.π (globalSectionMulPow f ℱ (n + 1)))

/-- Helper for Remark 20.36.6: on the degree-`p` branch of the local cohomology `δ`-functor,
`globalSectionMulPow` acts as scalar multiplication by `f^n`. -/
private theorem globalCohomologyDegree_map_globalSectionMulPow_eq_smul
    (f : globalSectionsRing X) (ℱ : ModX) (p n : ℕ) :
    ((globalCohomologyDeltaFunctor X p).obj).map (globalSectionMulPow f ℱ n) =
      ((f ^ n) • 𝟙 (((globalCohomologyDeltaFunctor X p).obj).obj ℱ)) := by
  simpa using cohomology_map_globalSectionMulPow_eq_smul f p ℱ n

private theorem cohomologyToQuotientStageMap_ker_le
    (f : globalSectionsRing X) (ℱ : ModX) (p n : ℕ) :
    principalPowerSubmodule
        f (((globalCohomologyDeltaFunctor X p).obj).obj ℱ) (n + 1) ≤
      LinearMap.ker (cohomologyToQuotientStageMap f ℱ p n).hom := by
  intro x hx
  rw [LinearMap.mem_ker]
  rcases exists_eq_smul_of_mem_principalPower_smul_top f hx with ⟨y, rfl⟩
  have hmul :
      (((globalCohomologyDeltaFunctor X p).obj).map
          (globalSectionMulPow f ℱ (n + 1))).hom y =
        (f ^ (n + 1)) • y := by
    simpa using
      congrArg (fun t ↦ ModuleCat.Hom.hom t y)
        (globalCohomologyDegree_map_globalSectionMulPow_eq_smul f ℱ p (n + 1))
  have hzero :
      ((globalCohomologyDeltaFunctor X p).obj).map
          (globalSectionMulPow f ℱ (n + 1)) ≫
        cohomologyToQuotientStageMap f ℱ p n =
      0 := by
    calc
      ((globalCohomologyDeltaFunctor X p).obj).map
          (globalSectionMulPow f ℱ (n + 1)) ≫
        cohomologyToQuotientStageMap f ℱ p n
          =
        ((globalCohomologyDeltaFunctor X p).obj).map
          (globalSectionMulPow f ℱ (n + 1) ≫
            cokernel.π (globalSectionMulPow f ℱ (n + 1))) := by
              simpa [cohomologyToQuotientStageMap] using
                (Functor.map_comp ((globalCohomologyDeltaFunctor X p).obj)
                  (globalSectionMulPow f ℱ (n + 1))
                  (cokernel.π (globalSectionMulPow f ℱ (n + 1)))).symm
      _ = ((globalCohomologyDeltaFunctor X p).obj).map 0 := by simp
      _ = 0 := by
            simpa using
              (Functor.map_zero ((globalCohomologyDeltaFunctor X p).obj) ℱ
                (cokernel (globalSectionMulPow f ℱ (n + 1))))
  have hzero_apply :
      (((globalCohomologyDeltaFunctor X p).obj).map
          (globalSectionMulPow f ℱ (n + 1)) ≫
        cohomologyToQuotientStageMap f ℱ p n).hom y =
      0 := by
    simpa using congrArg (fun t ↦ ModuleCat.Hom.hom t y) hzero
  calc
    (cohomologyToQuotientStageMap f ℱ p n).hom ((f ^ (n + 1)) • y)
        =
      (cohomologyToQuotientStageMap f ℱ p n).hom
        ((((globalCohomologyDeltaFunctor X p).obj).map
          (globalSectionMulPow f ℱ (n + 1))).hom y) := by
            rw [hmul.symm]
    _ =
      (((globalCohomologyDeltaFunctor X p).obj).map
          (globalSectionMulPow f ℱ (n + 1)) ≫
        cohomologyToQuotientStageMap f ℱ p n).hom y := by
          rfl
    _ = 0 := hzero_apply

private abbrev cohomologyBoundaryShortComplex
    (f : globalSectionsRing X) (ℱ : ModX) (n : ℕ) :
    ShortComplex ModX :=
  ShortComplex.mk
    (globalSectionMulPow f ℱ (n + 1))
    (cokernel.π (globalSectionMulPow f ℱ (n + 1)))
    (cokernel.condition (globalSectionMulPow f ℱ (n + 1)))

private theorem cohomologyBoundaryShortComplex_shortExact
    (f : globalSectionsRing X) (ℱ : ModX)
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) (n : ℕ) :
    (cohomologyBoundaryShortComplex f ℱ n).ShortExact := by
  let _ : Mono (globalSectionMulPow f ℱ (n + 1)) :=
    by
      letI : Mono (globalSectionMul f ℱ) := hℱ
      infer_instance
  refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
  simpa [cohomologyBoundaryShortComplex] using
    (ShortComplex.exact_cokernel (globalSectionMulPow f ℱ (n + 1)))

private theorem cohomologyToQuotientStageMap_step
    (f : globalSectionsRing X) (ℱ : ModX) (p n : ℕ) :
    cohomologyToQuotientStageMap f ℱ p (n + 1) ≫
        (globalSectionPowerQuotientCohomologyTower f ℱ p).map (homOfLE (Nat.le_succ n)).op =
      cohomologyToQuotientStageMap f ℱ p n := by
  have hπ :
      cokernel.π (globalSectionMulPow f ℱ (n + 2)) ≫
        globalSectionPowerQuotientTransition f ℱ n =
      cokernel.π (globalSectionMulPow f ℱ (n + 1)) := by
    simp [globalSectionPowerQuotientTransition]
  have hmap :
      ((globalCohomologyDeltaFunctor X p).obj).map
          (cokernel.π (globalSectionMulPow f ℱ (n + 2))) ≫
        ((globalCohomologyDeltaFunctor X p).obj).map
          (globalSectionPowerQuotientTransition f ℱ n) =
      ((globalCohomologyDeltaFunctor X p).obj).map
        (cokernel.π (globalSectionMulPow f ℱ (n + 1))) := by
    calc
      ((globalCohomologyDeltaFunctor X p).obj).map
          (cokernel.π (globalSectionMulPow f ℱ (n + 2))) ≫
        ((globalCohomologyDeltaFunctor X p).obj).map
          (globalSectionPowerQuotientTransition f ℱ n)
          =
        ((globalCohomologyDeltaFunctor X p).obj).map
          (cokernel.π (globalSectionMulPow f ℱ (n + 2)) ≫
            globalSectionPowerQuotientTransition f ℱ n) := by
              rw [← Functor.map_comp]
      _ = ((globalCohomologyDeltaFunctor X p).obj).map
            (cokernel.π (globalSectionMulPow f ℱ (n + 1))) := by
              rw [hπ]
  have hmap' :
      cohomologyToQuotientStageMap f ℱ p (n + 1) ≫
          (globalSectionPowerQuotientCohomologyTower f ℱ p).map (homOfLE (Nat.le_succ n)).op =
        ((globalCohomologyDeltaFunctor X p).obj).map
          (cokernel.π (globalSectionMulPow f ℱ (n + 1))) := by
    simpa [cohomologyToQuotientStageMap, globalSectionPowerQuotientCohomologyTower,
      Functor.comp_map] using hmap
  simpa [cohomologyToQuotientStageMap] using hmap'

/-- The canonical map from the quotient tower of `H^p(X, ℱ)` to the tower
`n ↦ H^p(X, ℱ / f^(n + 1)ℱ)`. -/
noncomputable def cohomologyTowerQuotientMap
    (f : globalSectionsRing X) (ℱ : ModX) (p : ℕ) :
    principalPowerQuotientTower f (((globalCohomologyDeltaFunctor X p).obj).obj ℱ) ⟶
      globalSectionPowerQuotientCohomologyTower f ℱ p :=
  NatTrans.ofOpSequence
    (fun n ↦
      ModuleCat.ofHom <|
        (principalPowerSubmodule
          f (((globalCohomologyDeltaFunctor X p).obj).obj ℱ) (n + 1)).liftQ
          (cohomologyToQuotientStageMap f ℱ p n).hom
          (cohomologyToQuotientStageMap_ker_le f ℱ p n))
    (fun n ↦ by
      ext x
      refine Quotient.inductionOn x ?_
      intro y
      simpa [globalSectionPowerQuotientCohomologyTower, principalPowerQuotientTower,
        principalPowerQuotientStep] using
        congrArg (fun t ↦ ModuleCat.Hom.hom t y)
          (cohomologyToQuotientStageMap_step f ℱ p n).symm)

private abbrev cohomologyBoundaryShortComplexStepHom
    (f : globalSectionsRing X) (ℱ : ModX) (n : ℕ) :
    cohomologyBoundaryShortComplex f ℱ (n + 1) ⟶
      cohomologyBoundaryShortComplex f ℱ n where
  τ₁ := globalSectionMul f ℱ
  τ₂ := 𝟙 ℱ
  τ₃ := globalSectionPowerQuotientTransition f ℱ n
  comm₁₂ := by
    simpa [cohomologyBoundaryShortComplex, Category.assoc] using
      globalSectionMul_comp_pow f ℱ (n + 1)
  comm₂₃ := by
    simp [cohomologyBoundaryShortComplex, globalSectionPowerQuotientTransition]

private theorem cohomologyToQuotientStageMap_comp_boundaryMap_zero
    (f : globalSectionsRing X) (ℱ : ModX)
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) (p n : ℕ) :
    cohomologyToQuotientStageMap f ℱ p n ≫
        (globalCohomologyDeltaFunctor X).δ
          (cohomologyBoundaryShortComplex_shortExact f ℱ hℱ n) p =
      0 := by
  simpa [cohomologyBoundaryShortComplex, cohomologyToQuotientStageMap] using
    ((globalCohomologyDeltaFunctor X).exact₅
      (cohomologyBoundaryShortComplex_shortExact f ℱ hℱ n) p).toIsComplex.zero 1

private theorem cohomologyBoundaryMap_mem_torsion
    (f : globalSectionsRing X) (ℱ : ModX)
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) (p n : ℕ)
    (x : (globalSectionPowerQuotientCohomologyTower f ℱ p).obj (op n)) :
    ((globalCohomologyDeltaFunctor X).δ
        (cohomologyBoundaryShortComplex_shortExact f ℱ hℱ n) p).hom x ∈
      ((((globalCohomologyDeltaFunctor X (p + 1)).obj).obj ℱ)[f ^ (n + 1)] :
        Submodule (globalSectionsRing X) (((globalCohomologyDeltaFunctor X (p + 1)).obj).obj ℱ)) := by
  rw [Submodule.mem_torsionBy_iff]
  have hδzero :
      (globalCohomologyDeltaFunctor X).δ
          (cohomologyBoundaryShortComplex_shortExact f ℱ hℱ n) p ≫
        ((globalCohomologyDeltaFunctor X (p + 1)).obj).map
          (globalSectionMulPow f ℱ (n + 1)) =
      0 := by
    simpa [cohomologyBoundaryShortComplex] using
      ((globalCohomologyDeltaFunctor X).exact₅
        (cohomologyBoundaryShortComplex_shortExact f ℱ hℱ n) p).toIsComplex.zero 2
  have hδzero_apply :
      (((globalCohomologyDeltaFunctor X).δ
            (cohomologyBoundaryShortComplex_shortExact f ℱ hℱ n) p) ≫
          ((globalCohomologyDeltaFunctor X (p + 1)).obj).map
            (globalSectionMulPow f ℱ (n + 1))).hom x =
        0 := by
    simpa using congrArg (fun t ↦ ModuleCat.Hom.hom t x) hδzero
  simpa [globalCohomologyDegree_map_globalSectionMulPow_eq_smul, Category.assoc] using
    hδzero_apply

private abbrev cohomologyTowerBoundaryMapApp
    (f : globalSectionsRing X) (ℱ : ModX) (p : ℕ)
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) (n : ℕ) :
    (globalSectionPowerQuotientCohomologyTower f ℱ p).obj (op n) ⟶
      (globalCohomologyPowerTorsionTower f ℱ (p + 1)).obj (op n) :=
  ModuleCat.ofHom <|
    LinearMap.codRestrict
      ((((globalCohomologyDeltaFunctor X (p + 1)).obj).obj ℱ)[f ^ (n + 1)] :
        Submodule (globalSectionsRing X) (((globalCohomologyDeltaFunctor X (p + 1)).obj).obj ℱ))
      (((globalCohomologyDeltaFunctor X).δ
        (cohomologyBoundaryShortComplex_shortExact f ℱ hℱ n) p).hom)
      (cohomologyBoundaryMap_mem_torsion f ℱ hℱ p n)

/-- The canonical boundary map from the cohomology quotient tower to the torsion tower of
`H^(p + 1)(X, ℱ)`. -/
noncomputable def cohomologyTowerBoundaryMap
    (f : globalSectionsRing X) (ℱ : ModX) (p : ℕ)
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    globalSectionPowerQuotientCohomologyTower f ℱ p ⟶
      globalCohomologyPowerTorsionTower f ℱ (p + 1) :=
  NatTrans.ofOpSequence
    (cohomologyTowerBoundaryMapApp f ℱ p hℱ)
    (fun _ ↦ by
      sorry)

private theorem cohomologyTowerMaps_comp_zero
    (f : globalSectionsRing X) (ℱ : ModX)
    (p : ℕ) (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    cohomologyTowerQuotientMap f ℱ p ≫ cohomologyTowerBoundaryMap f ℱ p hℱ = 0 := by
  sorry

/-- The canonical short complex of towers from Remark 20.36.6 (1). -/
noncomputable def cohomologyTowerShortComplex
    (f : globalSectionsRing X) (ℱ : ModX) (p : ℕ)
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    ShortComplex (SequentialInverseSystem ModΓX) :=
  ShortComplex.mk
    (cohomologyTowerQuotientMap f ℱ p)
    (cohomologyTowerBoundaryMap f ℱ p hℱ)
    (cohomologyTowerMaps_comp_zero f ℱ p hℱ)

/-- The left term of `cohomologyTowerShortComplex` is the principal-power quotient tower of
`H^p(X, ℱ)`. -/
@[simp] theorem cohomologyTowerShortComplex_X₁
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    (cohomologyTowerShortComplex f ℱ p hℱ).X₁ =
      principalPowerQuotientTower f (((globalCohomologyDeltaFunctor X p).obj).obj ℱ) := rfl

/-- The middle term of `cohomologyTowerShortComplex` is the cohomology quotient tower
`n ↦ H^p(X, ℱ / f^(n + 1)ℱ)`. -/
@[simp] theorem cohomologyTowerShortComplex_X₂
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    (cohomologyTowerShortComplex f ℱ p hℱ).X₂ =
      globalSectionPowerQuotientCohomologyTower f ℱ p := rfl

/-- The right term of `cohomologyTowerShortComplex` is the torsion tower
`n ↦ H^(p + 1)(X, ℱ)[f^(n + 1)]`. -/
@[simp] theorem cohomologyTowerShortComplex_X₃
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    (cohomologyTowerShortComplex f ℱ p hℱ).X₃ =
      globalCohomologyPowerTorsionTower f ℱ (p + 1) := rfl

/-- The left map of `cohomologyTowerShortComplex` is the canonical quotient comparison map. -/
@[simp] theorem cohomologyTowerShortComplex_f
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    (cohomologyTowerShortComplex f ℱ p hℱ).f = cohomologyTowerQuotientMap f ℱ p := rfl

/-- The right map of `cohomologyTowerShortComplex` is the canonical boundary map. -/
@[simp] theorem cohomologyTowerShortComplex_g
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    (cohomologyTowerShortComplex f ℱ p hℱ).g = cohomologyTowerBoundaryMap f ℱ p hℱ := rfl

/-- The canonical inverse-limit short complex from Remark 20.36.6 (2). -/
noncomputable def cohomologyCompletionShortComplex
    (f : globalSectionsRing X) (ℱ : ModX) (p : ℕ)
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    ShortComplex ModΓX :=
  (cohomologyTowerShortComplex f ℱ p hℱ).map lim

/-- The left term of `cohomologyCompletionShortComplex` is the inverse limit of the quotient tower
of `H^p(X, ℱ)`. -/
@[simp] theorem cohomologyCompletionShortComplex_X₁
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    (cohomologyCompletionShortComplex f ℱ p hℱ).X₁ =
      limit (principalPowerQuotientTower f (((globalCohomologyDeltaFunctor X p).obj).obj ℱ)) := rfl

/-- The middle term of `cohomologyCompletionShortComplex` is the inverse limit of the cohomology
quotient tower `n ↦ H^p(X, ℱ / f^(n + 1)ℱ)`. -/
@[simp] theorem cohomologyCompletionShortComplex_X₂
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    (cohomologyCompletionShortComplex f ℱ p hℱ).X₂ =
      limit (globalSectionPowerQuotientCohomologyTower f ℱ p) := rfl

/-- The right term of `cohomologyCompletionShortComplex` is the canonical principal Tate module
`T[f] H^(p + 1)(X, ℱ)`. -/
@[simp] theorem cohomologyCompletionShortComplex_X₃
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    (cohomologyCompletionShortComplex f ℱ p hℱ).X₃ =
      T[f] (((globalCohomologyDeltaFunctor X (p + 1)).obj).obj ℱ) := rfl

-- Proof sketch: apply the long exact cohomology sequence to the canonical short exact rows
-- `0 → ℱ ⟶ ℱ ⟶ ℱ / f^(n + 1)ℱ → 0`,
-- where the first map is multiplication by `f^(n + 1)`,
-- then identify the left and right terms with the quotient and torsion owners introduced above
-- and assemble the resulting stage maps into the tower short complex.
/-- Remark 20.36.6 (1): if multiplication by `f` on an `𝒪_X`-module `ℱ` is
injective, then the canonical sequence of inverse systems
`0 → (H^p(X, ℱ) / f^(n + 1)H^p(X, ℱ))_n →
  (H^p(X, ℱ / f^(n + 1)ℱ))_n →
  (H^(p + 1)(X, ℱ)[f^(n + 1)])_n → 0`
is short exact. -/
@[stacks 0H3A]
theorem cohomologyTowerShortComplex_shortExact
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    (cohomologyTowerShortComplex f ℱ p hℱ).ShortExact := by
  sorry

/-- Remark 20.36.6 (2): under the same torsion-free hypothesis, the canonical sequence
`0 → H^p(X, ℱ)^∧ → lim_n H^p(X, ℱ / f^(n + 1)ℱ) → T_f(H^(p + 1)(X, ℱ)) → 0`
is short exact. Here the right term is the canonical principal Tate-module owner from Example
`15.94.5`. -/
@[stacks 0H3A]
theorem cohomologyCompletionShortComplex_shortExact
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    (cohomologyCompletionShortComplex f ℱ p hℱ).ShortExact := by
  sorry

-- Proof sketch: use the six-term exact sequence for derived inverse limits on the short exact
-- system from part `(1)`. The left quotient tower is Mittag-Leffler by
-- `principalPowerQuotientTower_isMittagLeffler
--   f ((moduleCohomologyDegree p).obj ℱ)`, so its
-- `R¹ lim` term vanishes and the remaining two `R¹ lim` terms are compared
-- by the comparison map on `R¹ lim` induced by the right arrow of the short exact
-- tower sequence from part `(1)`.

/-- Remark 20.36.6 (3): under the same injectivity hypothesis, the canonical comparison morphism
on the degree-one Milnor terms
`R¹ lim_n H^p(X, ℱ / f^(n + 1)ℱ) ⟶
  R¹ lim_n H^(p + 1)(X, ℱ)[f^(n + 1)]`
is an isomorphism. -/
@[stacks 0H3A]
instance cohomologyTower_firstDerivedLimitMap_isIso
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    IsIso
      (SequentialInverseSystem.firstDerivedLimitMap
        (cohomologyTowerBoundaryMap f ℱ p hℱ)) := by
  sorry

/-- Object-level corollary of `cohomologyTower_firstDerivedLimitMap_isIso`. -/
theorem cohomologyTower_firstDerivedLimit_isomorphic
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    IsIsomorphic
      (globalSectionPowerQuotientCohomologyTower f ℱ p).firstDerivedLimit
      (globalCohomologyPowerTorsionTower f ℱ (p + 1)).firstDerivedLimit := by
  exact ⟨asIso (SequentialInverseSystem.firstDerivedLimitMap
    (cohomologyTowerBoundaryMap f ℱ p hℱ))⟩

-- Proof sketch: apply Remark `15.94.7` to the short exact sequence of cohomology towers from part
-- `(1)`. Since the left quotient tower is Mittag-Leffler by
-- `principalPowerQuotientTower_isMittagLeffler
--   f ((moduleCohomologyDegree p).obj ℱ)`, the middle tower is
-- Mittag-Leffler exactly when the right torsion tower is.
/-- Remark 20.36.6 (4): under the same injectivity hypothesis, the inverse system
`n ↦ H^(p + 1)(X, ℱ)[f^(n + 1)]` is Mittag-Leffler if and only if the inverse system
`n ↦ H^p(X, ℱ / f^(n + 1)ℱ)` is Mittag-Leffler. -/
@[stacks 0H3A]
theorem cohomologyTower_isMittagLeffler_iff_torsion
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    IsMittagLeffler (globalSectionPowerQuotientCohomologyTower f ℱ p) ↔
      IsMittagLeffler (globalCohomologyPowerTorsionTower f ℱ (p + 1)) := by
  let Hp := ((globalCohomologyDeltaFunctor X p).obj).obj ℱ
  let Hp1 := ((globalCohomologyDeltaFunctor X (p + 1)).obj).obj ℱ
  exact
    principalPower_shortExact_middle_isMittagLeffler_iff_torsion
      f Hp Hp1
      (globalSectionPowerQuotientCohomologyTower f ℱ p)
      (cohomologyTowerQuotientMap f ℱ p)
      (cohomologyTowerBoundaryMap f ℱ p hℱ)
      (cohomologyTowerMaps_comp_zero f ℱ p hℱ)
      (cohomologyTowerShortComplex_shortExact f ℱ p hℱ)

end

end AlgebraicGeometry.RingedSpace
