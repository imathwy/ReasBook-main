import StacksProject_2024.Chap17.Definition_17_25_6
import StacksProject_2024.Chap20.Lemma_20_55_1
import StacksProject_2024.Chap20.Lemma_20_55_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X)] [SymmetricCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)] [Abelian (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X
local notation "CpxX" => CochainComplex ModX ℤ
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)
local notation "ℐ[" I "]" => ((I : ModX))

/- Domain-style sampling for Lemma 20.55.5:
- primary domain: the Berthelot-Ogus `η_ℐ` construction on cochain complexes of
  `𝒪_X`-modules, expressed in the ambient abelian monoidal category
  `RingedSpace.Modules X`;
- sampled owner declarations of the same kind:
  `CategoryTheory.Subobject`,
  `CategoryTheory.Subobject.arrow`,
  `CochainComplex`,
  `idealTensorAction`,
  `idealTorsionSubsheaf`,
  `idealTorsionSubsheafι`,
  `IsIdealTorsionFreeModule`,
  `tensorPowerSheafIntOneAddIso`,
  `kernel`,
  `cokernel`;
- best owner abstraction:
  `source-facing`: the Berthelot-Ogus complex `idealEtaComplex I K hK` and the cohomology
    comparison theorem below;
  `core/canonical`: the canonical complex owner `CochainComplex (RingedSpace.Modules X) ℤ`, the
  ideal action owner `idealTensorAction I`, the termwise torsion-free predicate
  `IsIdealTorsionFreeModule`, and the integral tensor-power owner `ℐ ^⊗ i`;
  `bridge/view`: the bidegree tensor term
    `idealEtaComplexTensorObj I K i j = ℐ[I]^⊗ i ⊗ 𝓕^j`, its
    diagonal and off-diagonal specializations, the kernel/cokernel presentation of each
    Berthelot-Ogus term, and the induced differential built from the ambient differential of `K`.
- primitive data: an ideal sheaf `I : Subobject 𝒪X`, a cochain complex `K`, and the termwise
  torsion-free owner `IsIdealTorsionFreeComplex I K`;
- derived API: the ambient terms, the off-diagonal differential targets, the quotient targets,
  the kernel terms, the induced differential, the assembled complex `idealEtaComplex I K hK`,
  and the final cohomology comparison with the source-facing torsion quotient
  `H^i(K) / H^i(K)[I]`.

This file therefore keeps the source-facing `η_ℐ` owners public, but it reuses the chapter owners
`idealTensorAction`, `idealTorsionSubsheaf`, `idealTorsionSubsheafι`, and
`IsIdealTorsionFreeModule` from Lemma `20.55.3`, together with the canonical tensor-power owner
`(^⊗)`, instead of carrying parallel local copies. In Situation `20.55.2`, the source-facing
assumption here is `[SatisfiesLocallyPrincipalRegularIdealCondition I]`; the
monomorphism of `I.arrow` and the invertibility of `ℐ` are derived owner-level API coming from
`Situation_20_55_2` and `Lemma_20_55_1`. The auxiliary off-diagonal tensor term
`ℐ[I]^⊗ i ⊗ 𝓕^(i + 1)` is bridge data for the Berthelot-Ogus
quotient presentation, not a second source-facing owner. -/

section TorsionFreeComplex

omit [SymmetricCategory (RingedSpace.Modules X)] [MonoidalClosed (RingedSpace.Modules X)] in
/- A complex of `𝒪_X`-modules is `I`-torsion free when each term is `I`-torsion free. -/
class IsIdealTorsionFreeComplex
    (I : Subobject 𝒪X) (K : CpxX) : Prop where
  /-- The degree-`i` term of the complex is `I`-torsion free. -/
  isIdealTorsionFree (i : ℤ) : IsIdealTorsionFreeModule I (K.X i)

omit [SymmetricCategory (RingedSpace.Modules X)] [MonoidalClosed (RingedSpace.Modules X)]
  [Abelian (RingedSpace.Modules X)] in
/-- `IsIdealTorsionFreeComplex I K` is equivalent to degreewise `I`-torsion-freeness. -/
theorem isIdealTorsionFreeComplex_iff
    (I : Subobject 𝒪X) (K : CpxX) :
    IsIdealTorsionFreeComplex I K ↔ ∀ i : ℤ, IsIdealTorsionFreeModule I (K.X i) := by
  constructor
  · intro h i
    exact h.isIdealTorsionFree i
  · intro h
    exact ⟨h⟩

omit [SymmetricCategory (RingedSpace.Modules X)] [MonoidalClosed (RingedSpace.Modules X)] in
instance (I : Subobject 𝒪X) (K : CpxX) [h : IsIdealTorsionFreeComplex I K] (i : ℤ) :
    IsIdealTorsionFreeModule I (K.X i) :=
  h.isIdealTorsionFree i

end TorsionFreeComplex

section EtaAuxiliary

local notation "Pη[" I "]" => IsIdealTorsionFreeComplex I
local notation:70 A " ⊗ₘ " B =>
  (tensorObj A B : ModX)

/-- The bidegree tensor term `𝓘^⊗ i ⊗_{𝒪_X} 𝓕^j` underlying the sheaf-level
Berthelot-Ogus construction. -/
noncomputable abbrev idealEtaComplexTensorObj
    (J : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition J]
    (K : CpxX) (i j : ℤ) : ModX :=
  (ℐ[J] ^⊗ i) ⊗ₘ K.X j

/-- The degree-`i` ambient term `𝓘^⊗ i ⊗_{𝒪_X} 𝓕^i` used in the sheaf-level
Berthelot-Ogus construction. -/
noncomputable abbrev idealEtaComplexAmbientObj
    (J : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition J]
    (K : CpxX) (i : ℤ) : ModX :=
  idealEtaComplexTensorObj J K i i

/-- The auxiliary off-diagonal tensor term `𝓘^⊗ i ⊗_{𝒪_X} 𝓕^(i + 1)` through which the ambient
differential and the next-power inclusion factor. -/
noncomputable abbrev idealEtaComplexDifferentialTarget
    (J : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition J]
    (K : CpxX) (i : ℤ) : ModX :=
  idealEtaComplexTensorObj J K i (i + 1)

/-- The ambient differential
`ℐ[J]^⊗ i ⊗ 𝓕^i ⟶ ℐ[J]^⊗ i ⊗ 𝓕^(i + 1)` induced by the differential of `K`. -/
noncomputable def idealEtaComplexAmbientDifferential
    (J : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition J]
    (K : CpxX) (i : ℤ) :
    idealEtaComplexAmbientObj J K i ⟶ idealEtaComplexDifferentialTarget J K i :=
  tensorHom (𝟙 (ℐ[J] ^⊗ i)) (K.d i (i + 1))

/-- The canonical inclusion
`ℐ[J]^⊗ (i + 1) ⊗ 𝓕^(i + 1) ⟶ ℐ[J]^⊗ i ⊗ 𝓕^(i + 1)`. -/
noncomputable def idealEtaComplexNextPowerInclusion
    (J : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition J]
    (K : CpxX) (i : ℤ) :
    idealEtaComplexAmbientObj J K (i + 1) ⟶ idealEtaComplexDifferentialTarget J K i :=
  ((tensorHom (tensorPowerSheafIntOneAddIso ℐ[J] i).symm.hom (𝟙 (K.X (i + 1))) ≫
      (α_ ℐ[J] (ℐ[J] ^⊗ i) (K.X (i + 1))).hom :
        idealEtaComplexAmbientObj J K (i + 1) ⟶
          (ℐ[J] ⊗ₘ idealEtaComplexDifferentialTarget J K i)) ≫
    idealTensorAction J (idealEtaComplexDifferentialTarget J K i))

/-- The quotient
`(ℐ[J]^⊗ i ⊗ 𝓕^(i + 1)) / (ℐ[J]^⊗ (i + 1) ⊗ 𝓕^(i + 1))` appearing in the kernel
description of `η_ℐ`. -/
noncomputable abbrev idealEtaComplexQuotientTarget
    (J : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition J]
    (K : CpxX) (i : ℤ) : ModX :=
  cokernel (idealEtaComplexNextPowerInclusion J K i)

/-- The quotient map whose kernel defines the degree-`i` Berthelot-Ogus term. -/
noncomputable def idealEtaComplexToQuotient
    (J : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition J]
    (K : CpxX) (i : ℤ) :
    idealEtaComplexAmbientObj J K i ⟶ idealEtaComplexQuotientTarget J K i :=
  idealEtaComplexAmbientDifferential J K i ≫
    cokernel.π (idealEtaComplexNextPowerInclusion J K i)

/-- The degree-`i` term of the sheaf-level Berthelot-Ogus complex
`η_ℐ 𝓕^•`. -/
noncomputable def idealEtaComplexObj
    (J : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition J]
    (K : CpxX) (i : ℤ) : ModX :=
  kernel (idealEtaComplexToQuotient J K i)

/-- The next-power inclusion in the Berthelot-Ogus quotient presentation is monic for a
termwise `I`-torsion free complex. -/
private theorem idealEtaComplexNextPowerInclusion_mono
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX) (hK : Pη[I] K) (i : ℤ) :
    Mono (idealEtaComplexNextPowerInclusion I K i) := by
  sorry

/-- The degree-`i` Berthelot-Ogus term maps into the next ambient tensor term by dividing the
ambient differential by the next-power inclusion. -/
private theorem idealEtaComplexNextTerm_w
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX) (i : ℤ) :
    (kernel.ι (idealEtaComplexToQuotient I K i) ≫ idealEtaComplexAmbientDifferential I K i) ≫
        @cokernel.π ModX SheafOfModules.instCategory
          Abelian.nonPreadditiveAbelian.toHasZeroMorphisms
          (idealEtaComplexAmbientObj I K (i + 1))
          (idealEtaComplexDifferentialTarget I K i)
          (idealEtaComplexNextPowerInclusion I K i) _ =
      @Zero.zero
        (kernel (idealEtaComplexToQuotient I K i) ⟶
          @cokernel ModX SheafOfModules.instCategory
            Abelian.nonPreadditiveAbelian.toHasZeroMorphisms
            (idealEtaComplexAmbientObj I K (i + 1))
            (idealEtaComplexDifferentialTarget I K i)
            (idealEtaComplexNextPowerInclusion I K i) _)
        (@HasZeroMorphisms.zero ModX SheafOfModules.instCategory
          Abelian.nonPreadditiveAbelian.toHasZeroMorphisms
          (kernel (idealEtaComplexToQuotient I K i))
          (@cokernel ModX SheafOfModules.instCategory
            Abelian.nonPreadditiveAbelian.toHasZeroMorphisms
            (idealEtaComplexAmbientObj I K (i + 1))
            (idealEtaComplexDifferentialTarget I K i)
            (idealEtaComplexNextPowerInclusion I K i) _)) := by
  sorry

/-- The degree-`i` Berthelot-Ogus term maps into the next ambient tensor term by dividing the
ambient differential by the next-power inclusion. -/
private noncomputable def idealEtaComplexNextTerm
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX) (hK : Pη[I] K) (i : ℤ) :
    idealEtaComplexObj I K i ⟶ idealEtaComplexAmbientObj I K (i + 1) :=
  letI : Mono (idealEtaComplexNextPowerInclusion I K i) :=
    idealEtaComplexNextPowerInclusion_mono I K hK i
  CategoryTheory.Abelian.monoLift
    (idealEtaComplexNextPowerInclusion I K i)
    (kernel.ι (idealEtaComplexToQuotient I K i) ≫ idealEtaComplexAmbientDifferential I K i)
    (idealEtaComplexNextTerm_w I K i)

/-- The divided ambient differential lands in the next Berthelot-Ogus kernel term. -/
private theorem idealEtaComplexNextTerm_comp_toQuotient
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX) (hK : Pη[I] K) (i : ℤ) :
    idealEtaComplexNextTerm I K hK i ≫ idealEtaComplexToQuotient I K (i + 1) = 0 := by
  sorry

private noncomputable def idealEtaComplexD
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX) (hK : Pη[I] K) (i : ℤ) :
    idealEtaComplexObj I K i ⟶ idealEtaComplexObj I K (i + 1) :=
  kernel.lift
    (idealEtaComplexToQuotient I K (i + 1))
    (idealEtaComplexNextTerm I K hK i)
    (idealEtaComplexNextTerm_comp_toQuotient I K hK i)

/-- Successive Berthelot-Ogus differentials compose to zero. -/
private theorem idealEtaComplexD_sq
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX) (hK : Pη[I] K) (i : ℤ) :
    idealEtaComplexD I K hK i ≫ idealEtaComplexD I K hK (i + 1) = 0 := by
  sorry

/-- The sheaf-level Berthelot-Ogus complex `η_ℐ 𝓕^•`. -/
noncomputable def idealEtaComplex
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX) (hK : Pη[I] K) :
    CpxX :=
  CochainComplex.of
    (idealEtaComplexObj I K)
    (idealEtaComplexD I K hK)
    (by
      intro i
      exact idealEtaComplexD_sq I K hK i)

namespace IdealEtaComplex

scoped notation "η[" I "]" =>
  AlgebraicGeometry.RingedSpace.idealEtaComplex I

end IdealEtaComplex

open scoped IdealEtaComplex
open scoped IdealSheafTorsion

/-- The quotient `ℱ / ℱ[I]` by the canonical `I`-torsion subsheaf. -/
noncomputable abbrev idealTorsionQuotient
    (I : Subobject 𝒪X) (ℱ : ModX) : ModX :=
  cokernel (idealTorsionSubsheafι I ℱ)

/-- The canonical quotient map `ℱ ⟶ ℱ / ℱ[I]`. -/
noncomputable abbrev idealTorsionQuotientπ
    (I : Subobject 𝒪X) (ℱ : ModX) :
    ℱ ⟶ idealTorsionQuotient I ℱ :=
  cokernel.π (idealTorsionSubsheafι I ℱ)

section CohomologyComparison

variable [CategoryWithHomology (RingedSpace.Modules X)]

/-- Lemma 20.55.5: the `i`th cohomology of `η[I] K` is isomorphic to
`𝓘^⊗ i ⊗_{𝒪_X} (H^i(K) / H^i(K)[I])`, where the quotient is the cokernel of the canonical
torsion-subsheaf inclusion `H^i(K)[I] ⟶ H^i(K)`. -/
@[stacks 0F8N]
theorem eta_homology_isomorphic_ideal_tensor_power_tensor_homology_quotient
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX) (hK : Pη[I] K) (i : ℤ) :
    IsIsomorphic
      ((η[I] K hK).homology i)
      ((ℐ[I] ^⊗ i) ⊗ₘ idealTorsionQuotient I (K.homology i)) := by
  sorry

/-- Companion form of Lemma 20.55.5 with the tensor-quotient term as the source. -/
theorem ideal_tensor_power_tensor_homology_quotient_isomorphic_eta_homology
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX) (hK : Pη[I] K) (i : ℤ) :
    IsIsomorphic
      ((ℐ[I] ^⊗ i) ⊗ₘ idealTorsionQuotient I (K.homology i))
      ((η[I] K hK).homology i) := by
  rcases eta_homology_isomorphic_ideal_tensor_power_tensor_homology_quotient I K hK i with ⟨e⟩
  exact ⟨e.symm⟩

end CohomologyComparison

end EtaAuxiliary

end AlgebraicGeometry.RingedSpace
