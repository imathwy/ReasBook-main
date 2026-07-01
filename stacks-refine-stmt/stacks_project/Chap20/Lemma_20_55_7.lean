import Mathlib
import stacks_project.Chap20.Lemma_20_55_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open MonoidalCategory
open TopologicalSpace

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X)] [BraidedCategory (RingedSpace.Modules X)] [Abelian (RingedSpace.Modules X)]
variable {ℐ : (RingedSpace.Modules X)}

/-- The map on ambient degree-`i` Berthelot-Ogus objects induced by a morphism of complexes. -/
private noncomputable abbrev idealEtaComplexAmbientObjMap
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    {K L : CochainComplex (RingedSpace.Modules X) ℤ} (φ : K ⟶ L) (i : ℤ) :
    idealEtaComplexAmbientObj ι K i ⟶ idealEtaComplexAmbientObj ι L i :=
  moduleTensorLeftMap (idealTensorPowerZ ι i) (φ.f i)

/-- The map on ambient Berthelot-Ogus targets induced by a morphism of complexes. -/
private noncomputable abbrev idealEtaComplexAmbientTargetMap
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    {K L : CochainComplex (RingedSpace.Modules X) ℤ} (φ : K ⟶ L) (i : ℤ) :
    idealEtaComplexAmbientTarget ι K i ⟶ idealEtaComplexAmbientTarget ι L i :=
  moduleTensorLeftMap (idealTensorPowerZ ι i) (φ.f (i + 1))

-- Proof sketch: both sides are obtained by tensoring the chain-map identity
-- `φ.f i ≫ L.d i (i + 1) = K.d i (i + 1) ≫ φ.f (i + 1)` with the fixed tensor power
-- `\mathcal I^{\otimes i}`.
/-- The ambient Berthelot-Ogus differentials are natural in the complex variable. -/
private theorem idealEtaComplexAmbientDifferential_naturality
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    {K L : CochainComplex (RingedSpace.Modules X) ℤ} (φ : K ⟶ L) (i : ℤ) :
    idealEtaComplexAmbientObjMap ι φ i ≫ idealEtaComplexAmbientDifferential ι L i =
      idealEtaComplexAmbientDifferential ι K i ≫ idealEtaComplexAmbientTargetMap ι φ i := sorry

-- Proof sketch: the next-power inclusion acts only on the tensor-power factor, while the map
-- induced by `φ` acts only on the complex term, so the two constructions commute degreewise.
/-- The next-power inclusions in the Berthelot-Ogus construction are natural in the complex. -/
private theorem idealEtaComplexNextPowerInclusion_naturality
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    {K L : CochainComplex (RingedSpace.Modules X) ℤ} (φ : K ⟶ L) (i : ℤ) :
    idealEtaComplexAmbientObjMap ι φ (i + 1) ≫ idealEtaComplexNextPowerInclusion ι L i =
      idealEtaComplexNextPowerInclusion ι K i ≫ idealEtaComplexAmbientTargetMap ι φ i := sorry

/-- The map on the quotient targets defining the Berthelot-Ogus kernels, induced by a morphism of
complexes. -/
private noncomputable def idealEtaComplexQuotientTargetMap
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    {K L : CochainComplex (RingedSpace.Modules X) ℤ} (φ : K ⟶ L) (i : ℤ) :
    idealEtaComplexQuotientTarget ι K i ⟶ idealEtaComplexQuotientTarget ι L i :=
  show idealEtaComplexQuotientTarget ι K i ⟶ idealEtaComplexQuotientTarget ι L i from
    cokernel.map
      (idealEtaComplexNextPowerInclusion ι K i)
      (idealEtaComplexNextPowerInclusion ι L i)
      (idealEtaComplexAmbientObjMap ι φ (i + 1))
      (idealEtaComplexAmbientTargetMap ι φ i)
      (idealEtaComplexNextPowerInclusion_naturality ι φ i).symm

-- Proof sketch: compose `idealEtaComplexAmbientDifferential_naturality` with the cokernel
-- projection and use the defining relation of `cokernel.map`.
/-- The quotient maps defining the Berthelot-Ogus kernels are natural in the complex. -/
private theorem idealEtaComplexToQuotient_naturality
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    {K L : CochainComplex (RingedSpace.Modules X) ℤ} (φ : K ⟶ L) (i : ℤ) :
    idealEtaComplexAmbientObjMap ι φ i ≫ idealEtaComplexToQuotient ι L i =
      idealEtaComplexToQuotient ι K i ≫ idealEtaComplexQuotientTargetMap ι φ i := sorry

/-- The degree-`i` map on the Berthelot-Ogus kernels induced by a morphism of complexes. -/
private noncomputable def idealEtaComplexObjMap
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    {K L : CochainComplex (RingedSpace.Modules X) ℤ} (φ : K ⟶ L) (i : ℤ) :
    idealEtaComplexObj ι K i ⟶ idealEtaComplexObj ι L i :=
  show idealEtaComplexObj ι K i ⟶ idealEtaComplexObj ι L i from
    kernel.map
      (idealEtaComplexToQuotient ι K i)
      (idealEtaComplexToQuotient ι L i)
      (idealEtaComplexAmbientObjMap ι φ i)
      (idealEtaComplexQuotientTargetMap ι φ i)
      (idealEtaComplexToQuotient_naturality ι φ i).symm

-- Proof sketch: unfold the differentials on `idealEtaComplex`; both sides are the lifts of the
-- same ambient morphism, and the required equality follows from the kernel-map universal
-- property.
/-- The degreewise maps induced on Berthelot-Ogus kernels commute with the differentials. -/
private theorem idealEtaComplexObjMap_comm
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    {K L : CochainComplex (RingedSpace.Modules X) ℤ}
    (hK : IsIdealTorsionFreeComplex ι K) (hL : IsIdealTorsionFreeComplex ι L)
    (φ : K ⟶ L) :
    ∀ i j, (up ℤ).Rel i j →
      idealEtaComplexObjMap ι φ i ≫ (idealEtaComplex ι L hL).d i j =
        (idealEtaComplex ι K hK).d i j ≫ idealEtaComplexObjMap ι φ j := sorry

/-- The morphism of Berthelot-Ogus complexes induced by a morphism of
`\mathcal I`-torsion free complexes. -/
private noncomputable def idealEtaComplexMap
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    {K L : CochainComplex (RingedSpace.Modules X) ℤ}
    (hK : IsIdealTorsionFreeComplex ι K) (hL : IsIdealTorsionFreeComplex ι L)
    (φ : K ⟶ L) :
    idealEtaComplex ι K hK ⟶ idealEtaComplex ι L hL where
  f i := idealEtaComplexObjMap ι φ i
  comm' := idealEtaComplexObjMap_comm ι hK hL φ

-- Proof sketch: localize the full subcategory of `\mathcal I`-torsion free complexes at its
-- quasi-isomorphisms, use Lemma `13.5.8` together with Lemmas `20.26.12`, `20.55.3`, and
-- `20.55.6` to identify that localization with `D(\mathcal O_X)`, and transport the already
-- defined Berthelot-Ogus construction on torsion-free complexes across this equivalence.
/-- Lemma 20.55.7: in Situation `20.55.2`, there exists an additive endofunctor
`L\eta_\mathcal I : D(\mathcal O_X) \to D(\mathcal O_X)` whose restriction to the full
subcategory of derived objects represented by `\mathcal I`-torsion free complexes is naturally
isomorphic to the Berthelot-Ogus complex construction `\eta_\mathcal I`. This natural
isomorphism is the formal statement that if a derived object is represented by an
`\mathcal I`-torsion free complex `\mathcal F^\bullet`, then `L\eta_\mathcal I` is computed by
`\eta_\mathcal I \mathcal F^\bullet`, and likewise on morphisms represented by maps of such
complexes. -/
theorem idealEtaDerivedFunctor_exists
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι] :
    ∃ (Lη : DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory (RingedSpace.Modules X)),
      Lη.Additive := sorry

end AlgebraicGeometry.RingedSpace
