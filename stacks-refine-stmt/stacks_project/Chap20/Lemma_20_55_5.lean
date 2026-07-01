import Mathlib
import stacks_project.Chap20.Lemma_20_55_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open BraidedCategory
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open MonoidalCategory
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, viewed as a sheaf with values in `RingCat`. -/
/-- The category of `\mathcal O_X`-modules on a ringed space. -/
variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X)] [BraidedCategory (RingedSpace.Modules X)] [Abelian (RingedSpace.Modules X)]
variable {ℐ : (RingedSpace.Modules X)}

/-- The sheaf tensor product of two `\mathcal O_X`-modules. -/
noncomputable abbrev moduleTensor
    (ℱ 𝒢 : (RingedSpace.Modules X)) : (RingedSpace.Modules X) :=
  ℱ ⊗ 𝒢

/-- The morphism induced on tensor products by morphisms in both tensor factors. -/
noncomputable abbrev moduleTensorMap
    {ℱ₁ ℱ₂ 𝒢₁ 𝒢₂ : (RingedSpace.Modules X)}
    (α : ℱ₁ ⟶ ℱ₂) (β : 𝒢₁ ⟶ 𝒢₂) :
    moduleTensor ℱ₁ 𝒢₁ ⟶ moduleTensor ℱ₂ 𝒢₂ :=
  α ⊗ₘ β

/-- The morphism induced on tensor products by a morphism in the right tensor factor. -/
noncomputable abbrev moduleTensorLeftMap
    (ℱ : (RingedSpace.Modules X)) {𝒢₁ 𝒢₂ : (RingedSpace.Modules X)}
    (φ : 𝒢₁ ⟶ 𝒢₂) :
    moduleTensor ℱ 𝒢₁ ⟶ moduleTensor ℱ 𝒢₂ :=
  moduleTensorMap (𝟙 ℱ) φ

private instance tensorLeft_isEquivalence_of_isInvertible
    (ℱ : (RingedSpace.Modules X)) [IsInvertible ℱ] :
    Functor.IsEquivalence (tensorLeft ℱ) :=
  Functor.isEquivalence_of_iso (tensorLeftIsoTensorRight ℱ)

/-- The category of `\mathbf Z`-indexed cochain complexes of `\mathcal O_X`-modules on `X`. -/
abbrev CochainComplexModules (X : RingedSpace.{u}) :=
  CochainComplex (RingedSpace.Modules X) ℤ

/-- The action map `\mathcal I \otimes_{\mathcal O_X} \mathcal F \to \mathcal F` induced by the
ideal inclusion `\mathcal I \hookrightarrow \mathcal O_X`. -/
noncomputable def idealTensorAction
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X)) (ℱ : (RingedSpace.Modules X)) :
    moduleTensor ℐ ℱ ⟶ ℱ :=
  moduleTensorMap ι (𝟙 ℱ) ≫ (λ_ ℱ).hom

/-- An `\mathcal O_X`-module is `\mathcal I`-torsion free when multiplication by `\mathcal I`
embeds `\mathcal I \otimes_{\mathcal O_X} \mathcal F` into `\mathcal F`. -/
def IsIdealTorsionFreeModule
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X)) (ℱ : (RingedSpace.Modules X)) : Prop :=
  Mono (idealTensorAction ι ℱ)

/-- A complex of `\mathcal O_X`-modules is `\mathcal I`-torsion free when each term is
`\mathcal I`-torsion free. -/
def IsIdealTorsionFreeComplex
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    (K : CochainComplexModules X) : Prop :=
  ∀ i : ℤ, IsIdealTorsionFreeModule ι (K.X i)

/-- The morphism induced on tensor products by a morphism in the left tensor factor. -/
noncomputable abbrev moduleTensorRightMap
    (𝒢 : (RingedSpace.Modules X)) {ℱ₁ ℱ₂ : (RingedSpace.Modules X)} (φ : ℱ₁ ⟶ ℱ₂) :
    moduleTensor ℱ₁ 𝒢 ⟶ moduleTensor ℱ₂ 𝒢 :=
  moduleTensorMap φ (𝟙 𝒢)

-- Proof sketch: this is the identity law in the left variable of tensor-hom.
/-- Tensoring on the right by a fixed `\mathcal O_X`-module sends identity morphisms to
identity morphisms. -/
theorem moduleTensorRightMap_id
    (ℱ 𝒢 : (RingedSpace.Modules X)) :
    moduleTensorRightMap 𝒢 (𝟙 ℱ) = 𝟙 (moduleTensor ℱ 𝒢) := sorry

-- Proof sketch: this is functoriality of tensor-hom in the varying left factor.
/-- Tensoring on the right by a fixed `\mathcal O_X`-module sends compositions to compositions. -/
theorem moduleTensorRightMap_comp
    (𝒢 : (RingedSpace.Modules X))
    {ℱ₁ ℱ₂ ℱ₃ : (RingedSpace.Modules X)} (φ : ℱ₁ ⟶ ℱ₂) (ψ : ℱ₂ ⟶ ℱ₃) :
    moduleTensorRightMap 𝒢 (φ ≫ ψ) =
      moduleTensorRightMap 𝒢 φ ≫ moduleTensorRightMap 𝒢 ψ := sorry

-- Proof sketch: tensoring with a fixed factor preserves zero composites.
/-- Tensoring on the right by a fixed module preserves a composable pair with zero composite. -/
theorem moduleTensorRightMap_comp_zero
    {ℱ₁ ℱ₂ ℱ₃ 𝒢 : (RingedSpace.Modules X)}
    (f : ℱ₁ ⟶ ℱ₂) (g : ℱ₂ ⟶ ℱ₃) (hfg : f ≫ g = 0) :
    (moduleTensorRightMap 𝒢 f : moduleTensor ℱ₁ 𝒢 ⟶ moduleTensor ℱ₂ 𝒢) ≫
      (moduleTensorRightMap 𝒢 g : moduleTensor ℱ₂ 𝒢 ⟶ moduleTensor ℱ₃ 𝒢) = 0 := sorry

/-- Tensoring on the right by a fixed `\mathcal O_X`-module as an endofunctor on sheaves of
modules. -/
noncomputable def moduleTensorRightFunctor
    (𝒢 : (RingedSpace.Modules X)) :
    (RingedSpace.Modules X) ⥤ (RingedSpace.Modules X) where
  obj ℱ := moduleTensor ℱ 𝒢
  map φ := moduleTensorRightMap 𝒢 φ
  map_id ℱ := moduleTensorRightMap_id ℱ 𝒢
  map_comp φ ψ := moduleTensorRightMap_comp 𝒢 φ ψ

/-- Right tensoring with a fixed sheaf of modules preserves zero morphisms. -/
instance moduleTensorRightFunctor_preservesZeroMorphisms
    (𝒢 : (RingedSpace.Modules X)) :
    (moduleTensorRightFunctor 𝒢).PreservesZeroMorphisms := sorry

-- Proof sketch: tensoring preserves the cochain relation `d^i ≫ d^(i+1) = 0`.
/-- The tensorized differentials of a right-tensored complex compose to zero. -/
theorem tensorRightCochainComplex_d_sq
    (𝒢 : (RingedSpace.Modules X)) (K : CochainComplexModules X) :
    ∀ i : ℤ,
      moduleTensorRightMap 𝒢 (K.d i (i + 1)) ≫
        moduleTensorRightMap 𝒢 (K.d (i + 1) ((i + 1) + 1)) = 0 := sorry

/-- The complex obtained by tensoring every term of a cochain complex on the right by a fixed
sheaf of modules. -/
def tensorRightCochainComplex
    (𝒢 : (RingedSpace.Modules X)) (K : CochainComplexModules X) :
    CochainComplexModules X :=
  CochainComplex.of
    (fun i ↦ moduleTensor (K.X i) 𝒢)
    (fun i ↦ moduleTensorRightMap 𝒢 (K.d i (i + 1)))
    (tensorRightCochainComplex_d_sq 𝒢 K)

/-- A chosen inverse of the invertible ideal sheaf in Situation `20.55.2`. -/
noncomputable abbrev inverseIdealSheaf
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι] :
    (RingedSpace.Modules X) :=
  (tensorLeft ℐ).asEquivalence.inverse.obj (𝟙_ (RingedSpace.Modules X))

/-- The nonnegative tensor powers `\mathcal I^{\otimes n}` of the ideal sheaf. -/
noncomputable def idealTensorPower
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X)) :
    ℕ → (RingedSpace.Modules X)
  | 0 => 𝟙_ (RingedSpace.Modules X)
  | n + 1 => moduleTensor (idealTensorPower ι n) ℐ

/-- The nonnegative tensor powers of the chosen inverse ideal sheaf. -/
noncomputable def inverseIdealTensorPower
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι] :
    ℕ → (RingedSpace.Modules X)
  | 0 => 𝟙_ (RingedSpace.Modules X)
  | n + 1 => moduleTensor (inverseIdealTensorPower ι n) (inverseIdealSheaf ι)

/-- The integral tensor powers `\mathcal I^{\otimes i}` of the ideal sheaf, using the chosen
inverse ideal for negative powers. -/
noncomputable def idealTensorPowerZ
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι] :
    ℤ → (RingedSpace.Modules X)
  | Int.ofNat n => idealTensorPower ι n
  | Int.negSucc n => inverseIdealTensorPower ι (n + 1)

/-- The canonical map `\mathcal O_X \to \mathcal I^{-1}` obtained by applying the chosen inverse
of tensoring with `\mathcal I` to the multiplication map
`\mathcal I \otimes_{\mathcal O_X} \mathcal O_X \to \mathcal O_X`. -/
noncomputable def inverseIdealBaseStep
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι] :
    𝟙_ (RingedSpace.Modules X) ⟶ inverseIdealSheaf ι :=
  ((tensorLeft ℐ).asEquivalence.unitIso.app
      (𝟙_ (RingedSpace.Modules X))).hom ≫
    (tensorLeft ℐ).asEquivalence.inverse.map
      (idealTensorAction ι (𝟙_ (RingedSpace.Modules X)))

/-- The canonical morphism `\mathcal I^{\otimes (n + 1)} \to \mathcal I^{\otimes n}` for
nonnegative tensor powers. -/
noncomputable def idealTensorPowerPredecessor
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X)) (n : ℕ) :
    idealTensorPower ι (n + 1) ⟶ idealTensorPower ι n :=
  moduleTensorLeftMap (idealTensorPower ι n) ι ≫ (ρ_ (idealTensorPower ι n)).hom

/-- The canonical morphism `\mathcal I^{\otimes (-n)} \to \mathcal I^{\otimes (-(n + 1))}` for
negative tensor powers. -/
noncomputable def inverseIdealTensorPowerSuccessor
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι] (n : ℕ) :
    inverseIdealTensorPower ι n ⟶ inverseIdealTensorPower ι (n + 1) :=
  (ρ_ (inverseIdealTensorPower ι n)).inv ≫
    moduleTensorLeftMap (inverseIdealTensorPower ι n) (inverseIdealBaseStep ι)

/-- The degree-`i` ambient term `\mathcal I^{\otimes i} \otimes_{\mathcal O_X} \mathcal F^i`
used in the sheaf-level Berthelot-Ogus construction. -/
noncomputable abbrev idealEtaComplexAmbientObj
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    (K : CochainComplexModules X) (i : ℤ) :
    (RingedSpace.Modules X) :=
  moduleTensor (idealTensorPowerZ ι i) (K.X i)

/-- The degree-`i` ambient target
`\mathcal I^{\otimes i} \otimes_{\mathcal O_X} \mathcal F^{i + 1}` in the Berthelot-Ogus
construction. -/
noncomputable abbrev idealEtaComplexAmbientTarget
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    (K : CochainComplexModules X) (i : ℤ) :
    (RingedSpace.Modules X) :=
  moduleTensor (idealTensorPowerZ ι i) (K.X (i + 1))

/-- The ambient differential
`\mathcal I^{\otimes i} \otimes \mathcal F^i \to
\mathcal I^{\otimes i} \otimes \mathcal F^{i + 1}` induced by the differential of `K`. -/
noncomputable def idealEtaComplexAmbientDifferential
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    (K : CochainComplexModules X) (i : ℤ) :
    idealEtaComplexAmbientObj ι K i ⟶ idealEtaComplexAmbientTarget ι K i :=
  moduleTensorLeftMap (idealTensorPowerZ ι i) (K.d i (i + 1))

-- Proof sketch: expand the negative branch of `idealTensorPowerZ` and rewrite
-- `Int.negSucc n + 1` as the integer encoded by the `n`th inverse tensor power.
/-- The ambient tensor-power object in degree `Int.negSucc n + 1` identifies with the `n`th
inverse tensor power. -/
theorem idealEtaComplexAmbientObj_negSucc_add_one_eq
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    (K : CochainComplexModules X) (n : ℕ) :
    idealEtaComplexAmbientObj ι K (Int.negSucc n + 1) =
      moduleTensor (inverseIdealTensorPower ι n) (K.X (Int.negSucc n + 1)) := sorry

/-- The canonical inclusion
`\mathcal I^{\otimes (i + 1)} \otimes_{\mathcal O_X} \mathcal F^{i + 1}
\to \mathcal I^{\otimes i} \otimes_{\mathcal O_X} \mathcal F^{i + 1}`. -/
noncomputable def idealEtaComplexNextPowerInclusion
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    (K : CochainComplexModules X) (i : ℤ) :
    idealEtaComplexAmbientObj ι K (i + 1) ⟶ idealEtaComplexAmbientTarget ι K i :=
  match i with
  | Int.ofNat n =>
      moduleTensorMap
        (idealTensorPowerPredecessor ι n) (𝟙 (K.X (Int.ofNat n + 1)))
  | Int.negSucc n =>
      eqToHom (idealEtaComplexAmbientObj_negSucc_add_one_eq ι K n) ≫
        moduleTensorMap
          (inverseIdealTensorPowerSuccessor ι n) (𝟙 (K.X (Int.negSucc n + 1)))

/-- The quotient
`\bigl(\mathcal I^{\otimes i} \otimes \mathcal F^{i + 1}\bigr) /
\bigl(\mathcal I^{\otimes (i + 1)} \otimes \mathcal F^{i + 1}\bigr)` appearing in the kernel
description of `\eta_{\mathcal I}`. -/
noncomputable abbrev idealEtaComplexQuotientTarget
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    (K : CochainComplexModules X) (i : ℤ) :
    (RingedSpace.Modules X) :=
  cokernel (idealEtaComplexNextPowerInclusion ι K i)

/-- The quotient map whose kernel defines the degree-`i` Berthelot-Ogus term. -/
noncomputable def idealEtaComplexToQuotient
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    (K : CochainComplexModules X) (i : ℤ) :
    idealEtaComplexAmbientObj ι K i ⟶ idealEtaComplexQuotientTarget ι K i :=
  idealEtaComplexAmbientDifferential ι K i ≫
    cokernel.π (idealEtaComplexNextPowerInclusion ι K i)

/-- The degree-`i` term of the sheaf-level Berthelot-Ogus complex
`\eta_{\mathcal I}\mathcal F^\bullet`. -/
noncomputable def idealEtaComplexObj
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    (K : CochainComplexModules X) (i : ℤ) :
    (RingedSpace.Modules X) :=
  kernel (idealEtaComplexToQuotient ι K i)

-- Proof sketch: for an `\mathcal I`-torsion free complex, the map from
-- `\mathcal I^{\otimes (i + 1)} \mathcal F^{i + 1}` into
-- `\mathcal I^{\otimes i} \mathcal F^{i + 1}` is locally multiplication by a nonzerodivisor, so
-- it is a monomorphism.
/-- The next-power inclusion in the Berthelot-Ogus construction is a monomorphism for an
`\mathcal I`-torsion free complex. -/
theorem idealEtaComplexNextPowerInclusion_mono
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    (K : CochainComplexModules X) (hK : IsIdealTorsionFreeComplex ι K) (i : ℤ) :
    Mono (idealEtaComplexNextPowerInclusion ι K i) := sorry

-- Proof sketch: this is the kernel condition for `idealEtaComplexToQuotient`, rewritten after
-- expanding the quotient map as the ambient differential followed by the cokernel projection.
/-- The ambient differential of a Berthelot-Ogus section lands in the image of the next-power
inclusion. -/
theorem idealEtaComplexNextTerm_monoLift_condition
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    (K : CochainComplexModules X) (i : ℤ) :
    kernel.ι (idealEtaComplexToQuotient ι K i) ≫ idealEtaComplexToQuotient ι K i = 0 := sorry

/-- The chosen next-degree term of a Berthelot-Ogus section, obtained by lifting the ambient
differential through the next-power inclusion. -/
noncomputable def idealEtaComplexNextTerm
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    (K : CochainComplexModules X) (hK : IsIdealTorsionFreeComplex ι K) (i : ℤ) :
    idealEtaComplexObj ι K i ⟶ idealEtaComplexAmbientObj ι K (i + 1) := by
  letI : Mono (idealEtaComplexNextPowerInclusion ι K i) :=
    idealEtaComplexNextPowerInclusion_mono ι K hK i
  refine Abelian.monoLift
    (idealEtaComplexNextPowerInclusion ι K i)
    (kernel.ι (idealEtaComplexToQuotient ι K i) ≫ idealEtaComplexAmbientDifferential ι K i) ?_
  exact sorry

-- Proof sketch: the chosen next-degree term is defined by `Abelian.monoLift`, so composing it
-- with the next-power inclusion recovers the ambient differential of the kernel section.
/-- The chosen next-degree term realizes the ambient differential of a Berthelot-Ogus section. -/
theorem idealEtaComplexNextTerm_fac
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    (K : CochainComplexModules X) (hK : IsIdealTorsionFreeComplex ι K) (i : ℤ) :
    idealEtaComplexNextTerm ι K hK i ≫ idealEtaComplexNextPowerInclusion ι K i =
      kernel.ι (idealEtaComplexToQuotient ι K i) ≫ idealEtaComplexAmbientDifferential ι K i := sorry

-- Proof sketch: apply the ambient differential once more, use `d^{i + 1} d^i = 0`, and conclude
-- that the chosen next-degree term maps to zero in the defining quotient for degree `i + 1`.
/-- The chosen next-degree term satisfies the kernel condition in the next degree. -/
theorem idealEtaComplexD_lift_condition
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    (K : CochainComplexModules X) (hK : IsIdealTorsionFreeComplex ι K) (i : ℤ) :
    idealEtaComplexNextTerm ι K hK i ≫ idealEtaComplexToQuotient ι K (i + 1) = 0 := sorry

/-- The differential on the sheaf-level Berthelot-Ogus complex. -/
noncomputable def idealEtaComplexD
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    (K : CochainComplexModules X) (hK : IsIdealTorsionFreeComplex ι K) (i : ℤ) :
    idealEtaComplexObj ι K i ⟶ idealEtaComplexObj ι K (i + 1) :=
  kernel.lift
    (idealEtaComplexToQuotient ι K (i + 1))
    (idealEtaComplexNextTerm ι K hK i)
    (idealEtaComplexD_lift_condition ι K hK i)

-- Proof sketch: the Berthelot-Ogus differential is induced by the ambient differential on `K`,
-- and applying the ambient differential twice is zero.
/-- The successive differentials of the sheaf-level Berthelot-Ogus complex compose to zero. -/
theorem idealEtaComplexD_sq
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    (K : CochainComplexModules X) (hK : IsIdealTorsionFreeComplex ι K) :
    ∀ i : ℤ, idealEtaComplexD ι K hK i ≫ idealEtaComplexD ι K hK (i + 1) = 0 := sorry

/-- The sheaf-level Berthelot-Ogus complex `\eta_{\mathcal I}\mathcal F^\bullet`. -/
noncomputable def idealEtaComplex
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    (K : CochainComplexModules X) (hK : IsIdealTorsionFreeComplex ι K) :
    CochainComplexModules X :=
  CochainComplex.of
    (idealEtaComplexObj ι K)
    (idealEtaComplexD ι K hK)
    (idealEtaComplexD_sq ι K hK)

-- Proof sketch: in Situation `20.55.2`, the ideal sheaf is invertible, and every integral
-- tensor power is obtained by iterating tensor products with either `ℐ` or its chosen inverse.
/-- Every integral tensor power of the ideal sheaf is invertible in Situation `20.55.2`. -/
instance idealTensorPowerZ_isInvertible
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X)) [locally_principal_regular_ideal_situation ℐ ι] (i : ℤ) :
    IsInvertible (idealTensorPowerZ ι i) := sorry

-- Proof sketch: `tensorLeft ℱ` is an equivalence exactly when its defining module is
/-- The `\mathcal I`-torsion subobject of an `\mathcal O_X`-module, defined as the kernel of the
action map `\mathcal I \otimes \mathcal F \to \mathcal F`. -/
noncomputable abbrev idealTorsionSubobject
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X)) (ℱ : (RingedSpace.Modules X)) :
    (RingedSpace.Modules X) :=
  kernel (idealTensorAction ι ℱ)

/-- The quotient `\mathcal F / \mathcal F[\mathcal I]` of an `\mathcal O_X`-module by its
`\mathcal I`-torsion subobject. -/
noncomputable abbrev idealTorsionQuotient
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X)) (ℱ : (RingedSpace.Modules X))
    [HasCokernel (kernel.ι (idealTensorAction ι ℱ))] :
    (RingedSpace.Modules X) :=
  cokernel (kernel.ι (idealTensorAction ι ℱ))

/-- The quotient `H^i(K^\bullet) / H^i(K^\bullet)[\mathcal I]` appearing in Lemma `20.55.5`. -/
noncomputable abbrev idealTorsionQuotientHomology
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X)) (K : CochainComplexModules X) (i : ℤ)
    [K.HasHomology i] [HasCokernel (kernel.ι (idealTensorAction ι (K.homology i)))] :
    (RingedSpace.Modules X) :=
  show (RingedSpace.Modules X) from idealTorsionQuotient ι (K.homology i)

/-- The source sheaf
`\mathcal I^{\otimes i} \otimes_{\mathcal O_X}
\left(H^i(K^\bullet) / H^i(K^\bullet)[\mathcal I]\right)` of Lemma `20.55.5`. -/
noncomputable abbrev idealTensorPowerHomologyTorsionQuotientObj
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X)) [locally_principal_regular_ideal_situation ℐ ι]
    (K : CochainComplexModules X) (i : ℤ)
    [K.HasHomology i] [HasCokernel (kernel.ι (idealTensorAction ι (K.homology i)))] :
    (RingedSpace.Modules X) :=
  show (RingedSpace.Modules X) from (idealTensorPowerZ ι i) ⊗ (idealTorsionQuotientHomology ι K i)

/-- The target cohomology sheaf `H^i(\eta_\mathcal I K^\bullet)` of Lemma `20.55.5`. -/
noncomputable abbrev idealEtaComplexHomologyObj
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X)) [locally_principal_regular_ideal_situation ℐ ι]
    (K : CochainComplexModules X) (hK : IsIdealTorsionFreeComplex ι K) (i : ℤ)
    [(idealEtaComplex ι K hK).HasHomology i] :
    (RingedSpace.Modules X) :=
  show (RingedSpace.Modules X) from (idealEtaComplex ι K hK).homology i

-- Proof sketch: on stalks, Lemma `20.55.4` identifies the stalk of `η_\mathcal I K^\bullet`
-- with the local Berthelot-Ogus complex `η_f(K_x^\bullet)` for a local generator `f` of
-- `\mathcal I_x`; More on Algebra `15.96.2` then gives the local quotient-homology
-- isomorphism. These stalkwise isomorphisms glue to the displayed isomorphism of cohomology
-- sheaves.
/-- Lemma 20.55.5: in Situation `20.55.2`, for a complex `\mathcal F^\bullet` of
`\mathcal I`-torsion free `\mathcal O_X`-modules, there is a canonical isomorphism
`\mathcal I^{\otimes i} \otimes_{\mathcal O_X}
\left(H^i(\mathcal F^\bullet) / H^i(\mathcal F^\bullet)[\mathcal I]\right)
\to H^i(\eta_\mathcal I \mathcal F^\bullet)`. Lean records the statement as the existence of the
canonical isomorphism object between the two cohomology sheaves. -/
theorem ideal_tensor_power_tensor_homology_quotient_iso_eta_homology
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X)) [locally_principal_regular_ideal_situation ℐ ι]
    (K : CochainComplexModules X) (hK : IsIdealTorsionFreeComplex ι K) (i : ℤ)
    [K.HasHomology i] [(idealEtaComplex ι K hK).HasHomology i]
    [HasCokernel (kernel.ι (idealTensorAction ι (K.homology i)))] :
    Nonempty
      (idealTensorPowerHomologyTorsionQuotientObj ι K i ≅
        idealEtaComplexHomologyObj ι K hK i) := sorry

end AlgebraicGeometry.RingedSpace
