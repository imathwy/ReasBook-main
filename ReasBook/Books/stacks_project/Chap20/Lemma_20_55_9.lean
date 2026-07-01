import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open MonoidalCategory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, viewed as a sheaf with values in `RingCat`. -/
/-- The category of `\mathcal O_X`-modules on a ringed space. -/
variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X)] [BraidedCategory (RingedSpace.Modules X)]
variable {ℐ : (RingedSpace.Modules X)}

/-- The sheaf tensor product of two `\mathcal O_X`-modules. -/
noncomputable abbrev moduleTensor
    (ℱ 𝒢 : (RingedSpace.Modules X)) : (RingedSpace.Modules X) :=
  ℱ ⊗ 𝒢

/-- The portion of Situation `20.55.2` used by the Berthelot–Ogus construction in this file: the
ideal sheaf is included in the tensor unit and is invertible. -/
class ideal_eta_situation
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X)) : Prop
    extends Mono ι

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

-- Proof sketch: this is the identity law for tensor-hom on the underlying presheaf tensor
-- product, transported through sheafification.
/-- Tensoring on the left by a fixed `\mathcal O_X`-module preserves identities. -/
theorem moduleTensorLeftMap_id
    (ℱ 𝒢 : (RingedSpace.Modules X)) :
    moduleTensorLeftMap ℱ (𝟙 𝒢) = 𝟙 (moduleTensor ℱ 𝒢) := sorry

-- Proof sketch: this is functoriality of tensor-hom in the varying right factor, transported
-- through sheafification.
/-- Tensoring on the left by a fixed `\mathcal O_X`-module preserves composition. -/
theorem moduleTensorLeftMap_comp
    (ℱ : (RingedSpace.Modules X))
    {𝒢₁ 𝒢₂ 𝒢₃ : (RingedSpace.Modules X)}
    (φ : 𝒢₁ ⟶ 𝒢₂) (ψ : 𝒢₂ ⟶ 𝒢₃) :
    moduleTensorLeftMap ℱ (φ ≫ ψ) =
      moduleTensorLeftMap ℱ φ ≫ moduleTensorLeftMap ℱ ψ := sorry

/-- Tensoring on the left by a fixed sheaf of modules as an endofunctor on `\mathrm{Mod}(
\mathcal O_X)`. -/
noncomputable abbrev tensorLeftFunctor
    (ℱ : (RingedSpace.Modules X)) :
    (RingedSpace.Modules X) ⥤ (RingedSpace.Modules X) :=
  { obj := fun 𝒢 ↦ moduleTensor ℱ 𝒢
    map := fun φ ↦ moduleTensorLeftMap ℱ φ
    map_id := moduleTensorLeftMap_id ℱ
    map_comp := moduleTensorLeftMap_comp ℱ }

/-- An invertible `\mathcal O_X`-module is one whose left tensor functor is an equivalence. -/
class IsInvertible (ℱ : (RingedSpace.Modules X)) : Prop extends Functor.IsEquivalence (tensorLeftFunctor ℱ)

-- Proof sketch: in Situation `20.55.2`, the local principal regularity condition makes the ideal
-- locally free of rank `1`, hence invertible; this is the content of Lemma `20.55.1 (1)`.
/-- The ideal sheaf in Situation `20.55.2` is invertible. -/
theorem isInvertible_of_ideal_eta_situation
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι] :
    IsInvertible ℐ := sorry


/-- The category of `\mathbf{Z}`-indexed cochain complexes of `\mathcal O_X`-modules on a ringed
space `X`. -/
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

-- Proof sketch: on presheaves this is tensor-hom functoriality in the left factor with the
-- identity map on the fixed right factor, and sheafification preserves identities.
/-- Tensoring on the right by a fixed `\mathcal O_X`-module sends identity morphisms to
identity morphisms. -/
theorem moduleTensorRightMap_id
    (ℱ 𝒢 : (RingedSpace.Modules X)) :
    moduleTensorRightMap 𝒢 (𝟙 ℱ) = 𝟙 (moduleTensor ℱ 𝒢) := sorry

-- Proof sketch: on presheaves this is tensor-hom functoriality in the left factor with the
-- fixed right factor unchanged, and sheafification preserves composition.
/-- Tensoring on the right by a fixed `\mathcal O_X`-module sends compositions to compositions. -/
theorem moduleTensorRightMap_comp
    (𝒢 : (RingedSpace.Modules X))
    {ℱ₁ ℱ₂ ℱ₃ : (RingedSpace.Modules X)} (φ : ℱ₁ ⟶ ℱ₂) (ψ : ℱ₂ ⟶ ℱ₃) :
    moduleTensorRightMap 𝒢 (φ ≫ ψ) =
      moduleTensorRightMap 𝒢 φ ≫ moduleTensorRightMap 𝒢 ψ := sorry

-- Proof sketch: tensoring with the identity on the fixed right factor preserves composites, so a
-- zero composite remains zero after tensoring on the right.
/-- Tensoring on the right by a fixed module preserves a composable pair with zero composite. -/
theorem moduleTensorRightMap_comp_zero
    {ℱ₁ ℱ₂ ℱ₃ 𝒢 : (RingedSpace.Modules X)}
    (f : ℱ₁ ⟶ ℱ₂) (g : ℱ₂ ⟶ ℱ₃) (hfg : f ≫ g = 0) :
    (moduleTensorRightMap 𝒢 f : moduleTensor ℱ₁ 𝒢 ⟶ moduleTensor ℱ₂ 𝒢) ≫
      (moduleTensorRightMap 𝒢 g : moduleTensor ℱ₂ 𝒢 ⟶ moduleTensor ℱ₃ 𝒢) = 0 := sorry

/-- Tensoring on the right by a fixed `\mathcal O_X`-module, viewed as an endofunctor on sheaves
of modules. -/
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

-- Proof sketch: tensoring on the right preserves the relation `d^i ≫ d^(i+1) = 0`, so the
-- tensorized differentials again square to zero.
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
    [ideal_eta_situation ι] :
    (RingedSpace.Modules X) :=
  letI : IsInvertible ℐ := isInvertible_of_ideal_eta_situation ι
  (tensorLeftFunctor ℐ).asEquivalence.inverse.obj (𝟙_ (RingedSpace.Modules X))

/-- The nonnegative tensor powers `\mathcal I^{\otimes n}` of the ideal sheaf. -/
noncomputable def idealTensorPower
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X)) :
    ℕ → (RingedSpace.Modules X)
  | 0 => 𝟙_ (RingedSpace.Modules X)
  | n + 1 => moduleTensor (idealTensorPower ι n) ℐ

/-- The nonnegative tensor powers of the chosen inverse ideal sheaf. -/
noncomputable def inverseIdealTensorPower
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι] :
    ℕ → (RingedSpace.Modules X)
  | 0 => 𝟙_ (RingedSpace.Modules X)
  | n + 1 => moduleTensor (inverseIdealTensorPower ι n) (inverseIdealSheaf ι)

/-- The integral tensor powers `\mathcal I^{\otimes i}` of the ideal sheaf, using the chosen
inverse ideal for negative powers. -/
noncomputable def idealTensorPowerZ
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι] :
    ℤ → (RingedSpace.Modules X)
  | Int.ofNat n => idealTensorPower ι n
  | Int.negSucc n => inverseIdealTensorPower ι (n + 1)

/-- The canonical map `\mathcal O_X \to \mathcal I^{-1}` obtained by applying the chosen inverse
of tensoring with `\mathcal I` to the multiplication map
`\mathcal I \otimes_{\mathcal O_X} \mathcal O_X \to \mathcal O_X`. -/
noncomputable def inverseIdealBaseStep
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι] :
    𝟙_ (RingedSpace.Modules X) ⟶ inverseIdealSheaf ι :=
  letI : IsInvertible ℐ := isInvertible_of_ideal_eta_situation ι
  ((tensorLeftFunctor ℐ).asEquivalence.unitIso.app
      (𝟙_ (RingedSpace.Modules X))).hom ≫
    (tensorLeftFunctor ℐ).asEquivalence.inverse.map
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
    [ideal_eta_situation ι] (n : ℕ) :
    inverseIdealTensorPower ι n ⟶ inverseIdealTensorPower ι (n + 1) :=
  (ρ_ (inverseIdealTensorPower ι n)).inv ≫
    moduleTensorLeftMap (inverseIdealTensorPower ι n) (inverseIdealBaseStep ι)

/-- The degree-`i` ambient term `\mathcal I^{\otimes i} \otimes_{\mathcal O_X} \mathcal F^i`
used in the sheaf-level Berthelot–Ogus construction. -/
noncomputable abbrev idealEtaComplexAmbientObj
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι]
    (K : CochainComplexModules X) (i : ℤ) :
    (RingedSpace.Modules X) :=
  moduleTensor (idealTensorPowerZ ι i) (K.X i)

/-- The degree-`i` ambient target
`\mathcal I^{\otimes i} \otimes_{\mathcal O_X} \mathcal F^{i + 1}` in the Berthelot–Ogus
construction. -/
noncomputable abbrev idealEtaComplexAmbientTarget
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι]
    (K : CochainComplexModules X) (i : ℤ) :
    (RingedSpace.Modules X) :=
  moduleTensor (idealTensorPowerZ ι i) (K.X (i + 1))

/-- The ambient differential
`\mathcal I^{\otimes i} \otimes \mathcal F^i \to
\mathcal I^{\otimes i} \otimes \mathcal F^{i + 1}` induced by the differential of `K`. -/
noncomputable def idealEtaComplexAmbientDifferential
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι]
    (K : CochainComplexModules X) (i : ℤ) :
    idealEtaComplexAmbientObj ι K i ⟶ idealEtaComplexAmbientTarget ι K i :=
  moduleTensorLeftMap (idealTensorPowerZ ι i) (K.d i (i + 1))

-- Proof sketch: expand `idealTensorPowerZ` on the negative branch and rewrite
-- `Int.negSucc n + 1` as the integer encoded by the `n`th inverse tensor power.
/-- The ambient tensor-power object in degree `Int.negSucc n + 1` identifies with the `n`th
inverse tensor power. -/
theorem idealEtaComplexAmbientObj_negSucc_add_one_eq
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι]
    (K : CochainComplexModules X) (n : ℕ) :
    idealEtaComplexAmbientObj ι K (Int.negSucc n + 1) =
      moduleTensor (inverseIdealTensorPower ι n) (K.X (Int.negSucc n + 1)) := sorry

/-- The canonical inclusion
`\mathcal I^{\otimes (i + 1)} \otimes_{\mathcal O_X} \mathcal F^{i + 1}
\to \mathcal I^{\otimes i} \otimes_{\mathcal O_X} \mathcal F^{i + 1}`. -/
noncomputable def idealEtaComplexNextPowerInclusion
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι]
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
    [ideal_eta_situation ι]
    (K : CochainComplexModules X) (i : ℤ) :
    (RingedSpace.Modules X) :=
  cokernel (idealEtaComplexNextPowerInclusion ι K i)

/-- The quotient map whose kernel defines the degree-`i` Berthelot–Ogus term. -/
noncomputable def idealEtaComplexToQuotient
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι]
    (K : CochainComplexModules X) (i : ℤ) :
    idealEtaComplexAmbientObj ι K i ⟶ idealEtaComplexQuotientTarget ι K i :=
  idealEtaComplexAmbientDifferential ι K i ≫
    cokernel.π (idealEtaComplexNextPowerInclusion ι K i)

/-- The degree-`i` term of the sheaf-level Berthelot–Ogus complex
`\eta_{\mathcal I}\mathcal F^\bullet`. -/
noncomputable def idealEtaComplexObj
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι]
    (K : CochainComplexModules X) (i : ℤ) :
    (RingedSpace.Modules X) :=
  kernel (idealEtaComplexToQuotient ι K i)

-- Proof sketch: for an `\mathcal I`-torsion free complex, the map from
-- `\mathcal I^{\otimes (i + 1)} \mathcal F^{i + 1}` into
-- `\mathcal I^{\otimes i} \mathcal F^{i + 1}` is locally multiplication by a nonzerodivisor, so
-- it is a monomorphism.
/-- The next-power inclusion in the Berthelot–Ogus construction is a monomorphism for an
`\mathcal I`-torsion free complex. -/
theorem idealEtaComplexNextPowerInclusion_mono
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι]
    (K : CochainComplexModules X) (hK : IsIdealTorsionFreeComplex ι K) (i : ℤ) :
    Mono (idealEtaComplexNextPowerInclusion ι K i) := sorry

-- Proof sketch: this is the kernel condition for `idealEtaComplexToQuotient`, rewritten after
-- expanding the quotient map as the ambient differential followed by the cokernel projection.
/-- The ambient differential of a Berthelot–Ogus section lands in the image of the next-power
inclusion. -/
theorem idealEtaComplexNextTerm_monoLift_condition
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι]
    (K : CochainComplexModules X) (i : ℤ) :
    (kernel.ι (idealEtaComplexToQuotient ι K i) ≫ idealEtaComplexAmbientDifferential ι K i) ≫
      cokernel.π (idealEtaComplexNextPowerInclusion ι K i) = 0 := sorry

/-- The chosen next-degree term of a Berthelot–Ogus section, obtained by lifting the ambient
differential through the next-power inclusion. -/
noncomputable def idealEtaComplexNextTerm
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι]
    (K : CochainComplexModules X) (hK : IsIdealTorsionFreeComplex ι K) (i : ℤ) :
    idealEtaComplexObj ι K i ⟶ idealEtaComplexAmbientObj ι K (i + 1) :=
  letI : Mono (idealEtaComplexNextPowerInclusion ι K i) :=
    idealEtaComplexNextPowerInclusion_mono ι K hK i
  Abelian.monoLift
    (idealEtaComplexNextPowerInclusion ι K i)
    (kernel.ι (idealEtaComplexToQuotient ι K i) ≫ idealEtaComplexAmbientDifferential ι K i)
    (idealEtaComplexNextTerm_monoLift_condition ι K i)

-- Proof sketch: the chosen next-degree term is defined by `Abelian.monoLift`, so composing it
-- with the next-power inclusion recovers the ambient differential of the kernel section.
/-- The chosen next-degree term realizes the ambient differential of a Berthelot–Ogus section. -/
theorem idealEtaComplexNextTerm_fac
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι]
    (K : CochainComplexModules X) (hK : IsIdealTorsionFreeComplex ι K) (i : ℤ) :
    idealEtaComplexNextTerm ι K hK i ≫ idealEtaComplexNextPowerInclusion ι K i =
      kernel.ι (idealEtaComplexToQuotient ι K i) ≫ idealEtaComplexAmbientDifferential ι K i := sorry

-- Proof sketch: apply the ambient differential once more, use `d^{i + 1} d^i = 0`, and conclude
-- that the chosen next-degree term maps to zero in the defining quotient for degree `i + 1`.
/-- The chosen next-degree term satisfies the kernel condition in the next degree. -/
theorem idealEtaComplexD_lift_condition
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι]
    (K : CochainComplexModules X) (hK : IsIdealTorsionFreeComplex ι K) (i : ℤ) :
    idealEtaComplexNextTerm ι K hK i ≫ idealEtaComplexToQuotient ι K (i + 1) = 0 := sorry

/-- The differential on the sheaf-level Berthelot–Ogus complex. -/
noncomputable def idealEtaComplexD
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι]
    (K : CochainComplexModules X) (hK : IsIdealTorsionFreeComplex ι K) (i : ℤ) :
    idealEtaComplexObj ι K i ⟶ idealEtaComplexObj ι K (i + 1) :=
  kernel.lift
    (idealEtaComplexToQuotient ι K (i + 1))
    (idealEtaComplexNextTerm ι K hK i)
    (idealEtaComplexD_lift_condition ι K hK i)

-- Proof sketch: the Berthelot–Ogus differential is induced by the ambient differential on `K`,
-- and applying the ambient differential twice is zero.
/-- The successive differentials of the sheaf-level Berthelot–Ogus complex compose to zero. -/
theorem idealEtaComplexD_sq
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι]
    (K : CochainComplexModules X) (hK : IsIdealTorsionFreeComplex ι K) :
    ∀ i : ℤ, idealEtaComplexD ι K hK i ≫ idealEtaComplexD ι K hK (i + 1) = 0 := sorry

/-- The sheaf-level Berthelot–Ogus complex `\eta_{\mathcal I}\mathcal F^\bullet`. -/
noncomputable def idealEtaComplex
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι]
    (K : CochainComplexModules X) (hK : IsIdealTorsionFreeComplex ι K) :
    CochainComplexModules X :=
  CochainComplex.of
    (idealEtaComplexObj ι K)
    (idealEtaComplexD ι K hK)
    (idealEtaComplexD_sq ι K hK)

-- Proof sketch: tensoring on the right by an invertible sheaf is an equivalence, hence exact; it
-- preserves monomorphisms, so the injectivity of `\mathcal I \otimes \mathcal F^i \to \mathcal
-- F^i` passes to the tensored terms.
/-- Tensoring an `\mathcal I`-torsion free complex on the right by an invertible module preserves
`\mathcal I`-torsion freeness. -/
theorem isIdealTorsionFreeComplex_tensorRight_of_isInvertible
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι]
    (K : CochainComplexModules X) (hK : IsIdealTorsionFreeComplex ι K)
    (𝒢 : (RingedSpace.Modules X)) [IsInvertible 𝒢] :
    IsIdealTorsionFreeComplex ι (tensorRightCochainComplex 𝒢 K) := sorry

-- Proof sketch: in a braided monoidal category, right tensor by `\mathcal G` is naturally
-- isomorphic to left tensor by `\mathcal G` through the braiding. If `\mathcal G` is invertible,
-- left tensor by `\mathcal G` is an equivalence, hence so is right tensor by `\mathcal G`.
/-- Right tensoring with an invertible `\mathcal O_X`-module is an equivalence. -/
theorem moduleTensorRightFunctor_isEquivalence_of_isInvertible
    (𝒢 : (RingedSpace.Modules X)) [IsInvertible 𝒢] :
    (moduleTensorRightFunctor 𝒢).IsEquivalence := sorry

/-- The associator identifies right tensoring the ambient degree-`i` term with the ambient degree
`i` term of the right-tensored complex. -/
noncomputable def idealEtaComplexAmbientObjTensorRightIso
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι]
    (K : CochainComplexModules X) (𝒢 : (RingedSpace.Modules X)) (i : ℤ) :
    moduleTensor (idealEtaComplexAmbientObj ι K i) 𝒢 ≅
      idealEtaComplexAmbientObj ι (tensorRightCochainComplex 𝒢 K) i :=
  α_ (idealTensorPowerZ ι i) (K.X i) 𝒢

/-- The associator identifies right tensoring the ambient degree-`i` target with the ambient
degree `i` target of the right-tensored complex. -/
noncomputable def idealEtaComplexAmbientTargetTensorRightIso
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι]
    (K : CochainComplexModules X) (𝒢 : (RingedSpace.Modules X)) (i : ℤ) :
    moduleTensor (idealEtaComplexAmbientTarget ι K i) 𝒢 ≅
      idealEtaComplexAmbientTarget ι (tensorRightCochainComplex 𝒢 K) i :=
  α_ (idealTensorPowerZ ι i) (K.X (i + 1)) 𝒢

-- Proof sketch: both sides are obtained from the same associator square by tensoring the
-- differential `d^i : \mathcal F^i \to \mathcal F^{i + 1}` with the fixed factor
-- `\mathcal I^{\otimes i}` and then with `\mathcal G`.
/-- The ambient Berthelot–Ogus differentials commute with right tensoring by a fixed module. -/
theorem idealEtaComplexAmbientDifferential_tensorRight_naturality
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι]
    (K : CochainComplexModules X) (𝒢 : (RingedSpace.Modules X)) (i : ℤ) :
    moduleTensorRightMap 𝒢 (idealEtaComplexAmbientDifferential ι K i) ≫
        (idealEtaComplexAmbientTargetTensorRightIso ι K 𝒢 i).hom =
      (idealEtaComplexAmbientObjTensorRightIso ι K 𝒢 i).hom ≫
        idealEtaComplexAmbientDifferential ι (tensorRightCochainComplex 𝒢 K) i := sorry

-- Proof sketch: after re-associating tensor products, the next-power inclusion for the
-- right-tensored complex is obtained by tensoring the original next-power inclusion with
-- `\mathcal G` on the right.
/-- The next-power inclusions in the Berthelot–Ogus construction commute with right tensoring by
a fixed module. -/
theorem idealEtaComplexNextPowerInclusion_tensorRight_naturality
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι]
    (K : CochainComplexModules X) (𝒢 : (RingedSpace.Modules X)) (i : ℤ) :
    moduleTensorRightMap 𝒢 (idealEtaComplexNextPowerInclusion ι K i) ≫
        (idealEtaComplexAmbientTargetTensorRightIso ι K 𝒢 i).hom =
      (idealEtaComplexAmbientObjTensorRightIso ι K 𝒢 (i + 1)).hom ≫
        idealEtaComplexNextPowerInclusion ι (tensorRightCochainComplex 𝒢 K) i := sorry

/-- Right tensoring the Berthelot–Ogus quotient target is canonically isomorphic to the quotient
target of the right-tensored complex. -/
noncomputable def idealEtaComplexQuotientTargetTensorRightIso
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι]
    (K : CochainComplexModules X) (𝒢 : (RingedSpace.Modules X)) [IsInvertible 𝒢] (i : ℤ) :
    moduleTensor (idealEtaComplexQuotientTarget ι K i) 𝒢 ≅
      idealEtaComplexQuotientTarget ι (tensorRightCochainComplex 𝒢 K) i :=
  letI : (moduleTensorRightFunctor 𝒢).IsEquivalence :=
    moduleTensorRightFunctor_isEquivalence_of_isInvertible 𝒢
  (PreservesCokernel.iso (moduleTensorRightFunctor 𝒢)
      (idealEtaComplexNextPowerInclusion ι K i)) ≪≫
    cokernel.mapIso
      ((moduleTensorRightFunctor 𝒢).map (idealEtaComplexNextPowerInclusion ι K i))
      (idealEtaComplexNextPowerInclusion ι (tensorRightCochainComplex 𝒢 K) i)
      (idealEtaComplexAmbientObjTensorRightIso ι K 𝒢 (i + 1))
      (idealEtaComplexAmbientTargetTensorRightIso ι K 𝒢 i)
      (idealEtaComplexNextPowerInclusion_tensorRight_naturality ι K 𝒢 i)

-- Proof sketch: combine the naturality of the ambient differentials with the naturality of the
-- cokernel projections under right tensoring.
/-- The quotient maps defining the Berthelot–Ogus kernels commute with right tensoring by a fixed
invertible module. -/
theorem idealEtaComplexToQuotient_tensorRight_naturality
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι]
    (K : CochainComplexModules X) (𝒢 : (RingedSpace.Modules X)) [IsInvertible 𝒢] (i : ℤ) :
    moduleTensorRightMap 𝒢 (idealEtaComplexToQuotient ι K i) ≫
        (idealEtaComplexQuotientTargetTensorRightIso ι K 𝒢 i).hom =
      (idealEtaComplexAmbientObjTensorRightIso ι K 𝒢 i).hom ≫
        idealEtaComplexToQuotient ι (tensorRightCochainComplex 𝒢 K) i := sorry

/-- Right tensoring the degree-`i` Berthelot–Ogus term is canonically isomorphic to the degree-`i`
term of the right-tensored complex. -/
noncomputable def idealEtaComplexObjTensorRightIso
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι]
    (K : CochainComplexModules X) (𝒢 : (RingedSpace.Modules X)) [IsInvertible 𝒢] (i : ℤ) :
    moduleTensor (idealEtaComplexObj ι K i) 𝒢 ≅
      idealEtaComplexObj ι (tensorRightCochainComplex 𝒢 K) i :=
  letI : (moduleTensorRightFunctor 𝒢).IsEquivalence :=
    moduleTensorRightFunctor_isEquivalence_of_isInvertible 𝒢
  (PreservesKernel.iso (moduleTensorRightFunctor 𝒢)
      (idealEtaComplexToQuotient ι K i)) ≪≫
    kernel.mapIso
      ((moduleTensorRightFunctor 𝒢).map (idealEtaComplexToQuotient ι K i))
      (idealEtaComplexToQuotient ι (tensorRightCochainComplex 𝒢 K) i)
      (idealEtaComplexAmbientObjTensorRightIso ι K 𝒢 i)
      (idealEtaComplexQuotientTargetTensorRightIso ι K 𝒢 i)
      (idealEtaComplexToQuotient_tensorRight_naturality ι K 𝒢 i)

-- Proof sketch: both differentials are induced from the ambient differential after lifting
-- through the same next-power inclusions, and the kernel comparison isomorphisms are compatible
-- with these universal constructions.
/-- The degreewise Berthelot–Ogus comparison isomorphisms commute with the differentials. -/
theorem idealEtaComplexObjTensorRightIso_comm
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι]
    (K : CochainComplexModules X) (hK : IsIdealTorsionFreeComplex ι K)
    (𝒢 : (RingedSpace.Modules X)) [IsInvertible 𝒢] :
    ∀ i j, (ComplexShape.up ℤ).Rel i j →
      (idealEtaComplexObjTensorRightIso ι K 𝒢 i).hom ≫
          (idealEtaComplex ι (tensorRightCochainComplex 𝒢 K)
            (isIdealTorsionFreeComplex_tensorRight_of_isInvertible ι K hK 𝒢)).d i j =
        (tensorRightCochainComplex 𝒢 (idealEtaComplex ι K hK)).d i j ≫
          (idealEtaComplexObjTensorRightIso ι K 𝒢 j).hom := sorry

/-- Lemma 20.55.9: tensoring a complex of `\mathcal I`-torsion free `\mathcal O_X`-modules on the
right by an invertible module commutes with the Berthelot–Ogus construction
`\eta_{\mathcal I}`, up to the canonical complex isomorphism obtained from associativity of tensor
products and preservation of kernels and cokernels by tensoring with an invertible module. -/
noncomputable def idealEtaComplex_tensorRightIso
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι]
    (K : CochainComplexModules X) (hK : IsIdealTorsionFreeComplex ι K)
    (𝒢 : (RingedSpace.Modules X)) [IsInvertible 𝒢] :
    tensorRightCochainComplex 𝒢 (idealEtaComplex ι K hK) ≅
      idealEtaComplex ι (tensorRightCochainComplex 𝒢 K)
        (isIdealTorsionFreeComplex_tensorRight_of_isInvertible ι K hK 𝒢) :=
  HomologicalComplex.Hom.isoOfComponents
    (idealEtaComplexObjTensorRightIso ι K 𝒢)
    (idealEtaComplexObjTensorRightIso_comm ι K hK 𝒢)

-- Proof sketch: `idealEtaComplex_tensorRightIso` is defined by
-- `HomologicalComplex.Hom.isoOfComponents`, so its degreewise component is exactly the chosen
-- objectwise comparison isomorphism.
/-- The degree-`i` component of the Berthelot–Ogus right-tensor comparison isomorphism is the
objectwise comparison isomorphism. -/
theorem idealEtaComplex_tensorRightIso_app
    (ι : ℐ ⟶ 𝟙_ (RingedSpace.Modules X))
    [ideal_eta_situation ι]
    (K : CochainComplexModules X) (hK : IsIdealTorsionFreeComplex ι K)
    (𝒢 : (RingedSpace.Modules X)) [IsInvertible 𝒢] (i : ℤ) :
    HomologicalComplex.Hom.isoApp (idealEtaComplex_tensorRightIso ι K hK 𝒢) i =
      idealEtaComplexObjTensorRightIso ι K 𝒢 i := sorry

end AlgebraicGeometry.RingedSpace
