import StacksProject_2024.Chap20.Definition_20_26_14
import StacksProject_2024.Chap20.«20_55_7_2»
import StacksProject_2024.Chap20.Lemma_20_55_7
import StacksProject_2024.Chap20.Lemma_20_55_5
import StacksProject_2024.Chap20.RingedSpaceModuleHasDerivedCategory

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open MonoidalCategory
open scoped RingedSpaceDerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

open scoped IdealEtaComplex

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [SymmetricCategory (RingedSpace.Modules X)] [MonoidalClosed (RingedSpace.Modules X)]
variable [CategoryWithHomology (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X
local notation "CpxX" => CochainComplex ModX ℤ
local notation "DModX" => DerivedCategory ModX
local notation "QX" => (DerivedCategory.Q : CpxX ⥤ DModX)
local notation "OX" => (SheafOfModules.unit X.ringCatSheaf : ModX)
local notation:70 A " ⊗ₘ " B => (tensorObj A B : ModX)
local notation "single0" => DerivedCategory.singleFunctor ModX (0 : ℤ)
local notation "Pη[" I "]" => IsIdealTorsionFreeComplex I

/- Domain-style sampling for Lemma 20.55.8:
- primary domain: Berthelot-Ogus `Lη_𝓘` on the derived category of `𝒪_X`-modules, derived
  tensoring with `(𝒪_X/𝓘)[0]`, and the Chapter 20 Bockstein cohomology complex of the successive
  quotient tensor complexes;
- sampled owner declarations:
  `Functor.IsIdealEtaDerived`,
  `idealEtaDerivedFunctor_obj_isomorphic`,
  `derivedTensorProduct`,
  `ShortComplex.ShortExact.δ`,
  `idealQuotientBocksteinCohomologyComplex`;
- best owner abstraction:
  `source-facing`: the canonical derived-category comparison
    `F(QK^•) ⊗^L (𝒪_X/𝓘)[0] ≅ Q(H^•(M/𝓘))`;
  `core/canonical`: a functor `F : D(𝒪_X) ⥤ D(𝒪_X)` equipped with
    `Functor.IsIdealEtaDerived I F`, the derived tensor owner `⊗^L`, `DerivedCategory.Q`, the
    short exact row of successive quotient tensor complexes, and its connecting morphisms
    `idealQuotientBockstein I K i`;
  `bridge/view`: the Bockstein cohomology complex assembled from those connecting morphisms via
    `idealQuotientBocksteinCohomologyComplex`.
- primitive data: the Berthelot-Ogus complex `η[I] K hK`, the quotient module `𝒪_X/𝓘`, the
  successive quotient tensor complexes
  `(tensorRight (cokernel (idealPowerSuccInclusion I i))).mapHomologicalComplex (up ℤ)`, and the
  short exact rows relating the `i`, `i + 1`, and `i + 2` quotient stages.
- derived API: the degreewise Bockstein morphism, its square-zero theorem, the canonical
  Bockstein cohomology complex, and the derived isomorphism of Lemma `20.55.8`.

This file therefore keeps the source-facing theorem directly over the canonical Chapter 20
Bockstein differential family, instead of quantifying over user-supplied comparison data. -/

-- Proof sketch: represent `Lη_𝓘 M` by the Berthelot-Ogus complex `η[I] K hK` of a chosen
-- `𝓘`-torsion free model `K^•`, replace the derived tensor with `𝒪_X / 𝓘` by the termwise
-- quotient tensor representative used in the source proof, represent `H^•(M / 𝓘)` by the
-- Bockstein cohomology complex built from the successive quotient complexes, and then use the
-- stalkwise comparison from More on Algebra `15.96.6` to identify the two derived objects.
section

variable (I : Subobject OX)
variable [SatisfiesLocallyPrincipalRegularIdealCondition I]
variable (K : CpxX)
local notation "ℐ" => (I : ModX)
local notation "𝒪X/ℐ" => (cokernel (I.arrow : ℐ ⟶ OX))

/-- The canonical inclusion `𝓘^(i + 1) ⟶ 𝓘^i`. -/
private noncomputable def idealPowerSuccInclusion
    (I : Subobject OX)
    [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (i : ℤ) :
    ((I : ModX) ^⊗ (i + 1)) ⟶ ((I : ModX) ^⊗ i) :=
  (tensorPowerSheafIntOneAddIso (I : ModX) i).symm.hom ≫
    idealTensorAction I ((I : ModX) ^⊗ i)

/-- The degree-`i` successive quotient tensor complex
`K^• ⊗_{𝒪_X} (𝓘^i / 𝓘^(i + 1))` appearing in the
Bockstein complex `(20.55.7.2)`. -/
noncomputable abbrev tensorWithIdealPowerQuotientComplex
    (I : Subobject OX)
    [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX) (i : ℤ) :
    CpxX :=
  (((tensorRight (cokernel (idealPowerSuccInclusion I i))).mapHomologicalComplex
      (up ℤ)).obj K)

/-- Tensoring a fixed complex on the right by a module defines a functor from modules to
cochain complexes. -/
private noncomputable def tensorRightComplexFunctor (K : CpxX) : ModX ⥤ CpxX where
  obj ℱ := ((tensorRight ℱ).mapHomologicalComplex (up ℤ)).obj K
  map f := (NatTrans.mapHomologicalComplex ((tensoringRight ModX).map f) (up ℤ)).app K
  map_id ℱ := by
    ext i
    simp [CategoryTheory.Functor.mapHomologicalComplex_obj_X]
  map_comp f g := by
    ext i
    simp [CategoryTheory.Functor.mapHomologicalComplex_obj_X]

/-- The canonical inclusion `𝓘^(i + 2) ⟶ 𝓘^i`. -/
private noncomputable def idealPowerTwoStepInclusion
    (I : Subobject OX)
    [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (i : ℤ) :
    ((I : ModX) ^⊗ (i + 1 + 1)) ⟶ ((I : ModX) ^⊗ i) :=
  idealPowerSuccInclusion I (i + 1) ≫ idealPowerSuccInclusion I i

/-- The degree-`i` two-step successive quotient tensor complex
`K^• ⊗_{𝒪_X} (𝓘^i / 𝓘^(i + 2))` used to define the Bockstein connecting morphism. -/
private noncomputable abbrev tensorWithIdealPowerTwoStepQuotientComplex
    (I : Subobject OX)
    [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX) (i : ℤ) :
    CpxX :=
  (tensorRightComplexFunctor K).obj (cokernel (idealPowerTwoStepInclusion I i))

/-- The quotient map `𝓘^i / 𝓘^(i + 2) ⟶ 𝓘^i / 𝓘^(i + 1)`. -/
private noncomputable def idealPowerTwoStepProjection
    (I : Subobject OX)
    [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (i : ℤ) :
    cokernel (idealPowerTwoStepInclusion I i) ⟶
      cokernel (idealPowerSuccInclusion I i) :=
  cokernel.desc
    (idealPowerTwoStepInclusion I i)
    (cokernel.π (idealPowerSuccInclusion I i))
    (by
      simp [idealPowerTwoStepInclusion, Category.assoc])

/-- The quotient map `𝓘^(i + 1) / 𝓘^(i + 2) ⟶ 𝓘^i / 𝓘^(i + 2)`. -/
private noncomputable def idealPowerTwoStepLift
    (I : Subobject OX)
    [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (i : ℤ) :
    cokernel (idealPowerSuccInclusion I (i + 1)) ⟶
      cokernel (idealPowerTwoStepInclusion I i) :=
  cokernel.desc
    (idealPowerSuccInclusion I (i + 1))
    (idealPowerSuccInclusion I i ≫ cokernel.π (idealPowerTwoStepInclusion I i))
    (by
      simpa only [idealPowerTwoStepInclusion] using
        (cokernel.condition (idealPowerTwoStepInclusion I i)))

omit [CategoryWithHomology ModX] in
private theorem idealPowerTwoStepLift_comp_projection
    (I : Subobject OX)
    [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (i : ℤ) :
    idealPowerTwoStepLift I i ≫ idealPowerTwoStepProjection I i = 0 := by
  apply (cancel_epi (cokernel.π (idealPowerSuccInclusion I (i + 1)))).1
  simp [idealPowerTwoStepLift, idealPowerTwoStepProjection, Category.assoc]

/-- The canonical short exact row
`0 ⟶ K^• ⊗ (𝓘^(i + 1) / 𝓘^(i + 2))
   ⟶ K^• ⊗ (𝓘^i / 𝓘^(i + 2))
   ⟶ K^• ⊗ (𝓘^i / 𝓘^(i + 1)) ⟶ 0`
whose connecting morphism is the Chapter 20 Bockstein differential. -/
noncomputable def idealQuotientBocksteinShortComplex
    (I : Subobject OX)
    [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX) (i : ℤ) :
    ShortComplex CpxX :=
  ShortComplex.mk
    ((tensorRightComplexFunctor K).map (idealPowerTwoStepLift I i))
    ((tensorRightComplexFunctor K).map (idealPowerTwoStepProjection I i))
    (by
      rw [← Functor.map_comp]
      rw [idealPowerTwoStepLift_comp_projection]
      ext j X x
      simp [tensorRightComplexFunctor]
      rfl)

/-- The canonical Chapter 20 Bockstein morphism
`H^i(K^• ⊗ (𝓘^i / 𝓘^(i + 1))) ⟶ H^(i + 1)(K^• ⊗ (𝓘^(i + 1) / 𝓘^(i + 2)))`. -/
noncomputable abbrev idealQuotientBockstein
    (I : Subobject OX)
    [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX) (i : ℤ)
    (hS : (idealQuotientBocksteinShortComplex I K i).ShortExact) :
    (tensorWithIdealPowerQuotientComplex I K i).homology i ⟶
      (tensorWithIdealPowerQuotientComplex I K (i + 1)).homology (i + 1) :=
  hS.δ i (i + 1) (ComplexShape.up_mk i (i + 1) rfl)

/-- Two successive Chapter 20 Bockstein morphisms compose to zero. -/
theorem idealQuotientBockstein_sq
    (I : Subobject OX)
    [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX)
    (hS : ∀ i : ℤ, (idealQuotientBocksteinShortComplex I K i).ShortExact)
    (i : ℤ) :
    idealQuotientBockstein I K i (hS i) ≫
        idealQuotientBockstein I K (i + 1) (hS (i + 1)) = 0 := by
  sorry

/-- The Chapter 20 Bockstein cohomology complex attached to a chosen family of short exact rows of
successive quotient tensor complexes. -/
noncomputable abbrev idealQuotientBocksteinComplex
    (I : Subobject OX)
    [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX)
    (hS : ∀ i : ℤ, (idealQuotientBocksteinShortComplex I K i).ShortExact) :
    CpxX :=
  idealQuotientBocksteinCohomologyComplex
    (tensorWithIdealPowerQuotientComplex I K)
    (fun i ↦ idealQuotientBockstein I K i (hS i))
    (fun i ↦ idealQuotientBockstein_sq I K hS i)

@[simp] theorem idealQuotientBocksteinComplex_X
    (I : Subobject OX)
    [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX)
    (hS : ∀ i : ℤ, (idealQuotientBocksteinShortComplex I K i).ShortExact)
    (i : ℤ) :
    (idealQuotientBocksteinComplex I K hS).X i =
      (tensorWithIdealPowerQuotientComplex I K i).homology i :=
  rfl

@[simp] theorem idealQuotientBocksteinComplex_d
    (I : Subobject OX)
    [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX)
    (hS : ∀ i : ℤ, (idealQuotientBocksteinShortComplex I K i).ShortExact)
    (i : ℤ) :
    (idealQuotientBocksteinComplex I K hS).d i (i + 1) =
      idealQuotientBockstein I K i (hS i) := by
  simpa only [idealQuotientBocksteinComplex] using
    idealQuotientBocksteinCohomologyComplex_d
      (tensorWithIdealPowerQuotientComplex I K)
      (fun i ↦ idealQuotientBockstein I K i (hS i))
      (fun i ↦ idealQuotientBockstein_sq I K hS i)
      i

/-- The underived source complex for Lemma `20.55.8`, obtained by tensoring the Berthelot-Ogus
complex `η[I] K hK` with `𝒪_X / 𝓘`. -/
noncomputable abbrev idealQuotientBocksteinSourceComplex
    (I : Subobject OX)
    [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX) (hK : Pη[I] K) :
    CpxX :=
  (tensorRightComplexFunctor (η[I] K hK)).obj
    (cokernel (I.arrow : (I : ModX) ⟶ OX))

omit [CategoryWithHomology ModX] in
private theorem idealPowerSuccInclusion_tensorRight_commSq
    (I : Subobject OX)
    [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (i : ℤ) :
    CommSq
      (tensorPowerSheafIntOneAddIso (I : ModX) i).hom
      (((tensorRight ((I : ModX) ^⊗ i)).map (I.arrow : (I : ModX) ⟶ OX)))
      (idealPowerSuccInclusion I i)
      (((SheafOfModules.unitIsoTensorUnit ▷ᵢ ((I : ModX) ^⊗ i)) ≪≫
        λ_ ((I : ModX) ^⊗ i)).hom) := by
  refine CommSq.mk ?_
  simp [idealPowerSuccInclusion, idealTensorAction]

/-- The degree-`i` raw comparison from
`(η[I] K hK)^i ⊗ (𝒪_X / 𝓘)` to the degree-`i` term of
`K^• ⊗ (𝓘^i / 𝓘^(i + 1))`. -/
private noncomputable def idealQuotientBocksteinComparisonAmbient
    (I : Subobject OX)
    [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX) (hK : Pη[I] K) (i : ℤ) :
    ((((tensorRight (cokernel (I.arrow : (I : ModX) ⟶ OX))).mapHomologicalComplex
        (up ℤ)).obj (η[I] K hK)).X i) ⟶
      (tensorWithIdealPowerQuotientComplex I K i).X i :=
  (((tensorRight (cokernel (I.arrow : (I : ModX) ⟶ OX))).map
      (kernel.ι (idealEtaComplexToQuotient I K i))) ≫
      (α_ ((I : ModX) ^⊗ i) (K.X i)
        (cokernel (I.arrow : (I : ModX) ⟶ OX))).hom ≫
        tensorHom (𝟙 ((I : ModX) ^⊗ i))
          ((β_ (K.X i) (cokernel (I.arrow : (I : ModX) ⟶ OX))).hom) ≫
          (α_ ((I : ModX) ^⊗ i) (cokernel (I.arrow : (I : ModX) ⟶ OX))
            (K.X i)).inv ≫
            (β_ (((I : ModX) ^⊗ i) ⊗ₘ (cokernel (I.arrow : (I : ModX) ⟶ OX)))
              (K.X i)).hom ≫
              tensorHom (𝟙 (K.X i))
                ((β_ ((I : ModX) ^⊗ i) (cokernel (I.arrow : (I : ModX) ⟶ OX))).hom ≫
                  (PreservesCokernel.iso (tensorRight ((I : ModX) ^⊗ i))
                    (I.arrow : (I : ModX) ⟶ OX)).hom ≫
                    cokernel.map
                      (((tensorRight ((I : ModX) ^⊗ i)).map (I.arrow : (I : ModX) ⟶ OX)))
                      (idealPowerSuccInclusion I i)
                      (tensorPowerSheafIntOneAddIso (I : ModX) i).hom
                      (((SheafOfModules.unitIsoTensorUnit ▷ᵢ ((I : ModX) ^⊗ i)) ≪≫
                        λ_ ((I : ModX) ^⊗ i)).hom)
                      (idealPowerSuccInclusion_tensorRight_commSq I i).w.symm) :
      ((((tensorRight (cokernel (I.arrow : (I : ModX) ⟶ OX))).mapHomologicalComplex
          (up ℤ)).obj (η[I] K hK)).X i) ⟶
        (tensorWithIdealPowerQuotientComplex I K i).X i)

private theorem idealQuotientBocksteinComparisonAmbient_comp_d_eq_zero
    (I : Subobject OX)
    [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (K : CpxX) (hK : Pη[I] K) (i : ℤ) :
    idealQuotientBocksteinComparisonAmbient I K hK i ≫
        (tensorWithIdealPowerQuotientComplex I K i).d i (i + 1) =
      0 := by
  sorry

section Derived

variable [HasCountableCoproducts (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [HasColimits (RingedSpace.Modules X)]
variable [(curriedTensor (RingedSpace.Modules X)).Additive]
variable [∀ ℱ : RingedSpace.Modules X, ((curriedTensor (RingedSpace.Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (RingedSpace.Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (RingedSpace.Modules X))]

/-- Lemma 20.55.8: once the short exact rows of successive quotient tensor complexes are fixed,
the canonical tensor product
`F(QK^•) ⊗^L_{𝒪_X} (𝒪_X/𝓘)[0]` is isomorphic in `D(𝒪_X)` to the resulting Chapter 20
Bockstein cohomology complex built from the successive quotient tensor complexes
`K^• ⊗_{𝒪_X} (𝓘^i / 𝓘^(i + 1))`. -/
@[stacks 0GT9]
theorem idealEtaDerivedFunctor_tensor_quotient_isomorphic_bocksteinComplex
    (I : Subobject OX)
    [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (F : DModX ⥤ DModX) [Functor.IsIdealEtaDerived I F]
    (K : CpxX)
    (hS : ∀ i : ℤ, (idealQuotientBocksteinShortComplex I K i).ShortExact) :
    IsIsomorphic
      (F.obj ((QX).obj K) ⊗^L ((single0).obj 𝒪X/ℐ))
      ((QX).obj (idealQuotientBocksteinComplex I K hS)) := sorry

end Derived

end

end AlgebraicGeometry.RingedSpace
