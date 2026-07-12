import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.Chap20.Lemma_20_55_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

open scoped IdealEtaComplex

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X)] [SymmetricCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)] [Abelian (RingedSpace.Modules X)]
local notation "ModX" => RingedSpace.Modules X
local notation "CpxX" => CochainComplex ModX ℤ
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)

variable {I : Subobject 𝒪X}
local notation "Pη[" I "]" => (IsIdealTorsionFreeComplex I : ObjectProperty CpxX)

section Map

variable (I : Subobject 𝒪X)
variable [SatisfiesLocallyPrincipalRegularIdealCondition I]
variable {K L : CpxX}

/- Domain-style sampling for the Berthelot-Ogus `η_ℐ` construction on complexes:
- sampled owner declarations in this chapter/project:
  `idealEtaComplex`,
  `IdealEtaComplex.map`,
  `IdealEtaComplex.map_quasiIso`,
  `CategoryTheory.CommSq`,
  `kernel.map`,
  `cokernel.map`,
  `QuasiIso`.
- best owner abstraction: no earlier Chapter 20 declaration already owns the exact morphism-level
  interface for sheaf-level Berthelot-Ogus complexes, so this file remains the owner of the
  source-facing morphism `IdealEtaComplex.map`, reusing the namespace introduced around
  `idealEtaComplex` in Lemma `20.55.5` and following the Chapter 15 owner pattern
  `BerthelotOgusInt.map`; these maps canonically assemble into the underived functor on the
  canonical full subcategory `(Pη[I]).FullSubcategory`. The ambient tensor, quotient, and kernel
  maps are derived implementation data built from the canonical kernel/cokernel owners.
- source/core/bridge triage:
  - `source-facing`: `IdealEtaComplex.map` and `IdealEtaComplex.map_quasiIso`;
  - `core/canonical`: `idealEtaComplex`, `IdealEtaComplex.torsionFreeFunctor`,
    `CategoryTheory.CommSq`, `kernel.map`, `cokernel.map`, and `QuasiIso`;
  - `bridge/view`: the degreewise naturality squares relating the ambient tensor terms, quotient
    maps, and kernel maps needed to form `η[I] K hK` and `η[I] L hL`.
- derived API: the degreewise ambient/quotient/kernel maps and their naturality squares. -/

section Morphism

/-- The canonical tensor-factor map induced by a morphism of complexes on the auxiliary
`𝓘^⊗ i ⊗ 𝓕^j` terms. -/
private noncomputable def idealEtaComplexTensorObjMap
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (φ : K ⟶ L) (i j : ℤ) :
    (idealEtaComplexTensorObj I K i j : ModX) ⟶
      (idealEtaComplexTensorObj I L i j : ModX) :=
  (tensorLeft ((I : ModX) ^⊗ i)).map (φ.f j)

private noncomputable def tensorUnitLeftNatIso :
    tensorLeft (SheafOfModules.unit X.ringCatSheaf : ModX) ≅ 𝟭 ModX :=
  (tensoringLeft ModX).mapIso SheafOfModules.unitIsoTensorUnit ≪≫
    MonoidalCategory.leftUnitorNatIso ModX

private theorem idealTensorAction_naturality
    (I : Subobject 𝒪X) {ℱ 𝒢 : ModX} (f : ℱ ⟶ 𝒢) :
    (tensorLeft (I : ModX)).map f ≫ idealTensorAction I 𝒢 =
      idealTensorAction I ℱ ≫ f := by
  sorry

private noncomputable def idealTensorActionNat
    (I : Subobject 𝒪X) (A : ModX) :
    tensorLeft A ⋙ tensorLeft (I : ModX) ⟶ tensorLeft A where
  app Z := idealTensorAction I (A ⊗ Z)
  naturality {_ _} f := idealTensorAction_naturality I ((tensorLeft A).map f)

private noncomputable def idealEtaComplexNextPowerInclusionNat
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (i : ℤ) :
    tensorLeft ((I : ModX) ^⊗ (i + 1)) ⟶ tensorLeft ((I : ModX) ^⊗ i) :=
  (((tensoringLeft ModX).mapIso (tensorPowerSheafIntOneAddIso (I : ModX) i).symm) ≪≫
      tensorLeftTensor (I : ModX) ((I : ModX) ^⊗ i)).hom ≫
    idealTensorActionNat I ((I : ModX) ^⊗ i)

-- Proof sketch: both sides are obtained by tensoring the chain-map identity
-- `φ.f i ≫ L.d i (i + 1) = K.d i (i + 1) ≫ φ.f (i + 1)` with the fixed tensor power
-- `𝓘^⊗ i`.
/-- The ambient Berthelot-Ogus differentials are natural in the complex variable. -/
private theorem idealEtaComplexAmbientDifferential_commSq
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (φ : K ⟶ L)
    (i : ℤ) :
    CommSq
      (idealEtaComplexTensorObjMap I φ i i :
        (idealEtaComplexAmbientObj I K i : ModX) ⟶
          (idealEtaComplexAmbientObj I L i : ModX))
      (idealEtaComplexAmbientDifferential I K i)
      (idealEtaComplexAmbientDifferential I L i)
      (idealEtaComplexTensorObjMap I φ i (i + 1) :
        (idealEtaComplexDifferentialTarget I K i : ModX) ⟶
          (idealEtaComplexDifferentialTarget I L i : ModX)) := by
  refine CommSq.mk ?_
  simpa [idealEtaComplexTensorObjMap, idealEtaComplexAmbientDifferential] using
    congrArg ((tensorLeft ((I : ModX) ^⊗ i)).map) (φ.comm i (i + 1))

-- Proof sketch: the next-power inclusion acts only on the tensor-power factor, while the map
-- induced by `φ` acts only on the complex term, so the two constructions commute degreewise.
/-- The next-power inclusions in the Berthelot-Ogus construction are natural in the complex. -/
private theorem idealEtaComplexNextPowerInclusion_commSq
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (φ : K ⟶ L)
    (i : ℤ) :
    CommSq
      (idealEtaComplexTensorObjMap I φ (i + 1) (i + 1) :
        (idealEtaComplexAmbientObj I K (i + 1) : ModX) ⟶
          (idealEtaComplexAmbientObj I L (i + 1) : ModX))
      (idealEtaComplexNextPowerInclusion I K i)
      (idealEtaComplexNextPowerInclusion I L i)
      (idealEtaComplexTensorObjMap I φ i (i + 1) :
        (idealEtaComplexDifferentialTarget I K i : ModX) ⟶
          (idealEtaComplexDifferentialTarget I L i : ModX)) := by
  refine CommSq.mk ?_
  simpa [idealEtaComplexTensorObjMap, idealEtaComplexNextPowerInclusion,
    idealEtaComplexNextPowerInclusionNat, idealTensorActionNat, Category.assoc] using
    NatTrans.naturality (idealEtaComplexNextPowerInclusionNat I i) (φ.f (i + 1))

/-- The map on the quotient targets defining the Berthelot-Ogus kernels, induced by a morphism of
complexes. -/
private noncomputable def idealEtaComplexQuotientTargetMap
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (φ : K ⟶ L)
    (i : ℤ) :
    (idealEtaComplexQuotientTarget I K i : ModX) ⟶
      (idealEtaComplexQuotientTarget I L i : ModX) :=
  cokernel.map
    (idealEtaComplexNextPowerInclusion I K i)
    (idealEtaComplexNextPowerInclusion I L i)
    (idealEtaComplexTensorObjMap I φ i (i + 1))
    (idealEtaComplexTensorObjMap I φ i (i + 1))
    (idealEtaComplexNextPowerInclusion_commSq I φ i).w.symm

-- Proof sketch: compose `idealEtaComplexAmbientDifferential_commSq.w` with the cokernel
-- projection and use the defining relation of `cokernel.map`.
/-- The quotient maps defining the Berthelot-Ogus kernels are natural in the complex. -/
private theorem idealEtaComplexToQuotient_commSq
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (φ : K ⟶ L)
    (i : ℤ) :
    CommSq
      (idealEtaComplexTensorObjMap I φ i i :
        (idealEtaComplexAmbientObj I K i : ModX) ⟶
          (idealEtaComplexAmbientObj I L i : ModX))
      (idealEtaComplexToQuotient I K i)
      (idealEtaComplexToQuotient I L i)
      (idealEtaComplexQuotientTargetMap I φ i :
        (idealEtaComplexQuotientTarget I K i : ModX) ⟶
          (idealEtaComplexQuotientTarget I L i : ModX)) := by
  refine CommSq.mk ?_
  calc
    (idealEtaComplexTensorObjMap I φ i i :
        (idealEtaComplexAmbientObj I K i : ModX) ⟶
          (idealEtaComplexAmbientObj I L i : ModX)) ≫
        idealEtaComplexToQuotient I L i
      =
        (idealEtaComplexTensorObjMap I φ i i :
          (idealEtaComplexAmbientObj I K i : ModX) ⟶
            (idealEtaComplexAmbientObj I L i : ModX)) ≫
          idealEtaComplexAmbientDifferential I L i ≫
            cokernel.π (idealEtaComplexNextPowerInclusion I L i) := by
              simp [idealEtaComplexToQuotient]
    _ =
        idealEtaComplexAmbientDifferential I K i ≫
          (idealEtaComplexTensorObjMap I φ i (i + 1) :
            (idealEtaComplexDifferentialTarget I K i : ModX) ⟶
              (idealEtaComplexDifferentialTarget I L i : ModX)) ≫
            cokernel.π (idealEtaComplexNextPowerInclusion I L i) := by
              simpa [Category.assoc] using
                congrArg
                  (fun t ↦ t ≫ cokernel.π (idealEtaComplexNextPowerInclusion I L i))
                  (idealEtaComplexAmbientDifferential_commSq I φ i).w
    _ =
        idealEtaComplexAmbientDifferential I K i ≫
          cokernel.π (idealEtaComplexNextPowerInclusion I K i) ≫
            (idealEtaComplexQuotientTargetMap I φ i :
              (idealEtaComplexQuotientTarget I K i : ModX) ⟶
                (idealEtaComplexQuotientTarget I L i : ModX)) := by
              simpa [Category.assoc, idealEtaComplexQuotientTargetMap] using
                congrArg
                  (fun t ↦ idealEtaComplexAmbientDifferential I K i ≫ t)
                  (cokernel.π_desc
                    (idealEtaComplexNextPowerInclusion I K i)
                    (idealEtaComplexTensorObjMap I φ i (i + 1))
                    (idealEtaComplexNextPowerInclusion_commSq I φ i).w.symm)
    _ = idealEtaComplexToQuotient I K i ≫ idealEtaComplexQuotientTargetMap I φ i := by
          simp [idealEtaComplexToQuotient, Category.assoc]

/-- The degree-`i` map on the Berthelot-Ogus kernels induced by a morphism of complexes. -/
private noncomputable def idealEtaComplexObjMap
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (φ : K ⟶ L)
    (i : ℤ) :
    (idealEtaComplexObj I K i : ModX) ⟶
      (idealEtaComplexObj I L i : ModX) :=
  kernel.map
    (idealEtaComplexToQuotient I K i)
    (idealEtaComplexToQuotient I L i)
    (idealEtaComplexTensorObjMap I φ i i)
    (idealEtaComplexQuotientTargetMap I φ i)
    (idealEtaComplexToQuotient_commSq I φ i).w.symm

section TorsionFree

-- Proof sketch: unfold the differentials on `idealEtaComplex`; both sides are the lifts of the
-- same ambient morphism, and the required equality follows from the kernel-map universal property.
/-- The degreewise maps induced on Berthelot-Ogus kernels commute with the differentials. -/
private theorem idealEtaComplexObjMap_commSq
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (hK : Pη[I] K) (hL : Pη[I] L) (φ : K ⟶ L)
    (i j : ℤ) (hij : (up ℤ).Rel i j) :
    CommSq
      (idealEtaComplexObjMap I φ i :
        (idealEtaComplexObj I K i : ModX) ⟶
          (idealEtaComplexObj I L i : ModX))
      ((η[I] K hK).d i j)
      ((η[I] L hL).d i j)
      (idealEtaComplexObjMap I φ j :
        (idealEtaComplexObj I K j : ModX) ⟶
          (idealEtaComplexObj I L j : ModX)) := sorry

namespace IdealEtaComplex

/-- The morphism of Berthelot-Ogus complexes induced by a morphism of
`𝓘`-torsion free complexes. -/
  noncomputable def map
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (φ : K ⟶ L) (hK : IsIdealTorsionFreeComplex I K) (hL : IsIdealTorsionFreeComplex I L) :
    η[I] K hK ⟶ η[I] L hL where
  f i := idealEtaComplexObjMap I φ i
  comm' i j hij := (idealEtaComplexObjMap_commSq I hK hL φ i j hij).w

-- Proof sketch: `IdealEtaComplex.map I` is assembled degreewise from `kernel.map`, so for the
-- identity morphism of `K` each degree map is the identity on the defining kernel object.
private theorem map_id
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (hK : IsIdealTorsionFreeComplex I K) :
    map I (𝟙 K) hK hK = 𝟙 (η[I] K hK) := by
  sorry

section Composition

variable {M : CpxX}

-- Proof sketch: each degree map of `IdealEtaComplex.map I` is obtained from functorial ambient,
-- cokernel, and kernel maps, so the map for `φ ≫ ψ` equals the composite of the maps for `φ`
-- and `ψ` degreewise.
private theorem map_comp
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (φ : K ⟶ L) (ψ : L ⟶ M)
    (hK : IsIdealTorsionFreeComplex I K) (hL : IsIdealTorsionFreeComplex I L)
    (hM : IsIdealTorsionFreeComplex I M) :
    map I (φ ≫ ψ) hK hM = map I φ hK hL ≫ map I ψ hL hM := by
  sorry

end Composition

/-- The Berthelot-Ogus construction on the full subcategory of
`𝓘`-torsion free complexes. -/
  noncomputable def torsionFreeFunctor
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    :
    CategoryTheory.ObjectProperty.FullSubcategory
      (IsIdealTorsionFreeComplex I : ObjectProperty CpxX) ⥤ CpxX where
  obj K := η[I] K.obj K.property
  map {X Y} φ := IdealEtaComplex.map I φ.hom X.property Y.property
  map_id K := map_id I K.property
  map_comp {X Y Z} f g :=
    map_comp I f.hom g.hom X.property Y.property Z.property

-- Proof sketch: apply the canonical homology isomorphisms of Lemma `20.55.5` to the source and
-- target complexes, observe that they are compatible with maps of complexes, and reduce to the
-- fact that a quasi-isomorphism induces isomorphisms on the quotient homology sheaves.
instance
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (φ : K ⟶ L) [QuasiIso φ]
    [hK : IsIdealTorsionFreeComplex I K] [hL : IsIdealTorsionFreeComplex I L] :
    QuasiIso (map I φ hK hL) := by
  sorry

/-- Lemma 20.55.6: in Situation `20.55.2`, if `𝓕^• ⟶ 𝒢^•` is a
quasi-isomorphism of complexes of `𝓘`-torsion free `𝒪_X`-modules, then the
induced map `η[𝓘] 𝓕^• ⟶ η[𝓘] 𝒢^•` is also a
quasi-isomorphism. -/
@[stacks 0F8P]
theorem map_quasiIso
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (φ : K ⟶ L) (hφ : QuasiIso φ)
    (hK : IsIdealTorsionFreeComplex I K) (hL : IsIdealTorsionFreeComplex I L) :
    QuasiIso (map I φ hK hL) := by
  let _ : QuasiIso φ := hφ
  let _ : IsIdealTorsionFreeComplex I K := hK
  let _ : IsIdealTorsionFreeComplex I L := hL
  infer_instance

end IdealEtaComplex

end TorsionFree
end Morphism

end Map

end AlgebraicGeometry.RingedSpace
