import Mathlib
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1
import StacksProject_2024.stacks_project.Chap06.Lemma_6_26_4
import StacksProject_2024.stacks_project.Chap06.Lemma_6_21_5
import StacksProject_2024.stacks_project.Chap17.Lemma_17_25_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open SheafOfModules
open SheafOfModules.RingedSite
open TopologicalSpace
open scoped AlgebraicGeometry SectionNonvanishingOpen
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

open AlgebraicGeometry.RingedSpace

variable {X Y : LocallyRingedSpace.{u}}
variable [monoidalModX : MonoidalCategory (RingedSpace.Modules X.toRingedSpace)]
variable [monoidalModY : MonoidalCategory (RingedSpace.Modules Y.toRingedSpace)]

local notation "ModX" => RingedSpace.Modules X.toRingedSpace
local notation "IsInvertibleX" =>
  (fun ℒ : ModX ↦ Functor.IsEquivalence (tensorRight ℒ))

local instance ringedSiteMonoidalCategoryX :
    MonoidalCategory
      (ringedSiteModuleCategory
        (Opens.grothendieckTopology X.toRingedSpace) X.toRingedSpace.sheaf) := by
  simpa using monoidalModX

local instance ringedSiteMonoidalCategoryY :
    MonoidalCategory
      (ringedSiteModuleCategory
        (Opens.grothendieckTopology Y.toRingedSpace) Y.toRingedSpace.sheaf) := by
  simpa using monoidalModY

namespace Hom

private instance pullbackObjUnitToUnit_isIso (f : Y ⟶ X) :
    IsIso (pullbackObjUnitToUnit (RingedSpace.Hom.toRingCatSheafHom f.toShHom)) := by
  -- Proof comment: this is exactly the ringed-space pullback unit comparison specialized to
  -- the underlying morphism of ringed spaces.
  simpa using
    (AlgebraicGeometry.RingedSpace.Hom.pullbackObjUnitToUnit_isIso (f := f.toShHom))

/-- The canonical pullback of a global section along a morphism of locally ringed spaces. -/
noncomputable abbrev pullbackSections (f : Y ⟶ X)
    {ℒ : ModX} (s : ℒ.sections) :
    ((RingedSpace.Hom.pullback f.toShHom).obj ℒ).sections :=
  ((RingedSpace.Hom.pullback f.toShHom).obj ℒ).unitHomEquiv
    ((asIso (pullbackObjUnitToUnit (RingedSpace.Hom.toRingCatSheafHom f.toShHom))).inv ≫
      (RingedSpace.Hom.pullback f.toShHom).map (ℒ.unitHomEquiv.symm s))

end Hom

/- Domain-style sampling for Remark 17.25.11:
- primary domain: nonvanishing loci of sections of invertible module sheaves under pullback along
  morphisms of locally ringed spaces;
- inspected owner declarations:
  `RingedSpace.sectionNonvanishingOpen`,
  `RingedSpace.sectionNonvanishingLocus`,
  `RingedSpace.Hom.pullback`,
  `SheafOfModules.RingedSite.pullback_isInvertible`,
  `SheafOfModules.RingedSite.IsInvertible`,
  `SheafOfModules.unitHomEquiv`,
  `SheafOfModules.pullbackObjUnitToUnit`;
- best owner abstraction: the source-facing owner here is the nonvanishing locus/open of a
  section, while the immediate owner needed by
  `RingedSpace.sectionNonvanishingOpen` is the canonical invertibility owner
  `SheafOfModules.RingedSite.IsInvertible`, propagated along pullback by the owner theorem
  `SheafOfModules.RingedSite.pullback_isInvertible`, and pullback is owned canonically by
  `RingedSpace.Hom.pullback`; the pulled-back section is therefore exposed below through the thin
  locally-ringed-space bridge `LocallyRingedSpace.Hom.pullbackSections`, and the main chapter
  statement here is the source-facing open-subset identity on locally ringed spaces, with the
  underlying set-theoretic nonvanishing-locus equality kept only as a companion view;
- primitive data: a morphism `f : Y ⟶ X`, an `\mathcal O_X`-module `\mathcal L`, and a global
  section `s : \mathcal L(X)`;
- derived API: the equality identifying the inverse image open subset `X_s` with the pullback
  nonvanishing locus `Y_{f^*s}`, together with the canonical pullback-on-global-sections map and
  the companion equality of the corresponding open subsets under the invertibility owner used by
  `sectionNonvanishingOpen`.

Source/core/bridge triage:
- `source-facing`: `sectionNonvanishingLocus` and its associated open subset
  `sectionNonvanishingOpen`;
- `core/canonical`: `IsInvertibleX ℒ`, `SheafOfModules.RingedSite.pullback_isInvertible`, and
  `RingedSpace.Hom.pullback`;
- `bridge/view`: `LocallyRingedSpace.Hom.pullbackSections` and the open-subset equality derived
  from the locus identity.
-/

/-- Helper for Remark 17.25.11: over a local ring, membership in the maximal-ideal multiple of a
module is equivalent to vanishing after tensoring with the residue quotient. -/
theorem mem_maximalIdeal_smul_top_iff_quotient_tensor_zero
    {A : Type u} [CommRing A] [IsLocalRing A]
    {M : Type u} [AddCommGroup M] [Module A M]
    (m : M) :
    m ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) ↔
      TensorProduct.mk A (A ⧸ IsLocalRing.maximalIdeal A) M 1 m = 0 := by
  let e :
      TensorProduct A (A ⧸ IsLocalRing.maximalIdeal A) M ≃ₗ[A]
        M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)) :=
    TensorProduct.quotTensorEquivQuotSMul M (IsLocalRing.maximalIdeal A)
  have hm :
      e (TensorProduct.mk A (A ⧸ IsLocalRing.maximalIdeal A) M 1 m) =
        (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)).mkQ m := by
    -- Proof comment: the quotient-tensor equivalence sends the distinguished pure tensor
    -- `1 ⊗ m` to the quotient class of `m`.
    change e ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (1 : A)) ⊗ₜ[A] m) =
      (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)).mkQ m
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
    simp
  constructor
  · intro hmem
    -- Proof comment: if `m` already lies in `𝔪 M`, then its quotient class is zero, so the
    -- corresponding tensor class vanishes by injectivity of the quotient-tensor equivalence.
    exact e.injective <| by
      rw [hm]
      exact (Submodule.Quotient.mk_eq_zero (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))).2
        hmem
  · intro hzero
    -- Proof comment: conversely, a vanishing tensor has zero image under the quotient-tensor
    -- equivalence, so the quotient class of `m` is zero.
    have hquot :
        (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)).mkQ m = 0 := by
      have heq :
          e (TensorProduct.mk A (A ⧸ IsLocalRing.maximalIdeal A) M 1 m) = e 0 :=
        congrArg e hzero
      rw [hm] at heq
      simpa using heq
    exact (Submodule.Quotient.mk_eq_zero (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))).1
      hquot

/-- Helper for Remark 17.25.11: after extending scalars from `κ` to `K`, the map
`x ↦ 1 ⊗ x` is injective on any `κ`-module. -/
private theorem one_tmul_eq_zero_iff_of_baseChange
    {κ K V : Type u} [Field κ] [Field K] [Algebra κ K]
    [AddCommGroup V] [Module κ V]
    (x : TensorProduct κ K V) :
    TensorProduct.mk K K (TensorProduct κ K V) 1 x = 0 ↔ x = 0 := by
  constructor
  · intro hzero
    -- Proof comment: apply the left-unitor `K ⊗[K] X ≃ X`, which sends `1 ⊗ x` back to `x`.
    have hcollapsed :=
      congrArg (TensorProduct.lid K (TensorProduct κ K V)) hzero
    simpa using hcollapsed
  · intro hx
    -- Proof comment: once `x = 0`, the pure tensor `1 ⊗ x` vanishes by direct simplification.
    simpa [hx]

/-- Helper for Remark 17.25.11: the maximal-ideal residue-field model agrees with the usual
residue field of a local ring. -/
private noncomputable abbrev maximalIdealResidueFieldRingEquiv
    (R : Type u) [CommRing R] [IsLocalRing R] :
    (IsLocalRing.maximalIdeal R).ResidueField ≃+* IsLocalRing.ResidueField R :=
  (RingEquiv.ofBijective
    (algebraMap (IsLocalRing.ResidueField R) ((IsLocalRing.maximalIdeal R).ResidueField))
    (Ideal.bijective_algebraMap_quotient_residueField (IsLocalRing.maximalIdeal R))).symm

/-- Helper for Remark 17.25.11: quotienting a local ring by its maximal ideal identifies the
quotient model with the usual residue field. -/
private noncomputable abbrev maximalIdealQuotientResidueFieldRingEquiv
    (R : Type u) [CommRing R] [IsLocalRing R] :
    (R ⧸ IsLocalRing.maximalIdeal R) ≃+* IsLocalRing.ResidueField R :=
  (RingEquiv.ofBijective
    (algebraMap (R ⧸ IsLocalRing.maximalIdeal R)
      ((IsLocalRing.maximalIdeal R).ResidueField))
    (Ideal.bijective_algebraMap_quotient_residueField (IsLocalRing.maximalIdeal R))).trans
      (maximalIdealResidueFieldRingEquiv R)

/-- Helper for Remark 17.25.11: the quotient-to-residue-field comparison sends the class of `a`
to its usual residue class. -/
private theorem maximalIdealQuotientResidueFieldRingEquiv_apply_algebraMap
    (R : Type u) [CommRing R] [IsLocalRing R] (a : R) :
    maximalIdealQuotientResidueFieldRingEquiv R
        (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R) a) =
      algebraMap R (IsLocalRing.ResidueField R) a := by
  -- Proof comment: both maps factor through the canonical maximal-ideal residue-field quotient.
  change
    maximalIdealResidueFieldRingEquiv R
        (algebraMap R ((IsLocalRing.maximalIdeal R).ResidueField) a) =
      algebraMap R (IsLocalRing.ResidueField R) a
  rw [show algebraMap R ((IsLocalRing.maximalIdeal R).ResidueField) a =
      algebraMap (IsLocalRing.ResidueField R) ((IsLocalRing.maximalIdeal R).ResidueField)
        (algebraMap R (IsLocalRing.ResidueField R) a) by rfl]
  exact (maximalIdealResidueFieldRingEquiv R).apply_symm_apply
    (algebraMap R (IsLocalRing.ResidueField R) a)

/-- Helper for Remark 17.25.11: the maximal-ideal quotient of a local ring is linearly equivalent
over the base ring to its residue field. -/
private noncomputable abbrev maximalIdealQuotientLinearEquivResidueField
    (R : Type u) [CommRing R] [IsLocalRing R] :
    (R ⧸ IsLocalRing.maximalIdeal R) ≃ₗ[R] IsLocalRing.ResidueField R :=
  { toFun := maximalIdealQuotientResidueFieldRingEquiv R
    invFun := (maximalIdealQuotientResidueFieldRingEquiv R).symm
    left_inv := (maximalIdealQuotientResidueFieldRingEquiv R).left_inv
    right_inv := (maximalIdealQuotientResidueFieldRingEquiv R).right_inv
    map_add' := (maximalIdealQuotientResidueFieldRingEquiv R).map_add
    map_smul' := by
      intro a x
      have ha :
          maximalIdealQuotientResidueFieldRingEquiv R
              ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)) a) =
            IsLocalRing.residue R a := by
        simpa using maximalIdealQuotientResidueFieldRingEquiv_apply_algebraMap R a
      -- Proof comment: both scalar actions are multiplication by the residue class of `a`.
      change
        maximalIdealQuotientResidueFieldRingEquiv R
            (((Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)) a) * x) =
          (IsLocalRing.residue R a) *
            maximalIdealQuotientResidueFieldRingEquiv R x
      rw [(maximalIdealQuotientResidueFieldRingEquiv R).map_mul, ha] }

/-- Helper for Remark 17.25.11: the residue-quotient tensor criterion is preserved and reflected
by local base change. -/
private theorem quotientTensor_zero_iff_of_localBaseChange
    {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    {M : Type u} [AddCommGroup M] [Module A M]
    (m : M) :
    TensorProduct.mk A (A ⧸ IsLocalRing.maximalIdeal A) M 1 m = 0 ↔
      TensorProduct.mk B (B ⧸ IsLocalRing.maximalIdeal B) (TensorProduct A B M) 1
        (TensorProduct.mk A B M 1 m) = 0 := by
  let κA := IsLocalRing.ResidueField A
  let κB := IsLocalRing.ResidueField B
  let _ : Algebra κA κB := (IsLocalRing.ResidueField.map (algebraMap A B)).toAlgebra
  let _ : IsScalarTower A κA κB := IsScalarTower.of_algebraMap_eq fun a ↦ by
    -- Proof comment: scalar restriction through `κ(A)` is the residue-field map of the local
    -- homomorphism `A → B`.
    simpa using (IsLocalRing.ResidueField.map_residue (algebraMap A B) a).symm
  let _ : Module.FaithfullyFlat κA κB := inferInstance
  let eA : (A ⧸ IsLocalRing.maximalIdeal A) ≃ₗ[A] κA :=
    maximalIdealQuotientLinearEquivResidueField A
  let eB : (B ⧸ IsLocalRing.maximalIdeal B) ≃ₗ[B] κB :=
    maximalIdealQuotientLinearEquivResidueField B
  let eSrc :
      TensorProduct A (A ⧸ IsLocalRing.maximalIdeal A) M ≃ₗ[A] TensorProduct A κA M :=
    TensorProduct.congr eA (LinearEquiv.refl A M)
  let eTgt :
      TensorProduct B (B ⧸ IsLocalRing.maximalIdeal B) (TensorProduct A B M) ≃ₗ[B]
        TensorProduct B κB (TensorProduct A B M) :=
    TensorProduct.congr eB (LinearEquiv.refl B (TensorProduct A B M))
  let x : TensorProduct A κA M := TensorProduct.mk A κA M 1 m
  let y : TensorProduct A κB M := TensorProduct.mk A κB M 1 m
  let z : TensorProduct B κB (TensorProduct A B M) :=
    TensorProduct.mk B κB (TensorProduct A B M) 1 (TensorProduct.mk A B M 1 m)
  have hsrc :
      TensorProduct.mk A (A ⧸ IsLocalRing.maximalIdeal A) M 1 m = 0 ↔ x = 0 := by
    have hsrc_transport :
        eSrc (TensorProduct.mk A (A ⧸ IsLocalRing.maximalIdeal A) M 1 m) = x := by
      simp [eSrc, eA, x]
    constructor
    · intro hzero
      -- Proof comment: rewrite the source quotient ring as the source residue field.
      calc
        x = eSrc (TensorProduct.mk A (A ⧸ IsLocalRing.maximalIdeal A) M 1 m) := by
              simpa using hsrc_transport.symm
        _ = eSrc 0 := congrArg eSrc hzero
        _ = 0 := by simp
    · intro hzero
      -- Proof comment: the same quotient-to-residue-field equivalence reflects vanishing.
      exact eSrc.injective <| calc
        eSrc (TensorProduct.mk A (A ⧸ IsLocalRing.maximalIdeal A) M 1 m) = x := hsrc_transport
        _ = 0 := hzero
        _ = eSrc 0 := by simp
  have hmid :
      x = 0 ↔ y = 0 := by
    let eMid :
        TensorProduct κA κB (TensorProduct A κA M) ≃ₗ[κB] TensorProduct A κB M :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange A κA κB κB M
    let hx :
        TensorProduct A κA M →ₗ[κA] TensorProduct κA κB (TensorProduct A κA M) :=
      TensorProduct.mk κA κB (TensorProduct A κA M) 1
    have hx_injective : Function.Injective hx := by
      -- Proof comment: extending scalars from one field to another is faithfully flat, so the
      -- canonical tensor map is injective.
      simpa [hx] using
        (Module.FaithfullyFlat.tensorProduct_mk_injective
          (A := κA) (B := κB) (M := TensorProduct A κA M))
    have hmid_transport :
        eMid (TensorProduct.mk κA κB (TensorProduct A κA M) 1 x) = y := by
      simp [eMid, x, y, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    constructor
    · intro hzero
      -- Proof comment: after one scalar extension along `κ(A) → κ(B)`, the source tensor
      -- criterion becomes the same pure tensor over `κ(B)`.
      have houter :
          TensorProduct.mk κA κB (TensorProduct A κA M) 1 x = 0 := by
        simpa [x, hzero]
      calc
        y = eMid (TensorProduct.mk κA κB (TensorProduct A κA M) 1 x) := by
              simpa using hmid_transport.symm
        _ = eMid 0 := congrArg eMid houter
        _ = 0 := by simp
    · intro hzero
      -- Proof comment: conversely, pull back along the same cancellation equivalence and use the
      -- faithful-flat injectivity of the canonical tensor map.
      have houter :
          TensorProduct.mk κA κB (TensorProduct A κA M) 1 x = 0 := by
        exact eMid.injective <| calc
          eMid (TensorProduct.mk κA κB (TensorProduct A κA M) 1 x) = y := hmid_transport
          _ = 0 := hzero
          _ = eMid 0 := by simp
      exact hx_injective <| by simpa [hx] using houter
  have hbase :
      y = 0 ↔ z = 0 := by
    let eBase :
        TensorProduct B κB (TensorProduct A B M) ≃ₗ[κB] TensorProduct A κB M :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange A B κB κB M
    have hbase_transport : eBase z = y := by
      simp [eBase, y, z, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    constructor
    · intro hzero
      -- Proof comment: the canonical `cancelBaseChange` map identifies `1 ⊗ (1 ⊗ m)` with the
      -- pure tensor `1 ⊗ m` over the larger residue field.
      exact eBase.injective <| calc
        eBase z = y := hbase_transport
        _ = 0 := hzero
        _ = eBase 0 := by simp
    · intro hzero
      -- Proof comment: apply the same cancellation map to read vanishing on the target tensor as
      -- vanishing of the corresponding `κ(B)`-fiber tensor over `A`.
      calc
        y = eBase z := by simpa using hbase_transport.symm
        _ = eBase 0 := congrArg eBase hzero
        _ = 0 := by simp
  have htgt :
      TensorProduct.mk B (B ⧸ IsLocalRing.maximalIdeal B) (TensorProduct A B M) 1
          (TensorProduct.mk A B M 1 m) = 0 ↔
        z = 0 := by
    have htgt_transport :
        eTgt
            (TensorProduct.mk B (B ⧸ IsLocalRing.maximalIdeal B) (TensorProduct A B M) 1
              (TensorProduct.mk A B M 1 m)) = z := by
      simp [eTgt, eB, z]
    constructor
    · intro hzero
      -- Proof comment: rewrite the target quotient ring as the target residue field.
      calc
        z = eTgt
              (TensorProduct.mk B (B ⧸ IsLocalRing.maximalIdeal B) (TensorProduct A B M) 1
                (TensorProduct.mk A B M 1 m)) := by
              simpa using htgt_transport.symm
        _ = eTgt 0 := congrArg eTgt hzero
        _ = 0 := by simp
    · intro hzero
      -- Proof comment: the quotient-to-residue-field equivalence also reflects zero on the target.
      exact eTgt.injective <| calc
        eTgt
            (TensorProduct.mk B (B ⧸ IsLocalRing.maximalIdeal B) (TensorProduct A B M) 1
              (TensorProduct.mk A B M 1 m)) = z := htgt_transport
        _ = 0 := hzero
        _ = eTgt 0 := by simp
  exact hsrc.trans (hmid.trans (hbase.trans htgt.symm))

/-- Helper for Remark 17.25.11: evaluating `unitHomEquiv` on the top open is evaluation of the
corresponding unit morphism on the section `1`. -/
private theorem unitHomEquiv_apply_top
    (X : LocallyRingedSpace.{u}) [MonoidalCategory (RingedSpace.Modules X.toRingedSpace)]
    (M : RingedSpace.Modules X.toRingedSpace)
    (φ : SheafOfModules.unit X.toRingedSpace.ringCatSheaf ⟶ M) :
    (M.unitHomEquiv φ).1 (Opposite.op ⊤) =
      (φ.val.app (Opposite.op ⊤))
        (show ((SheafOfModules.unit X.toRingedSpace.ringCatSheaf).val.obj
            (Opposite.op (⊤ : Opens X))) from
          (1 : X.toRingedSpace.presheaf.obj (Opposite.op (⊤ : Opens X)))) := by
  -- Proof comment: `unitHomEquiv` is defined by evaluating the underlying unit morphism on the
  -- distinguished global section `1`.
  rfl

/-- Helper for Remark 17.25.11: evaluating the pulled-back section on the top open unwraps to the
top component of the defining pulled-back unit morphism. -/
private theorem pullbackSections_apply_top
    (f : Y ⟶ X) {ℒ : ModX} (s : ℒ.sections) :
    (LocallyRingedSpace.Hom.pullbackSections f s).1 (Opposite.op ⊤) =
      (((asIso (pullbackObjUnitToUnit (RingedSpace.Hom.toRingCatSheafHom f.toShHom))).inv ≫
          (RingedSpace.Hom.pullback f.toShHom).map (ℒ.unitHomEquiv.symm s)).val.app
        (Opposite.op ⊤))
        (show
          ((SheafOfModules.unit Y.toRingedSpace.ringCatSheaf).val.obj
            (Opposite.op (⊤ : Opens Y))) from
          (1 : Y.toRingedSpace.presheaf.obj (Opposite.op (⊤ : Opens Y)))) := by
  -- Proof comment: this is just `unitHomEquiv_apply_top` specialized to the pulled-back module
  -- and the defining morphism used in `LocallyRingedSpace.Hom.pullbackSections`.
  rw [LocallyRingedSpace.Hom.pullbackSections]
  exact unitHomEquiv_apply_top Y _ _

/-- Helper for Remark 17.25.11: a unit morphism sends the top-open unit germ to the stalk germ of
the associated global section. -/
private theorem unitHomStalkMap_top_eq_germ
    (X : LocallyRingedSpace.{u}) [MonoidalCategory (RingedSpace.Modules X.toRingedSpace)]
    (M : RingedSpace.Modules X.toRingedSpace)
    (φ : SheafOfModules.unit X.toRingedSpace.ringCatSheaf ⟶ M)
    (x : X) :
    RingedSpace.moduleStalkMap x φ
      (TopCat.Presheaf.Γgerm
        (SheafOfModules.unit X.toRingedSpace.ringCatSheaf).val.presheaf
        x
        (show ((SheafOfModules.unit X.toRingedSpace.ringCatSheaf).val.obj
            (Opposite.op (⊤ : Opens X))) from
          (1 : X.toRingedSpace.presheaf.obj (Opposite.op (⊤ : Opens X))))) =
      TopCat.Presheaf.Γgerm M.val.presheaf x ((M.unitHomEquiv φ).1 (Opposite.op ⊤)) := by
  have hx : x ∈ (⊤ : Opens X) := by
    simp
  -- Proof comment: rewrite the stalk map on the top open and then evaluate `unitHomEquiv`
  -- on the distinguished top-open section `1`.
  simpa [TopCat.Presheaf.Γgerm, unitHomEquiv_apply_top] using
    (RingedSpace.moduleStalkMap_germ x φ ⊤ hx
      (show ((SheafOfModules.unit X.toRingedSpace.ringCatSheaf).val.obj
          (Opposite.op (⊤ : Opens X))) from
        (1 : X.toRingedSpace.presheaf.obj (Opposite.op (⊤ : Opens X)))))

/-- Helper for Remark 17.25.11: the stalk pullback comparison should carry the unit tensor of the
source germ to the germ of the pulled-back section. -/
private theorem pullbackUnitGermTransport
    (f : Y ⟶ X) (ℒ : ModX)
    (s : ℒ.sections) (y : Y) :
    let A := X.toRingedSpace.presheaf.stalk (f.base y)
    let B := Y.toRingedSpace.presheaf.stalk y
    let fAB : A →+* B := CommRingCat.Hom.hom (f.stalkMap y)
    let M := RingedSpace.stalkModuleCat ℒ (f.base y)
    let gx := TopCat.Presheaf.Γgerm ℒ.val.presheaf (f.base y) (s.1 (Opposite.op ⊤))
    let _ : Algebra A B := fAB.toAlgebra
    (RingedSpace.Hom.pullbackStalkIso f.toShHom ℒ y).toLinearEquiv
        (TensorProduct.mk A B M 1 gx) =
      TopCat.Presheaf.Γgerm ((RingedSpace.Hom.pullback f.toShHom).obj ℒ).val.presheaf y
        ((LocallyRingedSpace.Hom.pullbackSections f s).1 (Opposite.op ⊤)) := by
  let α : SheafOfModules.unit X.toRingedSpace.ringCatSheaf ⟶ ℒ := ℒ.unitHomEquiv.symm s
  let β :
      SheafOfModules.unit Y.toRingedSpace.ringCatSheaf ⟶
        (RingedSpace.Hom.pullback f.toShHom).obj ℒ :=
    (asIso (pullbackObjUnitToUnit (RingedSpace.Hom.toRingCatSheafHom f.toShHom))).inv ≫
      (RingedSpace.Hom.pullback f.toShHom).map α
  let ux :
      RingedSpace.stalkModuleCat (SheafOfModules.unit X.toRingedSpace.ringCatSheaf) (f.base y) :=
    TopCat.Presheaf.Γgerm
      (SheafOfModules.unit X.toRingedSpace.ringCatSheaf).val.presheaf
      (f.base y)
      (show ((SheafOfModules.unit X.toRingedSpace.ringCatSheaf).val.obj
          (Opposite.op (⊤ : Opens X))) from
        (1 : X.toRingedSpace.presheaf.obj (Opposite.op (⊤ : Opens X))))
  let uy :
      RingedSpace.stalkModuleCat (SheafOfModules.unit Y.toRingedSpace.ringCatSheaf) y :=
    TopCat.Presheaf.Γgerm
      (SheafOfModules.unit Y.toRingedSpace.ringCatSheaf).val.presheaf
      y
      (show ((SheafOfModules.unit Y.toRingedSpace.ringCatSheaf).val.obj
          (Opposite.op (⊤ : Opens Y))) from
        (1 : Y.toRingedSpace.presheaf.obj (Opposite.op (⊤ : Opens Y))))
  have hgx : RingedSpace.moduleStalkMap (f.base y) α ux = gx := by
    -- Proof comment: the source section germ is the stalk image of the top-open unit generator
    -- under the unit morphism corresponding to `s`.
    simpa [α, ux, gx] using
      unitHomStalkMap_top_eq_germ (X := X) (M := ℒ) α (f.base y)
  have hgy :
      RingedSpace.moduleStalkMap y β uy =
        TopCat.Presheaf.Γgerm ((RingedSpace.Hom.pullback f.toShHom).obj ℒ).val.presheaf y
          ((LocallyRingedSpace.Hom.pullbackSections f s).1 (Opposite.op ⊤)) := by
    -- Proof comment: the pulled-back section is defined by the pulled-back unit morphism `β`,
    -- so its germ is the corresponding stalk-map image of the target unit generator.
    simpa [β, uy, pullbackSections_apply_top (f := f) (s := s)] using
      unitHomStalkMap_top_eq_germ
        (X := Y)
        (M := (RingedSpace.Hom.pullback f.toShHom).obj ℒ)
        β
        y
  -- Route correction: normalize both sides to stalk-map images of the unit generators first.
  -- The only remaining gap is the owner-level naturality statement saying that
  -- `RingedSpace.Hom.pullbackStalkIso` transports the tensor of `hgx` to the pulled-back stalk
  -- map `hgy`.
  -- TODO for Remark 17.25.11: specialize `TopCat.Sheaf.stalkPullbackIso_hom_naturality` to `α`,
  -- compose it with the unit comparison from `pullbackObjUnitToUnit`, rewrite the two stalk-map
  -- terms by `hgx` and `hgy`, and then identify the remaining extension-of-scalars generator with
  -- `TensorProduct.mk A B M 1 ux`.
  have htransport :
      (RingedSpace.Hom.pullbackStalkIso f.toShHom ℒ y).toLinearEquiv
          (TensorProduct.mk
            (X.toRingedSpace.presheaf.stalk (f.base y))
            (Y.toRingedSpace.presheaf.stalk y)
            (RingedSpace.stalkModuleCat ℒ (f.base y))
            1
            (RingedSpace.moduleStalkMap (f.base y) α ux)) =
        RingedSpace.moduleStalkMap y β uy := by
    -- Proof comment: reduce the pullback-stalk statement to the sheaf-level stalk pullback
    -- naturality square for `α`, evaluated on the unit germ.
    simpa [β, RingedSpace.moduleStalkMap, Category.assoc] using
      congrArg (fun k ↦ k ux)
        (TopCat.Sheaf.stalkPullbackIso_hom_naturality
          (A := AddCommGrpCat.{u}) (f := f.base) (x := y) α.val)
  -- Proof comment: substitute the source and target unit-germ descriptions prepared above.
  calc
    (RingedSpace.Hom.pullbackStalkIso f.toShHom ℒ y).toLinearEquiv
        (TensorProduct.mk
          (X.toRingedSpace.presheaf.stalk (f.base y))
          (Y.toRingedSpace.presheaf.stalk y)
          (RingedSpace.stalkModuleCat ℒ (f.base y))
          1
          gx) =
      (RingedSpace.Hom.pullbackStalkIso f.toShHom ℒ y).toLinearEquiv
        (TensorProduct.mk
          (X.toRingedSpace.presheaf.stalk (f.base y))
          (Y.toRingedSpace.presheaf.stalk y)
          (RingedSpace.stalkModuleCat ℒ (f.base y))
          1
          (RingedSpace.moduleStalkMap (f.base y) α ux)) := by
            rw [hgx]
    _ = RingedSpace.moduleStalkMap y β uy := htransport
    _ =
      TopCat.Presheaf.Γgerm ((RingedSpace.Hom.pullback f.toShHom).obj ℒ).val.presheaf y
        ((LocallyRingedSpace.Hom.pullbackSections f s).1 (Opposite.op ⊤)) := hgy

/-- Helper for Remark 17.25.11: `TensorProduct.congr` sends a pure residue-quotient tensor
`1 ⊗ m` to `1 ⊗ e(m)` when the second tensor factor is transported by a linear equivalence. -/
private theorem residueQuotientTensorCongr_apply
    {B : Type u} [CommRing B] [IsLocalRing B]
    {M N : Type u} [AddCommGroup M] [Module B M]
    [AddCommGroup N] [Module B N]
    (e : M ≃ₗ[B] N) (m : M) :
    (TensorProduct.congr
        (LinearEquiv.refl B (B ⧸ IsLocalRing.maximalIdeal B))
        e)
      (TensorProduct.mk B (B ⧸ IsLocalRing.maximalIdeal B) M 1 m) =
      TensorProduct.mk B (B ⧸ IsLocalRing.maximalIdeal B) N 1 (e m) := by
  -- Proof comment: evaluate `TensorProduct.congr` on a pure tensor and simplify the identity
  -- action on the residue-quotient factor.
  simpa using
    (TensorProduct.congr_tmul
      (LinearEquiv.refl B (B ⧸ IsLocalRing.maximalIdeal B))
      e
      (1 : B ⧸ IsLocalRing.maximalIdeal B)
      m)

/-- Helper for Remark 17.25.11: the residue-quotient tensor of a germ vanishes exactly when the
residue-quotient tensor of its pulled-back germ vanishes. -/
theorem pullback_germ_quotient_tensor_zero_iff
    (f : Y ⟶ X) (ℒ : ModX)
    (s : ℒ.sections) (y : Y) :
    TensorProduct.mk
        (X.toRingedSpace.presheaf.stalk (f.base y))
        ((X.toRingedSpace.presheaf.stalk (f.base y)) ⧸
          IsLocalRing.maximalIdeal (X.toRingedSpace.presheaf.stalk (f.base y)))
        (RingedSpace.stalkModuleCat ℒ (f.base y))
        1
        (TopCat.Presheaf.Γgerm ℒ.val.presheaf (f.base y) (s.1 (Opposite.op ⊤))) = 0 ↔
      TensorProduct.mk
        (Y.toRingedSpace.presheaf.stalk y)
        ((Y.toRingedSpace.presheaf.stalk y) ⧸
          IsLocalRing.maximalIdeal (Y.toRingedSpace.presheaf.stalk y))
        (RingedSpace.stalkModuleCat ((RingedSpace.Hom.pullback f.toShHom).obj ℒ) y)
        1
        (TopCat.Presheaf.Γgerm ((RingedSpace.Hom.pullback f.toShHom).obj ℒ).val.presheaf y
          ((LocallyRingedSpace.Hom.pullbackSections f s).1 (Opposite.op ⊤))) = 0 := by
  let A := X.toRingedSpace.presheaf.stalk (f.base y)
  let B := Y.toRingedSpace.presheaf.stalk y
  let fAB : A →+* B := CommRingCat.Hom.hom (f.stalkMap y)
  letI : Algebra A B := fAB.toAlgebra
  letI : IsLocalHom (algebraMap A B) := by
    change IsLocalHom fAB
    infer_instance
  let M := RingedSpace.stalkModuleCat ℒ (f.base y)
  let gx := TopCat.Presheaf.Γgerm ℒ.val.presheaf (f.base y) (s.1 (Opposite.op ⊤))
  let gy :=
    TopCat.Presheaf.Γgerm ((RingedSpace.Hom.pullback f.toShHom).obj ℒ).val.presheaf y
      ((LocallyRingedSpace.Hom.pullbackSections f s).1 (Opposite.op ⊤))
  let gxBase : (ModuleCat.extendScalars fAB).obj M := TensorProduct.mk A B M 1 gx
  let eStalk := (RingedSpace.Hom.pullbackStalkIso f.toShHom ℒ y).toLinearEquiv
  let eQuot :
      TensorProduct B (B ⧸ IsLocalRing.maximalIdeal B) ((ModuleCat.extendScalars fAB).obj M) ≃ₗ[B]
        TensorProduct B (B ⧸ IsLocalRing.maximalIdeal B)
          (RingedSpace.stalkModuleCat ((RingedSpace.Hom.pullback f.toShHom).obj ℒ) y) :=
    TensorProduct.congr
      (LinearEquiv.refl B (B ⧸ IsLocalRing.maximalIdeal B))
      eStalk
  have hBase :
      TensorProduct.mk
          A
          (A ⧸ IsLocalRing.maximalIdeal A)
          M
          1
          gx = 0 ↔
        TensorProduct.mk
            B
            (B ⧸ IsLocalRing.maximalIdeal B)
            ((ModuleCat.extendScalars fAB).obj M)
            1
            gxBase = 0 := by
    -- Proof comment: the local-base-change criterion already identifies vanishing of the source
    -- residue-quotient tensor with vanishing of the modeled tensor after extension of scalars.
    simpa [A, B, M, fAB, gx, gxBase] using
      (quotientTensor_zero_iff_of_localBaseChange
        (A := A)
        (B := B)
        (M := M)
        gx)
  have hInner :
      eStalk gxBase = gy := by
    -- Proof comment: this is the remaining stalk-level bridge from the modeled base-change germ
    -- to the actual germ of the pulled-back section.
    simpa [A, B, fAB, M, gx, gxBase, gy, eStalk] using
      pullbackUnitGermTransport (f := f) (ℒ := ℒ) (s := s) (y := y)
  have hTransport :
      TensorProduct.mk
          B
          (B ⧸ IsLocalRing.maximalIdeal B)
          ((ModuleCat.extendScalars fAB).obj M)
          1
          gxBase = 0 ↔
        TensorProduct.mk
            B
            (B ⧸ IsLocalRing.maximalIdeal B)
            (RingedSpace.stalkModuleCat ((RingedSpace.Hom.pullback f.toShHom).obj ℒ) y)
            1
            gy = 0 := by
    constructor
    · intro hZero
      -- Proof comment: apply the outer tensor equivalence and rewrite its value on the modeled
      -- pure tensor by the generic `TensorProduct.congr` computation plus the inner germ bridge.
      calc
        TensorProduct.mk
            B
            (B ⧸ IsLocalRing.maximalIdeal B)
            (RingedSpace.stalkModuleCat ((RingedSpace.Hom.pullback f.toShHom).obj ℒ) y)
            1
            gy =
            eQuot
              (TensorProduct.mk
                B
                (B ⧸ IsLocalRing.maximalIdeal B)
                ((ModuleCat.extendScalars fAB).obj M)
                1
                gxBase) := by
              symm
              calc
                eQuot
                    (TensorProduct.mk
                      B
                      (B ⧸ IsLocalRing.maximalIdeal B)
                      ((ModuleCat.extendScalars fAB).obj M)
                      1
                      gxBase) =
                    TensorProduct.mk
                      B
                      (B ⧸ IsLocalRing.maximalIdeal B)
                      (RingedSpace.stalkModuleCat ((RingedSpace.Hom.pullback f.toShHom).obj ℒ) y)
                      1
                      (eStalk gxBase) := by
                        simpa [eQuot] using residueQuotientTensorCongr_apply eStalk gxBase
                _ = TensorProduct.mk
                      B
                      (B ⧸ IsLocalRing.maximalIdeal B)
                      (RingedSpace.stalkModuleCat ((RingedSpace.Hom.pullback f.toShHom).obj ℒ) y)
                      1
                      gy := by rw [hInner]
        _ = eQuot 0 := congrArg eQuot hZero
        _ = 0 := by simp
    · intro hZero
      -- Proof comment: the same linear equivalence reflects zero, so the actual pulled-back
      -- tensor vanishes only if the modeled tensor already vanished.
      exact eQuot.injective <| calc
        eQuot
            (TensorProduct.mk
              B
              (B ⧸ IsLocalRing.maximalIdeal B)
              ((ModuleCat.extendScalars fAB).obj M)
              1
              gxBase) =
          TensorProduct.mk
            B
            (B ⧸ IsLocalRing.maximalIdeal B)
            (RingedSpace.stalkModuleCat ((RingedSpace.Hom.pullback f.toShHom).obj ℒ) y)
            1
            gy := by
              calc
                eQuot
                    (TensorProduct.mk
                      B
                      (B ⧸ IsLocalRing.maximalIdeal B)
                      ((ModuleCat.extendScalars fAB).obj M)
                      1
                      gxBase) =
                    TensorProduct.mk
                      B
                      (B ⧸ IsLocalRing.maximalIdeal B)
                      (RingedSpace.stalkModuleCat ((RingedSpace.Hom.pullback f.toShHom).obj ℒ) y)
                      1
                      (eStalk gxBase) := by
                        simpa [eQuot] using residueQuotientTensorCongr_apply eStalk gxBase
                _ = TensorProduct.mk
                      B
                      (B ⧸ IsLocalRing.maximalIdeal B)
                      (RingedSpace.stalkModuleCat ((RingedSpace.Hom.pullback f.toShHom).obj ℒ) y)
                      1
                      gy := by rw [hInner]
        _ = 0 := hZero
        _ = eQuot 0 := by simp
  -- Proof comment: combine the existing local-base-change criterion with the specialized outer
  -- tensor transport to reach the actual pulled-back stalk expression.
  exact hBase.trans hTransport

-- Proof sketch: the germ of the pulled-back section at `y : Y` is the image of the germ of `s`
-- at `f(y)` under base change along the local ring map
-- `\mathcal O_{X,f(y)} → \mathcal O_{Y,y}`. For an invertible module, nonvanishing is the
-- condition that the germ is not contained in the maximal-ideal multiple of the stalk, and this
-- condition is preserved and reflected by local base change.
/-- Companion to Remark 17.25.11: without using invertibility, the underlying nonvanishing loci
agree set-theoretically after pulling back the section along `f`. -/
theorem preimage_sectionNonvanishingLocus_eq_sectionNonvanishingLocus_pullback
    (f : Y ⟶ X) (ℒ : ModX)
    (s : ℒ.sections) :
    f.base ⁻¹' sectionNonvanishingLocus X.toRingedSpace ℒ s =
      sectionNonvanishingLocus Y.toRingedSpace ((RingedSpace.Hom.pullback f.toShHom).obj ℒ)
        (LocallyRingedSpace.Hom.pullbackSections f s) := by
  ext y
  -- Proof comment: unfold both loci so the pointwise goal is a comparison of stalk membership in
  -- maximal-ideal multiples.
  simp only [Set.mem_preimage, RingedSpace.sectionNonvanishingLocus, Set.mem_setOf_eq]
  -- Proof comment: residue-quotient tensor vanishing is the stable formulation of those
  -- maximal-ideal membership conditions.
  rw [mem_maximalIdeal_smul_top_iff_quotient_tensor_zero,
    mem_maximalIdeal_smul_top_iff_quotient_tensor_zero]
  -- Proof comment: the remaining pointwise comparison is exactly the pullback invariance of the
  -- residue-quotient germ tensor.
  exact not_congr (pullback_germ_quotient_tensor_zero_iff (f := f) (ℒ := ℒ) (s := s) (y := y))

/-- Remark 17.25.11: for a morphism of locally ringed spaces `f : Y → X`, an invertible
`\mathcal O_X`-module `\mathcal L`, and a global section `s`, the inverse image open subset
`(X.toRingedSpace)_[s]` is the nonvanishing open subset `(Y.toRingedSpace)_[f^*s]` cut out by
the pulled-back section. -/
theorem comap_sectionNonvanishingOpen_eq_sectionNonvanishingOpen_pullback
    (f : Y ⟶ X)
    (ℒ : ModX)
    [IsInvertibleX ℒ]
    (s : ℒ.sections) :
    Opens.comap f.base.hom ((X.toRingedSpace)_[s]) =
      (Y.toRingedSpace)_[LocallyRingedSpace.Hom.pullbackSections f s] := by
  apply TopologicalSpace.Opens.ext
  simpa using
    preimage_sectionNonvanishingLocus_eq_sectionNonvanishingLocus_pullback f ℒ s

end AlgebraicGeometry.LocallyRingedSpace
