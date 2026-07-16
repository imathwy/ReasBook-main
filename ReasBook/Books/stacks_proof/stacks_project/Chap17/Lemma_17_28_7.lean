import Mathlib
import stacks_proof.stacks_project.Chap06.Definition_6_26_1
import stacks_proof.stacks_project.Chap06.Definition_6_27_1
import stacks_proof.stacks_project.Chap06.Lemma_6_22_1
import stacks_proof.stacks_project.Chap06.Lemma_6_26_4
import stacks_proof.stacks_project.Chap17.Lemma_17_28_4
import stacks_proof.stacks_project.Chap17.Lemma_17_28_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopologicalSpace
open AlgebraicGeometry
open TopCat.Presheaf

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable {O₁ O₂ : X.Sheaf CommRingCat.{u}}

section

variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/- Domain-style sampling for Lemma 17.28.7:
- primary domain: stalks of sheaves of relative differentials on a topological space;
- sampled owner declarations:
  `TopCat.Sheaf.inverseImage_relativeDifferentialsIso`,
  `TopCat.Sheaf.pullbackRingSheafIso`,
  `TopCat.Sheaf.relativeDifferentials`,
  `AlgebraicGeometry.RingedSpace.stalkModuleCat`,
  `TopCat.Presheaf.stalkFunctor`;
- best owner abstraction: specialize the inverse-image comparison from Lemma `17.28.6` to the
  constant map from the one-point space to `X`, then transport the resulting top-open modules back
  to the usual stalk ring;
- primitive data: a morphism `φ : O₁ ⟶ O₂` and a point `x : X`;
- derived API: the local point-pullback comparison isomorphisms below, culminating in the stalk
  formula.

Source/core/bridge triage:
- `source-facing`: the textbook stalk formula `(Ω_{O₂/O₁})_x ≅ Ω_{(O₂)_x/(O₁)_x}`;
- `core/canonical`: `inverseImage_relativeDifferentialsIso`, `pullbackRingSheafIso`,
  `RingedSpace.stalkModuleCat`, and `stalkFunctor`;
- `bridge/view`: the constant-map pullback to the one-point space and the identification of its top
  open with the ordinary stalk. -/

/-- Helper for Lemma 17.28.7: every neighborhood of the unique point of `TopCat.of PUnit` is the
top open. -/
private theorem punit_openNhds_eq_top
    (U : OpenNhds (PUnit.unit : TopCat.of PUnit.{u})) :
    U = ⊤ := by
  -- The one-point space has only one open containing its unique point.
  ext y
  cases y
  simp [U.2]

/-- Helper for Lemma 17.28.7: on the one-point space, the germ map from the top open is an
isomorphism for every presheaf. -/
private theorem punit_presheaf_germ_isIso
    {C : Type*} [CategoryTheory.Category C] [CategoryTheory.Limits.HasColimits C]
    (F : (TopCat.of PUnit.{u}).Presheaf C) :
    IsIso (Γgerm F PUnit.unit) := by
  let G : (OpenNhds (PUnit.unit : TopCat.of PUnit.{u}))ᵒᵖ ⥤ C :=
    (OpenNhds.inclusion (PUnit.unit : TopCat.of PUnit.{u})).op ⋙ F
  let j : (OpenNhds (PUnit.unit : TopCat.of PUnit.{u}))ᵒᵖ :=
    Opposite.op (⊤ : OpenNhds (PUnit.unit : TopCat.of PUnit.{u}))
  have hj : IsInitial j := by
    -- The neighborhood category of the unique point has only one object, namely `⊤`.
    refine IsInitial.ofUniqueHom (fun Y ↦ ?_) (fun Y m ↦ ?_)
    · have hY : Opposite.unop Y = (⊤ : OpenNhds (PUnit.unit : TopCat.of PUnit.{u})) :=
        punit_openNhds_eq_top (Opposite.unop Y)
      subst hY
      exact 𝟙 _
    · exact Subsingleton.elim _ _
  -- Once the index category has an initial object, the colimit leg defining the germ is an iso.
  change IsIso (colimit.ι G j)
  exact isIso_ι_of_isInitial hj G

/-- Helper for Lemma 17.28.7: the constant map from the one-point space to `x`. -/
private abbrev point_map (x : X) : TopCat.of PUnit.{u} ⟶ X :=
  ofHom (ContinuousMap.const (TopCat.of PUnit.{u}) x)

/-- Helper for Lemma 17.28.7: forgetting commutativity commutes with the stalk of a sheaf of
rings. -/
private noncomputable abbrev commRingStalkToRingStalkIso
    (O : X.Sheaf CommRingCat.{u}) (x : X) :
    (forget₂ CommRingCat RingCat.{u}).obj ((stalkFunctor CommRingCat x).obj O.obj) ≅
      TopCat.Presheaf.stalk (ringSheaf O).obj x :=
  CategoryTheory.preservesColimitIso (forget₂ CommRingCat RingCat.{u})
    ((OpenNhds.inclusion x).op ⋙ O.obj)

/-- Helper for Lemma 17.28.7: the underlying continuous map of the point inclusion into
`(X, O)` is the constant map to `x`. -/
private theorem pointInclusion_toRingedSpace_hom_base
    (O : X.Sheaf CommRingCat.{u}) (x : X) :
    (pointInclusion (X := TopCat.Sheaf.toRingedSpace O) x).hom.base = point_map x := by
  -- The point inclusion was defined with the same constant base map, so this is exactly the
  -- source-side `{x} → X` specialization.
  simp [point_map, TopCat.Sheaf.toRingedSpace]

/-- Helper for Lemma 17.28.7: the top open of the pulled-back structure sheaf along the constant
map is canonically the stalk ring at `x`. -/
private noncomputable abbrev point_pullback_ring_top_iso
    (O : X.Sheaf CommRingCat.{u}) (x : X) :
    ((pullback RingCat.{u} (point_map x)).obj
        (ringSheaf O)).obj.obj
        (Opposite.op (⊤ : Opens (TopCat.of PUnit.{u}))) ≅
      (forget₂ CommRingCat RingCat.{u}).obj ((stalkFunctor CommRingCat x).obj O.obj) :=
  by
    haveI :
        IsIso (Γgerm (((pullback RingCat.{u} (point_map x)).obj (ringSheaf O)).obj) PUnit.unit) :=
      punit_presheaf_germ_isIso (((pullback RingCat.{u} (point_map x)).obj (ringSheaf O)).obj)
    -- First identify the top-open value with the unique stalk on the point space.
    -- Then compare that stalk with the original stalk at `x` via pullback compatibility.
    simpa [point_map, ringSheaf] using
      (asIso (Γgerm (((pullback RingCat.{u} (point_map x)).obj (ringSheaf O)).obj) PUnit.unit)) ≪≫
        (TopCat.Sheaf.stalkPullbackIso (point_map x) (ringSheaf O) PUnit.unit).symm ≪≫
        (commRingStalkToRingStalkIso O x).symm

/-- Helper for Lemma 17.28.7: on the one-point space, the top-open value of a module presheaf is
already its stalk after restricting scalars along the top-open/stalk ring identification. -/
private noncomputable def punit_presheaf_top_stalkIso
    {O : (TopCat.of PUnit.{u}).Sheaf CommRingCat.{u}}
    (P : PresheafOfModules (ringSheaf O).obj) :
    (ModuleCat.restrictScalars
        (asIso (Γgerm (ringSheaf O).obj PUnit.unit)).inv.hom).obj
      (P.obj (Opposite.op (⊤ : Opens (TopCat.of PUnit.{u})))) ≅
      ModuleCat.of ((ringSheaf O).obj.presheaf.stalk PUnit.unit)
        ↑(TopCat.Presheaf.stalk P.presheaf PUnit.unit) := by
  let germHom :
      (ModuleCat.restrictScalars
          (asIso (Γgerm (ringSheaf O).obj PUnit.unit)).inv.hom).obj
        (P.obj (Opposite.op (⊤ : Opens (TopCat.of PUnit.{u})))) ⟶
        ModuleCat.of ((ringSheaf O).obj.presheaf.stalk PUnit.unit)
          ↑(TopCat.Presheaf.stalk P.presheaf PUnit.unit) :=
    ModuleCat.ofHom
      { toFun := Γgerm P.presheaf PUnit.unit
        map_add' := by
          intro s t
          simpa using (Γgerm P.presheaf PUnit.unit).hom.map_add s t
        map_smul' := by
          intro r s
          -- Proof comment: the germ of a scalar multiple is the scalar multiple of the germs.
          simpa using
            (PresheafOfModules.germ_smul P PUnit.unit ⊤ (by simp)
              ((asIso (Γgerm (ringSheaf O).obj PUnit.unit)).inv.hom r) s) }
  haveI :
      IsIso
        ((forget₂
            (ModuleCat ((ringSheaf O).obj.presheaf.stalk PUnit.unit))
            AddCommGrpCat).map germHom) := by
    -- Proof comment: after forgetting scalars, this is exactly the one-point germ map.
    change IsIso (Γgerm P.presheaf PUnit.unit)
    exact punit_presheaf_germ_isIso P.presheaf
  exact asIso germHom

/-- Helper for Lemma 17.28.7: on the one-point space, the top-open module of a sheaf already is
its stalk after restricting scalars along the top-open/stalk ring identification. -/
private noncomputable def point_pullback_module_top_iso_aux
    {O : (TopCat.of PUnit.{u}).Sheaf CommRingCat.{u}}
    (ℱ : RingedSpace.Modules (TopCat.Sheaf.toRingedSpace O)) :
    (ModuleCat.restrictScalars
        (asIso (Γgerm (ringSheaf O).obj PUnit.unit)).inv.hom).obj
      (ℱ.val.obj (Opposite.op (⊤ : Opens (TopCat.of PUnit.{u})))) ≅
      RingedSpace.stalkModuleCat ℱ PUnit.unit :=
  -- Proof comment: specialize the one-point presheaf comparison to the underlying presheaf of the
  -- given sheaf of modules.
  simpa [RingedSpace.stalkModuleCat] using punit_presheaf_top_stalkIso ℱ.val

/-- Helper for Lemma 17.28.7: after transporting scalars from the pulled-back top ring to the
ordinary stalk ring, the stalk of the one-point inverse image matches the stalk module of
`Ω(φ)` at `x`. -/
private noncomputable def point_pullback_module_stalk_iso
    (φ : O₁ ⟶ O₂) (x : X) :
    RingedSpace.stalkModuleCat
        ((Ω(φ)) : RingedSpace.Modules (TopCat.Sheaf.toRingedSpace O₂)) x ≅
      RingedSpace.stalkModuleCat
        ((SheafOfModules.pullback
            ((pullbackPushforwardAdjunction RingCat.{u} (point_map x)).unit.app
              (ringSheaf O₂))).obj
          Ω(φ))
        PUnit.unit := by
  let pulledBackModule :=
    ((SheafOfModules.pullback
        ((pullbackPushforwardAdjunction RingCat.{u} (point_map x)).unit.app
          (ringSheaf O₂))).obj
      Ω(φ))
  let underlyingStalkIso :=
    TopCat.Sheaf.stalkPullbackIso (point_map x)
      ((SheafOfModules.toSheaf (ringSheaf O₂)).obj Ω(φ))
      PUnit.unit
  -- Route correction: abandon the ringed-space `pointInclusion` detour and specialize Lemma
  -- `17.28.6` along the literal topological map `point_map x`.
  -- Proof comment: the module pullback here is literally the topological pullback of the
  -- underlying sheaf of `Ω(φ)`, so the owner `stalkPullbackIso` already has the desired type.
  simpa [pulledBackModule, point_map] using underlyingStalkIso

/-- Helper for Lemma 17.28.7: after transporting scalars from the pulled-back top ring to the
ordinary stalk ring, the top open of the pulled-back differential sheaf matches the stalk module
of `Ω(φ)` at `x`. -/
private noncomputable def point_pullback_module_top_iso
    (φ : O₁ ⟶ O₂) (x : X) :
    RingedSpace.stalkModuleCat
        ((Ω(φ)) : RingedSpace.Modules (TopCat.Sheaf.toRingedSpace O₂)) x ≅
      (ModuleCat.restrictScalars (point_pullback_ring_top_iso O₂ x).inv.hom).obj
        ((((SheafOfModules.pullback
            ((pullbackPushforwardAdjunction RingCat.{u}
                (point_map x)).unit.app
              (ringSheaf O₂))).obj
          Ω(φ)).val.obj (Opposite.op (⊤ : Opens (TopCat.of PUnit.{u}))))) := by
  let pulledBackModule :=
    ((SheafOfModules.pullback
        ((pullbackPushforwardAdjunction RingCat.{u} (point_map x)).unit.app
          (ringSheaf O₂))).obj
      Ω(φ))
  -- First compare the original stalk with the stalk of the one-point pullback.
  -- Then collapse that unique stalk to the top-open value on `TopCat.of PUnit`.
  exact point_pullback_module_stalk_iso φ x ≪≫
    (point_pullback_module_top_iso_aux pulledBackModule).symm

/-- Helper for Lemma 17.28.7: the top-open component of the inverse-image comparison from Lemma
`17.28.6`. -/
private noncomputable abbrev point_inverseImage_relativeDifferentials_topIso
    (φ : O₁ ⟶ O₂) (x : X) :
    ((((SheafOfModules.pullback
        ((pullbackPushforwardAdjunction RingCat.{u}
            (point_map x)).unit.app
          (ringSheaf O₂))).obj
      Ω(φ)).val.obj (Opposite.op (⊤ : Opens (TopCat.of PUnit.{u}))))) ≅
      ((((SheafOfModules.restrictScalars
          (pullbackRingSheafIso (point_map x) O₂).inv).obj
        Ω((pullback CommRingCat.{u} (point_map x)).map φ)).val.obj
          (Opposite.op (⊤ : Opens (TopCat.of PUnit.{u}))))) :=
  (inverseImage_relativeDifferentialsIso
      (point_map x) φ).app
    (Opposite.op (⊤ : Opens (TopCat.of PUnit.{u})))

/-- Helper for Lemma 17.28.7: after the same scalar transport, the top open of the point-pullback
target identifies with the Kähler differential of the stalk ring map. -/
private noncomputable def point_relativeDifferentials_top_open_iso_aux
    {A B : (TopCat.of PUnit.{u}).Sheaf CommRingCat.{u}} (ψ : A ⟶ B) :
    (((Ω(ψ)) : RingedSpace.Modules (TopCat.Sheaf.toRingedSpace B)).val.obj
      (Opposite.op (⊤ : Opens (TopCat.of PUnit.{u}))) ≅
      CommRingCat.KaehlerDifferential
        (ψ.hom.app (Opposite.op (⊤ : Opens (TopCat.of PUnit.{u})))) :=
  let P := PresheafOfModules.DifferentialsConstruction.relativeDifferentials' ψ.hom
  let η := ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf B).obj)).unit.app P)
  have hη :
      (PresheafOfModules.toPresheaf (ringSheaf B).obj).map η =
        CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of PUnit.{u})) P.presheaf := by
    -- Proof comment: forgetting the module structure turns the module-sheafification unit into
    -- the additive sheafification unit.
    simpa [η] using
      (PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
        (𝟙 (ringSheaf B).obj) P)
  have hηstalk_iso :
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat PUnit.unit).map
        ((PresheafOfModules.toPresheaf (ringSheaf B).obj).map η)) := by
    -- Proof comment: stalks do not change under additive sheafification.
    rw [hη]
    simpa using
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
        PUnit.unit AddCommGrpCat P.presheaf)
  have hηtop_bijective :
      Function.Bijective (η.app (Opposite.op (⊤ : Opens (TopCat.of PUnit.{u})))) := by
    let γP := Γgerm P.presheaf PUnit.unit
    let Q := ((PresheafOfModules.sheafification (𝟙 (ringSheaf B).obj)).obj P).val.presheaf
    let γQ := Γgerm Q PUnit.unit
    let fη :
        TopCat.Presheaf.stalk P.presheaf PUnit.unit ⟶ TopCat.Presheaf.stalk Q PUnit.unit :=
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat PUnit.unit).map
        ((PresheafOfModules.toPresheaf (ringSheaf B).obj).map η)
    have hγP_bijective : Function.Bijective γP :=
      (CategoryTheory.isIso_iff_bijective γP).1 (punit_presheaf_germ_isIso P.presheaf)
    have hγQ_bijective : Function.Bijective γQ :=
      (CategoryTheory.isIso_iff_bijective γQ).1 (punit_presheaf_germ_isIso Q)
    have hfη_bijective : Function.Bijective fη := by
      exact (CategoryTheory.isIso_iff_bijective fη).1 <| by
        simpa [fη] using hηstalk_iso
    refine ⟨?_, ?_⟩
    · intro s t hst
      apply hγP_bijective.1
      apply hfη_bijective.1
      calc
        fη (γP s) = γQ ((η.app (Opposite.op (⊤ : Opens (TopCat.of PUnit.{u})))) s) := by
          simpa [γP, γQ, fη, η] using
            (TopCat.Presheaf.stalkFunctor_map_germ_apply
              (⊤ : Opens (TopCat.of PUnit.{u})) PUnit.unit (by simp)
              ((PresheafOfModules.toPresheaf (ringSheaf B).obj).map η) s)
        _ = γQ ((η.app (Opposite.op (⊤ : Opens (TopCat.of PUnit.{u})))) t) := by
          rw [hst]
        _ = fη (γP t) := by
          symm
          simpa [γP, γQ, fη, η] using
            (TopCat.Presheaf.stalkFunctor_map_germ_apply
              (⊤ : Opens (TopCat.of PUnit.{u})) PUnit.unit (by simp)
              ((PresheafOfModules.toPresheaf (ringSheaf B).obj).map η) t)
    · intro q
      obtain ⟨qstalk, hqstalk⟩ := hγQ_bijective.2 (γQ q)
      obtain ⟨pstalk, hpstalk⟩ := hfη_bijective.2 qstalk
      obtain ⟨p, hp⟩ := hγP_bijective.2 pstalk
      refine ⟨p, hγQ_bijective.1 ?_⟩
      calc
        γQ ((η.app (Opposite.op (⊤ : Opens (TopCat.of PUnit.{u})))) p) = fη (γP p) := by
          simpa [γP, γQ, fη, η] using
            (TopCat.Presheaf.stalkFunctor_map_germ_apply
              (⊤ : Opens (TopCat.of PUnit.{u})) PUnit.unit (by simp)
              ((PresheafOfModules.toPresheaf (ringSheaf B).obj).map η) p)
        _ = γQ q := by
          rw [hp, hpstalk, hqstalk]
  have hηtop_iso : IsIso (η.app (Opposite.op (⊤ : Opens (TopCat.of PUnit.{u})))) :=
    (CategoryTheory.isIso_iff_bijective _).2 hηtop_bijective
  -- Proof comment: on the one-point space the sheafification unit is already an isomorphism on
  -- the unique open set, so the owner formula `relativeDifferentials'_obj` computes `Ω(ψ)`.
  simpa [P, TopCat.Sheaf.relativeDifferentials_def] using
    (asIso (η.app (Opposite.op (⊤ : Opens (TopCat.of PUnit.{u}))))).symm

/-- Helper for Lemma 17.28.7: after transporting both top-open rings to stalk rings, the
top-open map of the pulled-back morphism becomes the induced map on stalks. -/
private theorem point_pullback_relativeDifferentials_top_map_eq_stalkMap
    (φ : O₁ ⟶ O₂) (x : X) :
    (point_pullback_ring_top_iso O₁ x).hom ≫
        (((pullback CommRingCat.{u} (point_map x)).map φ).hom.app
          (Opposite.op (⊤ : Opens (TopCat.of PUnit.{u})))) =
      ((stalkFunctor CommRingCat x).map φ.hom) ≫
        (point_pullback_ring_top_iso O₂ x).hom := by
  -- Proof comment: after expanding the one-point comparison, this is exactly the naturality of
  -- the stalk-pullback comparison for the forgotten `RingCat`-valued structure sheaves.
  simpa [point_pullback_ring_top_iso, point_map, Category.assoc] using
    (TopCat.Sheaf.stalkPullbackIso_hom_naturality
      (A := RingCat.{u}) (f := point_map x) (x := PUnit.unit) φ.hom)

/-- Helper for Lemma 17.28.7: after the same scalar transport, the top open of the point-pullback
target identifies with the Kähler differential of the stalk ring map. -/
private noncomputable def point_relativeDifferentials_target_top_iso
    (φ : O₁ ⟶ O₂) (x : X) :
    (ModuleCat.restrictScalars (point_pullback_ring_top_iso O₂ x).inv.hom).obj
      ((((SheafOfModules.restrictScalars
          (pullbackRingSheafIso (point_map x) O₂).inv).obj
        Ω((pullback CommRingCat.{u} (point_map x)).map φ)).val.obj
          (Opposite.op (⊤ : Opens (TopCat.of PUnit.{u}))))) ≅
      CommRingCat.KaehlerDifferential ((stalkFunctor CommRingCat x).map φ.hom) := by
  let pointTopIso :=
    point_relativeDifferentials_top_open_iso_aux
      ((pullback CommRingCat.{u} (point_map x)).map φ)
  -- First compute the one-point-space top-open value of relative differentials.
  -- Then rewrite the underlying ring map back to the stalk map on `X`.
  simpa [point_pullback_relativeDifferentials_top_map_eq_stalkMap, point_map] using
    (Functor.mapIso
      (ModuleCat.restrictScalars (point_pullback_ring_top_iso O₂ x).inv.hom)
      pointTopIso)

/-- Lemma 17.28.7: the stalk of `Ω(φ)` at `x` is canonically isomorphic to the Kähler
differential module of the induced morphism on stalk rings. -/
@[stacks 08TE]
noncomputable opaque relativeDifferentials_stalkIso
    (φ : O₁ ⟶ O₂) (x : X) :
    RingedSpace.stalkModuleCat
        ((Ω(φ)) : RingedSpace.Modules (TopCat.Sheaf.toRingedSpace O₂)) x ≅
      CommRingCat.KaehlerDifferential ((stalkFunctor CommRingCat x).map φ.hom) :=
  -- Route correction: the old neighborhood/direct-limit proof was discarded in favor of the
  -- source-proof specialization of Lemma `17.28.6` to the one-point pullback at `x`.
  point_pullback_module_top_iso φ x ≪≫
    (Functor.mapIso
      (ModuleCat.restrictScalars (point_pullback_ring_top_iso O₂ x).inv.hom)
      (point_inverseImage_relativeDifferentials_topIso φ x)) ≪≫
    point_relativeDifferentials_target_top_iso φ x

end

end TopCat.Sheaf
