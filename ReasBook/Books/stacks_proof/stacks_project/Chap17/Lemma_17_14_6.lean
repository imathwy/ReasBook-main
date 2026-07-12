import Mathlib
import StacksProject_2024.Chap07.Example_7_33_5
import StacksProject_2024.Chap07.Lemma_7_35_1
import StacksProject_2024.Chap10.Lemma_10_55_8
import StacksProject_2024.Chap15.Lemma_15_3_2
import StacksProject_2024.Chap17.Definition_17_14_1
import StacksProject_2024.Chap17.Lemma_17_18_2
import StacksProject_2024.Chap17.ModuleRestrictionAndStalks
import StacksProject_2024.Chap18.Lemma_18_23_3
import StacksProject_2024.Chap18.Example_18_29_1
import StacksProject_2024.Chap18.Lemma_18_36_3

open AlgebraicGeometry
open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X
local notation "IsLocallyDirectSummandOfFiniteFreeX" =>
  @SheafOfModules.RingedSite.IsLocallyDirectSummandOfFiniteFree _ _
    (Opens.grothendieckTopology X) _ X.sheaf

/- Domain-style sampling for Lemma 17.14.6:
- primary domain: finite locally free sheaves of modules on a ringed space and their behavior
  under direct-summand constructions;
- sampled owner declarations:
  `SheafOfModules.IsFiniteLocallyFree`,
  `SheafOfModules.RingedSite.IsLocallyDirectSummandOfFiniteFree`,
  `AlgebraicGeometry.RingedSpace.stalkModuleCat`,
  `CategoryTheory.Retract`;
- best owner abstraction: the canonical owner for the local direct-summand condition is
  `SheafOfModules.RingedSite.IsLocallyDirectSummandOfFiniteFree`, specialized to the opens site of
  `X`; a global retract into a finite locally free sheaf is only bridge data producing that owner
  locally;
- primitive data: a module sheaf `ℱ : ModX`, local-ring stalks on `X`, and local retracts of
  finite free restrictions of `ℱ`;
- derived API: private finite-presentation scaffolding used to feed the source-facing finite
  locally free conclusions below.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma asserting that a direct summand of a finite locally free sheaf
  is finite locally free;
- `core/canonical`: `SheafOfModules.RingedSite.IsLocallyDirectSummandOfFiniteFree`;
- `bridge/view`: a global categorical retract `Retract ℱ ℋ` with `ℋ` finite locally free. -/

/-- Helper for Lemma 17.14.6: a family of open neighborhoods containing each point yields a cover
of the terminal object in the opens site. -/
private theorem pointwise_open_cover_coversTop
    (U : X → Opens X) (hU : ∀ x : X, x ∈ U x) :
    (Opens.grothendieckTopology X).CoversTop U := by
  -- Proof comment: every point of an open `V` lies in the intersection `V ∩ U x`, which refines
  -- the chosen neighborhood and still maps into `V`.
  intro V x hx
  refine ⟨V ⊓ U x, homOfLE inf_le_left, ?_, ?_⟩
  · exact ⟨x, ⟨homOfLE inf_le_right⟩⟩
  · exact ⟨hx, hU x⟩

/-- Helper for Lemma 17.14.6: mapping a finite global presentation along restriction keeps the
same finite generator and relation index types. -/
private theorem presentation_map_isFinite
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {𝒪 : Sheaf J RingCat.{u}}
    [HasBinaryProducts C]
    [HasSheafify J AddCommGrpCat]
    [J.WEqualsLocallyBijective AddCommGrpCat]
    [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    [∀ Y, (J.over Y).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    [∀ Y, HasSheafify (J.over Y) AddCommGrpCat]
    [∀ Y, (J.over Y).WEqualsLocallyBijective AddCommGrpCat]
    {ℱ : SheafOfModules 𝒪} (P : ℱ.Presentation) [P.IsFinite] (Y : C) :
    ((P.map (pushforward (𝟙 (𝒪.over Y))) (by rfl))).IsFinite := by
  -- Proof comment: `Presentation.map` does not change the chosen index types, so finiteness is
  -- inherited directly after unfolding the mapped presentation.
  refine ⟨?_, ?_⟩
  · dsimp [SheafOfModules.Presentation.map, SheafOfModules.presentationOfIsCokernelFree,
      SheafOfModules.generatorsOfIsCokernelFree]
    refine ⟨?_⟩
    change Finite P.generators.I
    infer_instance
  · dsimp [SheafOfModules.Presentation.map, SheafOfModules.presentationOfIsCokernelFree,
      SheafOfModules.relationsOfIsCokernelFree]
    infer_instance

/-- Helper for Lemma 17.14.6: a finite global presentation upgrades to the owner
`IsFinitePresentation`. -/
private theorem isFinitePresentation_of_finite_presentation
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {𝒪 : Sheaf J RingCat.{u}}
    [HasBinaryProducts C]
    [HasSheafify J AddCommGrpCat]
    [J.WEqualsLocallyBijective AddCommGrpCat]
    [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    [∀ Y, (J.over Y).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    [∀ Y, HasSheafify (J.over Y) AddCommGrpCat]
    [∀ Y, (J.over Y).WEqualsLocallyBijective AddCommGrpCat]
    {ℱ : SheafOfModules 𝒪} (P : ℱ.Presentation) [P.IsFinite] :
    ℱ.IsFinitePresentation := by
  -- Proof comment: use the trivial-cover quasicoherent data from `P`; each restriction remains a
  -- finite presentation by the previous restriction lemma.
  refine ⟨P.quasicoherentData, ?_⟩
  constructor
  intro Y
  simpa using presentation_map_isFinite (P := P) Y

/-- Helper for Lemma 17.14.6: a retract of a finite free module sheaf on one open subset is
finitely presented there. -/
private theorem isFinitePresentation_of_retract_free_over
    {U : Opens X} {α : Type u} [Finite α]
    {M : SheafOfModules ((RingedSpace.ringCatSheaf X).over U)}
    (hret : Retract M (SheafOfModules.free α)) :
    M.IsFinitePresentation := by
  let φ :
      (SheafOfModules.free.{u} α :
        SheafOfModules ((RingedSpace.ringCatSheaf X).over U)) ⟶
      (SheafOfModules.free.{u} α :
        SheafOfModules ((RingedSpace.ringCatSheaf X).over U)) :=
    𝟙 _ - hret.r ≫ hret.i
  have hφr : φ ≫ hret.r = 0 := by
    -- Proof comment: the cokernel candidate is the retraction map; its vanishing on `φ` is the
    -- split-idempotent identity `hret.i ≫ hret.r = 𝟙`.
    simp [φ, Category.assoc, hret.retract]
  have hcok : IsColimit (CokernelCofork.ofπ hret.r hφr) := by
    -- Proof comment: any cofork annihilating `φ` factors uniquely through the retraction because
    -- the equation `φ ≫ π = 0` rewrites `π` as `hret.r ≫ (hret.i ≫ π)`.
    refine CokernelCofork.IsColimit.ofπ' hret.r hφr ?_
    intro Z s hs
    refine ⟨hret.i ≫ s.π, ?_⟩
    have hs' : s.π = hret.r ≫ hret.i ≫ s.π := by
      have hs'' : s.π - hret.r ≫ hret.i ≫ s.π = 0 := by
        simpa [φ, Category.assoc] using hs
      exact sub_eq_zero.mp hs''
    simpa [Category.assoc] using hs'
  let P : M.Presentation :=
    SheafOfModules.presentationOfIsCokernelFree φ hret.r hφr hcok
  let _ : P.IsFinite := by
    -- Proof comment: the cokernel presentation uses the same finite free index type `α` for both
    -- generators and relations, so finiteness is immediate after unfolding.
    refine ⟨?_, ?_⟩
    · dsimp [P, SheafOfModules.presentationOfIsCokernelFree,
        SheafOfModules.generatorsOfIsCokernelFree]
      refine ⟨?_⟩
      infer_instance
    · dsimp [P, SheafOfModules.presentationOfIsCokernelFree,
        SheafOfModules.relationsOfIsCokernelFree]
      infer_instance
  exact isFinitePresentation_of_finite_presentation P

-- Proof sketch: finite presentation is local on the opens site. Around each point, the owner
-- hypothesis gives a restriction `ℱ.over U` that is a retract of a finite free sheaf, and finite
-- free sheaves are finitely presented; retracts preserve finite presentation, so `ℱ` is locally
-- finitely presented and hence finitely presented globally.
private theorem isFinitePresentation_of_isLocallyDirectSummandOfFiniteFree
    (ℱ : ModX) [IsLocallyDirectSummandOfFiniteFreeX ℱ] :
    ℱ.IsFinitePresentation := by
  classical
  -- Proof comment: choose one retract-of-finite-free neighborhood around each point and package
  -- those local finite-presentation witnesses into the standard cover criterion.
  choose U hU α hα hret using
    fun x : X ↦
      RingedSite.IsLocallyDirectSummandOfFiniteFree.exists_open_neighborhood_retract_free ℱ x
  refine
    (SheafOfModules.RingedSite.isFinitePresentation_iff_exists_cover_isFinitePresentation_over
      (J := Opens.grothendieckTopology X) (𝒪 := X.sheaf) ℱ).2 ?_
  refine ⟨X, U, pointwise_open_cover_coversTop U hU, ?_⟩
  intro x
  let _ : Finite (α x) := hα x
  -- Proof comment: on the chosen neighborhood `U x`, the retract from the owner hypothesis is
  -- exactly the local finite-presentation bridge proved above.
  exact isFinitePresentation_of_retract_free_over (hret := Classical.choice (hret x))

/-- Helper for Lemma 17.14.6: the canonical ring carried by the opens-site point over `x` agrees
with the usual stalk ring `\mathcal O_{X, x}`. -/
private abbrev pointStalkRingEquivStalkRing (x : X) :
    ↑((Opens.pointGrothendieckTopology x).stalkRing (RingedSpace.ringCatSheaf X)) ≃+*
      ↑(X.presheaf.stalk x) :=
  (((Opens.pointGrothendieckTopology x).presheafFiberCompIso
      (forget₂ CommRingCat RingCat.{u})).app X.sheaf.obj).ringCatIsoToRingEquiv.trans
    (Iso.commRingCatIsoToRingEquiv
      (CategoryTheory.pointGrothendieckTopology_presheafFiber_obj_iso_stalk x X.sheaf.obj))

/-- Helper for Lemma 17.14.6: after localizing the opens-site point to a neighborhood `U`, the
slice-site stalk ring is still canonically the stalk ring `\mathcal O_{X, x}`. -/
private abbrev pointOverStalkRingEquivStalkRing
    (x : X) {U : Opens X}
    (xu : (Opens.pointGrothendieckTopology x).fiber.obj U) :
    ↑(((Opens.pointGrothendieckTopology x).over xu).stalkRing
        ((RingedSpace.ringCatSheaf X).over U)) ≃+*
      ↑(X.presheaf.stalk x) :=
  (CategoryTheory.point_over_sheafFiberObjIso
      (Opens.pointGrothendieckTopology x) xu (RingedSpace.ringCatSheaf X)).ringCatIsoToRingEquiv.trans
    pointStalkRingEquivStalkRing (X := X) x

/-- Helper for Lemma 17.14.6: freeze the localized-point stalk functor after retargeting scalars
to the usual stalk ring `\mathcal O_{X, x}`. -/
private abbrev pointOverStalkModuleFunctor
    (x : X) {U : Opens X}
    (xu : (Opens.pointGrothendieckTopology x).fiber.obj U) :
    SheafOfModules ((RingedSpace.ringCatSheaf X).over U) ⥤
      ModuleCat (X.presheaf.stalk x) :=
  ((Opens.pointGrothendieckTopology x).over xu).sheafModuleStalkFunctor
      ((RingedSpace.ringCatSheaf X).over U) ⋙
    ModuleCat.restrictScalars
      (pointOverStalkRingEquivStalkRing (X := X) x xu).symm.toRingHom

/-- Helper for Lemma 17.14.6: forgetting the retargeted localized-point stalk functor recovers the
underlying additive sheaf fiber. -/
@[simp] private theorem pointOverStalkModuleFunctor_forget_obj
    (x : X) {U : Opens X}
    (xu : (Opens.pointGrothendieckTopology x).fiber.obj U)
    (ℱ : SheafOfModules ((RingedSpace.ringCatSheaf X).over U)) :
    (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj
        ((pointOverStalkModuleFunctor (X := X) x xu).obj ℱ) =
      (((Opens.pointGrothendieckTopology x).over xu).sheafFiber.obj
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X).over U)).obj ℱ)) := by
  -- Proof comment: `restrictScalars` changes only the scalar action; the underlying additive
  -- group remains the original localized-point sheaf fiber.
  rfl

/-- Helper for Lemma 17.14.6: forgetting a morphism of retargeted localized-point stalks recovers
the underlying additive stalk map. -/
@[simp] private theorem pointOverStalkModuleFunctor_forget_map
    (x : X) {U : Opens X}
    (xu : (Opens.pointGrothendieckTopology x).fiber.obj U)
    {ℱ 𝒢 : SheafOfModules ((RingedSpace.ringCatSheaf X).over U)}
    (φ : ℱ ⟶ 𝒢) :
    (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map
        ((pointOverStalkModuleFunctor (X := X) x xu).map φ) =
      (((Opens.pointGrothendieckTopology x).over xu).sheafFiber.map
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X).over U)).map φ)) := by
  -- Proof comment: the retargeted module map is built from the same colimit map as the additive
  -- sheaf fiber map, so forgetting scalars leaves the morphism unchanged.
  rfl

/-- Helper for Lemma 17.14.6: the additive stalk of `ℱ.over U` at the localized opens-site point
over `x ∈ U` is canonically the usual additive stalk of `ℱ` at `x`. -/
private noncomputable def pointOverAddStalkIso
    (ℱ : ModX) (x : X) {U : Opens X}
    (xu : (Opens.pointGrothendieckTopology x).fiber.obj U) :
    (((Opens.pointGrothendieckTopology x).over xu).sheafFiber.obj
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X).over U)).obj (ℱ.over U))) ≅
      TopCat.Presheaf.stalk ℱ.val.presheaf x :=
  CategoryTheory.point_over_sheafFiberObjIso
      (Opens.pointGrothendieckTopology x) xu
      ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj ℱ) ≪≫
    CategoryTheory.pointGrothendieckTopology_sheafFiber_obj_iso_stalk x
      ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj ℱ)

/-- Helper for Lemma 17.14.6: over a local ring, a retract of a finite free module is isomorphic
to a standard finite free coordinate module. -/
private theorem local_ring_retract_of_finite_free_is_standard_free
    {R : Type u} [CommRing R] [IsLocalRing R]
    (M : ModuleCat R) {I : Type u} [Finite I]
    (hret : Retract M ((ModuleCat.free R).obj I)) :
    ∃ r : ℕ, Nonempty (M ≅ (ModuleCat.free R).obj (ULift.{u} (Fin r))) := by
  -- Proof comment: the retraction makes `M` a finite projective module over the local ring `R`.
  -- The algebra lemma `finite_projective_module_free_of_isLocalRing` then upgrades it to a free
  -- module, and `finite_free_linearEquiv_fin` packages the basis by a finite `Fin r`.
  have hsurj : Function.Surjective hret.r.hom := by
    intro m
    refine ⟨hret.i.hom m, ?_⟩
    simpa using congrArg (fun f : M ⟶ M ↦ f.hom m) hret.retract
  let _ : Module.Finite R M := Module.Finite.of_surjective hret.r.hom hsurj
  have hsplit : hret.r.hom.comp hret.i.hom = LinearMap.id := by
    ext m
    simpa [LinearMap.comp_apply] using congrArg (fun f : M ⟶ M ↦ f.hom m) hret.retract
  let _ : Module.Projective R M := Module.Projective.of_split hret.i.hom hret.r.hom hsplit
  let _ : Module.Free R M := finite_projective_module_free_of_isLocalRing (R := R)
  rcases finite_free_linearEquiv_fin (R := R) (F := M) with ⟨r, ⟨eFin⟩⟩
  let eULift :
      (Fin r → R) ≃ₗ[R] (ULift.{u} (Fin r) → R) :=
    LinearEquiv.funCongrLeft R R Equiv.ulift.symm
  let eFinsupp :
      (ULift.{u} (Fin r) →₀ R) ≃ₗ[R] (ULift.{u} (Fin r) → R) :=
    Finsupp.linearEquivFunOnFinite R R (ULift.{u} (Fin r))
  refine ⟨r, ?_⟩
  refine ⟨⟨ModuleCat.ofHom ((eFin.trans eULift.trans eFinsupp.symm).toLinearMap),
      ModuleCat.ofHom ((eFin.trans eULift.trans eFinsupp.symm).symm.toLinearMap), ?_, ?_⟩⟩
  · ext m
    rfl
  · ext m
    rfl

/-- Helper for Lemma 17.14.6: over a local ring, a retract of any finite module is already
isomorphic to a standard finite free coordinate module. This is the source-faithful algebra step:
the retract gives projectivity, finite generation descends along the retraction, and the local-ring
algebra lemma upgrades the resulting finite projective module to a free one. -/
private theorem local_ring_retract_of_finite_is_standard_free
    {R : Type u} [CommRing R] [IsLocalRing R]
    (M N : ModuleCat R) [Module.Finite R N]
    (hret : Retract M N) :
    ∃ r : ℕ, Nonempty (M ≅ (ModuleCat.free R).obj (ULift.{u} (Fin r))) := by
  have hsurj : Function.Surjective hret.r.hom := by
    -- Proof comment: the retraction identity provides a preimage `hret.i.hom m` for each `m`.
    intro m
    refine ⟨hret.i.hom m, ?_⟩
    simpa using congrArg (fun f : M ⟶ M ↦ f.hom m) hret.retract
  let _ : Module.Finite R M := Module.Finite.of_surjective hret.r.hom hsurj
  have hsplit : hret.r.hom.comp hret.i.hom = LinearMap.id := by
    -- Proof comment: the splitting equation is exactly the retract identity on underlying maps.
    ext m
    simpa [LinearMap.comp_apply] using congrArg (fun f : M ⟶ M ↦ f.hom m) hret.retract
  let _ : Module.Projective R M := Module.Projective.of_split hret.i.hom hret.r.hom hsplit
  let _ : Module.Free R M := finite_projective_module_free_of_isLocalRing (R := R)
  rcases finite_free_linearEquiv_fin (R := R) (F := M) with ⟨r, ⟨eFin⟩⟩
  let eULift :
      (Fin r → R) ≃ₗ[R] (ULift.{u} (Fin r) → R) :=
    LinearEquiv.funCongrLeft R R Equiv.ulift.symm
  let eFinsupp :
      (ULift.{u} (Fin r) →₀ R) ≃ₗ[R] (ULift.{u} (Fin r) → R) :=
    Finsupp.linearEquivFunOnFinite R R (ULift.{u} (Fin r))
  refine ⟨r, ?_⟩
  refine ⟨⟨ModuleCat.ofHom ((eFin.trans eULift.trans eFinsupp.symm).toLinearMap),
      ModuleCat.ofHom ((eFin.trans eULift.trans eFinsupp.symm).symm.toLinearMap), ?_, ?_⟩⟩
  · ext m
    rfl
  · ext m
    rfl

/-- Helper for Lemma 17.14.6: on the retargeted localized-point stalk, scalar multiplication by
`r : \mathcal O_{X, x}` is the underlying slice-site stalk scalar multiplication by the transported
scalar from `pointOverStalkRingEquivStalkRing`. -/
private theorem pointOverStalkModuleFunctor_smul_def
    (x : X) {U : Opens X}
    (xu : (Opens.pointGrothendieckTopology x).fiber.obj U)
    (ℱ : SheafOfModules ((RingedSpace.ringCatSheaf X).over U))
    (r : X.presheaf.stalk x)
    (m : (pointOverStalkModuleFunctor (X := X) x xu).obj ℱ) :
    (r • m :
      ↑((pointOverStalkModuleFunctor (X := X) x xu).obj ℱ)) =
      ((pointOverStalkRingEquivStalkRing (X := X) x xu).symm r) • m := by
  -- Proof comment: `pointOverStalkModuleFunctor` is defined by restricting scalars along the
  -- inverse ring equivalence, so the owner-side scalar action is exactly the transported action
  -- recorded by `ModuleCat.restrictScalars.smul_def'`.
  simpa [pointOverStalkModuleFunctor] using
    (ModuleCat.restrictScalars.smul_def'
      ((pointOverStalkRingEquivStalkRing (X := X) x xu).symm.toRingHom)
      r m)

/-- Helper for Lemma 17.14.6: the additive stalk comparison from the localized opens-site point to
the usual stalk is already linear over `\mathcal O_{X, x}` after retargeting scalars on the
source via `pointOverStalkModuleFunctor`. -/
private theorem pointOverAddStalkIso_linear
    (ℱ : ModX) (x : X) {U : Opens X}
    (xu : (Opens.pointGrothendieckTopology x).fiber.obj U)
    (r : X.presheaf.stalk x)
    (m : (pointOverStalkModuleFunctor (X := X) x xu).obj (ℱ.over U)) :
    (pointOverAddStalkIso (ℱ := ℱ) x xu).hom (r • m) =
      r • (pointOverAddStalkIso (ℱ := ℱ) x xu).hom m := by
  -- Route correction: the old equivalence-level placeholder kept the scalar transport and the
  -- additive stalk comparison entangled. The remaining blocker is exactly this `map_smul` fact.
  have hsmul :
      (r • m :
        ↑((pointOverStalkModuleFunctor (X := X) x xu).obj (ℱ.over U))) =
        ((pointOverStalkRingEquivStalkRing (X := X) x xu).symm r) • m :=
    pointOverStalkModuleFunctor_smul_def (X := X) x xu (ℱ.over U) r m
  -- Proof comment: the source scalar has now been rewritten into the actual slice-site stalk
  -- scalar. The remaining work is the germ-level compatibility of `pointOverAddStalkIso` with
  -- this slice-site action.
  -- TODO: represent `r` and `m` by slice-site germs, push both sides through the two components
  -- of `pointOverAddStalkIso`, and discharge the scalar compatibility with
  -- `PresheafOfModules.germ_smul` plus the canonical ring comparison
  -- `pointOverStalkRingEquivStalkRing`.
  rw [hsmul]
  sorry

/-- Helper for Lemma 17.14.6: cancel the scalar-retargeting equivalence to compare the localized
slice-site stalk module directly with the usual stalk module. -/
private noncomputable def point_over_stalk_module_iso
    (ℱ : ModX) (x : X) {U : Opens X}
    (xu : (Opens.pointGrothendieckTopology x).fiber.obj U) :
    (pointOverStalkModuleFunctor (X := X) x xu).obj (ℱ.over U) ≅
      RingedSpace.stalkModuleCat ℱ x := by
  let eAdd := pointOverAddStalkIso (ℱ := ℱ) x xu
  let eLin :
      ((pointOverStalkModuleFunctor (X := X) x xu).obj (ℱ.over U)) ≃ₗ[X.presheaf.stalk x]
        (RingedSpace.stalkModuleCat ℱ x) :=
    { toFun := eAdd.hom
      invFun := eAdd.inv
      left_inv := eAdd.inv_hom_id_apply
      right_inv := eAdd.hom_inv_id_apply
      map_add' := by
        intro m n
        simpa using eAdd.hom.hom.map_add m n
      map_smul' := by
        intro r m
        simpa using pointOverAddStalkIso_linear (X := X) (ℱ := ℱ) x xu r m }
  -- Proof comment: once the additive stalk isomorphism is known to respect the retargeted scalar
  -- actions, it upgrades immediately to a linear equivalence and hence to an isomorphism in
  -- `ModuleCat`.
  refine ⟨ModuleCat.ofHom eLin.toLinearMap, ModuleCat.ofHom eLin.symm.toLinearMap, ?_, ?_⟩
  · ext m
    exact eLin.left_inv m
  · ext m
    exact eLin.right_inv m

/-- Helper for Lemma 17.14.6: the localized stalk of a finite free sheaf is finitely generated
over the usual stalk ring. -/
private theorem point_over_stalk_free_finite
    (x : X) {U : Opens X}
    (xu : (Opens.pointGrothendieckTopology x).fiber.obj U)
    (I : Type u) [Finite I] :
    Module.Finite (X.presheaf.stalk x)
      ((pointOverStalkModuleFunctor (X := X) x xu).obj (SheafOfModules.free I)) := by
  -- Route correction: the source proof only needs finite generation of the ambient localized free
  -- stalk. A full public standard-free comparison is unnecessary once the local-ring retract lemma
  -- is available.
  -- TODO: use colimit preservation of the slice-site stalk functor together with `mapFree` on the
  -- finite free sheaf `SheafOfModules.free I`, then transport the resulting finite free module
  -- structure across the canonical ring-equivalence retargeting.
  sorry

/-- Helper for Lemma 17.14.6: the stalk of a local retract of a finite free sheaf is standard
finite free over the local stalk ring. -/
private theorem stalk_free_of_retract_free_over_of_isLocalRing
    (ℱ : ModX) [ℱ.IsFinitePresentation] (x : X)
    {U : Opens X} (hx : x ∈ U) {I : Type u} [Finite I]
    (hret : Retract (ℱ.over U) (SheafOfModules.free I))
    (hlocalx : IsLocalRing (X.presheaf.stalk x)) :
    ∃ r : ℕ,
      Nonempty
        (RingedSpace.stalkModuleCat ℱ x ≅
          (ModuleCat.free (X.presheaf.stalk x)).obj (ULift.{u} (Fin r))) := by
  classical
  let xu : (Opens.pointGrothendieckTopology x).fiber.obj U :=
    Classical.choice ((Opens.pointGrothendieckTopology_fiber_nonempty_iff x U).2 hx)
  let F := pointOverStalkModuleFunctor (X := X) x xu
  let hretStalk :
      Retract
        (F.obj (ℱ.over U))
        (F.obj (SheafOfModules.free I)) :=
    Retract.map hret F
  let _ : IsLocalRing (X.presheaf.stalk x) := hlocalx
  let _ : Module.Finite (X.presheaf.stalk x) (F.obj (SheafOfModules.free I)) :=
    point_over_stalk_free_finite (X := X) x xu I
  -- Proof comment: the stalk retract is now an algebra problem over the local ring
  -- `\mathcal O_{X, x}`. Apply the local-ring retract lemma and transport the resulting free model
  -- back across `point_over_stalk_module_iso`.
  rcases local_ring_retract_of_finite_is_standard_free
      (R := X.presheaf.stalk x)
      (M := F.obj (ℱ.over U))
      (N := F.obj (SheafOfModules.free I))
      hretStalk with ⟨r, hfree⟩
  rcases hfree with ⟨e⟩
  refine ⟨r, ?_⟩
  exact ⟨(point_over_stalk_module_iso (X := X) (ℱ := ℱ) x xu).symm ≪≫ e⟩

/-- Helper for Lemma 17.14.6: a retract of a finite free restriction near `x` should produce a
finite free neighborhood of `x` once the stalk ring `\mathcal O_{X, x}` is local. -/
private theorem exists_open_neighborhood_iso_free_of_retract_free_over_of_isLocalRing
    (ℱ : ModX) [ℱ.IsFinitePresentation] (x : X)
    {U : Opens X} (hx : x ∈ U) {I : Type u} [Finite I]
    (hret : Retract (ℱ.over U) (SheafOfModules.free I))
    (hlocalx : IsLocalRing (X.presheaf.stalk x)) :
    ∃ (r : ℕ) (V : Opens X) (_ : x ∈ V),
      Nonempty
        (ℱ.over V ≅
          (SheafOfModules.free.{u} (ULift.{u} (Fin r)) :
            SheafOfModules ((RingedSpace.ringCatSheaf X).over V))) := by
  -- Proof comment: first identify the stalk of the local retract with a standard free stalk over
  -- the local ring `\mathcal O_{X, x}`; then Lemma `17.11.7` upgrades that stalkwise free model
  -- to an actual free neighborhood of `x`.
  rcases stalk_free_of_retract_free_over_of_isLocalRing
      (X := X) (ℱ := ℱ) (x := x) (U := U) hx
      (hret := hret) hlocalx with ⟨r, hfreeStalk⟩
  exact exists_open_neighborhood_free_over_of_stalk_free (ℱ := ℱ) x r hfreeStalk

-- Proof sketch: first use the previous bridge to see that `ℱ` is finitely presented. Then for
-- each `x : X`, the owner hypothesis gives a neighbourhood `U` on which `ℱ.over U` is a retract
-- of a finite free sheaf. Passing to the stalk at `x`, the stalk module `ℱ_x` is therefore a
-- retract of a finite free module over the local ring `𝒪_{X, x}`, hence is finite free by
-- Algebra, Lemma `10.78.2`. Lemma `17.11.7` upgrades these stalkwise finite free models to finite
-- free neighbourhoods.
/-- Owner-level form of Lemma 17.14.6: on a ringed space whose stalk rings are local, an
`\mathcal O_X`-module that is locally a direct summand of a finite free module is finite locally
free. -/
theorem isFiniteLocallyFree_of_isLocallyDirectSummandOfFiniteFree_of_stalk_isLocalRing
    (ℱ : ModX) (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x))
    [IsLocallyDirectSummandOfFiniteFreeX ℱ] :
    ℱ.IsFiniteLocallyFree := by
  let _ : ℱ.IsFinitePresentation :=
    isFinitePresentation_of_isLocallyDirectSummandOfFiniteFree ℱ
  classical
  refine ⟨fun x ↦ ?_⟩
  -- Proof comment: choose the local retract-of-finite-free neighborhood given by the owner
  -- hypothesis, then upgrade it to a finite free neighborhood using the stalk-local-ring bridge.
  rcases RingedSite.IsLocallyDirectSummandOfFiniteFree.exists_open_neighborhood_retract_free ℱ x with
    ⟨U, hxU, I, hI, hret⟩
  let _ : Finite I := hI
  rcases exists_open_neighborhood_iso_free_of_retract_free_over_of_isLocalRing
      (ℱ := ℱ) (x := x) (U := U) hxU
      (hret := Classical.choice hret) (hlocal x) with
    ⟨r, V, hxV, e⟩
  exact ⟨V, hxV, ULift.{u} (Fin r), inferInstance, e⟩

/-- Helper for Lemma 17.14.6: a global retract of a finite locally free sheaf induces the local
direct-summand owner by restricting the retract to each member of the ambient local cover. -/
private theorem isLocallyDirectSummandOfFiniteFree_of_retract
    {ℱ ℋ : ModX} [ℋ.IsFiniteLocallyFree] (hret : Retract ℱ ℋ) :
    IsLocallyDirectSummandOfFiniteFreeX ℱ := by
  classical
  let _ : IsLocallyDirectSummandOfFiniteFreeX ℋ := inferInstance
  refine ⟨fun U ↦ ?_⟩
  rcases (inferInstance : IsLocallyDirectSummandOfFiniteFreeX ℋ).exists_cover_retract_free U with
    ⟨I, Ui, hUi, hsplit⟩
  refine ⟨I, Ui, hUi, ?_⟩
  intro i
  rcases hsplit i with ⟨α, hα, ⟨hretHi⟩⟩
  let hretUi :
      Retract ((ℱ.over U).over (Ui i)) ((ℋ.over U).over (Ui i)) :=
    Retract.map
      (SheafOfModules.pushforward
        (𝟙 (Sheaf.over (Sheaf.over (RingedSpace.ringCatSheaf X) U) (Ui i))))
      (Retract.map
        (SheafOfModules.pushforward
          (𝟙 (Sheaf.over (RingedSpace.ringCatSheaf X) U)))
        hret)
  refine ⟨α, hα, ⟨hretUi.i ≫ hretHi.i, hretHi.r ≫ hretUi.r, ?_⟩⟩
  -- Proof comment: compose the restricted split maps for `ℱ` into the already chosen local split
  -- maps for `ℋ`; the retract identity is preserved by both restriction functors.
  calc
    (hretUi.i ≫ hretHi.i) ≫ (hretHi.r ≫ hretUi.r) =
        hretUi.i ≫ (hretHi.i ≫ hretHi.r) ≫ hretUi.r := by
      simp [Category.assoc]
    _ = hretUi.i ≫ hretUi.r := by
      rw [hretHi.retract]
      simp
    _ = 𝟙 _ := hretUi.retract

-- Proof sketch: a global retract of a finite locally free sheaf restricts on each neighbourhood
-- where `ℋ` is finite free to a local retract of a finite free sheaf, so `ℱ` satisfies the owner
-- predicate `IsLocallyDirectSummandOfFiniteFree`; the owner theorem then applies directly.
/-- Lemma 17.14.6: if every stalk `\mathcal O_{X, x}` is a local ring, then any direct summand of
a finite locally free `\mathcal O_X`-module is finite locally free. Here the direct-summand
hypothesis is expressed by a categorical retract. -/
@[stacks 0BCI]
theorem isFiniteLocallyFree_of_retract_of_stalk_isLocalRing
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x))
    {ℱ ℋ : ModX} [ℋ.IsFiniteLocallyFree] (hret : Retract ℱ ℋ) :
    ℱ.IsFiniteLocallyFree := by
  let _ : IsLocallyDirectSummandOfFiniteFreeX ℱ :=
    isLocallyDirectSummandOfFiniteFree_of_retract (hret := hret)
  exact isFiniteLocallyFree_of_isLocallyDirectSummandOfFiniteFree_of_stalk_isLocalRing ℱ hlocal

end SheafOfModules
