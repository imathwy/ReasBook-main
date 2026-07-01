import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Ring.DirectLimit

universe u

noncomputable section

section

variable {I : Type u} [Preorder I]
variable {R S : I → Type u}
variable [∀ i, CommRing (R i)] [∀ i, CommRing (S i)] [∀ i, Algebra (R i) (S i)]
variable {ρ : ∀ i j, i ≤ j → R i →+* R j}
variable {σ : ∀ i j, i ≤ j → S i →+* S j}

local notation "R∞" => Ring.DirectLimit R (fun i j h ↦ ρ i j h)
local notation "S∞" => Ring.DirectLimit S (fun i j h ↦ σ i j h)

/- Domain triage:
* primary domain: Kähler differentials of a directed system of commutative ring maps and their
  behavior with respect to direct limits;
* sampled owner API:
  `Ring.DirectLimit.map`,
  `CommRingCat.KaehlerDifferential`,
  `CommRingCat.KaehlerDifferential.map`,
  `Module.DirectLimit`;
* source-facing layer: the direct limit of the stagewise differentials after scalar extension to
  `S∞` and the canonical comparison with `Ω[S∞⁄R∞]`;
* core/canonical owner: the target differential is owned by
  `CommRingCat.KaehlerDifferential` applied to the induced map on ring direct limits, while the
  source direct limit is canonically the quotient-model owner `Module.DirectLimit`;
* bridge/view: the stagewise maps into the target come from
  `CommRingCat.KaehlerDifferential.map`, and the comparison from the direct limit is induced by
  `Module.DirectLimit.lift`.

Primitive data are only the stagewise differential modules, their transition maps after extending
scalars to `S∞`, and the compatible family of maps into `Ω[S∞⁄R∞]`. The categorical diagram,
cocone, and colimit wrappers are therefore derived API and should not remain as parallel owners in
this file.
-/

private abbrev stageHom : ∀ i : I, CommRingCat.of (R i) ⟶ CommRingCat.of (S i) :=
  fun i ↦ CommRingCat.ofHom ((algebraMap (R i) (S i)) : R i →+* S i)

private abbrev directLimitRingHom
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    R∞ →+* S∞ :=
  Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h

private abbrev directLimitDifferential
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    ModuleCat S∞ :=
  CommRingCat.KaehlerDifferential (CommRingCat.ofHom (directLimitRingHom hcomm))

/-- The transition square in the directed system of ring maps. -/
private theorem stage_square
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) :
    CommRingCat.ofHom (ρ i j h) ≫ stageHom j =
      stageHom i ≫ CommRingCat.ofHom (σ i j h) := by
  ext x
  exact DFunLike.congr_fun (hcomm h) x

private abbrev stageKaehlerDifferential (i : I) : ModuleCat (S i) :=
  CommRingCat.KaehlerDifferential (@stageHom I R S _ _ _ i)

private abbrev stageDirectLimitTargetMap (i : I) : S i →+* S∞ :=
  Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i

private abbrev stageTargetHom {i j : I} (h : i ≤ j) :
    CommRingCat.of (S i) ⟶ CommRingCat.of (S j) :=
  CommRingCat.ofHom (σ i j h)

private abbrev stageDirectLimitTargetHom (i : I) :
    CommRingCat.of (S i) ⟶ CommRingCat.of S∞ :=
  CommRingCat.ofHom (stageDirectLimitTargetMap i)

private noncomputable def stageKaehlerDifferentialBaseChange (i : I) :
    ModuleCat S∞ :=
  (ModuleCat.extendScalars ((@stageDirectLimitTargetHom I _ S _ σ i).hom)).obj
    (@stageKaehlerDifferential I R S _ _ _ i)

/-- The transition map on stagewise Kähler differentials after extending scalars from
`S_i` to `S_j`. -/
private noncomputable def stageKaehlerDifferentialTransitionBase
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) :
    (ModuleCat.extendScalars ((@stageTargetHom I _ S _ σ i j h).hom)).obj
        (@stageKaehlerDifferential I R S _ _ _ i) ⟶
      @stageKaehlerDifferential I R S _ _ _ j :=
  ((ModuleCat.extendRestrictScalarsAdj ((@stageTargetHom I _ S _ σ i j h).hom)).homEquiv _ _).symm
    (CommRingCat.KaehlerDifferential.map (stage_square hcomm h))

/-- The canonical structure maps into the ring direct limit compose with the transition maps as
expected. -/
private theorem directLimitTarget_of_comp {i j : I} (h : i ≤ j) :
    (Ring.DirectLimit.of S (fun i j h ↦ σ i j h) j).comp (σ i j h) =
      Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i := by
  ext x
  change Ring.DirectLimit.of S (fun i j h ↦ σ i j h) j (σ i j h x) =
    Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i x
  simp [Ring.DirectLimit.of_f h x]

/-- The transition morphism in `ModuleCat S∞` between the stagewise differentials after extending
scalars along the canonical maps `S_i → S∞`. -/
private noncomputable def stageKaehlerDifferentialBaseChangeTransition
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) :
    @stageKaehlerDifferentialBaseChange I _ R S _ _ _ σ i ⟶
      @stageKaehlerDifferentialBaseChange I _ R S _ _ _ σ j := by
  let Ωi : ModuleCat (S i) := @stageKaehlerDifferential I R S _ _ _ i
  let σij : S i →+* S j := (@stageTargetHom I _ S _ σ i j h).hom
  let σjLim : S j →+* S∞ := (@stageDirectLimitTargetHom I _ S _ σ j).hom
  have hobj :
      @stageKaehlerDifferentialBaseChange I _ R S _ _ _ σ i =
        (ModuleCat.extendScalars (σjLim.comp σij)).obj Ωi := by
    simpa [stageKaehlerDifferentialBaseChange, Ωi] using
      congrArg
        (fun t ↦ (ModuleCat.extendScalars t).obj Ωi)
        (directLimitTarget_of_comp h).symm
  exact
    eqToHom hobj ≫
      (ModuleCat.extendScalarsComp σij σjLim).hom.app Ωi ≫
      (ModuleCat.extendScalars σjLim).map
        (stageKaehlerDifferentialTransitionBase hcomm h)

/-- The direct-limit square relating a stage map to the induced map on ring direct limits. -/
private theorem directLimit_square
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) :
    CommRingCat.ofHom (Ring.DirectLimit.of R (fun i j h ↦ ρ i j h) i) ≫
        CommRingCat.ofHom (directLimitRingHom hcomm) =
      stageHom i ≫
        CommRingCat.ofHom (Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i) := by
  ext x
  simp [directLimitRingHom]

/-- The canonical stage map into the Kähler differential of the induced direct-limit ring map. -/
private noncomputable def stageKaehlerDifferentialToTarget
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) :
    @stageKaehlerDifferential I R S _ _ _ i ⟶
      (ModuleCat.restrictScalars ((@stageDirectLimitTargetHom I _ S _ σ i).hom)).obj
        (@directLimitDifferential I _ R S _ _ _ ρ σ hcomm) :=
  CommRingCat.KaehlerDifferential.map (directLimit_square hcomm i)

private noncomputable def stageKaehlerDifferentialBaseChangeToTarget
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) :
    @stageKaehlerDifferentialBaseChange I _ R S _ _ _ σ i ⟶
      @directLimitDifferential I _ R S _ _ _ ρ σ hcomm := by
  exact
    ((ModuleCat.extendRestrictScalarsAdj ((@stageDirectLimitTargetHom I _ S _ σ i).hom)).homEquiv
      _ _).symm
      (stageKaehlerDifferentialToTarget hcomm i)

private theorem stageKaehlerDifferentialBaseChangeToTarget_compatible
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) (x : stageKaehlerDifferentialBaseChange i) :
    (stageKaehlerDifferentialBaseChangeToTarget hcomm j).hom
        ((stageKaehlerDifferentialBaseChangeTransition hcomm h).hom x) =
      (stageKaehlerDifferentialBaseChangeToTarget hcomm i).hom x := by
  sorry

/-- The quotient-model direct limit in `ModuleCat S∞` of the stagewise Kähler differentials after
extending scalars along the canonical maps `S_i → S∞`. -/
noncomputable def kaehlerDifferentialDirectLimitModule
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    ModuleCat S∞ :=
  let _ : DecidableEq I := Classical.decEq I
  let G : I → Type u := fun i ↦ stageKaehlerDifferentialBaseChange i
  let μ : ∀ i j, i ≤ j → G i →ₗ[S∞] G j :=
    fun _ _ h ↦ (stageKaehlerDifferentialBaseChangeTransition hcomm h).hom
  ModuleCat.of S∞ <|
    Module.DirectLimit G μ

/-- The canonical comparison from the direct limit of the stagewise Kähler differentials to the
Kähler differential of the induced direct-limit ring map. -/
noncomputable def kaehlerDifferential_directLimitComparison
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    kaehlerDifferentialDirectLimitModule hcomm ⟶
      CommRingCat.KaehlerDifferential
        (CommRingCat.ofHom
          (Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h)) :=
  let _ : DecidableEq I := Classical.decEq I
  let G : I → Type u := fun i ↦ stageKaehlerDifferentialBaseChange i
  let μ : ∀ i j, i ≤ j → G i →ₗ[S∞] G j :=
    fun _ _ h ↦ (stageKaehlerDifferentialBaseChangeTransition hcomm h).hom
  let ν : ∀ i, G i →ₗ[S∞] directLimitDifferential hcomm :=
    fun i ↦ (stageKaehlerDifferentialBaseChangeToTarget hcomm i).hom
  ModuleCat.ofHom <|
    Module.DirectLimit.lift S∞ I G μ ν fun _ _ h x ↦
      stageKaehlerDifferentialBaseChangeToTarget_compatible hcomm h x

-- Proof sketch: use the generators-and-relations presentation of Kähler differentials together
-- with the directed colimit description of `S∞`; the induced universal derivation on the direct
-- limit source identifies it with `Ω[S∞⁄R∞]`.
/-- Lemma 10.131.5: the canonical comparison from the direct limit module of the stagewise Kähler
differentials to the Kähler differential of the induced direct-limit ring map is an isomorphism. -/
theorem kaehlerDifferential_directLimitComparison_isIso
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    IsIso (kaehlerDifferential_directLimitComparison hcomm) := sorry

end
