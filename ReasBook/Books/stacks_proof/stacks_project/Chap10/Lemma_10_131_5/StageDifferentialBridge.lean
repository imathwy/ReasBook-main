import Mathlib

open CategoryTheory
open Ring.DirectLimit

universe u

noncomputable section

namespace Lemma_10_131_5

section

variable {I : Type u} [Preorder I]
variable {R S : I → Type u}
variable [∀ i, CommRing (R i)] [∀ i, CommRing (S i)] [∀ i, Algebra (R i) (S i)]
variable {ρ : ∀ i j, i ≤ j → R i →+* R j}
variable {σ : ∀ i j, i ≤ j → S i →+* S j}

local notation "R∞" => Ring.DirectLimit R (fun i j h ↦ ρ i j h)
local notation "S∞" => Ring.DirectLimit S (fun i j h ↦ σ i j h)

/-- Helper for Chap10 Lemma 10 131 5: the stagewise algebra map as a morphism of
commutative rings. -/
abbrev stageHom : ∀ i : I, CommRingCat.of (R i) ⟶ CommRingCat.of (S i) :=
  fun i ↦ CommRingCat.ofHom ((algebraMap (R i) (S i)) : R i →+* S i)

/-- Helper for Chap10 Lemma 10 131 5: the ring map induced on direct limits by a compatible
system of algebra maps. -/
abbrev directLimitRingHom
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    R∞ →+* S∞ :=
  Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h

/-- Helper for Chap10 Lemma 10 131 5: the Kähler differential of the induced direct-limit
ring map. -/
abbrev directLimitDifferential
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    ModuleCat S∞ :=
  CommRingCat.KaehlerDifferential (CommRingCat.ofHom (directLimitRingHom hcomm))

/-- Helper for Lemma 10.131.5: the target Kähler differential carries its canonical left
`S∞`-module structure on the underlying type. -/
instance directLimitDifferential_module
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    Module S∞ ↑(directLimitDifferential hcomm) :=
  inferInstance

/-- Helper for Lemma 10.131.5: the target Kähler differential carries the induced right action
needed to form its trivial square-zero extension over `S∞`. -/
instance directLimitDifferential_opModule
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    Module S∞ᵐᵒᵖ ↑(directLimitDifferential hcomm) :=
  Module.compHom _ ((RingHom.id S∞).fromOpposite mul_comm)

/-- Helper for Lemma 10.131.5: the target Kähler differential is central over the commutative
ring `S∞`. -/
instance directLimitDifferential_isCentral
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    IsCentralScalar S∞ ↑(directLimitDifferential hcomm) :=
  ⟨fun _ _ ↦ rfl⟩

/-- The transition square in the directed system of ring maps. -/
theorem stage_square
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) :
    CommRingCat.ofHom (ρ i j h) ≫ stageHom j =
      stageHom i ≫ CommRingCat.ofHom (σ i j h) := by
  ext x
  exact DFunLike.congr_fun (hcomm h) x

/-- Helper for Chap10 Lemma 10 131 5: the stagewise Kähler differential module. -/
abbrev stageKaehlerDifferential (i : I) : ModuleCat (S i) :=
  CommRingCat.KaehlerDifferential (@stageHom I R S _ _ _ i)

/-- Helper for Chap10 Lemma 10 131 5: the canonical map from a target stage to the target
direct limit. -/
abbrev stageDirectLimitTargetMap (i : I) : S i →+* S∞ :=
  Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i

/-- Helper for Chap10 Lemma 10 131 5: a transition map between target stages as a morphism of
commutative rings. -/
abbrev stageTargetHom {i j : I} (h : i ≤ j) :
    CommRingCat.of (S i) ⟶ CommRingCat.of (S j) :=
  CommRingCat.ofHom (σ i j h)

/-- Helper for Chap10 Lemma 10 131 5: the canonical map from a target stage to the target
direct limit as a morphism of commutative rings. -/
abbrev stageDirectLimitTargetHom (i : I) :
    CommRingCat.of (S i) ⟶ CommRingCat.of S∞ :=
  CommRingCat.ofHom (stageDirectLimitTargetMap i)

/-- Helper for Lemma 10.131.5: each transition map in the stagewise target system induces the
canonical algebra structure on the later stage. -/
instance stageTargetHom_algebra {i j : I} (h : i ≤ j) : Algebra (S i) (S j) :=
  (σ i j h).toAlgebra

/-- Helper for Lemma 10.131.5: each stage ring acts on the direct-limit target ring through its
canonical structure map. -/
instance stageDirectLimitTargetMap_algebra (i : I) : Algebra (S i) S∞ :=
  (stageDirectLimitTargetMap i).toAlgebra

/-- Helper for Chap10 Lemma 10 131 5: the stagewise Kähler differential after base change to
the target direct limit. -/
noncomputable def stageKaehlerDifferentialBaseChange (i : I) :
    ModuleCat S∞ :=
  (ModuleCat.extendScalars ((@stageDirectLimitTargetHom I _ S _ σ i).hom)).obj
    (@stageKaehlerDifferential I R S _ _ _ i)

/-- Helper for Lemma 10.131.5: an extended stagewise differential carries the canonical
`S∞`-module structure on its underlying type. -/
instance stageKaehlerDifferentialBaseChange_module (i : I) :
    Module S∞ ↑(@stageKaehlerDifferentialBaseChange I _ R S _ _ _ σ i) :=
  inferInstance

/-- The transition map on stagewise Kähler differentials after extending scalars from
`S_i` to `S_j`. -/
noncomputable def stageKaehlerDifferentialTransitionBase
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) :=
  letI : Algebra (S i) (S j) := (σ i j h).toAlgebra
  ((ModuleCat.extendRestrictScalarsAdj ((@stageTargetHom I _ S _ σ i j h).hom)).homEquiv _ _).symm
    (CommRingCat.KaehlerDifferential.map (stage_square hcomm h))

/-- The canonical structure maps into the ring direct limit compose with the transition maps as
expected. -/
theorem directLimitTarget_of_comp {i j : I} (h : i ≤ j) :
    (Ring.DirectLimit.of S (fun i j h ↦ σ i j h) j).comp (σ i j h) =
      Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i := by
  ext x
  change Ring.DirectLimit.of S (fun i j h ↦ σ i j h) j (σ i j h x) =
    Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i x
  simp [Ring.DirectLimit.of_f h x]

/-- The transition morphism in `ModuleCat S∞` between the stagewise differentials after extending
scalars along the canonical maps `S_i → S∞`. -/
noncomputable def stageKaehlerDifferentialBaseChangeTransition
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
theorem directLimit_square
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
noncomputable def stageKaehlerDifferentialToTarget
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) :
    @stageKaehlerDifferential I R S _ _ _ i ⟶
      (ModuleCat.restrictScalars ((@stageDirectLimitTargetHom I _ S _ σ i).hom)).obj
        (@directLimitDifferential I _ R S _ _ _ ρ σ hcomm) :=
  CommRingCat.KaehlerDifferential.map (directLimit_square hcomm i)

/-- Helper for Chap10 Lemma 10 131 5: the canonical base-changed stage map into the Kähler
differential of the induced direct-limit ring map. -/
noncomputable def stageKaehlerDifferentialBaseChangeToTarget
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

/-- Helper for Lemma 10.131.5: after extending scalars from `S_i` to `S_j`, the transition on
stagewise Kähler differentials sends the generator `1 ⊗ d x` to `d (σᵢⱼ x)`. -/
theorem stageKaehlerDifferentialTransitionBase_on_d
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) (x : S i) :
    (stageKaehlerDifferentialTransitionBase hcomm h).hom
        (((ModuleCat.extendRestrictScalarsAdj ((@stageTargetHom I _ S _ σ i j h).hom)).unit.app
            (@stageKaehlerDifferential I R S _ _ _ i))
          (CommRingCat.KaehlerDifferential.d x)) =
      CommRingCat.KaehlerDifferential.d (σ i j h x) := by
  -- Apply the adjunction formula so that functoriality on differentials can be read off on `d x`.
  rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  have hAdj :
      ((ModuleCat.extendRestrictScalarsAdj ((@stageTargetHom I _ S _ σ i j h).hom)).homEquiv _ _
          (stageKaehlerDifferentialTransitionBase hcomm h))
        (CommRingCat.KaehlerDifferential.d x) =
      (stageKaehlerDifferentialTransitionBase hcomm h).hom
        ((1 : S j) ⊗ₜ[↑(CommRingCat.of (S i))] CommRingCat.KaehlerDifferential.d x) := by
    simpa using (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
      (f := (@stageTargetHom I _ S _ σ i j h).hom)
      (φ := stageKaehlerDifferentialTransitionBase hcomm h)
      (m := CommRingCat.KaehlerDifferential.d x))
  exact hAdj.symm.trans <| by
    simpa [stageKaehlerDifferentialTransitionBase] using
      CommRingCat.KaehlerDifferential.map_d (stage_square hcomm h) x

/-- Helper for Lemma 10.131.5: the canonical stage map to the target differential sends
`1 ⊗ d x` to the differential of the direct-limit image of `x`. -/
theorem stageKaehlerDifferentialBaseChangeToTarget_on_d
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) (x : S i) :
    (stageKaehlerDifferentialBaseChangeToTarget hcomm i).hom
        (((ModuleCat.extendRestrictScalarsAdj ((@stageDirectLimitTargetHom I _ S _ σ i).hom)).unit.app
            (@stageKaehlerDifferential I R S _ _ _ i))
          (CommRingCat.KaehlerDifferential.d x)) =
      CommRingCat.KaehlerDifferential.d (stageDirectLimitTargetMap i x) := by
  -- Again, transport back across the adjunction and use the defining formula for `map_d`.
  rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  simpa [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply,
      stageKaehlerDifferentialBaseChangeToTarget, stageKaehlerDifferentialToTarget] using
    CommRingCat.KaehlerDifferential.map_d (directLimit_square hcomm i) x

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

/-- Helper for Lemma 10.131.5: the direct-limit source module carries its canonical left
`S∞`-module structure on the underlying type. -/
instance kaehlerDifferentialDirectLimitModule_module
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    Module S∞ ↑(kaehlerDifferentialDirectLimitModule hcomm) :=
  inferInstance

/-- Helper for Lemma 10.131.5: the direct-limit source module carries the induced right action
needed to form the trivial square-zero extension over the commutative ring `S∞`. -/
instance kaehlerDifferentialDirectLimitModule_opModule
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    Module S∞ᵐᵒᵖ ↑(kaehlerDifferentialDirectLimitModule hcomm) :=
  Module.compHom _ ((RingHom.id S∞).fromOpposite mul_comm)

/-- Helper for Lemma 10.131.5: the direct-limit source module is central over the commutative ring
`S∞`, so `TrivSqZeroExt` carries its standard commutative ring structure. -/
instance kaehlerDifferentialDirectLimitModule_isCentral
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    IsCentralScalar S∞ ↑(kaehlerDifferentialDirectLimitModule hcomm) :=
  ⟨fun _ _ ↦ rfl⟩

end

end Lemma_10_131_5
