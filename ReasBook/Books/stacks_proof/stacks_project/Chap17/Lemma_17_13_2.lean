import Mathlib
import stacks_proof.stacks_project.Chap06.Definition_6_26_1
import stacks_proof.stacks_project.Chap17.Definition_17_13_1

open CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 17.13.2:
- primary domain: quasi-coherent sheaves of modules on ringed spaces and pushforward along a
  closed immersion of ringed spaces;
- inspected owner declarations:
  `RingedSpace.IsClosedImmersion`,
  `ringedSpaceModulePushforward_isLeftAdjoint_of_isClosedImmersion`,
  `RingedSpace.ringCatSheaf`,
  `RingedSpace.Modules`,
  `SheafOfModules.IsQuasicoherent`,
  `AlgebraicGeometry.RingedSpace.Hom.pushforward`;
- best owner abstraction: the chapter source-facing owner `RingedSpace.IsClosedImmersion i`,
  together with the ambient owner categories `X.Modules` and `Z.Modules`, the canonical owner
  predicate `SheafOfModules.IsQuasicoherent`, the pushforward functor `i _*`, and the canonical
  left-adjoint owner layer on `i _*` supplied by the closed-immersion instance
  `ringedSpaceModulePushforward_isLeftAdjoint_of_isClosedImmersion`;
- primitive data: a closed immersion `i : Z ⟶ X` and a quasi-coherent module `ℱ : Z.Modules`;
- derived API: the quasi-coherence of `(i _*).obj (SheafOfModules.unit Z.ringCatSheaf)` supplied
  by the closed-immersion hypothesis, the colimit-preservation of `i _*` supplied by its
  left-adjoint structure, and then the quasi-coherence of `((i _*).obj ℱ)`.

Source/core/bridge triage:
- `source-facing`: the Stacks assertion that for a closed immersion `i`, the pushforward `i_* ℱ`
  of a quasi-coherent `\mathcal O_Z`-module is quasi-coherent;
- `core/canonical`: `X.Modules`, `Z.Modules`, `SheafOfModules.IsQuasicoherent`, and `i _*`,
  together with the owner-level left-adjoint structure on `i _*` and the explicit hypothesis that
  `i_* \mathcal O_Z` is quasi-coherent;
- `bridge/view`: the theorem that a closed immersion supplies that explicit structure-sheaf
  quasi-coherence hypothesis and the left-adjoint structure on `i_*`.

This file therefore keeps the numbered item at the `source-facing` layer and records the
closed-embedding plus owner-level left-adjoint / `i_* \mathcal O_Z` formulation as a companion
core theorem. -/

variable {X Z : RingedSpace.{u}}

local notation "𝒪Z" => SheafOfModules.unit Z.ringCatSheaf

/-- Helper for Lemma 17.13.2: the trivial zero map into a free sheaf composes to zero with the
identity. -/
private theorem freePresentation_zero_comp_id
    {C : Type u} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
    [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    (I : Type u) :
    (0 :
      SheafOfModules.free.{u} (ULift.{u} (Fin 0)) ⟶
        (SheafOfModules.free.{u} I : SheafOfModules R)) ≫
      𝟙 (SheafOfModules.free.{u} I : SheafOfModules R) = 0 := by
  -- Proof comment: the cokernel presentation of a free sheaf starts from the zero relation map.
  simp

/-- Helper for Lemma 17.13.2: the identity is the cokernel of the zero map into a free sheaf. -/
private noncomputable def freePresentation_id_isColimit
    {C : Type u} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
    [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    (I : Type u) :
    CategoryTheory.Limits.IsColimit
      (CategoryTheory.Limits.CokernelCofork.ofπ
        (𝟙 (SheafOfModules.free.{u} I : SheafOfModules R))
        (freePresentation_zero_comp_id (R := R) I)) := by
  -- Proof comment: the identity presents a free sheaf as the cokernel of the zero map.
  exact
    CategoryTheory.Limits.CokernelCofork.IsColimit.ofId
      (0 :
        SheafOfModules.free.{u} (ULift.{u} (Fin 0)) ⟶
          (SheafOfModules.free.{u} I : SheafOfModules R))
      rfl

/-- Helper for Lemma 17.13.2: every free sheaf carries its tautological global presentation. -/
private noncomputable def freePresentation
    {C : Type u} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
    [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    (I : Type u) :
    (SheafOfModules.free.{u} I : SheafOfModules R).Presentation :=
  SheafOfModules.presentationOfIsCokernelFree
    (0 :
      SheafOfModules.free.{u} (ULift.{u} (Fin 0)) ⟶
        (SheafOfModules.free.{u} I : SheafOfModules R))
    (𝟙 (SheafOfModules.free.{u} I : SheafOfModules R))
    (freePresentation_zero_comp_id (R := R) I)
    (freePresentation_id_isColimit (R := R) I)

/-- Helper for Lemma 17.13.2: the unit sheaf is the free sheaf on a singleton basis. -/
private noncomputable def unitSingletonCofan
    {C : Type u} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
    [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)] :
    CategoryTheory.Limits.Cofan (fun _ : PUnit ↦ SheafOfModules.unit R) :=
  CategoryTheory.Limits.Cofan.mk (P := SheafOfModules.unit R) (fun _ ↦ 𝟙 _)

/-- Helper for Lemma 17.13.2: the singleton family of copies of the unit sheaf has colimit the
unit sheaf itself. -/
private noncomputable def unitSingletonCofan_isColimit
    {C : Type u} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
    [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)] :
    CategoryTheory.Limits.IsColimit (unitSingletonCofan (R := R)) := by
  -- Proof comment: every cocone over a singleton family is determined by its single leg.
  exact
    CategoryTheory.Limits.mkCofanColimit (unitSingletonCofan (R := R))
      (fun t ↦ t.inj PUnit.unit)
      (fun t j ↦ by cases j; simp [unitSingletonCofan])
      (fun t m hm ↦ by simpa using hm PUnit.unit)

/-- Helper for Lemma 17.13.2: the unit sheaf is the free sheaf on a singleton basis. -/
private noncomputable def unitIsoFreeSingleton
    {C : Type u} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
    [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)] :
    SheafOfModules.unit R ≅ (SheafOfModules.free.{u} PUnit : SheafOfModules R) :=
  -- Proof comment: both cocones exhibit the coproduct of a singleton family of copies of `R`.
  CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso
    (unitSingletonCofan_isColimit (R := R))
    (SheafOfModules.isColimitFreeCofan (R := R) PUnit)

/-- Helper for Lemma 17.13.2: the unit module on a ringed space is quasi-coherent. -/
private theorem ringedSpaceModuleUnit_isQuasicoherent
    (Y : RingedSpace.{u}) :
    (SheafOfModules.unit Y.ringCatSheaf : Y.Modules).IsQuasicoherent := by
  let topOpen : Opens Y := ⟨Set.univ, isOpen_univ⟩
  let q :
      (SheafOfModules.unit Y.ringCatSheaf : Y.Modules).QuasicoherentData :=
    { I := PUnit
      X := fun _ ↦ topOpen
      coversTop := by
        intro U x hx
        -- Proof comment: the single open `⊤` refines every neighborhood of every point.
        refine ⟨U, homOfLE le_rfl, ?_, ?_⟩
        · exact ⟨PUnit.unit, ⟨homOfLE (by
            intro y hy
            trivial)⟩⟩
        · exact hx
      presentation := fun _ ↦
        let e :
            ((SheafOfModules.unit Y.ringCatSheaf : Y.Modules).over topOpen) ≅
              (SheafOfModules.free.{u} PUnit :
                SheafOfModules ((Y.ringCatSheaf).over topOpen)) :=
          unitIsoFreeSingleton (R := (Y.ringCatSheaf).over topOpen)
        -- Proof comment: transport the standard free presentation across the singleton-basis iso.
        (freePresentation (R := (Y.ringCatSheaf).over topOpen) PUnit).of_isIso e.inv }
  -- Proof comment: a single global free presentation on `⊤` already gives quasi-coherent data.
  exact q.isQuasicoherent

/-- Helper for Lemma 17.13.2: local surjectivity of a morphism of sheaves of rings is unchanged
after forgetting to sheaves of abelian groups. -/
private theorem underlyingLocallySurjective_of_commRingSheafMap
    {𝒜 ℬ : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}} (π : 𝒜 ⟶ ℬ)
    (hπ : Sheaf.IsLocallySurjective π) :
    Sheaf.IsLocallySurjective
      ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat AddCommGrpCat)).map π) := by
  -- Proof comment: the image sieve only depends on the underlying sections and restriction maps.
  change Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
    (Functor.whiskerRight π.hom (forget₂ CommRingCat AddCommGrpCat))
  change Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) π.hom at hπ
  refine Presheaf.IsLocallySurjective.mk ?_
  intro U s
  simpa [Presheaf.imageSieve] using hπ.imageSieve_mem (U := U) s

/-- Helper for Lemma 17.13.2: if the underlying additive-sheaf map of a morphism of
`\mathcal O_X`-modules is epic, then the original module morphism is epic. -/
private theorem module_epi_of_underlying_epi
    {𝒢 ℋ : RingedSpace.Modules X} (φ : 𝒢 ⟶ ℋ)
    (hφ : Epi ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map φ)) :
    Epi φ := by
  let toAbelianSheaf : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
    SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)
  letI : Epi (toAbelianSheaf.map φ) := hφ
  refine ⟨?_⟩
  intro T g h hcomp
  have hmapComp : toAbelianSheaf.map φ ≫ toAbelianSheaf.map g =
      toAbelianSheaf.map φ ≫ toAbelianSheaf.map h := by
    simpa using congrArg (fun f ↦ toAbelianSheaf.map f) hcomp
  have hmapEq : toAbelianSheaf.map g = toAbelianSheaf.map h :=
    (cancel_epi (toAbelianSheaf.map φ)).1 hmapComp
  -- Proof comment: equality after forgetting the module structure is already equality of the
  -- original module morphisms.
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext s
  simpa [toAbelianSheaf, PresheafOfModules.toPresheaf] using
    congrArg (fun k ↦ (k.hom.app U) s) hmapEq

/-- Helper for Lemma 17.13.2: for a closed immersion, the canonical module morphism
`\mathcal O_X \to i_* \mathcal O_Z` is epic. -/
private theorem unitToPushforwardObjUnit_epi_of_isClosedImmersion
    (i : Z ⟶ X) [RingedSpace.IsClosedImmersion i] :
    Epi (SheafOfModules.unitToPushforwardObjUnit (RingedSpace.Hom.toRingCatSheafHom i)) := by
  let hloc : Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i) :=
    inferInstance
  have hlocAdd :
      Sheaf.IsLocallySurjective
        ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat AddCommGrpCat)).map
          (RingedSpace.Hom.commRingSheafPushforwardMap i)) :=
    underlyingLocallySurjective_of_commRingSheafMap
      (X := X) (RingedSpace.Hom.commRingSheafPushforwardMap i) hloc
  have hEpiAdd :
      Epi
        ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat AddCommGrpCat)).map
          (RingedSpace.Hom.commRingSheafPushforwardMap i)) :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u}
      ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat AddCommGrpCat)).map
        (RingedSpace.Hom.commRingSheafPushforwardMap i))).1 hlocAdd
  have hEpiToSheaf :
      Epi
        ((SheafOfModules.toSheaf X.ringCatSheaf).map
          (SheafOfModules.unitToPushforwardObjUnit (RingedSpace.Hom.toRingCatSheafHom i))) := by
    -- Proof comment: both morphisms are the same after forgetting to additive sheaves.
    simpa [RingedSpace.Hom.commRingSheafPushforwardMap, RingedSpace.Hom.toRingCatSheafHom,
      SheafOfModules.toSheaf, SheafOfModules.unitToPushforwardObjUnit] using hEpiAdd
  exact module_epi_of_underlying_epi
    (X := X) (SheafOfModules.unitToPushforwardObjUnit (RingedSpace.Hom.toRingCatSheafHom i))
    hEpiToSheaf

/-- Helper for Lemma 17.13.2: a point outside the image of a closed embedding has an open
neighborhood disjoint from that image. -/
private theorem exists_open_neighborhood_disjoint_range_of_isClosedEmbedding
    {f : Z → X} (hf : Topology.IsClosedEmbedding f)
    {x : X} (hx : x ∉ Set.range f) :
    ∃ W : Opens X, x ∈ W ∧ Disjoint (W : Set X) (Set.range f) := by
  let W : Opens X := ⟨(Set.range f)ᶜ, by
    -- Proof comment: the image of a closed embedding is closed, so its complement is open.
    simpa using hf.isClosed_range.isOpen_compl⟩
  refine ⟨W, hx, ?_⟩
  -- Proof comment: by construction, the chosen open sits entirely inside the complement
  -- of the image.
  rw [Set.disjoint_left]
  intro y hyW hyRange
  exact hyW hyRange

/-- Helper for Chap17 Lemma 17 13 2: an open disjoint from the image of `i` has empty preimage in
`Z`. -/
private theorem preimage_eq_bot_of_disjointRange
    (i : Z ⟶ X) {W : Opens X}
    (hW : Disjoint (W : Set X) (Set.range i.hom.base)) :
    (Opens.map i.hom.base).obj W = ⊥ := by
  ext z
  constructor
  · intro hz
    -- Proof comment: any point of the preimage would map into both `W` and the image of `i`,
    -- contradicting disjointness.
    exact (Set.disjoint_left.1 hW (i.hom.base z) hz ⟨z, rfl⟩).elim
  · intro hz
    exact False.elim hz

/-- Helper for Lemma 17.13.2: a source open lying over `U` along a closed embedding is the exact
preimage of some ambient open contained in `U`. -/
private theorem ambientOpenOfPreimage_eq_of_isClosedEmbedding
    {f : Z → X} (hf : Topology.IsClosedEmbedding f)
    {U : Opens X} {V : Opens Z} (hV : V ≤ (Opens.map f).obj U) :
    ∃ W : Opens X, W ≤ U ∧ (Opens.map f).obj W = V := by
  let W : Opens X :=
    ⟨f '' (V : Set Z), by
      rw [hf.isInducing.isOpen_iff]
      simpa using V.isOpen⟩
  refine ⟨W, ?_, ?_⟩
  · intro x hx
    rcases hx with ⟨z, hz, rfl⟩
    exact hV hz
  · ext z
    constructor
    · intro hz
      rcases hz with ⟨z', hz', hzz'⟩
      exact hf.inj hzz' ▸ hz'
    · intro hz
      exact ⟨z, hz, rfl⟩

/-- Helper for Chap17 Lemma 17 13 2: the sieve generated in the slice over `U` by a family of
opens is the sieve generated by their underlying inclusions into `U`. -/
private theorem overSieveOfObjectsEqOfArrows
    {U : Opens X} {ι : Type u} (V : ι → Opens X) (π : ∀ i : ι, V i ⟶ U) :
    (Sieve.overEquiv (Over.mk (𝟙 U)))
        (Sieve.ofObjects (fun i ↦ Over.mk (π i)) (Over.mk (𝟙 U))) =
      Sieve.ofArrows V π := by
  -- Proof comment: forgetting the over-structure preserves exactly the same factorization data
  -- through the chosen open inclusions `π i`.
  ext W f
  constructor
  · intro hf
    rw [Sieve.overEquiv_iff] at hf
    rw [Sieve.mem_ofObjects_iff] at hf
    rcases hf with ⟨i, ⟨g⟩⟩
    rw [Sieve.mem_ofArrows_iff]
    exact ⟨i, g.left, by simpa using g.w.symm⟩
  · intro hf
    rw [Sieve.overEquiv_iff]
    rw [Sieve.mem_ofArrows_iff] at hf
    rcases hf with ⟨i, g, hg⟩
    rw [Sieve.mem_ofObjects_iff]
    exact ⟨i, ⟨Over.homMk g (by simpa using hg.symm)⟩⟩

/-- Helper for Chap17 Lemma 17 13 2: a pointwise open cover of `U` yields a cover of the terminal
object in the slice site `(Opens X)/U`. -/
private theorem overOpenCoverCoversTop
    {U : Opens X} {ι : Type u} (V : ι → Opens X) (π : ∀ i, V i ⟶ U)
    (hV : ∀ x ∈ U, ∃ i, x ∈ V i) :
    ((Opens.grothendieckTopology X).over U).CoversTop (fun i ↦ Over.mk (π i)) := by
  -- Proof comment: rewrite the slice-site cover condition in terms of the ambient sieve generated
  -- by the open inclusions `π i`, then use the pointwise covering hypothesis.
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal
    (J := (Opens.grothendieckTopology X).over U)
    (Over.mk (𝟙 U)) Over.mkIdTerminal]
  rw [GrothendieckTopology.mem_over_iff]
  rw [overSieveOfObjectsEqOfArrows]
  intro x hxU
  rcases hV x hxU with ⟨i, hxi⟩
  exact ⟨V i, π i, Sieve.ofArrows_mk V π i, hxi⟩

/-- Helper for Chap17 Lemma 17 13 2: a presentation on `M.over U` restricts to any smaller open
`W ≤ U`. -/
private noncomputable def presentationRestrictOverOpen
    {M : X.Modules} {U W : Opens X} (P : (M.over U).Presentation) (hWU : W ≤ U) :
    (M.over W).Presentation := by
  let V : Over U := Over.mk (homOfLE hWU)
  letI :
      PreservesColimitsOfSize.{u, u}
        (SheafOfModules.pushforward (𝟙 (((X.ringCatSheaf).over U).over V))) :=
    (SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf.over U) V)
      .leftAdjoint_preservesColimits
  -- Proof comment: first restrict the chosen presentation one step further inside the slice over
  -- `U`, then transport it across the canonical iterated-slice equivalence.
  let P' : ((M.over U).over V).Presentation :=
    P.map (SheafOfModules.pushforward (𝟙 (((X.ringCatSheaf).over U).over V))) (by rfl)
  let e := pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv V)
    (S := ((X.ringCatSheaf).over U).over V) (R := (X.ringCatSheaf).over W) (𝟙 _) (𝟙 _)
    (by ext : 2; exact X.sheaf.1.map_id _)
    (by ext : 2; exact X.sheaf.1.map_id _)
  exact
    ((P'.map e.inverse (.refl _)).of_isIso
      (e.fullyFaithfulFunctor.preimageIso
        (by exact e.counitIso.app ((M.over U).over V))).hom)

/-- Helper for Chap17 Lemma 17 13 2: a presentation on the slice object `V : Over U` identifies
with a presentation on the corresponding smaller open `V.left`. -/
private noncomputable def presentationOnSliceObject
    {M : X.Modules} {U : Opens X} (V : Over U)
    (P : ((M.over U).over V).Presentation) :
    (M.over V.left).Presentation := by
  let e := pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv V)
    (S := ((X.ringCatSheaf).over U).over V) (R := (X.ringCatSheaf).over V.left) (𝟙 _) (𝟙 _)
    (by ext : 2; exact X.sheaf.1.map_id _) (by ext : 2; exact X.sheaf.1.map_id _)
  -- Proof comment: transport the iterated-slice presentation across the canonical equivalence
  -- between the slice over `V` and the ordinary slice over `V.left`.
  exact
    ((P.map e.inverse (.refl _)).of_isIso
      (e.fullyFaithfulFunctor.preimageIso
        (by exact e.counitIso.app ((M.over U).over V))).hom)

/-- Helper for Lemma 17.13.2: on an open where `i_* \mathcal O_Z` is already quasi-coherent, the
remaining task is to push a local presentation of `\mathcal F` through the restricted left
adjoint and then replace the resulting coproducts of `i_* \mathcal O_Z` by free
`\mathcal O_X`-presentations. -/
private theorem pushforwardOverPresentation_of_exactPreimage
    (i : Z ⟶ X) {U W : Opens X} (hWU : W ≤ U)
    [(RingedSpace.Hom.pushforward i).IsLeftAdjoint]
    (ℱ : Z.Modules) {V : Opens Z}
    (hWV : (Opens.map i.hom.base).obj W = V)
    (PV : (ℱ.over V).Presentation)
    (QW : (((RingedSpace.Hom.pushforward i).obj 𝒪Z).over W).Presentation) :
    (((RingedSpace.Hom.pushforward i).obj ℱ).over W).Presentation := by
  -- TODO: map `PV` through the slice pushforward over `W`, transport the result across the
  -- exact-preimage identification `hWV`, and then splice the mapped presentation with `QW` so the
  -- free terms are rewritten over `\mathcal O_X|_W` rather than over `(i_* \mathcal O_Z)|_W`.
  -- This isolates the coefficient-layer mismatch that blocked the direct local proof.
  let _ := hWU
  let _ := hWV
  let _ := PV
  let _ := QW
  sorry

/-- Helper for Lemma 17.13.2: away from the image of a closed embedding, the restricted
pushforward is quasi-coherent because the source restriction is supported on the empty open. -/
private theorem pushforwardOver_isQuasicoherent_of_disjointRange
    (i : Z ⟶ X) (W : Opens X) (ℱ : Z.Modules)
    (hW : Disjoint (W : Set X) (Set.range i.hom.base)) :
    (((RingedSpace.Hom.pushforward i).obj ℱ).over W).IsQuasicoherent := by
  -- TODO: normalize `(((i_*).obj ℱ).over W)` to the source restriction over
  -- `(Opens.map i.hom.base).obj W = ⊥`, show that restriction is the zero module on the empty
  -- slice site, and transport the trivial zero presentation back across the pushforward/restriction
  -- equivalence.
  let _ := hW
  sorry

/-- Helper for Lemma 17.13.2: on an open where `i_* \mathcal O_Z` is already quasi-coherent, the
remaining task is to push a local presentation of `\mathcal F` through the restricted left
adjoint and then replace the resulting coproducts of `i_* \mathcal O_Z` by free
`\mathcal O_X`-presentations. -/
private theorem pushforwardOver_isQuasicoherent_of_pushforwardUnitOver_isQuasicoherent
    (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i.hom.base) (U : Opens X)
    [(RingedSpace.Hom.pushforward i).IsLeftAdjoint]
    (ℱ : Z.Modules) [ℱ.IsQuasicoherent]
    (hU : (((RingedSpace.Hom.pushforward i).obj 𝒪Z).over U).IsQuasicoherent) :
    (((RingedSpace.Hom.pushforward i).obj ℱ).over U).IsQuasicoherent := by
  classical
  -- Route correction: `Presentation.map` does not apply directly to `i_*` on `X` because
  -- `i_* \mathcal O_Z` is not definitionally the unit sheaf on `X`. The corrected local route is
  -- to use `hi` to match a source chart with an ambient chart inside `U`, then map that source
  -- presentation through the restricted left adjoint and splice it with a presentation of
  -- `((i_* \mathcal O_Z).over U)` coming from `hU`.
  -- TODO: use the new transport helper `presentationOnSliceObject` to turn the chosen local chart
  -- from `hU` into an honest presentation on a smaller open, then package the pointwise matched
  -- opens into a cover of `U`.
  -- The in-image branch should combine a local chart from `qℱ` with a local coefficient chart
  -- from `hU` and then invoke `pushforwardOverPresentation_of_exactPreimage`.
  -- The off-image branch should shrink to an open disjoint from `Set.range i.hom.base` and apply
  -- `pushforwardOver_isQuasicoherent_of_disjointRange`.
  let _ := hi
  let _ := hU
  sorry

/-- Helper for Lemma 17.13.2: the restricted structure-sheaf pushforward of a closed immersion has
an explicit local presentation coming from generators of the ideal sheaf. -/
private noncomputable def pushforwardUnitOverPresentation
    (i : Z ⟶ X) [RingedSpace.IsClosedImmersion i]
    (σ : (RingedSpace.closedImmersionIdealSheaf i).LocalGeneratorsData)
    (a : σ.I) :
    (((RingedSpace.Hom.pushforward i).obj 𝒪Z).over (σ.X a)).Presentation := by
  let φi := SheafOfModules.unitToPushforwardObjUnit (RingedSpace.Hom.toRingCatSheafHom i)
  let U := σ.X a
  let restriction :
      X.Modules ⥤ SheafOfModules ((X.ringCatSheaf).over U) :=
    SheafOfModules.pushforward (𝟙 ((X.ringCatSheaf).over U))
  letI : PreservesColimitsOfSize.{u, u} restriction :=
    (SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) U).leftAdjoint_preservesColimits
  have hφi_epi : Epi φi := unitToPushforwardObjUnit_epi_of_isClosedImmersion (X := X) i
  let unitMap :
      (SheafOfModules.unit X.ringCatSheaf : X.Modules).over U ⟶
        (((RingedSpace.Hom.pushforward i).obj 𝒪Z).over U) :=
    φi.over U
  let idealInclusion :
      (RingedSpace.closedImmersionIdealSheaf i).over U ⟶
        (SheafOfModules.unit X.ringCatSheaf : X.Modules).over U :=
    (kernel.ι φi).over U
  have hUnitZero : idealInclusion ≫ unitMap = 0 := by
    -- Proof comment: the restricted ideal inclusion still lands in the kernel of the restricted
    -- structure-sheaf map.
    simpa [idealInclusion, unitMap] using congrArg (fun t ↦ t.over U) (kernel.condition φi)
  have hUnitCokernel :
      IsColimit (CokernelCofork.ofπ unitMap hUnitZero) := by
    -- Proof comment: restriction to `U` is a left adjoint, so it preserves the global cokernel
    -- presentation of `\mathcal O_X \to i_* \mathcal O_Z`.
    let hGlobal :
        IsColimit (CokernelCofork.ofπ φi (kernel.condition φi)) :=
      Abelian.epiIsCokernelOfKernel φi (limit.isLimit _)
    simpa [restriction, unitMap, idealInclusion] using isColimitOfPreserves restriction hGlobal
  let e :
      (SheafOfModules.unit X.ringCatSheaf : X.Modules).over U ≅
        (SheafOfModules.free.{u} PUnit : SheafOfModules ((X.ringCatSheaf).over U)) :=
    unitIsoFreeSingleton (R := (X.ringCatSheaf).over U)
  let f :
      SheafOfModules.free.{u} ((σ.generators a).I) ⟶
        (SheafOfModules.free.{u} PUnit : SheafOfModules ((X.ringCatSheaf).over U)) :=
    (σ.generators a).π ≫ idealInclusion ≫ e.hom
  let g :
      (SheafOfModules.free.{u} PUnit : SheafOfModules ((X.ringCatSheaf).over U)) ⟶
        (((RingedSpace.Hom.pushforward i).obj 𝒪Z).over U) :=
    e.inv ≫ unitMap
  have hfg : f ≫ g = 0 := by
    -- Proof comment: the ideal generators first map into the kernel, so they vanish after the
    -- quotient map to `i_* \mathcal O_Z`.
    simp [f, g, Category.assoc, hUnitZero]
  have hCokernelIdealGenerators :
      IsColimit
        (CokernelCofork.ofπ unitMap
          (by
            change ((σ.generators a).π ≫ idealInclusion) ≫ unitMap = 0
            simp [Category.assoc, hUnitZero])) := by
    -- Proof comment: the chosen generators surject onto the restricted ideal sheaf, so replacing
    -- the kernel inclusion by that epimorphic presentation does not change the cokernel.
    simpa [Category.assoc] using
      isCokernelEpiComp
        (c := CokernelCofork.ofπ unitMap hUnitZero)
        hUnitCokernel (σ.generators a).π rfl
  have hCokernel :
      IsColimit (CokernelCofork.ofπ g hfg) := by
    -- Proof comment: transport the source of the cokernel map across the singleton free-unit iso.
    refine CokernelCofork.IsColimit.ofπ' g hfg ?_
    intro A k hk
    have hk' : ((σ.generators a).π ≫ idealInclusion) ≫ (e.hom ≫ k) = 0 := by
      simpa [f, Category.assoc] using hk
    refine ⟨hCokernelIdealGenerators.desc (CokernelCofork.ofπ (e.hom ≫ k) hk'), ?_⟩
    -- Proof comment: descend against `unitMap`, then cancel the source iso.
    calc
      g ≫ hCokernelIdealGenerators.desc (CokernelCofork.ofπ (e.hom ≫ k) hk')
          = e.inv ≫
              (unitMap ≫ hCokernelIdealGenerators.desc (CokernelCofork.ofπ (e.hom ≫ k) hk')) := by
            simp [g, Category.assoc]
      _ = e.inv ≫ (e.hom ≫ k) := by
            rw [hCokernelIdealGenerators.fac (CokernelCofork.ofπ (e.hom ≫ k) hk')
              WalkingParallelPair.one]
      _ = k := by simp [Category.assoc]
  -- Proof comment: the relation map from the ideal generators and the quotient map from the unit
  -- sheaf give the desired finite-step local presentation.
  exact SheafOfModules.presentationOfIsCokernelFree f g hfg hCokernel

-- Proof sketch: choose local quasi-coherent presentations of `ℱ` on `Z`; the closed-embedding
-- hypothesis identifies neighbourhoods on the image, and quasi-coherence of `i_* \mathcal O_Z`
-- makes the pushed-forward free terms quasi-coherent on `X`. The canonical left-adjoint owner
-- layer on `i_*` then supplies the coproduct-preservation needed by `Presentation.map`, so
-- pushing forward those local presentations yields local cokernel presentations of `i_* ℱ`.
/-- Core companion: if `i : (Z, \mathcal{O}_Z) \to (X, \mathcal{O}_X)` has underlying map a
closed embedding, if pushforward on module sheaves along `i` is a left adjoint, and if the
pushed-forward structure sheaf `i_* \mathcal O_Z` is quasi-coherent, then for any quasi-coherent
`\mathcal{O}_Z`-module `\mathcal{F}`, the pushforward `i_* \mathcal{F}` is quasi-coherent. -/
theorem ringedSpaceModulePushforward_isQuasicoherent_of_closedEmbedding_of_isLeftAdjoint_of_pushforwardUnit_isQuasicoherent
    (i : Z ⟶ X)
    (hi : Topology.IsClosedEmbedding i.hom.base)
    [(RingedSpace.Hom.pushforward i).IsLeftAdjoint]
    (hOZ : ((RingedSpace.Hom.pushforward i).obj 𝒪Z).IsQuasicoherent)
    (ℱ : Z.Modules) [ℱ.IsQuasicoherent] :
    ((RingedSpace.Hom.pushforward i).obj ℱ).IsQuasicoherent := by
  classical
  let _ : ((i _*).obj 𝒪Z).IsQuasicoherent := hOZ
  rcases SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData
      (M := ((i _*).obj 𝒪Z)) with ⟨q⟩
  let D : ∀ a : q.I, ((((i _*).obj ℱ).over (q.X a))).QuasicoherentData :=
    fun a ↦ by
      let hQa :
          ((((i _*).obj 𝒪Z).over (q.X a))).IsQuasicoherent := by
        infer_instance
      let _ :
          ((((i _*).obj ℱ).over (q.X a))).IsQuasicoherent :=
        pushforwardOver_isQuasicoherent_of_pushforwardUnitOver_isQuasicoherent
          i hi (q.X a) ℱ hQa
      -- Proof comment: once the restricted pushforward is quasi-coherent, choose any local data.
      exact Classical.choice
        (SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData
          (M := (((i _*).obj ℱ).over (q.X a))))
  let q' : ((i _*).obj ℱ).QuasicoherentData :=
    SheafOfModules.QuasicoherentData.bind ((i _*).obj ℱ) q.X q.coversTop D
  -- Proof comment: gluing the local quasi-coherent data along the cover of `i_* \mathcal O_Z`
  -- reduces the theorem to the single local pushforward step isolated above.
  exact q'.isQuasicoherent

/-- Helper for Lemma 17.13.2: on a neighborhood where the ideal sheaf of the closed immersion is
generated by explicit sections, the pushed-forward structure sheaf is locally the cokernel of the
corresponding relation map into `\mathcal O_X`. -/
private theorem pushforwardUnitOver_isQuasicoherent_of_localGenerators
    (i : Z ⟶ X) [RingedSpace.IsClosedImmersion i]
    (σ : (RingedSpace.closedImmersionIdealSheaf i).LocalGeneratorsData)
    (a : σ.I) :
    (((RingedSpace.Hom.pushforward i).obj 𝒪Z).over (σ.X a)).IsQuasicoherent := by
  let P := pushforwardUnitOverPresentation (X := X) i σ a
  -- Proof comment: once the explicit cokernel presentation is available on `σ.X a`, quasi-
  -- coherence follows immediately from the global-presentation criterion.
  exact P.isQuasicoherent

-- Proof sketch: a closed immersion is defined by local surjectivity of
-- `\mathcal O_X \to i_* \mathcal O_Z` with locally generated kernel ideal sheaf, so
-- `i_* \mathcal O_Z` is locally the cokernel of a map between locally free modules and hence is
-- quasi-coherent.
/-- Closed-immersion bridge: the source-facing owner `RingedSpace.IsClosedImmersion i` supplies
the quasi-coherence of the pushed-forward structure sheaf `i_* \mathcal O_Z`. -/
theorem ringedSpaceModulePushforward_unit_isQuasicoherent_of_isClosedImmersion
    (i : Z ⟶ X) [RingedSpace.IsClosedImmersion i] :
    ((RingedSpace.Hom.pushforward i).obj 𝒪Z).IsQuasicoherent := by
  classical
  let hi : RingedSpace.IsClosedImmersion i := inferInstance
  rcases hi.idealSheaf_locallyGenerated with ⟨σ⟩
  let D : ∀ a : σ.I, ((((i _*).obj 𝒪Z).over (σ.X a))).QuasicoherentData :=
    fun a ↦ by
      let _ :
          ((((i _*).obj 𝒪Z).over (σ.X a))).IsQuasicoherent :=
        pushforwardUnitOver_isQuasicoherent_of_localGenerators i σ a
      -- Proof comment: choose local quasi-coherent data from the local cokernel presentation.
      exact Classical.choice
        (SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData
          (M := (((i _*).obj 𝒪Z).over (σ.X a))))
  let q : ((i _*).obj 𝒪Z).QuasicoherentData :=
    SheafOfModules.QuasicoherentData.bind ((i _*).obj 𝒪Z) σ.X σ.coversTop D
  -- Proof comment: the local closed-immersion presentations glue along the ideal-sheaf cover.
  exact q.isQuasicoherent

/-- Lemma 17.13.2: if `i : (Z, \mathcal{O}_Z) \to (X, \mathcal{O}_X)` is a closed immersion, then
for any quasi-coherent `\mathcal{O}_Z`-module `\mathcal{F}`, the pushforward `i_* \mathcal{F}` is
quasi-coherent. -/
@[stacks 01C3]
theorem ringedSpaceModulePushforward_isQuasicoherent_of_isClosedImmersion
    (i : Z ⟶ X) [RingedSpace.IsClosedImmersion i]
    (ℱ : Z.Modules) [ℱ.IsQuasicoherent] :
    ((RingedSpace.Hom.pushforward i).obj ℱ).IsQuasicoherent := by
  let hi : RingedSpace.IsClosedImmersion i := inferInstance
  -- Route correction: this file no longer imports the later closed-immersion adjunction file.
  -- The remaining work is entirely in the two local quasi-coherence bridge lemmas above.
  exact
    ringedSpaceModulePushforward_isQuasicoherent_of_closedEmbedding_of_isLeftAdjoint_of_pushforwardUnit_isQuasicoherent
      i hi.isClosedEmbedding
      (ringedSpaceModulePushforward_unit_isQuasicoherent_of_isClosedImmersion i) ℱ

end AlgebraicGeometry
