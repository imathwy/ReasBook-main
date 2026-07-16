import Mathlib
import stacks_proof.stacks_project.Chap18.Definition_18_17_1
import stacks_proof.stacks_project.Chap18.Lemma_18_17_2
import stacks_proof.stacks_project.Chap18.Lemma_18_19_2
import stacks_proof.stacks_project.Chap18.RingedSiteModuleCategory

open CategoryTheory Limits

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]

/- 
Domain-style sampling for Definition 18.23.1:
- primary domain: local module-theoretic properties of sheaves of modules on a ringed site;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.LocalGeneratorsData`,
  `SheafOfModules.IsFiniteType`,
  `SheafOfModules.IsQuasicoherent`,
  `SheafOfModules.IsFinitePresentation`,
  `SheafOfModules.IsFree`,
  `SheafOfModules.IsFiniteFree`,
  `SheafOfModules.IsGeneratedBy`;
- best owner abstraction:
  the ambient owner category `ringedSiteModuleCategory J 𝒪`, together with the existing
  `SheafOfModules` owner predicates/data applied to each localized restriction `ℱ.over U`;
- primitive data:
  for clauses `(1)`, `(2)`, and `(4)`, a covering family in each over-site `J.over U` together
  with the corresponding global owner on each iterated restriction `((ℱ.over U).over V)`; for
  clauses `(3)`, `(5)`, `(6)`, and `(7)`, the corresponding canonical `SheafOfModules` owner on
  every restriction `ℱ.over U`; and, for coherence, the finite-type kernel condition on every
  localized site `(C/U, 𝒪_U)`;
- derived API:
  the source-facing ringed-site local properties, finite locally free implies locally free, local
  generation by `r` sections implies local generation by sections, finite type implies local
  generation by sections, and coherence implies finite type.

Source/core/bridge triage:
- `source-facing`: local freeness, finite local freeness, local generation by `r` sections, and
  local generation by sections, finite type, quasi-coherence, finite presentation, and coherence
  on a ringed site;
- `core/canonical`: `ringedSiteModuleCategory J 𝒪`,
  `SheafOfModules.LocalGeneratorsData`,
  `SheafOfModules.IsFiniteType`,
  `SheafOfModules.IsQuasicoherent`,
  `SheafOfModules.IsFinitePresentation`,
  `SheafOfModules.IsFree`,
  `SheafOfModules.IsFiniteFree`,
  `SheafOfModules.IsGeneratedBy`;
- `bridge/view`: restriction from `ℱ` to `ℱ.over U`, the source-facing existence condition
  from a ringed-site local property to the corresponding global owner on each `ℱ.over U`, and
  the implication from finite local freeness to local freeness.

The ringed-site local owners below therefore keep only the per-object locality quantifier that is
genuinely new in this file, while reusing the canonical ambient category of `𝒪`-module sheaves
directly rather than redeclaring a public alias for it, together with the owners `IsFree`,
`IsFiniteFree`, `IsGeneratedBy`, `LocalGeneratorsData`, `IsFiniteType`, `IsQuasicoherent`, and
`IsFinitePresentation` on the corresponding restrictions. For the four exact-interface lifts
`IsLocallyGeneratedBySections`, `IsFiniteType`, `IsQuasicoherent`, and `IsFinitePresentation`,
the public API uses those owner names directly; their reducible implementation via `Fact`
remains internal, no duplicate one-field wrapper class is introduced, and restriction to `ℱ.over U`
is exposed by instances rather than theorem-level unpacking aliases.
-/

section IteratedSlices

/-- Definition 18.23.1 (1): a sheaf of `\mathcal O`-modules on a ringed site is locally free if
for every object `U` there is a covering of `U` such that each further restriction
`\mathcal F|_{U_i}` is free over `\mathcal O_{U_i}`. -/
@[stacks 03DL]
class IsLocallyFree (ℱ : ringedSiteModuleCategory J 𝒪) : Prop where
  /-- Every object admits a covering on which the restriction of `ℱ` is free. -/
  isFree_over (U : C) :
      ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
        ∀ i : I, ((ℱ.over U).over (X i)).IsFree

/-- Definition 18.23.1 (2): a sheaf of `\mathcal O`-modules on a ringed site is finite locally
free if for every object `U` there is a covering of `U` such that each further restriction
`\mathcal F|_{U_i}` is finite free over `\mathcal O_{U_i}`. -/
@[stacks 03DL]
class IsFiniteLocallyFree (ℱ : ringedSiteModuleCategory J 𝒪) : Prop where
  /-- Every object admits a covering on which the restriction of `ℱ` is finite free. -/
  isFiniteFree_over (U : C) :
      ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
        ∀ i : I, ((ℱ.over U).over (X i)).IsFiniteFree

/-- Finite locally free sheaves are locally free. -/
instance isFiniteLocallyFree_to_isLocallyFree (ℱ : ringedSiteModuleCategory J 𝒪)
    [IsFiniteLocallyFree ℱ] :
    IsLocallyFree ℱ := by
  refine ⟨fun U ↦ ?_⟩
  -- Reuse the same local cover and forget the finiteness in each local free witness.
  obtain ⟨I, X, hX, hfree⟩ := IsFiniteLocallyFree.isFiniteFree_over (ℱ := ℱ) U
  exact ⟨I, X, hX, fun i ↦ inferInstanceAs (((ℱ.over U).over (X i)).IsFree)⟩

/-- Definition 18.23.1 (4): a sheaf of `\mathcal O`-modules on a ringed site is locally
generated by `r` sections if for every object `U` there is a covering of `U` such that on each
member the further restriction is generated by `r` global sections. -/
@[stacks 03DL]
class IsLocallyGeneratedBy (ℱ : ringedSiteModuleCategory J 𝒪) (r : ℕ) : Prop where
  /-- Every object admits a covering on which the restriction of `ℱ` is generated by `r`
  sections. -/
  isGeneratedBy_over (U : C) :
    ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
      ∀ i : I, ((ℱ.over U).over (X i)).IsGeneratedBy r

/-- Definition 18.23.1 (6): a sheaf of `\mathcal O`-modules on a ringed site is quasi-coherent
if, for every object `U`, the restricted sheaf `\mathcal F|_U` is quasi-coherent on the
localized ringed site `(C/U, \mathcal O_U)`. -/
@[stacks 03DL]
abbrev IsQuasicoherent (ℱ : ringedSiteModuleCategory J 𝒪) : Prop :=
  Fact (∀ U : C, (ℱ.over U).IsQuasicoherent)

/-- Every localized restriction of a quasi-coherent sheaf on a ringed site is quasi-coherent. -/
instance (ℱ : ringedSiteModuleCategory J 𝒪)
    [h : IsQuasicoherent ℱ] (U : C) :
    (ℱ.over U).IsQuasicoherent :=
  h.1 U

/-- Definition 18.23.1 (7): a sheaf of `\mathcal O`-modules on a ringed site is of finite
presentation if, for every object `U`, the restricted sheaf `\mathcal F|_U` is of finite
presentation on the localized ringed site `(C/U, \mathcal O_U)`. -/
@[stacks 03DL]
abbrev IsFinitePresentation (ℱ : ringedSiteModuleCategory J 𝒪) : Prop :=
  Fact (∀ U : C, (ℱ.over U).IsFinitePresentation)

/-- Every localized restriction of a finitely presented sheaf on a ringed site is finitely
presented. -/
instance (ℱ : ringedSiteModuleCategory J 𝒪)
    [h : IsFinitePresentation ℱ] (U : C) :
    (ℱ.over U).IsFinitePresentation :=
  h.1 U

variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [∀ U : C, ∀ X : Over U, HasWeakSheafify ((J.over U).over X) AddCommGrpCat]
variable [∀ U : C, ∀ X : Over U, ((J.over U).over X).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, ∀ X : Over U, ((J.over U).over X).HasSheafCompose
  (forget₂ RingCat AddCommGrpCat)]
variable [∀ U : C, ∀ X : Over U, ((J.over U).over X).HasSheafCompose
  (forget₂ CommRingCat RingCat)]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [∀ U : C, ∀ X : Over U, HasWeakSheafify ((J.over U).over X) AddCommGrpCat]
  [∀ U : C, ∀ X : Over U, ((J.over U).over X).WEqualsLocallyBijective AddCommGrpCat]
  [∀ U : C, ∀ X : Over U, ((J.over U).over X).HasSheafCompose
    (forget₂ RingCat AddCommGrpCat)]
  [∀ U : C, ∀ X : Over U, ((J.over U).over X).HasSheafCompose
    (forget₂ CommRingCat RingCat)] in
/-- Helper for Definition 18.23.1: the singleton family given by the identity of `U` covers the
top object in the slice site `(C / U, J.over U)`. -/
private theorem identity_singleton_coversTop_over (U : C) :
    (J.over U).CoversTop (fun _ : PUnit => Over.mk (𝟙 U)) := by
  -- The terminal object `Over.mk (𝟙 U)` is already one member of this singleton family.
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal (J := J.over U) (X := Over.mk (𝟙 U))
    (hX := Over.mkIdTerminal)]
  rw [GrothendieckTopology.mem_over_iff]
  have htop :
      (Sieve.overEquiv (Over.mk (𝟙 U)))
        (Sieve.ofObjects (fun _ : PUnit => Over.mk (𝟙 U)) (Over.mk (𝟙 U))) = ⊤ := by
    ext Z g
    constructor
    · intro _
      trivial
    · intro _
      rw [Sieve.overEquiv_iff]
      exact ⟨PUnit.unit, ⟨Over.homMk g⟩⟩
  rw [htop]
  exact J.top_mem U

section IteratedRestrictionModels

private abbrev iteratedSliceTerminal (U : C) : Over U := Over.mk (𝟙 U)

private abbrev iteratedLocalizedRingSheaf (U : C) :
    Sheaf ((J.over U).over (iteratedSliceTerminal U)) RingCat :=
  ringSheaf ((J.over U).over (iteratedSliceTerminal U))
    ((𝒪.over U).over (iteratedSliceTerminal U))

private abbrev iteratedLocalizedModuleCategory (U : C) :=
  ringedSiteModuleCategory ((J.over U).over (iteratedSliceTerminal U))
    ((𝒪.over U).over (iteratedSliceTerminal U))

private noncomputable abbrev iteratedRestriction
    (ℱ : ringedSiteModuleCategory J 𝒪) (U : C) :
    iteratedLocalizedModuleCategory (J := J) (𝒪 := 𝒪) U :=
  (ℱ.over U).over (iteratedSliceTerminal U)

private noncomputable abbrev iteratedRestrictionFree
    (I : Type (max u v)) (U : C) :
    iteratedLocalizedModuleCategory (J := J) (𝒪 := 𝒪) U :=
  iteratedRestriction (_root_.SheafOfModules.free (R := ringSheaf J 𝒪) I) U

variable [HasBinaryProducts C] [HasPullbacks C]

attribute [local instance] CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback

private local instance localizedPushforwardOver_isRightAdjoint (U : C) :
    (SheafOfModules.pushforward
      (SheafOfModules.pushforwardOver (R := ringSheaf J 𝒪) U)).IsRightAdjoint :=
  (SheafOfModules.overPushforwardOverAdj (R := ringSheaf J 𝒪) U).isRightAdjoint

private local instance iteratedLocalizedPushforwardOver_isRightAdjoint (U : C) :
    (SheafOfModules.pushforward
      (SheafOfModules.pushforwardOver
        (R := ringSheaf (J.over U) (𝒪.over U)) (iteratedSliceTerminal U))).IsRightAdjoint :=
  (SheafOfModules.overPushforwardOverAdj
    (R := ringSheaf (J.over U) (𝒪.over U)) (iteratedSliceTerminal U)).isRightAdjoint

private noncomputable def localizedRestrictionPullbackIso (U : C) :
    SheafOfModules.pullback (SheafOfModules.pushforwardOver (R := ringSheaf J 𝒪) U) ≅
      ringedSiteLocalizedRestriction (J := J) (𝒪 := 𝒪) U :=
  Adjunction.leftAdjointUniq
    (SheafOfModules.pullbackPushforwardAdjunction
      (SheafOfModules.pushforwardOver (R := ringSheaf J 𝒪) U))
    (SheafOfModules.overPushforwardOverAdj (R := ringSheaf J 𝒪) U)

private noncomputable def iteratedLocalizedRestrictionPullbackIso (U : C) :
    SheafOfModules.pullback
        (SheafOfModules.pushforwardOver
          (R := ringSheaf (J.over U) (𝒪.over U)) (iteratedSliceTerminal U)) ≅
      ringedSiteLocalizedRestriction
        (J := J.over U) (𝒪 := 𝒪.over U) (iteratedSliceTerminal U) :=
  Adjunction.leftAdjointUniq
    (SheafOfModules.pullbackPushforwardAdjunction
      (SheafOfModules.pushforwardOver
        (R := ringSheaf (J.over U) (𝒪.over U)) (iteratedSliceTerminal U)))
    (SheafOfModules.overPushforwardOverAdj
      (R := ringSheaf (J.over U) (𝒪.over U)) (iteratedSliceTerminal U))

private theorem iteratedRestrictionFree_nonempty_iso_free
    (I : Type (max u v)) (U : C) :
    Nonempty
      (iteratedRestrictionFree (J := J) (𝒪 := 𝒪) I U ≅
        (_root_.SheafOfModules.free
          (R := iteratedLocalizedRingSheaf (J := J) (𝒪 := 𝒪) U) I :
          iteratedLocalizedModuleCategory (J := J) (𝒪 := 𝒪) U)) := by
  let restrictionApp₁ :
      (ringedSiteLocalizedRestriction (J := J) (𝒪 := 𝒪) U).obj
          (_root_.SheafOfModules.free (R := ringSheaf J 𝒪) I) ≅
        (SheafOfModules.pullback
          (SheafOfModules.pushforwardOver (R := ringSheaf J 𝒪) U)).obj
          (_root_.SheafOfModules.free (R := ringSheaf J 𝒪) I) :=
    ((localizedRestrictionPullbackIso (J := J) (𝒪 := 𝒪) U).app
      (_root_.SheafOfModules.free (R := ringSheaf J 𝒪) I :
        ringedSiteModuleCategory J 𝒪)).symm
  let e₁' :
      (ringedSiteLocalizedRestriction (J := J) (𝒪 := 𝒪) U).obj
          (_root_.SheafOfModules.free (R := ringSheaf J 𝒪) I) ≅
        (_root_.SheafOfModules.free
          (R := ringSheaf (J.over U) (𝒪.over U)) I :
          ringedSiteModuleCategory (J.over U) (𝒪.over U)) :=
    restrictionApp₁ ≪≫ SheafOfModules.pullbackObjFreeIso
      (SheafOfModules.pushforwardOver (R := ringSheaf J 𝒪) U) I
  let e₁ :
      (((_root_.SheafOfModules.free (R := ringSheaf J 𝒪) I :
            ringedSiteModuleCategory J 𝒪).over U) :
          ringedSiteModuleCategory (J.over U) (𝒪.over U)) ≅
        (_root_.SheafOfModules.free
          (R := ringSheaf (J.over U) (𝒪.over U)) I :
          ringedSiteModuleCategory (J.over U) (𝒪.over U)) := by
    simpa [ringedSiteLocalizedRestriction, SheafOfModules.over] using e₁'
  let restrictionApp₂ :
      (ringedSiteLocalizedRestriction
          (J := J.over U) (𝒪 := 𝒪.over U) (iteratedSliceTerminal U)).obj
          (_root_.SheafOfModules.free
            (R := ringSheaf (J.over U) (𝒪.over U)) I) ≅
        (SheafOfModules.pullback
          (SheafOfModules.pushforwardOver
            (R := ringSheaf (J.over U) (𝒪.over U)) (iteratedSliceTerminal U))).obj
          (_root_.SheafOfModules.free
            (R := ringSheaf (J.over U) (𝒪.over U)) I) :=
    ((iteratedLocalizedRestrictionPullbackIso (J := J) (𝒪 := 𝒪) U).app
      (_root_.SheafOfModules.free
        (R := ringSheaf (J.over U) (𝒪.over U)) I :
        ringedSiteModuleCategory (J.over U) (𝒪.over U))).symm
  let e₂' :
      (ringedSiteLocalizedRestriction
          (J := J.over U) (𝒪 := 𝒪.over U) (iteratedSliceTerminal U)).obj
          (_root_.SheafOfModules.free
            (R := ringSheaf (J.over U) (𝒪.over U)) I) ≅
        (_root_.SheafOfModules.free
          (R := iteratedLocalizedRingSheaf (J := J) (𝒪 := 𝒪) U) I :
          iteratedLocalizedModuleCategory (J := J) (𝒪 := 𝒪) U) :=
    restrictionApp₂ ≪≫ SheafOfModules.pullbackObjFreeIso
      (SheafOfModules.pushforwardOver
        (R := ringSheaf (J.over U) (𝒪.over U)) (iteratedSliceTerminal U)) I
  let e₂ :
      (((_root_.SheafOfModules.free
            (R := ringSheaf (J.over U) (𝒪.over U)) I :
            ringedSiteModuleCategory (J.over U) (𝒪.over U)).over
            (iteratedSliceTerminal U)) :
          iteratedLocalizedModuleCategory (J := J) (𝒪 := 𝒪) U) ≅
        (_root_.SheafOfModules.free
          (R := iteratedLocalizedRingSheaf (J := J) (𝒪 := 𝒪) U) I :
          iteratedLocalizedModuleCategory (J := J) (𝒪 := 𝒪) U) := by
    simpa [ringedSiteLocalizedRestriction, SheafOfModules.over] using e₂'
  exact ⟨(ringedSiteLocalizedRestriction
      (J := J.over U) (𝒪 := 𝒪.over U) (iteratedSliceTerminal U)).mapIso e₁ ≪≫ e₂⟩

/-- Helper for Definition 18.23.1: restricting a free sheaf twice along identity slice maps
keeps it free. -/
private theorem iteratedRestrictionFree_isFree
    (I : Type (max u v)) (U : C) :
    SheafOfModules.IsFree (iteratedRestrictionFree (J := J) (𝒪 := 𝒪) I U) := by
  obtain ⟨e⟩ := iteratedRestrictionFree_nonempty_iso_free (J := J) (𝒪 := 𝒪) I U
  exact ⟨I, ⟨e⟩⟩

/-- Helper for Definition 18.23.1: restricting a finite free sheaf twice along identity slice
maps keeps it finite free. -/
private theorem iteratedRestrictionFree_isFiniteFree
    (I : Type (max u v)) [Finite I] (U : C) :
    SheafOfModules.IsFiniteFree (iteratedRestrictionFree (J := J) (𝒪 := 𝒪) I U) := by
  obtain ⟨e⟩ := iteratedRestrictionFree_nonempty_iso_free (J := J) (𝒪 := 𝒪) I U
  exact ⟨I, inferInstance, ⟨e⟩⟩

/-- Helper for Definition 18.23.1: restricting the free rank-`r` sheaf twice along identity slice
maps keeps the same `r`-generator presentation. -/
private theorem iteratedRestrictionFree_fin_isGeneratedBy
    (r : ℕ) (U : C) :
    SheafOfModules.IsGeneratedBy
      (iteratedRestrictionFree (J := J) (𝒪 := 𝒪) (ULift.{max u v} (Fin r)) U) r := by
  obtain ⟨e⟩ := iteratedRestrictionFree_nonempty_iso_free
    (J := J) (𝒪 := 𝒪) (ULift.{max u v} (Fin r)) U
  exact ⟨e.inv, inferInstance⟩

/-- A free sheaf on a ringed site is locally free. -/
instance free_isLocallyFree (α : Type (max u v)) :
    IsLocallyFree
      (_root_.SheafOfModules.free (R := ringSheaf J 𝒪) α : ringedSiteModuleCategory J 𝒪) := by
  refine ⟨fun U ↦ ?_⟩
  -- The identity slice already covers `U`, and the corresponding iterated restriction stays free.
  exact ⟨PUnit, fun _ ↦ iteratedSliceTerminal U, identity_singleton_coversTop_over (J := J) U,
    fun _ ↦ iteratedRestrictionFree_isFree (J := J) (𝒪 := 𝒪) α U⟩

/-- A finite free sheaf on a ringed site is finite locally free. -/
instance free_isFiniteLocallyFree (α : Type (max u v)) [Finite α] :
    IsFiniteLocallyFree
      (_root_.SheafOfModules.free (R := ringSheaf J 𝒪) α : ringedSiteModuleCategory J 𝒪) := by
  refine ⟨fun U ↦ ?_⟩
  -- The identity slice already covers `U`, and the corresponding iterated restriction stays
  -- finite free.
  exact ⟨PUnit, fun _ ↦ iteratedSliceTerminal U, identity_singleton_coversTop_over (J := J) U,
    fun _ ↦ iteratedRestrictionFree_isFiniteFree (J := J) (𝒪 := 𝒪) α U⟩

/-- The free rank-`r` sheaf on a ringed site is locally generated by `r` sections. -/
instance free_fin_isLocallyGeneratedBy (r : ℕ) :
    IsLocallyGeneratedBy
      (_root_.SheafOfModules.free
        (R := ringSheaf J 𝒪) (ULift.{max u v} (Fin r)) : ringedSiteModuleCategory J 𝒪) r :=
  by
    refine ⟨fun U ↦ ?_⟩
    -- The identity slice already covers `U`, and the corresponding iterated restriction retains
    -- the same rank-`r` generating family.
    exact ⟨PUnit, fun _ ↦ iteratedSliceTerminal U, identity_singleton_coversTop_over (J := J) U,
      fun _ ↦ iteratedRestrictionFree_fin_isGeneratedBy (J := J) (𝒪 := 𝒪) r U⟩

end IteratedRestrictionModels

end IteratedSlices

section OverAndIteratedSlices

variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [∀ U : C, ∀ X : Over U, HasWeakSheafify ((J.over U).over X) AddCommGrpCat]
variable [∀ U : C, ∀ X : Over U, ((J.over U).over X).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, ∀ X : Over U, ((J.over U).over X).HasSheafCompose
  (forget₂ RingCat AddCommGrpCat)]

/-- Definition 18.23.1 (3): a sheaf of `\mathcal O`-modules on a ringed site is locally
generated by sections if, for every object `U`, the restricted sheaf `\mathcal F|_U` admits
local generators on `(C/U, \mathcal O_U)`. -/
@[stacks 03DL]
abbrev IsLocallyGeneratedBySections (ℱ : ringedSiteModuleCategory J 𝒪) : Prop :=
  Fact (∀ U : C, Nonempty (ℱ.over U).LocalGeneratorsData)

omit [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat)] in
/-- Every localized restriction of a sheaf locally generated by sections admits local generators
data. -/
instance (ℱ : ringedSiteModuleCategory J 𝒪)
    [h : IsLocallyGeneratedBySections ℱ] (U : C) :
    Nonempty (ℱ.over U).LocalGeneratorsData :=
  h.1 U

omit [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat)] in
/-- Helper for Definition 18.23.1: a covering whose local restrictions are generated by `r`
sections packages into `LocalGeneratorsData` on the slice over `U`. -/
private theorem localGeneratorsData_of_cover_isGeneratedBy
    {ℱ : ringedSiteModuleCategory J 𝒪} {U : C} {r : ℕ}
    {I : Type (max u v)} {X : I → Over U}
    (hX : (J.over U).CoversTop X)
    (hgen : ∀ i : I, ((ℱ.over U).over (X i)).IsGeneratedBy r) :
    Nonempty (ℱ.over U).LocalGeneratorsData := by
  classical
  -- Choose explicit generating sections on each cover member and package them into local data.
  refine ⟨{ I := I, X := X, coversTop := hX, generators := ?_ }⟩
  intro i
  exact Classical.choice
    (_root_.SheafOfModules.generatingSections_of_isGeneratedBy
      (ℱ := ((ℱ.over U).over (X i))) r (hgen i))

omit [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat)] in
/-- Being locally generated by `r` sections implies being locally generated by sections. -/
theorem isLocallyGeneratedBySections_of_isLocallyGeneratedBy
    (ℱ : ringedSiteModuleCategory J 𝒪) (r : ℕ) [IsLocallyGeneratedBy ℱ r] :
    IsLocallyGeneratedBySections ℱ := by
  refine ⟨fun U ↦ ?_⟩
  -- Unpack the local `r`-generator cover and repackage it as `LocalGeneratorsData`.
  obtain ⟨I, X, hX, hgen⟩ := IsLocallyGeneratedBy.isGeneratedBy_over (ℱ := ℱ) (r := r) U
  exact localGeneratorsData_of_cover_isGeneratedBy (ℱ := ℱ) (U := U) (r := r) hX hgen

/-- Definition 18.23.1 (5): a sheaf of `\mathcal O`-modules on a ringed site is of finite type
if, for every object `U`, the restricted sheaf `\mathcal F|_U` is of finite type on the
localized ringed site `(C/U, \mathcal O_U)`. -/
@[stacks 03DL]
abbrev IsFiniteType (ℱ : ringedSiteModuleCategory J 𝒪) : Prop :=
  Fact (∀ U : C, (ℱ.over U).IsFiniteType)

omit [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat)] in
/-- Every localized restriction of a finite-type sheaf on a ringed site is of finite type. -/
instance (ℱ : ringedSiteModuleCategory J 𝒪)
    [h : IsFiniteType ℱ] (U : C) :
    (ℱ.over U).IsFiniteType :=
  h.1 U

/-- A sheaf of finite type on a ringed site is locally generated by sections. -/
instance isLocallyGeneratedBySections_of_isFiniteType
    (ℱ : ringedSiteModuleCategory J 𝒪) [IsFiniteType ℱ] :
    IsLocallyGeneratedBySections ℱ := by
  refine ⟨fun U ↦ ?_⟩
  -- Each slice already has local generator data from the finite-type owner in Chapter 17.
  obtain ⟨σ, _⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData (ℱ.over U)
  exact ⟨σ⟩

/-- Definition 18.23.1 (8): a sheaf of `\mathcal O`-modules on a ringed site is coherent if it
is of finite type and, for every object `U` and every morphism from a finite free
`\mathcal O_U`-module to `\mathcal F|_U`, the kernel is of finite type on `(C/U, \mathcal O_U)`. -/
@[stacks 03DL]
class IsCoherent (ℱ : ringedSiteModuleCategory J 𝒪) : Prop where
  /-- A coherent sheaf on a ringed site is of finite type. -/
  toIsFiniteType : IsFiniteType ℱ
  /-- Kernels of maps from finite free modules into local restrictions are of finite type. -/
  isFiniteType_kernel (U : C)
      (r : ℕ)
      (φ :
        (_root_.SheafOfModules.free
          (R := ringSheaf (J.over U) (𝒪.over U)) (ULift.{max u v} (Fin r)) :
          ringedSiteModuleCategory (J.over U) (𝒪.over U)) ⟶
          ℱ.over U) :
      (kernel φ).IsFiniteType

/-- A coherent sheaf on a ringed site is of finite type. -/
instance isFiniteType_of_isCoherent (ℱ : ringedSiteModuleCategory J 𝒪) [h : IsCoherent ℱ] :
    IsFiniteType ℱ :=
  h.toIsFiniteType

end OverAndIteratedSlices

end SheafOfModules.RingedSite
