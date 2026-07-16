import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import stacks_proof.stacks_project.Chap07.Definition_7_42_3
import stacks_proof.stacks_project.Chap07.Lemma_7_44_2
import stacks_proof.stacks_project.Chap12.Lemma_12_7_2
import stacks_proof.stacks_project.Chap18.Lemma_18_3_1
import stacks_proof.stacks_project.Chap18.Lemma_18_14_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/- Domain-style sampling for Lemma 18.15.3:
- primary domain: exactness of direct-image functors on sheaves of abelian groups and on sheaves
  of modules over a ringed morphism of sites;
- sampled owner declarations:
  `Functor.sheafPushforwardContinuous`,
  `exactFunctor`,
  `sheafPushforwardContinuous_exact_of_preservesEpimorphisms_or_underlyingPreservesEpimorphisms_or_coequalizers_or_pushouts`,
  `SheafOfModules.pushforward`;
- best owner abstraction:
  the abelian-sheaf exactness owner
  `exactFunctor _ _ (u.sheafPushforwardContinuous AddCommGrpCat JC JD)`;
- primitive-vs-derived split:
  the primitive data are the continuous functor `u`, the almost-cocontinuity hypothesis, the
  two ring sheaves, and the structure-sheaf morphism `φ`;
  the exactness statements below are owner-level consequences, while the module statement is a
  bridge through `SheafOfModules.toSheaf`.

Source/core/bridge triage:
- `source-facing`: the Stacks exactness statements for `f_*` on abelian sheaves and on module
  sheaves under almost cocontinuity;
- `core/canonical`: the exactness owner
  `exactFunctor _ _ (u.sheafPushforwardContinuous AddCommGrpCat JC JD)`;
- `bridge/view`: the module pushforward exactness statement obtained by forgetting to abelian
  sheaves.
-/

section Exactness

variable [HasWeakSheafify JC AddCommGrpCat.{max u v}]
variable [HasSheafify JC AddCommGrpCat.{max u v}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasWeakSheafify JD AddCommGrpCat.{max u v}]
variable [HasSheafify JD AddCommGrpCat.{max u v}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

local notation "Mod(" 𝒪 ")" => SheafOfModules.{max u v} 𝒪

omit [HasWeakSheafify JC AddCommGrpCat.{max u v}] [HasSheafify JC AddCommGrpCat.{max u v}]
  [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- Helper for Lemma 18.15.3: local surjectivity of an abelian-sheaf morphism survives after
forgetting the additive structure. -/
private theorem underlying_locally_surjective_of_additive_sheaf_map
    {F G : Sheaf JC AddCommGrpCat.{max u v}} (π : F ⟶ G)
    (hπ : Sheaf.IsLocallySurjective π) :
    Sheaf.IsLocallySurjective ((sheafCompose JC (forget AddCommGrpCat.{max u v})).map π) := by
  -- Proof comment: forgetting additive structure does not change the underlying image sieve.
  change Presheaf.IsLocallySurjective JC
    (Functor.whiskerRight π.hom (forget AddCommGrpCat.{max u v}))
  change Presheaf.IsLocallySurjective JC π.hom at hπ
  refine Presheaf.IsLocallySurjective.mk ?_
  intro V s
  simpa [Presheaf.imageSieve] using hπ.imageSieve_mem (U := V) s

omit [HasWeakSheafify JC AddCommGrpCat.{max u v}] in
/-- Helper for Lemma 18.15.3: a morphism of sheaves of abelian groups is epic exactly when the
underlying morphism of set-valued sheaves is epic. -/
private theorem sheafAddCommGrp_epi_iff_forget_epi
    {X Y : Sheaf JC AddCommGrpCat.{max u v}} (φ : X ⟶ Y) :
    Epi φ ↔ Epi ((sheafCompose JC (forget AddCommGrpCat.{max u v})).map φ) := by
  constructor
  · intro hφ
    -- Proof comment: convert the additive epi to local surjectivity, then forget it to sets.
    let hloc : Sheaf.IsLocallySurjective φ :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max u v} φ).2 hφ
    exact (Sheaf.isLocallySurjective_iff_epi _).1
      (underlying_locally_surjective_of_additive_sheaf_map (JC := JC) φ hloc)
  · intro hφ
    -- Proof comment: faithful forgetting reflects right-cancellability back to abelian sheaves.
    refine ⟨?_⟩
    intro Z g h hgh
    apply (sheafCompose JC (forget AddCommGrpCat.{max u v})).map_injective
    apply (cancel_epi ((sheafCompose JC (forget AddCommGrpCat.{max u v})).map φ)).1
    simpa using congrArg ((sheafCompose JC (forget AddCommGrpCat.{max u v})).map) hgh

/-- Helper for Lemma 18.15.3: if the underlying set-valued direct image preserves epimorphisms,
then the additive direct image does as well. -/
private theorem sheafPushforwardContinuous_preservesEpimorphisms_of_underlyingPreservesEpimorphisms
    (u : C ⥤ D) [u.IsContinuous JC JD]
    (hpush :
      (u.sheafPushforwardContinuous (Type (max u v)) JC JD).PreservesEpimorphisms) :
    (u.sheafPushforwardContinuous AddCommGrpCat.{max u v} JC JD).PreservesEpimorphisms := by
  constructor
  intro X Y φ hφ
  let Fadd := u.sheafPushforwardContinuous AddCommGrpCat.{max u v} JC JD
  let Ftype := u.sheafPushforwardContinuous (Type (max u v)) JC JD
  letI : Ftype.PreservesEpimorphisms := hpush
  -- Proof comment: first forget the source epimorphism to sheaves of sets on `JD`.
  have hφForget : Epi ((sheafCompose JD (forget AddCommGrpCat.{max u v})).map φ) :=
    (sheafAddCommGrp_epi_iff_forget_epi (JC := JD) (φ := φ)).1 hφ
  -- Proof comment: the set-valued pushforward preserves that epi by hypothesis.
  have hmapForget :
      Epi
        (Ftype.map ((sheafCompose JD (forget AddCommGrpCat.{max u v})).map φ)) := by
    infer_instance
  -- Proof comment: `sheaf_pushforward_forget` identifies the forgotten pushed-forward map.
  have hmapUnderlying :
      Epi ((sheafCompose JC (forget AddCommGrpCat.{max u v})).map (Fadd.map φ)) := by
    simpa [Fadd, Ftype, sheaf_pushforward_forget] using hmapForget
  -- Proof comment: reflect the target epi back to abelian sheaves on `JC`.
  exact (sheafAddCommGrp_epi_iff_forget_epi (JC := JC) (φ := Fadd.map φ)).2 hmapUnderlying

omit [HasWeakSheafify JC AddCommGrpCat.{max u v}] [HasSheafify JC AddCommGrpCat.{max u v}]
  [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify JD AddCommGrpCat.{max u v}] [HasSheafify JD AddCommGrpCat.{max u v}]
  [JD.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- Helper for Lemma 18.15.3: a set-valued functor that preserves coequalizers preserves
epimorphisms. -/
private theorem sheafType_preservesEpimorphisms_of_preservesCoequalizers
    {F : Sheaf JD (Type (max u v)) ⥤ Sheaf JC (Type (max u v))}
    [PreservesColimitsOfShape WalkingParallelPair F] :
    F.PreservesEpimorphisms := by
  constructor
  intro X Y φ hφ
  letI : Epi φ := hφ
  letI : IsRegularEpi φ := isRegularEpi_of_regularEpi <| regularEpiOfEpi φ
  -- Proof comment: map the canonical regular-epi cofork through `F`.
  have hcofork :
      IsColimit
        (Cofork.ofπ (F.map φ)
          (by
            simpa only [Functor.map_comp] using congrArg (fun k ↦ F.map k) (IsRegularEpi.w φ))) := by
    exact
      isColimitCoforkMapOfIsColimit F (IsRegularEpi.w φ) (IsRegularEpi.isColimit φ)
  -- Proof comment: the cocone map of a colimiting cofork is epic.
  exact Cofork.IsColimit.epi hcofork

omit [HasWeakSheafify JC AddCommGrpCat.{max u v}] [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [JD.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- Helper for Lemma 18.15.3: if the additive direct image preserves epimorphisms, then it is
exact. -/
private theorem sheafPushforwardContinuous_exact_of_preservesEpimorphisms
    (u : C ⥤ D) [u.IsContinuous JC JD]
    (hpush :
      (u.sheafPushforwardContinuous AddCommGrpCat.{max u v} JC JD).PreservesEpimorphisms) :
    exactFunctor (Sheaf JD AddCommGrpCat.{max u v})
      (Sheaf JC AddCommGrpCat.{max u v})
      (u.sheafPushforwardContinuous AddCommGrpCat.{max u v} JC JD) := by
  let F := u.sheafPushforwardContinuous AddCommGrpCat.{max u v} JC JD
  -- Proof comment: the sheaf pushforward is a right adjoint, so it preserves finite limits.
  let _ : F.IsRightAdjoint :=
    (u.sheafAdjunctionContinuous AddCommGrpCat.{max u v} JC JD).isRightAdjoint
  let _ : PreservesFiniteLimits F := inferInstance
  let _ : Abelian (Sheaf JD AddCommGrpCat.{max u v}) := by infer_instance
  let _ : Abelian (Sheaf JC AddCommGrpCat.{max u v}) := by infer_instance
  have hLeft : leftExactFunctor _ _ F := by
    simpa [leftExactFunctor_iff] using (inferInstance : PreservesFiniteLimits F)
  let _ : F.Additive :=
    CategoryTheory.functor_additive_of_leftExact_or_rightExact (F := F) (.inl hLeft)
  let _ : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  let _ : F.PreservesEpimorphisms := hpush
  -- Proof comment: in an abelian target, preserving epis and kernels upgrades to finite colimits.
  let _ : F.PreservesHomology :=
    CategoryTheory.Functor.preservesHomology_of_preservesEpis_and_kernels F
  let _ : PreservesFiniteColimits F :=
    CategoryTheory.Functor.preservesFiniteColimits_of_preservesHomology F
  exact (exactFunctor_iff F).2 ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 18.15.3: forgetting module pushforward to additive sheaves is definitionally
the same as first forgetting and then applying additive-sheaf pushforward. -/
private theorem sheafOfModules_pushforward_comp_toSheaf
    (u : C ⥤ D) [u.IsContinuous JC JD]
    (𝒪C : Sheaf JC RingCat.{max u v}) (𝒪D : Sheaf JD RingCat.{max u v})
    (φ : 𝒪C ⟶ (u.sheafPushforwardContinuous RingCat.{max u v} JC JD).obj 𝒪D) :
    SheafOfModules.pushforward φ ⋙ SheafOfModules.toSheaf 𝒪C =
      SheafOfModules.toSheaf 𝒪D ⋙
        u.sheafPushforwardContinuous AddCommGrpCat.{max u v} JC JD := by
  rfl

/-- Helper for Lemma 18.15.3: `toSheaf` reflects epimorphisms of module sheaves because it is
faithful. -/
private theorem epi_of_toSheaf_map_epi
    (𝒪 : Sheaf JC RingCat.{max u v})
    {M N : Mod(𝒪)} (g : M ⟶ N)
    [Epi ((SheafOfModules.toSheaf 𝒪).map g)] :
    Epi g := by
  -- Proof comment: faithfulness of `toSheaf` reflects right-cancellability back to module
  -- sheaves.
  refine ⟨?_⟩
  intro Z h k hg
  apply (SheafOfModules.toSheaf 𝒪).map_injective
  apply (cancel_epi ((SheafOfModules.toSheaf 𝒪).map g)).1
  simpa using congrArg ((SheafOfModules.toSheaf 𝒪).map) hg

/-- Helper for Lemma 18.15.3: if the additive direct image preserves epimorphisms, then the
module direct image preserves epimorphisms as well. -/
private theorem sheafOfModules_pushforward_preservesEpimorphisms_of_underlyingPreservesEpimorphisms
    (u : C ⥤ D) [u.IsContinuous JC JD]
    (𝒪C : Sheaf JC RingCat.{max u v}) (𝒪D : Sheaf JD RingCat.{max u v})
    (φ : 𝒪C ⟶ (u.sheafPushforwardContinuous RingCat.{max u v} JC JD).obj 𝒪D)
    [Functor.PreservesEpimorphisms
      (u.sheafPushforwardContinuous AddCommGrpCat.{max u v} JC JD)] :
    Functor.PreservesEpimorphisms (SheafOfModules.pushforward φ) := by
  let F : Mod(𝒪D) ⥤ Mod(𝒪C) := SheafOfModules.pushforward φ
  let TSource : Mod(𝒪D) ⥤ Sheaf JD AddCommGrpCat.{max u v} :=
    SheafOfModules.toSheaf 𝒪D
  let TTarget : Mod(𝒪C) ⥤ Sheaf JC AddCommGrpCat.{max u v} :=
    SheafOfModules.toSheaf 𝒪C
  let Fadd :
      Sheaf JD AddCommGrpCat.{max u v} ⥤
        Sheaf JC AddCommGrpCat.{max u v} :=
    u.sheafPushforwardContinuous AddCommGrpCat.{max u v} JC JD
  -- Proof comment: the source forgetful functor is exact, hence preserves finite colimits and
  -- therefore epimorphisms.
  let _ : PreservesFiniteColimits TSource :=
    ((exactFunctor_iff TSource).1 (ExactFunctor.of TSource).property).2
  constructor
  intro M N g hg
  -- Proof comment: forget the source module structure, preserve the epi additively, and rewrite
  -- the result through the pushforward comparison.
  have hmapUnderlying : Epi (Fadd.map (TSource.map g)) := by
    letI : Epi g := hg
    infer_instance
  have hmap :
      Epi (TTarget.map (F.map g)) := by
    simpa [Functor.comp_map, F, TSource, TTarget, Fadd, sheafOfModules_pushforward_comp_toSheaf]
      using
      hmapUnderlying
  -- Proof comment: once the forgotten target map is epic, faithfulness of `toSheaf` reflects the
  -- epi back to module sheaves.
  letI : Epi (TTarget.map (F.map g)) := hmap
  exact epi_of_toSheaf_map_epi (𝒪 := 𝒪C) (g := F.map g)

/-- Helper for Lemma 18.15.3: once module pushforward preserves epimorphisms, the right-adjoint
pushforward functor is exact. -/
private theorem sheafOfModules_pushforward_exact_of_preservesEpimorphisms
    (u : C ⥤ D) [u.IsContinuous JC JD]
    (𝒪C : Sheaf JC RingCat.{max u v}) (𝒪D : Sheaf JD RingCat.{max u v})
    (φ : 𝒪C ⟶ (u.sheafPushforwardContinuous RingCat.{max u v} JC JD).obj 𝒪D)
    (hpush : Functor.PreservesEpimorphisms (SheafOfModules.pushforward φ)) :
    exactFunctor (Mod(𝒪D)) (Mod(𝒪C))
      (SheafOfModules.pushforward φ) := by
  let F : Mod(𝒪D) ⥤ Mod(𝒪C) := SheafOfModules.pushforward φ
  let _ : F.IsRightAdjoint := by
    simpa [F] using (SheafOfModules.instIsRightAdjointPushforward (φ := φ))
  let _ : PreservesFiniteLimits F := inferInstance
  let _ : Abelian (Mod(𝒪D)) := SheafOfModules.instAbelian 𝒪D
  let _ : Abelian (Mod(𝒪C)) := SheafOfModules.instAbelian 𝒪C
  have hLeft : leftExactFunctor _ _ F := by
    -- Proof comment: right adjoints preserve finite limits, providing the left exactness input.
    simpa [leftExactFunctor_iff] using (inferInstance : PreservesFiniteLimits F)
  let _ : F.Additive :=
    CategoryTheory.functor_additive_of_leftExact_or_rightExact (F := F) (.inl hLeft)
  let _ : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  let _ : Functor.PreservesEpimorphisms F := hpush
  -- Proof comment: in the abelian module categories, preserving epis and kernels upgrades the
  -- right adjoint to preserve homology and then finite colimits.
  let _ : F.PreservesHomology :=
    CategoryTheory.Functor.preservesHomology_of_preservesEpis_and_kernels F
  let _ : PreservesFiniteColimits F :=
    CategoryTheory.Functor.preservesFiniteColimits_of_preservesHomology F
  exact (exactFunctor_iff F).2 ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 18.15.3: a sheaf of sets has exactly one section on a sheaf-theoretically
empty object. -/
private theorem unique_sections_of_isSheafTheoreticallyEmpty
    {F : Sheaf JD (Type (max u v))} (V : D) (hV : JD.IsSheafTheoreticallyEmpty V) :
    Nonempty (Unique (F.1.obj (Opposite.op V))) := by
  rw [GrothendieckTopology.isSheafTheoreticallyEmpty_iff_bot_mem] at hV
  exact ⟨CategoryTheory.Limits.Types.isTerminalEquivUnique _ (F.isTerminalOfBotCover V hV)⟩

/-- Helper for Lemma 18.15.3: almost cocontinuity makes the set-valued direct image preserve
epimorphisms. -/
private theorem sheafPushforwardContinuous_type_preservesEpimorphisms_of_isAlmostCocontinuous
    (u : C ⥤ D) [u.IsContinuous JC JD] [u.IsAlmostCocontinuous JC JD] :
    Functor.PreservesEpimorphisms
      (u.sheafPushforwardContinuous (Type (max u v)) JC JD) := by
  let F := u.sheafPushforwardContinuous (Type (max u v)) JC JD
  constructor
  intro X Y φ hφ
  have hloc : Sheaf.IsLocallySurjective φ := by
    have himage : Epi (Sheaf.imageι φ) := epi_of_epi_fac (Sheaf.toImage_ι φ)
    exact (Sheaf.isLocallySurjective_iff_isIso φ).2 <|
      isIso_of_mono_of_epi (Sheaf.imageι φ)
  let ψ : F.obj X ⟶ F.obj Y := F.map φ
  have hψ : Sheaf.IsLocallySurjective ψ := by
    change Presheaf.IsLocallySurjective JC ψ.hom
    refine Presheaf.IsLocallySurjective.mk ?_
    intro U s
    let T : JD.Cover (u.obj U) :=
      ⟨Presheaf.imageSieve φ.hom s, hloc.imageSieve_mem s⟩
    obtain ⟨S, hS⟩ := Functor.cover_lift_factors u JC JD T
    refine JC.superset_covering ?_ S.condition
    intro V f hf
    let I : S.Arrow := ⟨V, f, hf⟩
    rcases hS I with hEmpty | ⟨j, g, hg⟩
    · obtain ⟨hUniqueX⟩ :=
        unique_sections_of_isSheafTheoreticallyEmpty (JD := JD) (F := X) (V := u.obj V) hEmpty
      obtain ⟨hUniqueY⟩ :=
        unique_sections_of_isSheafTheoreticallyEmpty (JD := JD) (F := Y) (V := u.obj V) hEmpty
      refine ⟨hUniqueX.default, ?_⟩
      simpa using hUniqueY.uniq _
    · rcases (show Presheaf.imageSieve φ.hom s j.f from by simpa [T] using j.hf) with ⟨t, ht⟩
      refine ⟨X.1.map g.op t, ?_⟩
      calc
        φ.hom.app (Opposite.op (u.obj V)) (X.1.map g.op t) =
            Y.1.map g.op (φ.hom.app (Opposite.op j.Y) t) := by
              exact FunctorToTypes.naturality _ _ φ.hom g.op t
        _ = Y.1.map g.op (Y.1.map j.f.op s) := by
              simpa using congrArg (Y.1.map g.op) ht
        _ = Y.1.map (u.map f).op s := by
              rw [← hg]
              simp [op_comp]
  letI : Sheaf.IsLocallySurjective ψ := hψ
  infer_instance

/- Lemma 18.15.3 (1): if `f : \mathcal D \to \mathcal C` is the morphism of sites associated to
the continuous functor `u : \mathcal C \to \mathcal D` and `u` is almost cocontinuous, then the
direct image functor `f_*`, identified here with
`u.sheafPushforwardContinuous AddCommGrpCat JC JD`, is exact on sheaves of abelian groups. -/
theorem sheafPushforwardContinuous_exact_of_isAlmostCocontinuous
    (u : C ⥤ D) [u.IsContinuous JC JD] [u.IsAlmostCocontinuous JC JD] :
    exactFunctor (Sheaf JD AddCommGrpCat.{max u v})
      (Sheaf JC AddCommGrpCat.{max u v})
      (u.sheafPushforwardContinuous AddCommGrpCat.{max u v} JC JD) := by
  let Ftype := u.sheafPushforwardContinuous (Type (max u v)) JC JD
  have hTypeEpi : Ftype.PreservesEpimorphisms :=
    sheafPushforwardContinuous_type_preservesEpimorphisms_of_isAlmostCocontinuous
      (JC := JC) (JD := JD) (u := u)
  have hAddEpi :
      (u.sheafPushforwardContinuous AddCommGrpCat.{max u v} JC JD).PreservesEpimorphisms :=
    sheafPushforwardContinuous_preservesEpimorphisms_of_underlyingPreservesEpimorphisms
      (JC := JC) (JD := JD) (u := u) hTypeEpi
  exact sheafPushforwardContinuous_exact_of_preservesEpimorphisms
    (JC := JC) (JD := JD) (u := u) hAddEpi

/-- Helper for Lemma 18.15.3: almost cocontinuity makes additive-sheaf pushforward preserve
epimorphisms. -/
private theorem sheafPushforwardContinuous_preservesEpimorphisms_of_isAlmostCocontinuous
    (u : C ⥤ D) [u.IsContinuous JC JD] [u.IsAlmostCocontinuous JC JD] :
    Functor.PreservesEpimorphisms
      (u.sheafPushforwardContinuous AddCommGrpCat.{max u v} JC JD) := by
  let F :
      Sheaf JD AddCommGrpCat.{max u v} ⥤
        Sheaf JC AddCommGrpCat.{max u v} :=
    u.sheafPushforwardContinuous AddCommGrpCat.{max u v} JC JD
  have hExact :
      exactFunctor
        (Sheaf JD AddCommGrpCat.{max u v})
        (Sheaf JC AddCommGrpCat.{max u v})
        F :=
    sheafPushforwardContinuous_exact_of_isAlmostCocontinuous (JC := JC) (JD := JD) (u := u)
  -- Proof comment: exact additive pushforward preserves finite colimits, hence epimorphisms.
  let _ : PreservesFiniteColimits F := ((exactFunctor_iff F).1 hExact).2
  infer_instance

/- Lemma 18.15.3 (2): if `f^\sharp : f^{-1}\mathcal O_\mathcal C \to \mathcal O_\mathcal D` is
given so that `f` becomes a morphism of ringed sites, encoded in Lean by a morphism
`φ : \mathcal O_\mathcal C \to u_* \mathcal O_\mathcal D`, then the direct image functor
`f_* = SheafOfModules.pushforward φ` is exact on sheaves of modules. -/
theorem sheafOfModules_pushforward_exact_of_isAlmostCocontinuous
    (u : C ⥤ D) [u.IsContinuous JC JD] [u.IsAlmostCocontinuous JC JD]
    (𝒪C : Sheaf JC RingCat.{max u v}) (𝒪D : Sheaf JD RingCat.{max u v})
    (φ : 𝒪C ⟶ (u.sheafPushforwardContinuous RingCat.{max u v} JC JD).obj 𝒪D) :
    exactFunctor (Mod(𝒪D)) (Mod(𝒪C))
      (SheafOfModules.pushforward φ) := by
  let _ :
      Functor.PreservesEpimorphisms
        (u.sheafPushforwardContinuous AddCommGrpCat.{max u v} JC JD) :=
    sheafPushforwardContinuous_preservesEpimorphisms_of_isAlmostCocontinuous
      (JC := JC) (JD := JD) (u := u)
  let hModuleEpi :
      Functor.PreservesEpimorphisms (SheafOfModules.pushforward φ) :=
    sheafOfModules_pushforward_preservesEpimorphisms_of_underlyingPreservesEpimorphisms
      (JC := JC) (JD := JD) (u := u) (𝒪C := 𝒪C) (𝒪D := 𝒪D) (φ := φ)
  -- Proof comment: once epi preservation is established, exactness follows from the generic
  -- right-adjoint abelian argument isolated above.
  exact sheafOfModules_pushforward_exact_of_preservesEpimorphisms
    (JC := JC) (JD := JD) (u := u) (𝒪C := 𝒪C) (𝒪D := 𝒪D) (φ := φ) hModuleEpi

end Exactness

end CategoryTheory.Functor
