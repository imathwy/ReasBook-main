import StacksProject_2024.stacks_project.Chap20.Open_subspace_module_core
import StacksProject_2024.stacks_project.Chap20.OpensInstances
import StacksProject_2024.stacks_project.Chap20.«20_11_0_1»
import StacksProject_2024.stacks_project.Chap06.Lemma_6_26_4
import StacksProject_2024.stacks_project.Chap17.ModuleRestrictionAndStalks
import StacksProject_2024.stacks_project.Chap17.Lemma_17_4_2
import StacksProject_2024.stacks_project.Chap17.Lemma_17_14_5.FreeSections
import StacksProject_2024.stacks_project.Chap21.Definition_21_44_1

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open scoped ModuleRestriction

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).HasSheafCompose
  (forget₂ RingCat.{u} AddCommGrpCat.{u})]

/- Domain-style sampling for Lemma 20.46.5:
- primary domain: local lifting of morphisms of `𝒪_X`-modules on a ringed space;
- sampled owner declarations:
  `SheafOfModules.finiteFreeRetractModuleProperty`,
  `moduleRestrictionToOpen`,
  `SheafOfModules.overRestrictionFunctor`;
- best owner abstraction:
  `source-facing`: the point-neighborhood lifting statement on the ringed space `X`;
  `core/canonical`: `SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf`, the
    restriction functors `(-).over U` and `moduleRestrictionToOpen X U`, and local surjectivity of
    the underlying additive sheaf;
  `bridge/view`: the comparison `ℱ.over U ≅ (moduleRestrictionToOpen X U).obj ℱ`.

This file keeps the source-facing neighborhood theorem while proving it directly on the opens site
of `X`: first lift finitely many basis sections on a common neighborhood, then assemble the local
map on `ℱ.over U`, and finally transport once to `moduleRestrictionToOpen X U`. -/
/-- Helper for Lemma 20.46.5: an epimorphism of `\mathcal O_X`-modules remains epic after
forgetting to the underlying sheaf of abelian groups. -/
private theorem moduleUnderlyingSheafMapEpiOfEpi
    {ℱ 𝒢 : X.Modules} (p : 𝒢 ⟶ ℱ) [Epi p] :
    Epi ((moduleUnderlyingSheaf X).map p) := by
  -- Proof comment: only a pushout-preservation witness is needed to map an epimorphism, so keep
  -- the bridge at the `WalkingSpan` level instead of asking typeclass search for the full exact
  -- functor package.
  let F : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X.carrier := moduleUnderlyingSheaf X
  let _ : PreservesColimitsOfShape WalkingSpan F := by
    infer_instance
  exact preserves_epi_of_preservesColimit (F := F) p

/-- Helper for Lemma 20.46.5: an epimorphism of `\mathcal O_X`-modules yields an opens-site cover
on which a chosen section lifts locally. -/
private theorem exists_cover_lift_of_epi_section
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    {ℱ 𝒢 : X.Modules} (p : 𝒢 ⟶ ℱ) [Epi p]
    (U : Opens X.carrier) (s : ℱ.val.obj (op U)) :
    ∃ T : (Opens.grothendieckTopology X).Cover U, ∀ I : T.Arrow,
      ∃ t : 𝒢.val.obj (op I.Y),
        (p.val.app (op I.Y)) t = (ℱ.val.map I.f.op) s := by
  let p' := (moduleUnderlyingSheaf X).map p
  have hEpi : Epi p' := moduleUnderlyingSheafMapEpiOfEpi (X := X) p
  let _ : Epi p' := hEpi
  have hπ : Sheaf.IsLocallySurjective p' :=
    (Sheaf.isLocallySurjective_iff_epi'
      (J := Opens.grothendieckTopology X) AddCommGrpCat.{u} p').2 inferInstance
  let T : (Opens.grothendieckTopology X).Cover U :=
    ⟨Presheaf.imageSieve p'.hom s,
      by
        simpa [Presheaf.imageSieve] using hπ.imageSieve_mem (U := U) s⟩
  refine ⟨T, ?_⟩
  intro I
  refine ⟨Presheaf.localPreimage p'.hom s I.f I.hf, ?_⟩
  -- Proof comment: the chosen local preimage from the image sieve maps to the required
  -- restricted section by construction.
  simpa using Presheaf.app_localPreimage p'.hom s I.f I.hf

/-- Helper for Lemma 20.46.5: a section of `ℱ` on `U` lifts after shrinking to a neighborhood of
`x` because the underlying additive sheaf map of an epimorphism is locally surjective. -/
private theorem exists_open_lift_of_epi_section
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    {ℱ 𝒢 : X.Modules} (p : 𝒢 ⟶ ℱ) [Epi p]
    {U : Opens X.carrier} {x : X} (hx : x ∈ U)
    (s : ℱ.val.obj (op U)) :
    ∃ V : Opens X.carrier, x ∈ V ∧ ∃ hVU : V ≤ U,
      ∃ t : 𝒢.val.obj (op V),
        (p.val.app (op V)) t = (ℱ.val.map (homOfLE hVU).op) s := by
  obtain ⟨T, hT⟩ := exists_cover_lift_of_epi_section (X := X) (p := p) U s
  obtain ⟨V, i, hi, hxV⟩ := T.condition x hx
  let I : T.Arrow := ⟨V, i, hi⟩
  obtain ⟨t, ht⟩ := hT I
  refine ⟨V, hxV, leOfHom i, t, ?_⟩
  -- Proof comment: choosing the member of the cover that contains `x` turns the opens-site lift
  -- into the requested neighborhood lift.
  simpa [I] using ht

/-- Helper for Lemma 20.46.5: restricting a section from `U` to `U ∩ V` along the left inclusion
recovers the section's value on the intersection. -/
private theorem section_restrict_inf_left
    {ℱ : X.Modules} (s : ℱ.sections) (U V : Opens X.carrier) :
    (ℱ.val.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op) (s.1 (op U)) =
      s.1 (op (U ⊓ V)) := by
  -- Proof comment: this is exactly the compatibility relation built into a sheaf section.
  simpa using
    PresheafOfModules.sections_property s (homOfLE (inf_le_left : U ⊓ V ≤ U)).op

/-- Helper for Lemma 20.46.5: restricting a section from `V` to `U ∩ V` along the right inclusion
recovers the section's value on the intersection. -/
private theorem section_restrict_inf_right
    {ℱ : X.Modules} (s : ℱ.sections) (U V : Opens X.carrier) :
    (ℱ.val.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op) (s.1 (op V)) =
      s.1 (op (U ⊓ V)) := by
  -- Proof comment: this is the same section-compatibility identity for the right inclusion.
  simpa using
    PresheafOfModules.sections_property s (homOfLE (inf_le_right : U ⊓ V ≤ V)).op

/-- Helper for Lemma 20.46.5: finitely many global sections admit simultaneous local lifts on a
single neighborhood of `x`. -/
private theorem exists_open_lifts_of_finite_sections
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    {I : Type u} [Finite I] {ℱ 𝒢 : X.Modules}
    (p : 𝒢 ⟶ ℱ) [Epi p] (x : X) (s : I → ℱ.sections) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ t : I → 𝒢.val.obj (op U), ∀ i, (p.val.app (op U)) (t i) = (s i).1 (op U) := by
  classical
  induction I using Finite.induction_empty_option with
  | @of_equiv I₁ I₂ e IH =>
      obtain ⟨U, hxU, t, ht⟩ := IH (s ∘ e)
      refine ⟨U, hxU, fun i ↦ t (e.symm i), ?_⟩
      -- Proof comment: transport the common lifting neighborhood across the finite equivalence.
      intro i
      simpa using ht (e.symm i)
  | h_empty =>
      refine ⟨⊤, by simp, fun i ↦ PEmpty.elim i, ?_⟩
      -- Proof comment: with no sections to lift, the top open and the empty family are enough.
      intro i
      exact PEmpty.elim i
  | @h_option I _ IH =>
      obtain ⟨U₀, hxU₀, t₀, ht₀⟩ := IH (s ∘ Option.some)
      obtain ⟨V, hxV, _hVTop, tnone, htnone⟩ :=
        exists_open_lift_of_epi_section (X := X) (p := p) (x := x)
          (U := ⊤) (by simp) ((s none).1 (op ⊤))
      refine ⟨U₀ ⊓ V, ⟨hxU₀, hxV⟩, ?_, ?_⟩
      · -- Proof comment: restrict the inductive lifts and the new lift to the intersection.
        intro i
        cases i with
        | none =>
            exact (𝒢.val.map (homOfLE (inf_le_right : U₀ ⊓ V ≤ V)).op) tnone
        | some i =>
            exact (𝒢.val.map (homOfLE (inf_le_left : U₀ ⊓ V ≤ U₀)).op) (t₀ i)
      · intro i
        cases i with
        | none =>
            have htnone' : (p.val.app (op V)) tnone = (s none).1 (op V) := by
              have hs :
                  (ℱ.val.map (homOfLE _hVTop).op) ((s none).1 (op ⊤)) = (s none).1 (op V) := by
                    simpa using PresheafOfModules.sections_property
                      (s none) (homOfLE _hVTop).op
              exact htnone.trans hs
            -- Proof comment: naturality of `p` moves the newly chosen lift from `V` to
            -- `U₀ ⊓ V`, and the right-intersection restriction identifies the target section.
            rw [PresheafOfModules.naturality_apply p.val
              (homOfLE (inf_le_right : U₀ ⊓ V ≤ V)).op tnone]
            rw [htnone']
            simpa using section_restrict_inf_right (s := s none) U₀ V
        | some i =>
            -- Proof comment: the inductive lifts behave the same way after restricting from `U₀`
            -- to the common intersection.
            rw [PresheafOfModules.naturality_apply p.val
              (homOfLE (inf_le_left : U₀ ⊓ V ≤ U₀)).op (t₀ i)]
            rw [ht₀ i]
            simpa using section_restrict_inf_left (s := s (Option.some i)) U₀ V

/-- Helper for Lemma 20.46.5: a finite-free-retract module can be represented by an explicit
canonical free sheaf together with a retract. -/
private theorem finiteFreeRetract_exists_retract_free
    {ℰ : X.Modules}
    (hℰ : SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf ℰ) :
    ∃ I : Type u, Finite I ∧
      Nonempty (Retract ℰ (SheafOfModules.free.{u} (R := X.ringCatSheaf) I : X.Modules)) := by
  have hℰ' :
      CategoryTheory.ObjectProperty.retractClosure
        (_root_.SheafOfModules.IsFiniteFree : ObjectProperty X.Modules) ℰ := by
    -- Proof comment: first expose the owner as retract-closure membership in finite free modules.
    simpa [SheafOfModules.finiteFreeRetractModuleProperty] using hℰ
  obtain ⟨P, hP, ⟨r⟩⟩ :=
    (CategoryTheory.ObjectProperty.prop_retractClosure_iff
      (_root_.SheafOfModules.IsFiniteFree : ObjectProperty X.Modules) ℰ).mp hℰ'
  obtain ⟨I, hI, ⟨e⟩⟩ := _root_.SheafOfModules.IsFiniteFree.exists_iso_free (ℱ := P)
  -- Proof comment: replace the abstract finite free model by the canonical free sheaf via the
  -- isomorphism provided by `IsFiniteFree.exists_iso_free`.
  exact ⟨I, hI, ⟨r.trans (Retract.ofIso e)⟩⟩

/-- Helper for Lemma 20.46.5: restricting to an open immersion satisfies the finality hypothesis
used by `SheafOfModules.pullbackObjFreeIso`. -/
private instance opensMapOfRestrictFinal (U : Opens X.carrier) :
    Functor.Final (Opens.map (X.ofRestrict U.isOpenEmbedding).hom.base) := by
  -- Proof comment: the inclusion of an open subset is an open map, so finality follows from the
  -- standard adjunction on opens.
  let hU : IsOpenMap U.inclusion' := U.isOpenEmbedding.isOpenMap
  simpa using
    (CategoryTheory.Functor.final_of_adjunction hU.adjunction :
      Functor.Final (Opens.map U.inclusion'))

/-- Helper for Lemma 20.46.5: the top open of the restricted ringed space `X|_U` maps back to the
ambient open `U`. -/
private theorem restrictedTopOpen_obj_eq_open
    (U : Opens X.carrier) :
    ((U.isOpenEmbedding.functor).obj
      (⊤ : Opens ((Opens.toTopCat X.toPresheafedSpace).obj U))) = U := by
  -- Proof comment: a point of the top open of `X|_U` is exactly a point of `X` together with the
  -- proof that it already lies in `U`.
  ext x
  simp

/-- Helper for Lemma 20.46.5: the inverse identity restriction-of-scalars transport on a section
object acts as the identity. -/
private theorem sectionMapIdTransportApply
    {Y : RingedSpace.{u}} (M : Y.Modules) (U : (Opens Y.carrier)ᵒᵖ)
    (m : M.val.obj U) :
    (ModuleCat.Hom.hom
        ((ModuleCat.restrictScalarsId' (Y.presheaf.map (𝟙 U)).hom
          (congrArg CommRingCat.Hom.hom (Y.presheaf.map_id U))).inv.app
          (M.val.obj U))) m = m := by
  -- Proof comment: the identity restriction map induces the standard identity coherence isomorphism
  -- on sections, and its inverse is pointwise the identity.
  simpa using
    (ModuleCat.restrictScalarsId'App_inv_apply (Y.presheaf.map (𝟙 U)).hom
      (congrArg CommRingCat.Hom.hom (Y.presheaf.map_id U)) (M.val.obj U) m)

/-- Helper for Lemma 20.46.5: sections of a module on a ringed space are determined by their
value on the top open. -/
private noncomputable def topSectionEquiv
    {Y : RingedSpace.{u}} (M : Y.Modules) :
    M.sections ≃ M.val.obj (op (⊤ : Opens Y.carrier)) where
  toFun s := s.1 (op ⊤)
  invFun m :=
    M.val.sectionsMk
      (fun V ↦ M.val.map (homOfLE (show V.unop ≤ (⊤ : Opens Y.carrier) from by
        intro x hx
        trivial)).op m)
      (fun V W f ↦ by
        -- Proof comment: every open of `Y` has a unique restriction map from the top open.
        have h :
            (homOfLE (show V.unop ≤ (⊤ : Opens Y.carrier) from by
              intro x hx
              trivial)).op ≫ f =
              (homOfLE (show W.unop ≤ (⊤ : Opens Y.carrier) from by
                intro x hx
                trivial)).op := Subsingleton.elim _ _
        rw [← PresheafOfModules.map_comp_apply, h])
  left_inv s := by
    -- Proof comment: each component is the restriction of the top-open component.
    ext V
    simpa using PresheafOfModules.sections_property s
      ((homOfLE (show V.unop ≤ (⊤ : Opens Y.carrier) from by
        intro x hx
        trivial)).op)
  right_inv m := by
    -- Proof comment: evaluating the reconstructed section at the top open reduces to the identity
    -- restriction transport on `M.val.obj (op ⊤)`.
    simpa using
      sectionMapIdTransportApply (M := M) (U := op (⊤ : Opens Y.carrier)) m

/-- Helper for Lemma 20.46.5: the inverse top-section equivalence is natural in a module
morphism. -/
private theorem sectionsMap_topSectionEquiv_symm
    {Y : RingedSpace.{u}} {M N : Y.Modules}
    (ψ : M ⟶ N) (m : M.val.obj (op (⊤ : Opens Y.carrier))) :
    SheafOfModules.sectionsMap ψ ((topSectionEquiv M).symm m) =
      (topSectionEquiv N).symm ((ψ.val.app (op ⊤)) m) := by
  -- Proof comment: compare the two sections after evaluating them on the terminal open `⊤`.
  apply (topSectionEquiv N).injective
  -- Proof comment: after evaluation at `⊤`, the left side is `ψ` applied to the reconstructed
  -- top section, and both evaluations collapse by `topSectionEquiv.right_inv`.
  change
    (ψ.val.app (op ⊤)) (((topSectionEquiv M).symm m).1 (op ⊤)) =
      ((topSectionEquiv N).symm ((ψ.val.app (op ⊤)) m)).1 (op ⊤)
  calc
    (ψ.val.app (op ⊤)) (((topSectionEquiv M).symm m).1 (op ⊤)) =
        (ψ.val.app (op ⊤)) m := by
          exact congrArg (ψ.val.app (op ⊤)) ((topSectionEquiv M).right_inv m)
    _ = ((topSectionEquiv N).symm ((ψ.val.app (op ⊤)) m)).1 (op ⊤) := by
          symm
          exact (topSectionEquiv N).right_inv ((ψ.val.app (op ⊤)) m)

/-- Helper for Lemma 20.46.5: top-open sections of the restricted module `M|_U` are canonically
the same as ambient sections of `M` on `U`. -/
private noncomputable def moduleRestrictionTopSectionIso
    (U : Opens X.carrier) (M : X.Modules) :
    ((moduleUnderlyingSheaf (X.restrict U.isOpenEmbedding)).obj
        ((X.moduleRestrictionToOpen U).obj M)).presheaf.obj
          (op (⊤ : Opens (X.restrict U.isOpenEmbedding).carrier)) ≅
      ((moduleUnderlyingSheaf X).obj M).presheaf.obj (op U) := by
  -- Route correction: the attempted slice-language transport is mathematically correct but still
  -- hits deterministic elaboration timeouts in `mapFree`/equivalence normalization here, so the
  -- file keeps the older top-open interface while that owner-level bridge is refactored.
  -- TODO: rebuild this transport on the owner `moduleUnderlyingSheaf` rather than on the raw
  -- presheaf `M.val`; the current broken attempt showed that the available `sheafPullbackIso`
  -- expects the bundled additive sheaf and that the module structures on the two section objects
  -- differ by an explicit scalar-transport iso.
  sorry

/-- Helper for Lemma 20.46.5: the top-open section transport for `M|_U` is natural in a module
morphism `ψ : M ⟶ N`. -/
private theorem moduleRestrictionTopSectionIso_naturality
    (U : Opens X.carrier) {M N : X.Modules} (ψ : M ⟶ N)
    (t :
      ((moduleUnderlyingSheaf (X.restrict U.isOpenEmbedding)).obj
        ((X.moduleRestrictionToOpen U).obj M)).presheaf.obj
          (op (⊤ : Opens (X.restrict U.isOpenEmbedding).carrier))) :
    (moduleRestrictionTopSectionIso (X := X) U N).hom
        ((((moduleUnderlyingSheaf (X.restrict U.isOpenEmbedding)).map
            ((X.moduleRestrictionToOpen U).map ψ)).hom.app (op ⊤)) t) =
      (((moduleUnderlyingSheaf X).map ψ).hom.app (op U))
        ((moduleRestrictionTopSectionIso (X := X) U M).hom t) := by
  -- TODO: once `moduleRestrictionTopSectionIso` is rebuilt on `moduleUnderlyingSheaf`, this
  -- naturality statement should follow by evaluating the corresponding `sheafPullbackIso`
  -- naturality square at the top open of `X|_U`.
  sorry

/-- Helper for Lemma 20.46.5: a morphism from a finite free module lifts on some neighborhood of
`x`. -/
private theorem exists_open_lift_of_epi_of_finiteFree
    {I : Type u} [Finite I] {ℱ 𝒢 : X.Modules}
    (q : (SheafOfModules.free.{u} (R := X.ringCatSheaf) I : X.Modules) ⟶ ℱ)
    (p : 𝒢 ⟶ ℱ) [Epi p] (x : X) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      let j := X.moduleRestrictionToOpen U
      ∃ l : j.obj (SheafOfModules.free.{u} (R := X.ringCatSheaf) I : X.Modules) ⟶ j.obj 𝒢,
        l ≫ j.map p = j.map q := by
  -- Route correction: the correct proof now factors through simultaneous slice lifts of the free
  -- basis sections and a single normalization by `pullbackObjFreeIso`, but the owner-level
  -- transport from slice modules to `moduleRestrictionToOpen` still needs a low-cost API.
  -- TODO: package the slice-language finite-free lift into a restricted-ringed-space morphism via
  -- a canonical owner comparison, then finish with the same `pullbackObjFreeIso` cancellation used
  -- in the retract step below.
  sorry

omit [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).HasSheafCompose
    (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- Lemma 20.46.5: if `ℰ` is a direct summand of a finite free `𝒪_X`-module and
`p : 𝒢 ⟶ ℱ` is surjective, then every morphism `ℰ ⟶ ℱ`
locally lifts through `p`. -/
@[stacks 08C6]
theorem exists_open_neighborhood_lift_of_epi_of_retract_finiteFree
    {ℰ ℱ 𝒢 : X.Modules}
    (f : ℰ ⟶ ℱ) (p : 𝒢 ⟶ ℱ) [Epi p]
    (hℰ : SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf ℰ)
    (x : X) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      let j := X.moduleRestrictionToOpen U
      ∃ l : j.obj ℰ ⟶ j.obj 𝒢, l ≫ j.map p = j.map f := by
  -- Route correction: the retract closing step is straightforward once the finite-free lift is
  -- available on `moduleRestrictionToOpen`; the current blocker is still the owner-level transport
  -- that turns simultaneous basis lifts on the slice over `U` into that restricted finite-free
  -- morphism.
  -- TODO: combine `finiteFreeRetract_exists_retract_free` with the corrected finite-free local
  -- lifting lemma and then postcompose the resulting local free lift with the restricted retract
  -- section.
  sorry

omit [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).HasSheafCompose
    (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- Companion bridge: if `ℰ` is a direct summand of a finite free `𝒪_X`-module and
`p : 𝒢 ⟶ ℱ` is surjective, then every morphism `ℰ ⟶ ℱ` lifts after restricting to the
members of some open cover of `X`. -/
theorem exists_open_cover_lift_of_epi_of_retract_finiteFree
    {ℰ ℱ 𝒢 : X.Modules}
    (f : ℰ ⟶ ℱ) (p : 𝒢 ⟶ ℱ) [Epi p]
    (hℰ : SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf ℰ) :
    ∃ (ι : Type u) (cover : ι → Opens X.carrier), IsOpenCover cover ∧
      ∀ i : ι,
        let j := X.moduleRestrictionToOpen (cover i)
        ∃ l : j.obj ℰ ⟶ j.obj 𝒢, l ≫ j.map p = j.map f := by
  classical
  let cover : X → Opens X.carrier := fun x ↦
    Classical.choose
      (exists_open_neighborhood_lift_of_epi_of_retract_finiteFree
        (X := X) f p hℰ x)
  have hmem : ∀ x : X, x ∈ cover x := by
    intro x
    exact
      (Classical.choose_spec
        (exists_open_neighborhood_lift_of_epi_of_retract_finiteFree
          (X := X) f p hℰ x)).1
  have hlift :
      ∀ x : X,
        let j := X.moduleRestrictionToOpen (cover x)
        ∃ l : j.obj ℰ ⟶ j.obj 𝒢, l ≫ j.map p = j.map f := by
    intro x
    simpa [cover] using
      (Classical.choose_spec
        (exists_open_neighborhood_lift_of_epi_of_retract_finiteFree
          (X := X) f p hℰ x)).2
  refine ⟨X, cover, ?_, hlift⟩
  -- Proof comment: choose one lifting neighborhood for each point; those neighborhoods cover `X`
  -- because each chosen neighborhood contains its indexing point.
  rw [TopologicalSpace.IsOpenCover]
  apply le_antisymm
  · refine iSup_le ?_
    intro x
    exact le_top
  · intro x hx
    rw [Opens.mem_iSup]
    exact ⟨x, hmem x⟩

end

end AlgebraicGeometry.RingedSpace
