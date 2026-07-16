import Mathlib
import stacks_proof.stacks_project.Chap06.Definition_6_26_1
import stacks_proof.stacks_project.Chap17.Lemma_17_4_2
import stacks_proof.stacks_project.Chap17.Lemma_17_11_4
import stacks_proof.stacks_project.Chap17.ModuleRestrictionAndStalks
import stacks_proof.stacks_project.Chap17.Lemma_17_9_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X

/- Domain-style sampling for Lemma 17.11.7:
- primary domain: finitely presented sheaves of modules on ringed spaces and local freeness from a
  stalkwise finite free model;
- inspected owner declarations:
  `AlgebraicGeometry.RingedSpace.Modules`,
  `AlgebraicGeometry.RingedSpace.stalkModuleCat`,
  `ModuleCat.free`,
  `SheafOfModules.IsFiniteLocallyFreeOfRank`;
- best owner abstraction: the ambient owner category `RingedSpace.Modules X`, with the stalk
  bundled by `RingedSpace.stalkModuleCat` and the canonical finite free stalk model supplied by
  `ModuleCat.free (X.presheaf.stalk x)`;
- primitive data: a finitely presented module sheaf `ℱ`, a point `x`, a rank `r`, and a stalk
  isomorphism from `RingedSpace.stalkModuleCat ℱ x` to the free `X.presheaf.stalk x`-module on
  `ULift (Fin r)`;
- derived API: after shrinking around `x`, the restricted sheaf `ℱ.over U` becomes isomorphic to
  the free sheaf `SheafOfModules.free (ULift (Fin r))`.

Source/core/bridge triage:
- `source-facing`: the local trivialization statement around a point with free stalk;
- `core/canonical`: `RingedSpace.Modules`, `RingedSpace.stalkModuleCat`, and `ModuleCat.free`;
- `bridge/view`: the restriction `ℱ.over U` and the local free sheaf `SheafOfModules.free`. -/

/-- Helper for Lemma 17.11.7: the open subset `U` defines the corresponding restricted ringed
space `X|_U`. -/
private abbrev restrictedRingedSpace (U : Opens X) : RingedSpace.{u} :=
  X.restrict U.isOpenEmbedding

/-- Helper for Lemma 17.11.7: the canonical open immersion of the restricted ringed space
`X|_U` back into `X`. -/
private abbrev restrictedOpenInclusion (U : Opens X) :
    restrictedRingedSpace (X := X) U ⟶ X :=
  X.ofRestrict U.isOpenEmbedding

/-- Helper for Lemma 17.11.7: restricting a free sheaf to an open subset preserves the same free
basis type. -/
private abbrev freeOverIso
    {Y : RingedSpace.{u}} (U : Opens Y) (I : Type u) :
    ((SheafOfModules.free.{u} I : RingedSpace.Modules Y).over U) ≅
      (SheafOfModules.free.{u} I : RingedSpace.Modules (Y.restrict U.isOpenEmbedding)) :=
  SheafOfModules.mapFree
    (SheafOfModules.pushforward (𝟙 ((Y.ringCatSheaf).over U)))
    (Iso.refl (SheafOfModules.unit ((Y.ringCatSheaf).over U)))
    I

-- Proof sketch: choose lifts on some neighbourhood of a basis of the free stalk module, obtaining
-- a morphism from the finite free sheaf to `ℱ|_U`. Lemma `17.9.4` makes this morphism surjective
-- after shrinking, Lemma `17.11.4` gives finite type for its kernel, and Lemma `17.9.5` kills the
-- kernel after another shrinking because its stalk at `x` is zero.
/-- Helper for Lemma 17.11.7: evaluating a section of `𝒢.over U` at the terminal object
`U \to U` recovers all of its data. -/
private theorem overSectionsEquivEvaluation
    {Y : RingedSpace.{u}} (𝒢 : RingedSpace.Modules Y) (U : Opens Y) :
    (𝒢.over U).sections ≃ (𝒢.over U).val.obj (op (Over.mk (𝟙 U))) := by
  refine
    { toFun := fun s ↦ s.1 (op (Over.mk (𝟙 U)))
      invFun := fun m ↦
        (𝒢.over U).val.sectionsMk
          (fun W ↦ (𝒢.over U).val.map ((Over.mkIdTerminal.from W.unop).op) m)
          (by
            intro W Y f
            -- Proof comment: every object of `Over U` has a unique map to the terminal object.
            have h :
                (Over.mkIdTerminal.from W.unop).op ≫ f =
                  (Over.mkIdTerminal.from Y.unop).op := by
              apply Quiver.Hom.unop_inj
              simp only [Quiver.Hom.unop_op]
              exact Over.mkIdTerminal.hom_ext
                (f.unop ≫ Over.mkIdTerminal.from W.unop)
                (Over.mkIdTerminal.from Y.unop)
            rw [← PresheafOfModules.map_comp_apply, h])
      left_inv := ?_
      right_inv := ?_ }
  · intro s
    -- Proof comment: a section on the slice is determined by its restrictions from the terminal
    -- object.
    ext W
    simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from W.unop).op)
  · intro m
    -- Proof comment: the reconstructed section evaluates back to the original terminal value.
    change (𝒢.over U).val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 U))).op) m = m
    have h :
        Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 (Over.mk (𝟙 U)) :=
      Over.mkIdTerminal.hom_ext _ _
    simpa using (𝒢.over U).val.congr_map_apply (congrArg Quiver.Hom.op h) m

/-- Helper for Lemma 17.11.7: an ambient section on `U` defines the corresponding global section
of the restricted module sheaf `𝒢.over U`. -/
private noncomputable abbrev overSectionOfOpenSection
    {Y : RingedSpace.{u}} (𝒢 : RingedSpace.Modules Y) (U : Opens Y) (s : 𝒢.val.obj (op U)) :
    (𝒢.over U).sections :=
  (overSectionsEquivEvaluation 𝒢 U).symm
    (show (𝒢.over U).val.obj (op (Over.mk (𝟙 U))) from s)

/-- Helper for Lemma 17.11.7: terminal evaluation of the section associated to an ambient section
returns the original ambient section. -/
private theorem overSectionOfOpenSection_eval
    {Y : RingedSpace.{u}} (𝒢 : RingedSpace.Modules Y) (U : Opens Y) (s : 𝒢.val.obj (op U)) :
    overSectionsEquivEvaluation 𝒢 U (overSectionOfOpenSection 𝒢 U s) =
      (show (𝒢.over U).val.obj (op (Over.mk (𝟙 U))) from s) := by
  -- Proof comment: this is the `apply_symm_apply` identity for terminal evaluation.
  exact Equiv.apply_symm_apply (overSectionsEquivEvaluation 𝒢 U)
    (show (𝒢.over U).val.obj (op (Over.mk (𝟙 U))) from s)

/-- Helper for Lemma 17.11.7: the restricted global section associated to an ambient section
evaluates to that ambient section at the terminal object of `Over U`. -/
private theorem overSectionOfOpenSection_terminal
    {Y : RingedSpace.{u}} (𝒢 : RingedSpace.Modules Y) (U : Opens Y) (s : 𝒢.val.obj (op U)) :
    (overSectionOfOpenSection 𝒢 U s).1 (op (Over.mk (𝟙 U))) = s := by
  -- Proof comment: unfold the terminal-evaluation equivalence used to define
  -- `overSectionOfOpenSection` and then apply the computation lemma above.
  simpa [overSectionsEquivEvaluation] using
    (overSectionOfOpenSection_eval (𝒢 := 𝒢) (U := U) s)

/-- Helper for Lemma 17.11.7: the chosen stalk basis vectors lift simultaneously to sections on a
single common neighborhood of `x`. -/
private theorem existsCommonOpenWithFreeBasisLifts
    (ℱ : ModX) (x : X) (r : ℕ)
    (e : RingedSpace.stalkModuleCat ℱ x ≅
      (ModuleCat.free (X.presheaf.stalk x)).obj (ULift.{u} (Fin r))) :
    ∃ (U : Opens X) (_ : x ∈ U) (s : ULift.{u} (Fin r) → ℱ.val.obj (op U)),
      ∀ i,
        TopCat.Presheaf.germ ℱ.val.presheaf U x ‹x ∈ U› (s i) =
          e.inv.hom (Finsupp.single i 1) := by
  classical
  choose U hxU s hs using
    fun i : ULift.{u} (Fin r) ↦
      TopCat.Presheaf.germ_exist ℱ.val.presheaf x (e.inv.hom (Finsupp.single i 1))
  let U' : Opens X := ⨅ i, U i
  have hxU' : x ∈ U' := by
    -- Proof comment: the common neighborhood is the finite intersection of the chosen lifts.
    change x ∈ iInf U
    exact Set.mem_iInter.2 hxU
  have hU'_le : ∀ i : ULift.{u} (Fin r), U' ≤ U i := by
    intro i
    exact iInf_le U i
  let s' : ULift.{u} (Fin r) → ℱ.val.obj (op U') := fun i ↦
    ℱ.val.map (homOfLE (hU'_le i)).op (s i)
  refine ⟨U', hxU', s', ?_⟩
  intro i
  -- Proof comment: restricting a representative section does not change its germ at `x`.
  rw [TopCat.Presheaf.germ_res_apply ℱ.val.presheaf (homOfLE (hU'_le i)) x hxU' (s i)]
  exact hs i

/-- Helper for Lemma 17.11.7: injectivity of the stalk map of `φ` forces the stalk of its kernel
at `x` to be zero. -/
private theorem isZero_stalkKernel_of_moduleStalkMap_injective
    {𝒢 ℋ : ModX} (φ : 𝒢 ⟶ ℋ) (x : X)
    (hφx : Function.Injective (RingedSpace.moduleStalkMap x φ)) :
    IsZero (RingedSpace.stalkModuleCat (kernel φ) x) := by
  have hιx : Function.Injective (RingedSpace.moduleStalkMap x (kernel.ι φ)) := by
    have hmono :
        Mono ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map (kernel.ι φ)) := by
      infer_instance
    have hstalk_mono :
        Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map (kernel.ι φ)).hom) :=
      (TopCat.Presheaf.mono_iff_stalk_mono
        ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map (kernel.ι φ))).1
        hmono x
    simpa [RingedSpace.moduleStalkMap] using
      (AddCommGrpCat.mono_iff_injective _).1 hstalk_mono
  have hkernel_map_eq_zero (m : RingedSpace.stalkModuleCat (kernel φ) x) :
      RingedSpace.moduleStalkMap x φ
          (RingedSpace.moduleStalkMap x (kernel.ι φ) m) = 0 := by
    let ι : kernel φ ⟶ 𝒢 := kernel.ι φ
    have hcomp :
        RingedSpace.moduleStalkMap x ι ≫ RingedSpace.moduleStalkMap x φ =
          RingedSpace.moduleStalkMap x (ι ≫ φ) := by
      change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map ι.val) ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map φ.val) =
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map ι.val) ≫
            ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map φ.val))
      exact ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map_comp
        ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map ι.val)
        ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map φ.val)).symm
    have hzero : RingedSpace.moduleStalkMap x (ι ≫ φ) = 0 := by
      rw [show ι ≫ φ = 0 by simpa [ι] using kernel.condition φ]
      change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map 0 = 0
      exact (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map_zero
        ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).obj (kernel φ).val)
        ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).obj ℋ.val)
    have hm :
        (RingedSpace.moduleStalkMap x ι ≫ RingedSpace.moduleStalkMap x φ) m = 0 := by
      rw [hcomp, hzero]
      rfl
    simpa [ι, ConcreteCategory.comp_apply] using hm
  letI : Subsingleton (RingedSpace.stalkModuleCat (kernel φ) x) := ⟨fun m n ↦ by
    apply hιx
    apply hφx
    rw [hkernel_map_eq_zero m, hkernel_map_eq_zero n]⟩
  -- Proof comment: a subsingleton module object is zero in `ModuleCat`.
  exact ModuleCat.isZero_of_subsingleton (RingedSpace.stalkModuleCat (kernel φ) x)

/-- Helper for Lemma 17.11.7: restricting a finitely presented module sheaf to an open subset
preserves finite presentation. -/
private theorem over_isFinitePresentation
    (ℱ : ModX) [ℱ.IsFinitePresentation] (U : Opens X) :
    (ℱ.over U).IsFinitePresentation := by
  let j : restrictedRingedSpace (X := X) U ⟶ X := restrictedOpenInclusion (X := X) U
  -- Proof comment: `ℱ.over U` is exactly the pullback of `ℱ` along the canonical open immersion
  -- `X|_U ⟶ X`, so finite presentation descends from Lemma `17.11.5`.
  simpa [SheafOfModules.over, RingedSpace.Hom.pullback] using
    (SheafOfModules.RingedSite.pullback_isFinitePresentation
      (TopologicalSpace.Opens.map j.hom.base) (RingedSpace.Hom.toRingCatSheafHom j) ℱ)

/-- Helper for Lemma 17.11.7: the iterated slice module category over `U` and `I` is canonically
equivalent to the ordinary slice module category over `I.left`. -/
private noncomputable def iteratedRestrictionEquivalence
    {U : Opens X} (I : Over U) :
    SheafOfModules (((RingedSpace.ringCatSheaf X).over U).over I) ≌
      SheafOfModules ((RingedSpace.ringCatSheaf X).over I.left) :=
  pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv I)
    (S := ((RingedSpace.ringCatSheaf X).over U).over I)
    (R := (RingedSpace.ringCatSheaf X).over I.left)
    (𝟙 _) (𝟙 _)
    (by ext : 2; exact X.sheaf.1.map_id _)
    (by ext : 2; exact X.sheaf.1.map_id _)

/-- Helper for Lemma 17.11.7: under the canonical iterated-slice equivalence, the free rank-`r`
module on the iterated slice corresponds to the free rank-`r` module on the underlying open. -/
private theorem iteratedRestrictionFreeIso
    (r : ℕ) {U : Opens X} (I : Over U) :
    (((SheafOfModules.free.{u} (ULift.{u} (Fin r)) :
          SheafOfModules (((RingedSpace.ringCatSheaf X).over U).over I)))
        ≅
      (iteratedRestrictionEquivalence (X := X) I).functor.obj
        (SheafOfModules.free.{u} (ULift.{u} (Fin r)) :
          SheafOfModules ((RingedSpace.ringCatSheaf X).over I.left))) := by
  -- Proof comment: the equivalence is induced by identity maps on the restricted ring sheaves, so
  -- the free module with the same basis transports unchanged.
  simpa [iteratedRestrictionEquivalence]
    using ((iteratedRestrictionEquivalence (X := X) I).unitIso.app
      (SheafOfModules.free.{u} (ULift.{u} (Fin r)) :
        SheafOfModules ((RingedSpace.ringCatSheaf X).over I.left))).symm

/-- Helper for Lemma 17.11.7: a rank-`r` trivialization on an iterated restriction
`((ℱ.over U).over I)` is equivalent to a rank-`r` trivialization on the ordinary restriction
`ℱ.over I.left`. -/
private theorem iteratedRestrictionIsoFree_iff
    (ℱ : ModX) (r : ℕ) {U : Opens X} {I : Over U} :
    Nonempty
      (((ℱ.over U).over I) ≅
        (SheafOfModules.free.{u} (ULift.{u} (Fin r)) :
          SheafOfModules (((RingedSpace.ringCatSheaf X).over U).over I))) ↔
      Nonempty
        (ℱ.over I.left ≅
          (SheafOfModules.free.{u} (ULift.{u} (Fin r)) :
            SheafOfModules ((RingedSpace.ringCatSheaf X).over I.left))) := by
  let e := iteratedRestrictionEquivalence (X := X) I
  constructor
  · intro h
    rcases h with ⟨hiso⟩
    -- Proof comment: move the trivialization across the canonical equivalence from the iterated
    -- slice to the ordinary slice, then normalize both endpoints.
    refine ⟨?_⟩
    simpa [e, iteratedRestrictionEquivalence] using
      (e.inverse.mapIso (hiso ≪≫ iteratedRestrictionFreeIso (X := X) r I))
  · intro h
    rcases h with ⟨hiso⟩
    -- Proof comment: transport the ordinary-slice trivialization back to the iterated slice and
    -- compose with the free-side comparison in the opposite direction.
    refine ⟨?_⟩
    simpa [e, iteratedRestrictionEquivalence] using
      (e.functor.mapIso hiso ≪≫ (iteratedRestrictionFreeIso (X := X) r I).symm)

/-- Helper for Lemma 17.11.7: a local rank-`r` trivialization around `x` yields the corresponding
free rank-`r` stalk module at `x`. -/
private theorem stalkFreeIsoOfRankTrivialization
    (ℱ : ModX) (r : ℕ) {U : Opens X} {x : X} (hx : x ∈ U)
    (e : ℱ.over U ≅
      (SheafOfModules.free.{u} (ULift.{u} (Fin r)) :
        SheafOfModules ((RingedSpace.ringCatSheaf X).over U))) :
    Nonempty
      (RingedSpace.stalkModuleCat ℱ x ≅
        (ModuleCat.free (X.presheaf.stalk x)).obj (ULift.{u} (Fin r))) := by
  let XU : RingedSpace := X.restrict U.isOpenEmbedding
  let j : XU ⟶ X := X.ofRestrict U.isOpenEmbedding
  let xU : XU := ⟨x, hx⟩
  let eOver :
      ((RingedSpace.Hom.pullback j).obj ℱ) ≅
        (SheafOfModules.free.{u} (ULift.{u} (Fin r)) : XU.Modules) := by
    -- Proof comment: rewrite the slice restriction `ℱ.over U` as the actual pullback to the
    -- restricted ringed space `X|_U`.
    simpa [SheafOfModules.over, RingedSpace.Hom.pullback] using e
  let eStalk :
      RingedSpace.stalkModuleCat ((RingedSpace.Hom.pullback j).obj ℱ) xU ≅
        RingedSpace.stalkModuleCat
          (SheafOfModules.free.{u} (ULift.{u} (Fin r)) : XU.Modules) xU :=
    (RingedSpace.stalkModuleFunctor (X := XU) xU).mapIso eOver
  -- Proof comment: transfer the neighborhood trivialization to the stalk and then transport back
  -- along the canonical pullback/stalk comparison for the open immersion `j`.
  exact ⟨(RingedSpace.Hom.pullbackStalkIso j ℱ xU).symm ≪≫ by simpa using eStalk⟩

/-- Helper for Lemma 17.11.7: after identifying the source and target with the same standard free
module, a surjective stalk map is automatically bijective. -/
private theorem bijectiveOfSurjectiveConjugateFreeEndomorphism
    {R : Type u} [CommRing R]
    {M N : ModuleCat R} (r : ℕ)
    (f : M ⟶ N)
    (eM : M ≅ (ModuleCat.free R).obj (ULift.{u} (Fin r)))
    (eN : N ≅ (ModuleCat.free R).obj (ULift.{u} (Fin r)))
    (hsurj : Function.Surjective f.hom) :
    Function.Bijective f.hom := by
  let _ : Fintype (ULift.{u} (Fin r)) := inferInstance
  let _ : Module.Finite R ↑((ModuleCat.free R).obj (ULift.{u} (Fin r))) := by
    change Module.Finite R ((ULift.{u} (Fin r)) →₀ R)
    exact Module.Finite.of_basis
      (Finsupp.basisSingleOne :
        Module.Basis (ULift.{u} (Fin r)) R ((ULift.{u} (Fin r)) →₀ R))
  let u :
      (ModuleCat.free R).obj (ULift.{u} (Fin r)) ⟶
        (ModuleCat.free R).obj (ULift.{u} (Fin r)) :=
    eM.inv ≫ f ≫ eN.hom
  have hsurjU : Function.Surjective u.hom := by
    intro y
    obtain ⟨m, hm⟩ := hsurj (eN.inv.hom y)
    refine ⟨eM.hom m, ?_⟩
    change eN.hom (f (eM.inv.hom (eM.hom m))) = y
    simp [hm]
  have hbijU : Function.Bijective u.hom :=
    OrzechProperty.bijective_of_surjective_endomorphism u.hom hsurjU
  constructor
  · intro m₁ m₂ hm
    -- Proof comment: transport equality through the conjugated free endomorphism and then cancel
    -- the chosen free-module identifications.
    have hu :
        u.hom (eM.hom m₁) = u.hom (eM.hom m₂) := by
      simpa [u, hm]
    have heq : eM.hom m₁ = eM.hom m₂ := hbijU.1 hu
    simpa using congrArg eM.inv.hom heq
  · exact hsurj

/-- Helper for Lemma 17.11.7: once a common open `U` and lifts of the chosen stalk basis are
fixed, the remaining proof is to shrink inside `U` until the induced free morphism becomes an
isomorphism, then repackage the nested restriction as an ambient open of `X`. -/
private theorem existsAmbientFreeRestrictionOfLiftedBasis
    (ℱ : ModX) [ℱ.IsFinitePresentation] (x : X) (r : ℕ)
    (e : RingedSpace.stalkModuleCat ℱ x ≅
      (ModuleCat.free (X.presheaf.stalk x)).obj (ULift.{u} (Fin r)))
    {U : Opens X} (hxU : x ∈ U)
    (s : ULift.{u} (Fin r) → ℱ.val.obj (op U))
    (hs : ∀ i,
      TopCat.Presheaf.germ ℱ.val.presheaf U x hxU (s i) =
        e.inv.hom (Finsupp.single i 1)) :
    ∃ (U₀ : Opens X) (_ : x ∈ U₀),
      Nonempty (ℱ.over U₀ ≅ SheafOfModules.free (ULift.{u} (Fin r))) := by
  -- Route correction: the previous attempts kept reopening the same transport seam after each
  -- shrink. The right route is to work on `X|_U`, prove the initial stalk map is an isomorphism
  -- once using Lemma `17.4.2`, transport that fact through later restrictions, and only then
  -- normalize the nested restriction back to an ambient open of `X`.
  -- Proof comment: the executable skeleton is:
  -- 1. form the free morphism `ψ : O_U^r ⟶ ℱ|_U` from the lifted sections `s`;
  -- 2. use the Chapter 17 basis-germ theorem on `X|_U` plus the restricted-stalk comparison to
  --    show `ψ_x` is an isomorphism;
  -- 3. shrink once to make `ψ` epi, apply Lemma `17.11.4` to its kernel, then shrink again to
  --    kill that kernel by Lemma `17.9.5`;
  -- 4. conclude the final restricted morphism is mono and epi, hence an isomorphism;
  -- 5. rewrite the resulting doubly restricted sheaf as restriction to a single ambient open.
  let Y : RingedSpace := restrictedRingedSpace (X := X) U
  let j : Y ⟶ X := restrictedOpenInclusion (X := X) U
  let xU : Y := ⟨x, hxU⟩
  let ψ : SheafOfModules.free.{u} (ULift.{u} (Fin r)) ⟶ ℱ.over U :=
    ((ℱ.over U).freeHomEquiv).symm
      (fun i ↦ overSectionOfOpenSection ℱ U (s i))
  have hSectionTerminal :
      ∀ i : ULift.{u} (Fin r),
        (overSectionOfOpenSection ℱ U (s i)).1 (op (Over.mk (𝟙 U))) = s i := by
    intro i
    -- Proof comment: the chosen restricted global section was built to recover `s i` at the
    -- terminal object of the slice.
    exact overSectionOfOpenSection_terminal (𝒢 := ℱ) (U := U) (s := s i)
  have hψx_bijective :
      Function.Bijective (RingedSpace.moduleStalkMap xU ψ) := by
    -- TODO for Lemma 17.11.7: prove the restricted stalk map is bijective.
    -- The missing bridge is the stalk-germ comparison between
    -- `Γgerm (ℱ.over U).val.presheaf xU ((overSectionOfOpenSection ℱ U (s i)).1 (op ⊤))`
    -- and the ambient germ `TopCat.Presheaf.germ ℱ.val.presheaf U x hxU (s i)` transported across
    -- `RingedSpace.Hom.pullbackStalkIso j ℱ xU`.
    -- Once that bridge is available, `freeHomEquiv_symm_stalk_range_eq_span` and the basis-germ
    -- identities `hs` give surjectivity, and
    -- `bijectiveOfSurjectiveConjugateFreeEndomorphism` upgrades it to bijectivity.
    sorry
  have hψx_epi : Epi (RingedSpace.moduleStalkHom xU ψ) := by
    -- Proof comment: for module maps, bijectivity of the underlying linear map in particular gives
    -- the stalk epimorphism required for the first shrinking step.
    simpa [RingedSpace.moduleStalkHom] using
      (ModuleCat.epi_iff_surjective (RingedSpace.moduleStalkHom xU ψ)).2 hψx_bijective.2
  -- TODO for Lemma 17.11.7: after the stalk-bijectivity step, run the two shrinking theorems on
  -- `Y = X|_U`: first use `exists_open_neighborhood_epi_restriction_of_stalk_epi` with `hψx_epi`,
  -- then apply `isFiniteType_kernel_of_epi_free_of_finitePresentation` and
  -- `exists_open_neighborhood_restriction_isZero_of_stalk_isZero` to kill the kernel, and finally
  -- package the resulting iterated restriction back to an ambient open via
  -- `iteratedRestrictionIsoFree_iff`.
  sorry

/-- Lemma 17.11.7: if a finitely presented `\mathcal O_X`-module has stalk at `x` isomorphic to
the free rank-`r` `\mathcal O_{X, x}`-module, then on some open neighbourhood `U` of `x` its
restriction `ℱ|_U` is isomorphic to the free sheaf `\mathcal O_U^{\oplus r}`. -/
@[stacks 0B8J]
theorem exists_open_neighborhood_free_over_of_stalk_free
    (ℱ : ModX)
    [ℱ.IsFinitePresentation] (x : X) (r : ℕ)
    (hℱx : Nonempty
      (RingedSpace.stalkModuleCat ℱ x ≅
        (ModuleCat.free (X.presheaf.stalk x)).obj (ULift.{u} (Fin r)))) :
    ∃ (U : Opens X) (_ : x ∈ U),
      Nonempty (ℱ.over U ≅ SheafOfModules.free (ULift.{u} (Fin r))) := by
  classical
  rcases hℱx with ⟨e⟩
  rcases existsCommonOpenWithFreeBasisLifts (ℱ := ℱ) x r e with ⟨U, hxU, s, hs⟩
  -- Proof comment: all remaining work now sits in the specialized shrink-and-normalize helper.
  exact existsAmbientFreeRestrictionOfLiftedBasis
    (ℱ := ℱ) (x := x) (r := r) e hxU s hs

end SheafOfModules
