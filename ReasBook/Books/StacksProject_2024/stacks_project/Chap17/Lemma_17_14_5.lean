import Mathlib
import StacksProject_2024.Chap17.Definition_17_14_1
import StacksProject_2024.Chap17.Lemma_17_3_1
import StacksProject_2024.Chap06.Lemma_6_26_4

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

attribute [local instance] CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback

/- Domain-style sampling for Lemma 17.14.5:
- primary domain: finite locally free sheaves of modules of constant rank on a ringed space;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `SheafOfModules.IsLocallyFree`,
  `SheafOfModules.IsFiniteLocallyFree`,
  `SheafOfModules.IsFiniteLocallyFreeOfRank`,
  `SheafOfModules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank`;
- best owner abstraction:
  the ambient owner category `RingedSpace.Modules X` together with the owner predicate
  `SheafOfModules.IsFiniteLocallyFreeOfRank r ℱ`;
- primitive data:
  only the module sheaves `ℱ`, `𝒢`, the common rank `r`, and the owner instances asserting their
  local rank-`r` trivializations;
- derived API:
  the source-facing comparison `IsIso φ ↔ Epi φ` for a morphism between such sheaves.

Source/core/bridge triage:
- `source-facing`: the Stacks Project criterion that a morphism between finite locally free sheaves
  of the same rank is an isomorphism exactly when it is surjective;
- `core/canonical`: the ambient owner `RingedSpace.Modules X` and the owner predicate
  `SheafOfModules.IsFiniteLocallyFreeOfRank`;
- `bridge/view`: this file should use those owners directly rather than restating the ambient
  module category by its raw `SheafOfModules (RingedSpace.ringCatSheaf X)` presentation. -/

variable {X : RingedSpace.{u}} {ℱ 𝒢 : X.Modules}

/-- Helper for Lemma 17.14.5: the stalk map on underlying sections of a morphism of
`\mathcal O_X`-modules. -/
noncomputable abbrev moduleStalkMap
    (x : X) {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    TopCat.Presheaf.stalk ℱ.val.presheaf x ⟶ TopCat.Presheaf.stalk 𝒢.val.presheaf x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map φ.val)

/-- Helper for Lemma 17.14.5: the stalk map preserves addition because it is induced by the stalk
functor on additive presheaves. -/
private theorem moduleStalkMap_map_add
    (x : X) {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢)
    (m n : ↑(TopCat.Presheaf.stalk ℱ.val.presheaf x)) :
    RingedSpace.moduleStalkMap x φ (m + n) =
      RingedSpace.moduleStalkMap x φ m + RingedSpace.moduleStalkMap x φ n := by
  simpa using (RingedSpace.moduleStalkMap x φ).hom.map_add m n

/-- Helper for Lemma 17.14.5: the stalk map carries germs to the germs of the mapped sections. -/
theorem moduleStalkMap_germ
    {ℱ 𝒢 : X.Modules} (x : X) (φ : ℱ ⟶ 𝒢)
    (U : Opens X) (hx : x ∈ U) (s : ℱ.val.obj (op U)) :
    RingedSpace.moduleStalkMap x φ (TopCat.Presheaf.germ ℱ.val.presheaf U x hx s) =
      TopCat.Presheaf.germ 𝒢.val.presheaf U x hx ((φ.val.app (op U)) s) := by
  simpa [RingedSpace.moduleStalkMap] using
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
      ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map φ.val) s)

/-- Helper for Lemma 17.14.5: the stalk map is linear over the stalk ring. -/
private theorem moduleStalkMap_map_smul
    (x : X) {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢)
    (r : X.presheaf.stalk x)
    (m : ↑(RingedSpace.stalkModuleCat ℱ x)) :
    RingedSpace.moduleStalkMap x φ (r • m) =
      r • RingedSpace.moduleStalkMap x φ m := by
  obtain ⟨U, hxU, rU, hrU⟩ := TopCat.Presheaf.germ_exist X.presheaf x r
  obtain ⟨V, hxV, mV, hmV⟩ := TopCat.Presheaf.germ_exist ℱ.val.presheaf x m
  let W : Opens X := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  let iWU : W ⟶ U := homOfLE inf_le_left
  let iWV : W ⟶ V := homOfLE inf_le_right
  let rW : X.presheaf.obj (op W) := X.presheaf.map iWU.op rU
  let mW : ℱ.val.obj (op W) := ℱ.val.map iWV.op mV
  have hrW : X.presheaf.germ W x hxW rW = r := by
    -- Proof comment: represent the scalar by a germ on the common refinement `W = U ∩ V`.
    calc
      X.presheaf.germ W x hxW rW = X.presheaf.germ U x hxU rU := by
        simpa [rW] using TopCat.Presheaf.germ_res_apply X.presheaf iWU x hxW rU
      _ = r := hrU
  have hmW : TopCat.Presheaf.germ ℱ.val.presheaf W x hxW mW = m := by
    -- Proof comment: represent the module element by a germ on the same common refinement.
    calc
      TopCat.Presheaf.germ ℱ.val.presheaf W x hxW mW =
          TopCat.Presheaf.germ ℱ.val.presheaf V x hxV mV := by
            simpa [mW] using TopCat.Presheaf.germ_res_apply ℱ.val.presheaf iWV x hxW mV
      _ = m := hmV
  rw [← hrW, ← hmW]
  -- Proof comment: once both inputs are represented on the same open, the result follows from
  -- germ compatibility with scalar multiplication and the sectionwise linearity of `φ`.
  calc
    RingedSpace.moduleStalkMap x φ
        (X.presheaf.germ W x hxW rW •
          TopCat.Presheaf.germ ℱ.val.presheaf W x hxW mW) =
      RingedSpace.moduleStalkMap x φ
        (TopCat.Presheaf.germ ℱ.val.presheaf W x hxW (rW • mW)) := by
          exact congrArg (RingedSpace.moduleStalkMap x φ)
            (PresheafOfModules.germ_smul ℱ.val x W hxW rW mW).symm
    _ =
      TopCat.Presheaf.germ 𝒢.val.presheaf W x hxW
        ((φ.val.app (op W)) (rW • mW)) := by
          rw [RingedSpace.moduleStalkMap_germ x φ W hxW (rW • mW)]
    _ =
      TopCat.Presheaf.germ 𝒢.val.presheaf W x hxW
        (rW • (φ.val.app (op W)) mW) := by
          simpa using (φ.val.app (op W)).hom.map_smul rW mW
    _ =
      X.presheaf.germ W x hxW rW •
        TopCat.Presheaf.germ 𝒢.val.presheaf W x hxW ((φ.val.app (op W)) mW) := by
          exact PresheafOfModules.germ_smul 𝒢.val x W hxW rW ((φ.val.app (op W)) mW)
    _ =
      X.presheaf.germ W x hxW rW •
        RingedSpace.moduleStalkMap x φ
          (TopCat.Presheaf.germ ℱ.val.presheaf W x hxW mW) := by
            rw [RingedSpace.moduleStalkMap_germ x φ W hxW mW]

/-- Helper for Lemma 17.14.5: the stalk map promoted to a morphism in the module category over
`\mathcal O_{X,x}`. -/
noncomputable def moduleStalkHom
    (x : X) {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    RingedSpace.stalkModuleCat ℱ x ⟶ RingedSpace.stalkModuleCat 𝒢 x :=
  ModuleCat.ofHom
    { toFun := RingedSpace.moduleStalkMap x φ
      map_add' := RingedSpace.moduleStalkMap_map_add x φ
      map_smul' := by
        intro r m
        simpa using RingedSpace.moduleStalkMap_map_smul x φ r m }

/-- Helper for Lemma 17.14.5: stalks define a functor from `\mathcal O_X`-modules to modules over
the stalk ring `\mathcal O_{X,x}`. -/
noncomputable def stalkModuleFunctor (x : X) :
    X.Modules ⥤ ModuleCat (X.presheaf.stalk x) where
  obj ℱ := RingedSpace.stalkModuleCat ℱ x
  map φ := RingedSpace.moduleStalkHom x φ
  map_id ℱ := by
    -- Proof comment: reduce equality of module morphisms to the identity law for the additive
    -- presheaf stalk functor.
    apply ModuleCat.hom_ext
    ext m
    change RingedSpace.moduleStalkMap x (𝟙 ℱ) m = m
    change
      (ConcreteCategory.hom
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
            ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map
              (𝟙 ℱ.val)))) m = m
    rw [(PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map_id]
    have hid :
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (𝟙
            ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).obj ℱ.val))) =
          𝟙 _ := by
      exact (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map_id _
    rw [hid]
    rfl
  map_comp φ ψ := by
    -- Proof comment: reduce to the composition law for the additive-presheaf stalk functor.
    apply ModuleCat.hom_ext
    ext m
    change RingedSpace.moduleStalkMap x (φ ≫ ψ) m =
      RingedSpace.moduleStalkMap x ψ (RingedSpace.moduleStalkMap x φ m)
    change
      (ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map
            (φ ≫ ψ).val))) m =
      (ConcreteCategory.hom
          (((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
              ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map φ.val)) ≫
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
              ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map ψ.val)))) m
    calc
      (ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map
            (φ ≫ ψ).val))) m =
      (ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map φ.val) ≫
            ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map ψ.val)))) m := by
              rfl
      _ =
        (ConcreteCategory.hom
          (((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
              ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map φ.val)) ≫
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
              ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map ψ.val)))) m := by
                simp

-- Route correction: keep this file dependency-light and follow the source proof through local
-- rank-`r` trivializations, rather than importing the unfinished stalk helper file.

/-- Helper for Lemma 17.14.5: an isomorphism of `\mathcal O_X`-modules is automatically an
epimorphism. -/
private theorem epi_of_isIso_module_hom
    (φ : ℱ ⟶ 𝒢) [IsIso φ] :
    Epi φ := by
  -- The forward implication is purely categorical.
  infer_instance

/-- Helper for Lemma 17.14.5: exact short complexes of `\mathcal O_X`-modules stay exact after
forgetting to sheaves of abelian groups. -/
private theorem toAbelianSheaf_map_exact
    (S : ShortComplex X.Modules) (hS : S.Exact) :
    (S.map (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X))).Exact := by
  let toAbelianSheaf : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
    SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)
  letI : toAbelianSheaf.PreservesZeroMorphisms := by
    change (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).PreservesZeroMorphisms
    exact { map_zero _ _ := by rfl }
  let stalkAddCommGrpFunctor : X → X.Modules ⥤ AddCommGrpCat.{u} :=
    fun x ↦
      toAbelianSheaf ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  letI : ∀ x : X, (stalkAddCommGrpFunctor x).PreservesZeroMorphisms := by
    intro x
    let G : TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
      TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    letI : G.PreservesZeroMorphisms := by infer_instance
    simpa [stalkAddCommGrpFunctor, G] using
      (inferInstance : (toAbelianSheaf ⋙ G).PreservesZeroMorphisms)
  -- Proof comment: exactness is detected stalkwise on module sheaves, and stalk exactness is
  -- unchanged after forgetting the module structure to abelian groups.
  refine (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map toAbelianSheaf)).mpr ?_
  intro x
  have hx : (RingedSpace.stalkShortComplex S x).Exact :=
    (RingedSpace.ringedSpaceModule_exact_iff_stalkwise_exact S).mp hS x
  simpa [stalkAddCommGrpFunctor] using hx

/-- Helper for Lemma 17.14.5: an additive-sheaf morphism is epic exactly when all of its stalk
maps are surjective. -/
private theorem additive_sheaf_epi_iff_stalk_surjective
    {A B : TopCat.Sheaf AddCommGrpCat.{u} X} (φ : A ⟶ B) :
    Epi φ ↔
      ∀ x : X,
        Function.Surjective (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ.hom).hom) := by
  -- Proof comment: for sheaves of abelian groups, epimorphy is the same as local surjectivity,
  -- and local surjectivity is detected on stalks.
  rw [← TopCat.Sheaf.isLocallySurjective_iff_epi φ]
  simpa using TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks φ.hom

/-- Helper for Lemma 17.14.5: an epimorphism of `\mathcal O_X`-modules remains an epimorphism on
the underlying additive sheaf. -/
private theorem underlying_epi_of_module_epi
    (φ : ℱ ⟶ 𝒢) [Epi φ] :
    Epi ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map φ) := by
  let toAbelianSheaf : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
    SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)
  letI : toAbelianSheaf.PreservesZeroMorphisms := by
    change (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).PreservesZeroMorphisms
    exact { map_zero _ _ := by rfl }
  letI : toAbelianSheaf.PreservesEpimorphisms :=
    CategoryTheory.Functor.preservesEpimorphisms_of_map_exact toAbelianSheaf
      (fun S hS ↦ toAbelianSheaf_map_exact (X := X) S hS)
  -- Proof comment: once exactness of short complexes survives forgetting, `map_epi` becomes
  -- available for the underlying additive-sheaf functor.
  exact Functor.map_epi toAbelianSheaf φ

/-- Helper for Lemma 17.14.5: an epimorphism of `\mathcal O_X`-modules is surjective on every
stalk. -/
private theorem stalk_surjective_of_epi
    (φ : ℱ ⟶ 𝒢) [Epi φ] (x : X) :
    Function.Surjective (RingedSpace.moduleStalkMap x φ) := by
  have hunderlying :
      Epi ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map φ) :=
    underlying_epi_of_module_epi (X := X) φ
  -- Proof comment: the additive-sheaf epi criterion translates the categorical epimorphism into
  -- surjectivity of the induced map on the stalk at `x`.
  have hsurj :=
    (additive_sheaf_epi_iff_stalk_surjective
      (X := X) ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map φ)).1
      hunderlying x
  simpa [RingedSpace.moduleStalkMap] using hsurj

/-- Helper for Lemma 17.14.5: stalkwise injectivity of a module-sheaf morphism forces the
original morphism to be a monomorphism. -/
private theorem mono_of_stalkwise_injective
    (φ : ℱ ⟶ 𝒢)
    (hφ :
      ∀ x : X, Function.Injective (RingedSpace.moduleStalkMap x φ)) :
    Mono φ := by
  let toAbelianSheaf : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
    SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)
  have hmonoUnderlying : Mono (toAbelianSheaf.map φ) := by
    refine (TopCat.Presheaf.mono_iff_stalk_mono (toAbelianSheaf.map φ)).2 ?_
    intro x
    -- Proof comment: injectivity of the module stalk map is exactly injectivity of the underlying
    -- additive stalk map after forgetting scalars.
    exact (AddCommGrpCat.mono_iff_injective _).2 <| by
      simpa [RingedSpace.moduleStalkMap, toAbelianSheaf] using hφ x
  let _ : Mono (toAbelianSheaf.map φ) := hmonoUnderlying
  refine ⟨?_⟩
  intro Z g h hcomp
  -- Proof comment: cancel the mono after forgetting to additive sheaves, then reflect equality of
  -- morphisms back through the faithful forgetful functor.
  have hmapEq : toAbelianSheaf.map g = toAbelianSheaf.map h :=
    (cancel_mono (toAbelianSheaf.map φ)).1 <| by
      simpa using congrArg (fun k ↦ toAbelianSheaf.map k) hcomp
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext s
  simpa [toAbelianSheaf, PresheafOfModules.toPresheaf] using
    congrArg (fun k ↦ (k.hom.app U) s) hmapEq

/-- Helper for Lemma 17.14.5: under the common rank-`r` finite locally free hypotheses, an
epimorphism should induce a bijection on each stalk map. -/
private noncomputable def restrictedOverEquivalence
    {U : Opens X} :
    SheafOfModules ((RingedSpace.ringCatSheaf X).over U) ≌
      RingedSpace.Modules (X.restrict U.isOpenEmbedding) :=
  pushforwardPushforwardEquivalence (U.overEquivalence)
    (S := (RingedSpace.ringCatSheaf X).over U)
    (R := RingedSpace.ringCatSheaf (X.restrict U.isOpenEmbedding))
    (𝟙 _)
    (𝟙 _)
    (by
      ext : 2
      exact X.sheaf.1.map_id _)
    (by
      ext : 2
      exact X.sheaf.1.map_id _)

/-- Helper for Lemma 17.14.5: a rank-`r` local trivialization identifies the stalk with the
standard free module of rank `r` over the stalk ring. -/
private theorem stalkFreeIsoOfRankTrivialization
    (r : ℕ) {U : Opens X} {x : X} (hx : x ∈ U)
    (e : ℱ.over U ≅
      (SheafOfModules.free.{u} (ULift.{u} (Fin r)) :
        SheafOfModules ((RingedSpace.ringCatSheaf X).over U))) :
    Nonempty
      (RingedSpace.stalkModuleCat ℱ x ≅
        (ModuleCat.free (X.presheaf.stalk x)).obj (ULift.{u} (Fin r))) := by
  let XU : RingedSpace := X.restrict U.isOpenEmbedding
  let j : XU ⟶ X := X.ofRestrict U.isOpenEmbedding
  let xU : XU := ⟨x, hx⟩
  let eRestrict :
      (restrictedOverEquivalence (X := X) (U := U)).functor.obj (ℱ.over U) ≅
        (restrictedOverEquivalence (X := X) (U := U)).functor.obj
          (SheafOfModules.free.{u} (ULift.{u} (Fin r)) :
            SheafOfModules ((RingedSpace.ringCatSheaf X).over U)) :=
    (restrictedOverEquivalence (X := X) (U := U)).functor.mapIso e
  let eOver :
      ((RingedSpace.Hom.pullback j).obj ℱ) ≅
        (SheafOfModules.free.{u} (ULift.{u} (Fin r)) : XU.Modules) := by
    -- Proof comment: transport the slice-site trivialization across the canonical equivalence
    -- between `Over U` and the restricted ringed space `X|_U`.
    simpa [restrictedOverEquivalence, SheafOfModules.over, RingedSpace.Hom.pullback] using
      eRestrict
  let eStalk :
      RingedSpace.stalkModuleCat ((RingedSpace.Hom.pullback j).obj ℱ) xU ≅
        RingedSpace.stalkModuleCat
          (SheafOfModules.free.{u} (ULift.{u} (Fin r)) : XU.Modules) xU :=
    (RingedSpace.stalkModuleFunctor (X := XU) xU).mapIso eOver
  -- Proof comment: transfer the neighborhood trivialization to the restricted stalk and then
  -- move back to the ambient stalk with the canonical open-immersion pullback comparison.
  exact ⟨(RingedSpace.Hom.pullbackStalkIso j ℱ xU).symm ≪≫ by simpa using eStalk⟩

/-- Helper for Lemma 17.14.5: after identifying the source and target with the same standard free
module, a surjective stalk map is bijective by the finite-module Orzech criterion. -/
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
    -- Proof comment: transport equality through the conjugated endomorphism on the standard free
    -- module and cancel the chosen isomorphisms.
    have hu :
        u.hom (eM.hom m₁) = u.hom (eM.hom m₂) := by
      simpa [u, hm]
    have heq : eM.hom m₁ = eM.hom m₂ := hbijU.1 hu
    simpa using congrArg eM.inv.hom heq
  · exact hsurj

/-- Helper for Lemma 17.14.5: under the common rank-`r` finite locally free hypotheses, an
epimorphism should induce a bijection on each stalk map. -/
private theorem stalk_bijective_of_epi_same_rank
    (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r ℱ]
    [SheafOfModules.IsFiniteLocallyFreeOfRank r 𝒢]
    (φ : ℱ ⟶ 𝒢) [Epi φ] :
    ∀ x : X, Function.Bijective (RingedSpace.moduleStalkMap x φ) := by
  intro x
  rcases SheafOfModules.IsFiniteLocallyFreeOfRank.exists_open_neighborhood_iso_free
      (ℱ := ℱ) (r := r) x with
    ⟨Uℱ, hxUℱ, hUℱ⟩
  rcases hUℱ with ⟨eUℱ⟩
  rcases SheafOfModules.IsFiniteLocallyFreeOfRank.exists_open_neighborhood_iso_free
      (ℱ := 𝒢) (r := r) x with
    ⟨U𝒢, hxU𝒢, hU𝒢⟩
  rcases hU𝒢 with ⟨eU𝒢⟩
  rcases stalkFreeIsoOfRankTrivialization (X := X) (ℱ := ℱ) r hxUℱ eUℱ with ⟨eℱ⟩
  rcases stalkFreeIsoOfRankTrivialization (X := X) (ℱ := 𝒢) r hxU𝒢 eU𝒢 with ⟨e𝒢⟩
  -- Proof comment: both stalks are now identified with the same standard free rank-`r` module, so
  -- the surjective stalk map is a surjective endomorphism of a finite module after conjugation.
  simpa [RingedSpace.moduleStalkHom, RingedSpace.moduleStalkMap] using
    bijectiveOfSurjectiveConjugateFreeEndomorphism (r := r)
      (f := RingedSpace.moduleStalkHom x φ) eℱ e𝒢
      (stalk_surjective_of_epi (X := X) φ x)

/-- Helper for Lemma 17.14.5: if the underlying additive sheaf map is stalkwise bijective, then
the original module-sheaf morphism is an isomorphism. -/
private theorem isIso_of_toSheaf_stalkwise_bijective
    (φ : ℱ ⟶ 𝒢)
    (hφ : ∀ x : X,
      Function.Bijective
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom))) :
    IsIso φ := by
  let ψ : (SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ ⟶
      (SheafOfModules.toSheaf X.ringCatSheaf).obj 𝒢 :=
    (SheafOfModules.toSheaf X.ringCatSheaf).map φ
  have hψ : IsIso ψ := by
    -- Proof comment: the generic sheaf criterion upgrades stalkwise bijectivity of the
    -- underlying additive sheaf map to a global isomorphism.
    exact (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso (f := ψ)).2
      (fun x ↦ (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).2 (hφ x))
  let _ : IsIso ψ := hψ
  -- Proof comment: forgetting the module structure reflects isomorphisms, so the original
  -- morphism in `X.Modules` is already an isomorphism.
  exact isIso_of_reflects_iso φ (SheafOfModules.toSheaf X.ringCatSheaf)

variable (X)

-- Proof sketch: the forward implication is categorical. For the converse, surjectivity may be
-- checked on stalks, where both source and target become free modules of rank `r` over the local
-- ring `𝒪_{X,x}`; then Algebra, Lemma `10.16.4` upgrades surjectivity to bijectivity, and stalkwise
-- bijectivity implies that `φ` is an isomorphism.
/-- Lemma 17.14.5: for a morphism `φ : \mathcal F \to \mathcal G` of finite locally free
`\mathcal O_X`-modules of the same rank `r` on a ringed space `(X,\mathcal O_X)`, `φ` is an
isomorphism if and only if it is surjective, i.e. an epimorphism. -/
theorem isIso_iff_epi_of_isFiniteLocallyFreeOfRank
    (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r ℱ]
    [SheafOfModules.IsFiniteLocallyFreeOfRank r 𝒢]
    (φ : ℱ ⟶ 𝒢) :
    IsIso φ ↔ Epi φ := by
  constructor
  · intro hφ
    -- The easy direction only uses that isomorphisms are epimorphisms.
    let _ : IsIso φ := hφ
    exact epi_of_isIso_module_hom φ
  · intro hφ
    let _ : Epi φ := hφ
    have hstalk :
        ∀ x : X, Function.Bijective (RingedSpace.moduleStalkMap x φ) :=
      stalk_bijective_of_epi_same_rank (X := X) r φ
    -- Proof comment: after forgetting to the additive sheaf, the stalk maps are still exactly the
    -- same maps, so the generic stalkwise-bijective criterion yields the global isomorphism.
    exact isIso_of_toSheaf_stalkwise_bijective (X := X) (φ := φ) <| by
      intro x
      simpa [RingedSpace.moduleStalkMap] using hstalk x

end AlgebraicGeometry.RingedSpace
