import Mathlib
import StacksProject_2024.Chap12.Definition_12_27_5
import StacksProject_2024.Chap19.«19_2_0_1»
import StacksProject_2024.Chap19.Lemma_19_2_7

open CategoryTheory Limits Opposite
open CategoryTheory.SmallObject
open CategoryTheory.SmallObject.SuccStruct

universe u

section

variable (R : Type u) [Ring R]

/-- The successor structure on `ModuleCat R ⥤ ModuleCat R` determined by the one-step Baer
construction `M ↦ 𝐌(M)`. -/
private noncomputable abbrev baerModuleTransfiniteSuccStruct :
    SuccStruct (ModuleCat R ⥤ ModuleCat R) :=
  SuccStruct.ofNatTrans (baerModuleStepInclusionNatTrans R)

/-- The transfinite Baer functor `N ↦ \mathbf{M}_α(N)`. -/
noncomputable def baerModuleTransfiniteFunctor (α : Ordinal.{u}) :
    ModuleCat R ⥤ ModuleCat R :=
  if hα : α = 0 then
    𝟭 (ModuleCat R)
  else
    letI := Ordinal.toTypeOrderBot hα
    (baerModuleTransfiniteSuccStruct R).iteration α.ToType

notation:max "𝐌_[" α "](" N ")" => Functor.obj (baerModuleTransfiniteFunctor _ α) N

-- Proof sketch: unfold `baerModuleTransfiniteFunctor`; when `α = 0`, the defining `if` chooses the
-- identity functor branch.
/-- At ordinal `0`, the transfinite Baer functor is the identity functor on `ModuleCat R`. -/
private theorem baerModuleTransfiniteFunctor_eq_id (α : Ordinal.{u}) (hα : α = 0) :
    baerModuleTransfiniteFunctor R α = 𝟭 (ModuleCat R) := by
  -- Unfold the defining `if` and select the zero-stage branch.
  subst hα
  simp [baerModuleTransfiniteFunctor]

-- Proof sketch: unfold `baerModuleTransfiniteFunctor`; when `α ≠ 0`, the defining `if` chooses the
-- branch given by the transfinite iteration of the one-step Baer successor structure over
-- `α.ToType`.
/-- For `α ≠ 0`, the transfinite Baer functor is the standard transfinite iteration of the
one-step Baer successor structure over `α.ToType`. -/
private theorem baerModuleTransfiniteFunctor_eq_iteration (α : Ordinal.{u}) (hα : α ≠ 0) :
    baerModuleTransfiniteFunctor R α =
      letI := Ordinal.toTypeOrderBot hα
      (baerModuleTransfiniteSuccStruct R).iteration α.ToType := by
  -- Unfold the defining `if` and select the nonzero branch.
  simp [baerModuleTransfiniteFunctor, hα]

/-- The canonical natural transformation `N ⟶ \mathbf{M}_α(N)`. -/
noncomputable def baerModuleTransfiniteInclusion (α : Ordinal.{u}) :
    𝟭 (ModuleCat R) ⟶ baerModuleTransfiniteFunctor R α :=
  if hα : α = 0 then
    eqToHom (baerModuleTransfiniteFunctor_eq_id R α hα).symm
  else
    letI := Ordinal.toTypeOrderBot hα
    (baerModuleTransfiniteSuccStruct R).ιIteration α.ToType ≫
      eqToHom (baerModuleTransfiniteFunctor_eq_iteration R α hα).symm

notation:max "ι_𝐌[" α "](" N ")" => NatTrans.app (baerModuleTransfiniteInclusion _ α) N

-- Proof sketch: each successor map `\mathbf{M}_β(N) ⟶ \mathbf{M}_{β + 1}(N)` is injective by
-- Lemma `19.2.7 (2)`, and the transfinite stage `N ⟶ \mathbf{M}_α(N)` is obtained by composing
-- these injections and taking the canonical maps into limit-stage colimits.
/-- For every `R`-module `N`, the canonical map `N ⟶ \mathbf{M}_α(N)` is injective. -/
theorem baerModuleTransfiniteInclusion_app_injective
    (α : Ordinal.{u}) (N : ModuleCat R) :
    Function.Injective (ι_𝐌[α](N)).hom := by
  by_cases hα : α = 0
  · -- At stage `0`, the inclusion is the identity map.
    subst hα
    let hobj : (baerModuleTransfiniteFunctor R 0).obj N = N :=
      congrArg (fun F : ModuleCat R ⥤ ModuleCat R ↦ F.obj N)
        (baerModuleTransfiniteFunctor_eq_id R 0 rfl)
    have hmonoEq : Mono (eqToHom hobj.symm) := by infer_instance
    have hinjEq : Function.Injective ((eqToHom hobj.symm).hom) :=
      (ModuleCat.mono_iff_injective _).1 hmonoEq
    simpa [baerModuleTransfiniteInclusion] using hinjEq
  · let Φ : SuccStruct (ModuleCat R ⥤ ModuleCat R) := baerModuleTransfiniteSuccStruct R
    letI := Ordinal.toTypeOrderBot hα
    have hmonoProp :
        Φ.prop ≤ MorphismProperty.monomorphisms (ModuleCat R ⥤ ModuleCat R) := by
      rw [← MorphismProperty.functorCategory_monomorphisms (C := ModuleCat R)
        (J := ModuleCat R)]
      intro F G f hf M
      -- Each successor morphism is objectwise the one-step Baer inclusion.
      cases hf
      simpa [Φ, baerModuleTransfiniteSuccStruct] using
        (ModuleCat.mono_iff_injective _).2 (baerModuleStepInclusion_injective R (F.obj M))
    let htrans :
        (MorphismProperty.monomorphisms (ModuleCat R ⥤ ModuleCat R)).TransfiniteCompositionOfShape
          α.ToType (Φ.ιIteration α.ToType) :=
      (Φ.transfiniteCompositionOfShapeιIteration α.ToType).ofLE hmonoProp
    have hmonoNat : Mono (Φ.ιIteration α.ToType) := by
      letI :
          (MorphismProperty.monomorphisms (ModuleCat R ⥤ ModuleCat R)).IsStableUnderTransfiniteCompositionOfShape
            α.ToType := by infer_instance
      exact
        (CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_le
          (W := MorphismProperty.monomorphisms (ModuleCat R ⥤ ModuleCat R))
          (J := α.ToType)) (Φ.ιIteration α.ToType) htrans.mem
    letI : Mono (Φ.ιIteration α.ToType) := hmonoNat
    have hmonoApp : Mono ((Φ.ιIteration α.ToType).app N) := by infer_instance
    have hinjIter :
        Function.Injective ((Φ.ιIteration α.ToType).app N).hom :=
      (ModuleCat.mono_iff_injective _).1 hmonoApp
    let hobj :
        (baerModuleTransfiniteFunctor R α).obj N = (Φ.iteration α.ToType).obj N :=
      congrArg (fun F : ModuleCat R ⥤ ModuleCat R ↦ F.obj N)
        (baerModuleTransfiniteFunctor_eq_iteration R α hα)
    have hinjEq :
        Function.Injective
          ((eqToHom hobj.symm).hom) := by
      have hmonoEq : Mono (eqToHom hobj.symm) := by infer_instance
      exact (ModuleCat.mono_iff_injective _).1 hmonoEq
    -- The public inclusion is the transfinite iteration map followed by the branch-identifying
    -- isomorphism, so injectivity is preserved.
    simpa [baerModuleTransfiniteInclusion, hα, ModuleCat.hom_comp] using
      hinjEq.comp hinjIter

-- Proof sketch: send a submodule of the ideal `I` to its image in `R`; this is injective because
-- the ideal subtype `I → R` is injective, so the resulting cardinal bound follows from `hα`.
/-- Helper for Theorem 19.2.8: the set of submodules of an ideal has cardinality bounded by the set
of ideals of `R`, so the same cofinality hypothesis applies to each ideal as an `R`-module. -/
private theorem idealSubmoduleCardinal_lt_cof
    (α : Ordinal.{u}) (hα : Cardinal.mk (Ideal R) < α.cof) (I : Ideal R) :
    Cardinal.mk (Submodule R I) < α.cof := by
  have hle : Cardinal.mk (Submodule R I) ≤ Cardinal.mk (Ideal R) := by
    refine Cardinal.mk_le_of_injective (f := fun S : Submodule R I ↦ (S.map I.subtype : Ideal R)) ?_
    intro S T hST
    exact (Submodule.map_injective_of_injective I.injective_subtype) hST
  exact lt_of_le_of_lt hle hα

/-- Helper for Theorem 19.2.8: a family of stage indices of cardinality below `α.cof` has one
common upper bound in `α.ToType`. -/
private theorem existsStageDominatingSmallFamily
    {S : Type u} {α : Ordinal.{u}} (hS : Cardinal.mk S < α.cof) (ι : S → α.ToType) :
    ∃ j : α.ToType, ∀ s : S, ι s ≤ j := by
  -- The supremum of fewer than `α.cof` many ordinals below `α` still lies below `α`.
  let j : α.ToType := Ordinal.ToType.mk
    ⟨⨆ s : S, (ι s : Ordinal),
      Ordinal.iSup_lt_of_lt_cof hS fun s ↦
        (show (ι s : Ordinal) < α from (ι s).toOrd.2)⟩
  refine ⟨j, ?_⟩
  intro s
  -- Each chosen stage contributes to that supremum, so it is below the common bound.
  have hle : (ι s).toOrd ≤ j.toOrd := by
    exact
      show (ι s : Ordinal) ≤ j.toOrd from by
        simpa [j] using Ordinal.le_iSup (fun t : S ↦ (ι t : Ordinal)) s
  simpa [j] using Ordinal.ToType.mk.monotone hle

/-- Helper for Theorem 19.2.8: every element of a colimit of `R`-modules comes from some stage of
the tower. -/
private theorem moduleCatColimitHasStageRepresentative
    (α : Ordinal.{u}) (hα0 : α ≠ 0) (B : α.ToType ⥤ ModuleCat.{u} R)
    (z : ((forget (ModuleCat.{u} R)).obj (colimit B))) :
    ∃ j : α.ToType, ∃ x : B.obj j, ((colimit.ι B j).hom) x = z := by
  letI := Ordinal.toTypeOrderBot hα0
  letI : PreservesFilteredColimits (forget (ModuleCat.{u} R)) := by infer_instance
  let F : α.ToType ⥤ Type u := B ⋙ forget (ModuleCat.{u} R)
  let e : ((forget (ModuleCat.{u} R)).obj (colimit B)) ≅ colimit F :=
    preservesColimitIso (forget (ModuleCat.{u} R)) B
  -- Move the chosen element to the filtered colimit of underlying types.
  let z' : colimit F := e.hom z
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective' z'
  refine ⟨j, x, ?_⟩
  have hmor :
      (forget (ModuleCat.{u} R)).map (colimit.ι B j) ≫ e.hom =
        colimit.ι F j := by
    simpa [F] using ι_preservesColimitIso_hom (G := forget (ModuleCat.{u} R)) (F := B) (j := j)
  have hstage :
      e.hom (((colimit.ι B j).hom) x) = z' := by
    calc
      e.hom (((colimit.ι B j).hom) x) = colimit.ι F j x := by
        simpa [CategoryTheory.types_comp_apply] using congrArg (fun f ↦ f x) hmor
      _ = z' := hx
  -- Pull the stage representative back through the comparison isomorphism.
  simpa [z', e] using congrArg e.inv hstage

/-- Helper for Theorem 19.2.8: if all transition maps in an ordinal-indexed tower of modules are
mono, then each stage coprojection into the colimit is also mono. -/
private theorem colimitIota_mono_of_monoTower
    (α : Ordinal.{u}) (hα0 : α ≠ 0) (B : α.ToType ⥤ ModuleCat.{u} R)
    (hB : ∀ ⦃i j : α.ToType⦄ (f : i ⟶ j), Mono (B.map f)) (j : α.ToType) :
    Mono (colimit.ι B j) := by
  -- Forget to the filtered colimit of underlying types and use injectivity of the transition maps.
  refine (ModuleCat.mono_iff_injective _).2 ?_
  intro x y hxy
  letI := Ordinal.toTypeOrderBot hα0
  letI : PreservesFilteredColimits (forget (ModuleCat.{u} R)) := by infer_instance
  let F : α.ToType ⥤ Type u := B ⋙ forget (ModuleCat.{u} R)
  let e : ((forget (ModuleCat.{u} R)).obj (colimit B)) ≅ colimit F :=
    preservesColimitIso (forget (ModuleCat.{u} R)) B
  have hmor :
      (forget (ModuleCat.{u} R)).map (colimit.ι B j) ≫ e.hom =
        colimit.ι F j := by
    simpa [F] using ι_preservesColimitIso_hom (G := forget (ModuleCat.{u} R)) (F := B) (j := j)
  have hxy' : colimit.ι F j x = colimit.ι F j y := by
    -- Apply the comparison isomorphism to move the equality into the canonical `Type` colimit.
    have hx' :
        e.hom (((colimit.ι B j).hom) x) = colimit.ι F j x := by
      simpa [CategoryTheory.types_comp_apply] using congrArg (fun f ↦ f x) hmor
    have hy' :
        e.hom (((colimit.ι B j).hom) y) = colimit.ι F j y := by
      simpa [CategoryTheory.types_comp_apply] using congrArg (fun f ↦ f y) hmor
    calc
      colimit.ι F j x = e.hom (((colimit.ι B j).hom) x) := hx'.symm
      _ = e.hom (((colimit.ι B j).hom) y) := by simpa using congrArg e.hom hxy
      _ = colimit.ι F j y := hy'
  obtain ⟨k, f, g, hfg⟩ := (Types.FilteredColimit.colimit_eq_iff (F := F)).1 hxy'
  have hfg' : F.map f x = F.map f y := by
    simpa [Subsingleton.elim f g] using hfg
  exact (ModuleCat.mono_iff_injective _).1 (hB f) <| by
    simpa [F] using hfg'

/-- Helper for Theorem 19.2.8: once the image of `f` is contained in the range of the `j`-th
stage coprojection, the map `f` factors through that stage. -/
private theorem factorThroughStage_of_comap_eq_top
    {M : Type u} [AddCommGroup M] [Module R M]
    (α : Ordinal.{u}) (hα0 : α ≠ 0) (B : α.ToType ⥤ ModuleCat.{u} R)
    (hB : ∀ ⦃i j : α.ToType⦄ (f : i ⟶ j), Mono (B.map f))
    {j : α.ToType} (f : ModuleCat.of R M ⟶ colimit B)
    (hTop : Submodule.comap f.hom (LinearMap.range (colimit.ι B j).hom) = ⊤) :
    ∃ g : ModuleCat.of R M ⟶ B.obj j, g ≫ colimit.ι B j = f := by
  have hιmono : Mono (colimit.ι B j) :=
    colimitIota_mono_of_monoTower (R := R) α hα0 B hB j
  have hιinj :
      Function.Injective (colimit.ι B j).hom :=
    (ModuleCat.mono_iff_injective _).1 hιmono
  let eRange : B.obj j ≃ₗ[R] LinearMap.range (colimit.ι B j).hom :=
    LinearEquiv.ofInjective (colimit.ι B j).hom hιinj
  let fRange : M →ₗ[R] LinearMap.range (colimit.ι B j).hom :=
    LinearMap.codRestrict (LinearMap.range (colimit.ι B j).hom) f.hom fun x ↦ by
      -- The top-comap hypothesis says each `f x` already lies in the stage range.
      have hx : x ∈ Submodule.comap f.hom (LinearMap.range (colimit.ι B j).hom) := by
        simpa [hTop]
      exact hx
  let g : ModuleCat.of R M ⟶ B.obj j := ModuleCat.ofHom (eRange.symm.toLinearMap.comp fRange)
  refine ⟨g, ?_⟩
  -- Evaluate pointwise and use that `eRange.symm` is the inverse to the range equivalence.
  ext x
  have hx :
      ((colimit.ι B j).hom) (eRange.symm (fRange x)) = f.hom x := by
    have happly :
        eRange (eRange.symm (fRange x)) = fRange x := by
      exact eRange.apply_symm_apply (fRange x)
    exact congrArg Subtype.val happly
  simpa [g, fRange, LinearMap.comp_apply] using hx

/-- Helper for Theorem 19.2.8: the canonical comparison map from the colimit of Hom-sets is
surjective whenever the source module has fewer submodules than `α.cof`. -/
private theorem colimitPost_surjective_of_submodule_cardinal_lt_cof
    {M : Type u} [AddCommGroup M] [Module R M]
    (α : Ordinal.{u}) (hα0 : α ≠ 0) (hα : Cardinal.mk (Submodule R M) < α.cof)
    (B : α.ToType ⥤ ModuleCat.{u} R)
    (hB : ∀ ⦃i j : α.ToType⦄ (f : i ⟶ j), Mono (B.map f)) :
    Function.Surjective (colimit.post B (coyoneda.obj (op (ModuleCat.of R M)))) := by
  classical
  intro f
  let preimageStage : α.ToType → Submodule R M := fun j ↦
    Submodule.comap f.hom (LinearMap.range (colimit.ι B j).hom)
  have hpreimage_mono : Monotone preimageStage := by
    intro i j hij
    refine Submodule.comap_mono ?_
    intro z hz
    rcases hz with ⟨x, rfl⟩
    refine ⟨(B.map (homOfLE hij)).hom x, ?_⟩
    -- Naturality of the colimit coprojections moves the smaller-stage representative upward.
    simpa [CategoryTheory.types_comp_apply] using
      congrArg (fun t ↦ t x) (colimit.w B (homOfLE hij))
  have hx_mem_some_stage : ∀ x : M, ∃ j : α.ToType, x ∈ preimageStage j := by
    intro x
    obtain ⟨j, y, hy⟩ :=
      moduleCatColimitHasStageRepresentative (R := R) α hα0 B (f.hom x)
    refine ⟨j, ?_⟩
    change f.hom x ∈ LinearMap.range (colimit.ι B j).hom
    exact hy.symm ▸ LinearMap.mem_range_self _ y
  have hrange_lt : Cardinal.mk (Set.range preimageStage) < α.cof := by
    refine lt_of_le_of_lt ?_ hα
    exact Cardinal.mk_le_of_injective
      (f := fun Q : Set.range preimageStage ↦ Q.1)
      (fun _ _ hQ ↦ Subtype.ext hQ)
  let representative : Set.range preimageStage → α.ToType := fun Q ↦ Classical.choose Q.2
  have hrepresentative :
      ∀ Q : Set.range preimageStage, preimageStage (representative Q) = Q.1 := by
    intro Q
    exact Classical.choose_spec Q.2
  obtain ⟨j0, hj0⟩ :=
    existsStageDominatingSmallFamily (S := Set.range preimageStage) (α := α) hrange_lt
      representative
  have htop : preimageStage j0 = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    rcases hx_mem_some_stage x with ⟨j, hxj⟩
    let Q : Set.range preimageStage := ⟨preimageStage j, ⟨j, rfl⟩⟩
    have hleQ : preimageStage j ≤ preimageStage j0 := by
      calc
        preimageStage j = preimageStage (representative Q) := by
          symm
          simpa [Q] using hrepresentative Q
        _ ≤ preimageStage j0 := hpreimage_mono (hj0 Q)
    exact hleQ hxj
  obtain ⟨g, hg⟩ :=
    factorThroughStage_of_comap_eq_top (R := R) (M := M) α hα0 B hB f htop
  refine ⟨colimit.ι (B ⋙ coyoneda.obj (op (ModuleCat.of R M))) j0 g, ?_⟩
  -- A stage factorization is exactly a preimage under the canonical comparison map.
  simpa [hg] using colimit_post_coyoneda_ι_app (ModuleCat.of R M) B j0 g

-- Proof sketch: first view `Φ.ιIteration α.ToType` as a transfinite composition of monomorphisms
-- in the functor category, then restrict that composition to the interval `[i, j]` so that the
-- transition map `i ⟶ j` becomes a bottom-to-top transfinite composition and is therefore mono.
/-- Helper for Theorem 19.2.8: every transition morphism in the evaluated transfinite Baer tower is
monic. -/
private theorem baerModuleEvaluatedTowerMap_mono
    (α : Ordinal.{u}) (hα0 : α ≠ 0) (N : ModuleCat R) :
    letI := Ordinal.toTypeOrderBot hα0
    let Φ : SuccStruct (ModuleCat R ⥤ ModuleCat R) := baerModuleTransfiniteSuccStruct R
    let B := (Φ.iterationFunctor α.ToType) ⋙
      (CategoryTheory.evaluation (C := ModuleCat R) (D := ModuleCat R)).obj N
    ∀ ⦃i j : α.ToType⦄ (f : i ⟶ j), Mono (B.map f) := by
  let Φ : SuccStruct (ModuleCat R ⥤ ModuleCat R) := baerModuleTransfiniteSuccStruct R
  letI := Ordinal.toTypeOrderBot hα0
  let B := (Φ.iterationFunctor α.ToType) ⋙
    (CategoryTheory.evaluation (C := ModuleCat R) (D := ModuleCat R)).obj N
  have hmonoProp :
      Φ.prop ≤ MorphismProperty.monomorphisms (ModuleCat R ⥤ ModuleCat R) := by
    rw [← MorphismProperty.functorCategory_monomorphisms (C := ModuleCat R)
      (J := ModuleCat R)]
    intro F G f hf M
    -- Each successor map is the one-step Baer inclusion on the evaluated module.
    cases hf
    simpa [Φ, baerModuleTransfiniteSuccStruct] using
      (ModuleCat.mono_iff_injective _).2 (baerModuleStepInclusion_injective R (F.obj M))
  let htrans :
      (MorphismProperty.monomorphisms (ModuleCat R ⥤ ModuleCat R)).TransfiniteCompositionOfShape
        α.ToType (Φ.ιIteration α.ToType) :=
    (Φ.transfiniteCompositionOfShapeιIteration α.ToType).ofLE hmonoProp
  change ∀ ⦃i j : α.ToType⦄ (f : i ⟶ j), Mono (B.map f)
  intro i j f
  let hij : i ≤ j := leOfHom f
  let hstage := (htrans.ici i).iic (⟨j, hij⟩ : Set.Ici i)
  letI :
      (MorphismProperty.monomorphisms (ModuleCat R ⥤ ModuleCat R)).IsStableUnderTransfiniteCompositionOfShape
        (Set.Iic (⟨j, hij⟩ : Set.Ici i)) := by
    infer_instance
  have hmonoMap : Mono ((Φ.iterationFunctor α.ToType).map f) := by
    simpa using
      (CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_le
        (W := MorphismProperty.monomorphisms (ModuleCat R ⥤ ModuleCat R))
        (J := Set.Iic (⟨j, hij⟩ : Set.Ici i))) _ hstage.mem
  letI : Mono ((Φ.iterationFunctor α.ToType).map f) := hmonoMap
  simpa [B] using (inferInstance : Mono (((Φ.iterationFunctor α.ToType).map f).app N))

-- Proof sketch: Proposition 19.2.5 makes the represented Hom functor preserve the colimit of the
-- mono tower `B`, so the given ideal map comes from some stage representative in that Hom-colimit.
/-- Helper for Theorem 19.2.8: every map from an ideal into the transfinite Baer object factors
through some stage of the evaluated tower. -/
private theorem baerModuleStageFactorOfSmall
    (α : Ordinal.{u}) (hα0 : α ≠ 0) (hα : Cardinal.mk (Ideal R) < α.cof)
    (N : ModuleCat R) (I : Ideal R) :
    letI := Ordinal.toTypeOrderBot hα0
    ∀ (φ : ModuleCat.of R I ⟶ ((baerModuleTransfiniteSuccStruct R).iteration α.ToType).obj N),
      let Φ : SuccStruct (ModuleCat R ⥤ ModuleCat R) := baerModuleTransfiniteSuccStruct R
      let B := (Φ.iterationFunctor α.ToType) ⋙
        (CategoryTheory.evaluation (C := ModuleCat R) (D := ModuleCat R)).obj N
      let e := colimitObjIsoColimitCompEvaluation (Φ.iterationFunctor α.ToType) N
      ∃ j : α.ToType, ∃ ψ : ModuleCat.of R I ⟶ B.obj j, ψ ≫ colimit.ι B j ≫ e.inv = φ := by
  intro φ
  let Φ : SuccStruct (ModuleCat R ⥤ ModuleCat R) := baerModuleTransfiniteSuccStruct R
  letI := Ordinal.toTypeOrderBot hα0
  let B := (Φ.iterationFunctor α.ToType) ⋙
    (CategoryTheory.evaluation (C := ModuleCat R) (D := ModuleCat R)).obj N
  let e := colimitObjIsoColimitCompEvaluation (Φ.iterationFunctor α.ToType) N
  change ∃ j : α.ToType, ∃ ψ : ModuleCat.of R I ⟶ B.obj j, ψ ≫ colimit.ι B j ≫ e.inv = φ
  have hB : ∀ ⦃i j : α.ToType⦄ (f : i ⟶ j), Mono (B.map f) :=
    baerModuleEvaluatedTowerMap_mono R α hα0 N
  have hsurj :
      Function.Surjective (colimit.post B (coyoneda.obj (op (ModuleCat.of R I)))) := by
    -- Apply the local smallness-to-surjectivity bridge directly to the ideal module `I`.
    exact
      colimitPost_surjective_of_submodule_cardinal_lt_cof
        (R := R) (M := I) α hα0 (idealSubmoduleCardinal_lt_cof R α hα I) B hB
  obtain ⟨x, hx⟩ := hsurj (φ ≫ e.hom)
  obtain ⟨j, ψ, rfl⟩ := Types.jointly_surjective' x
  refine ⟨j, ψ, ?_⟩
  have hfactorToColimit : ψ ≫ colimit.ι B j = φ ≫ e.hom := by
    simpa using (colimit_post_coyoneda_ι_app (ModuleCat.of R I) B j ψ).symm.trans hx
  calc
    ψ ≫ colimit.ι B j ≫ e.inv = φ ≫ e.hom ≫ e.inv := by
      simpa [Category.assoc] using congrArg (fun k ↦ k ≫ e.inv) hfactorToColimit
    _ = φ := by
      apply (cancel_mono e.hom).1
      rw [Category.assoc, Category.assoc, e.inv_hom_id, Category.comp_id]
      rfl

-- Proof sketch: use Lemma 19.2.7 to extend across the ideal inclusion into the one-step Baer
-- object of stage `j`, identify that one-step Baer object with stage `j + 1`, and compose into
-- the colimit/top object.
/-- Helper for Theorem 19.2.8: a factorization through stage `j` extends one successor step and
therefore extends all the way to the top transfinite Baer object. -/
private theorem baerModuleStageExtensionToTop
    (α : Ordinal.{u}) (hα0 : α ≠ 0) (hsucc : Order.IsSuccLimit α)
    (N : ModuleCat R) (I : Ideal R) :
    letI := Ordinal.toTypeOrderBot hα0
    ∀ {j : α.ToType}
      (ψ : ModuleCat.of R I ⟶
        (((baerModuleTransfiniteSuccStruct R).iterationFunctor α.ToType) ⋙
          (CategoryTheory.evaluation (C := ModuleCat R) (D := ModuleCat R)).obj N).obj j),
      let Φ : SuccStruct (ModuleCat R ⥤ ModuleCat R) := baerModuleTransfiniteSuccStruct R
      let B := (Φ.iterationFunctor α.ToType) ⋙
        (CategoryTheory.evaluation (C := ModuleCat R) (D := ModuleCat R)).obj N
      let e := colimitObjIsoColimitCompEvaluation (Φ.iterationFunctor α.ToType) N
      ∃ g : ModuleCat.of R R ⟶ (Φ.iteration α.ToType).obj N,
        ModuleCat.ofHom I.subtype ≫ g = ψ ≫ colimit.ι B j ≫ e.inv := by
  intro j ψ
  let Φ : SuccStruct (ModuleCat R ⥤ ModuleCat R) := baerModuleTransfiniteSuccStruct R
  letI := Ordinal.toTypeOrderBot hα0
  letI : NoMaxOrder α.ToType := Ordinal.toType_noMax_of_succ_lt fun a ha ↦ hsucc.succ_lt ha
  let B := (Φ.iterationFunctor α.ToType) ⋙
    (CategoryTheory.evaluation (C := ModuleCat R) (D := ModuleCat R)).obj N
  let e := colimitObjIsoColimitCompEvaluation (Φ.iterationFunctor α.ToType) N
  change ∃ g : ModuleCat.of R R ⟶ (Φ.iteration α.ToType).obj N,
      ModuleCat.ofHom I.subtype ≫ g = ψ ≫ colimit.ι B j ≫ e.inv
  have hj : ¬ IsMax j := not_isMax j
  have hsuccMap :
      B.map (homOfLE (Order.le_succ j)) =
        baerModuleStepInclusion R (B.obj j) ≫ ((Φ.iterationFunctorObjSuccIso j hj).app N).inv := by
    -- Route correction: evaluate the generic successor-map formula once so that the extension
    -- step can remain on the one-step Baer API from Lemma 19.2.7.
    simpa [B, Φ, baerModuleTransfiniteSuccStruct] using
      congrArg (fun η ↦ η.app N) (Φ.iterationFunctor_map_succ j hj)
  let gStage : ModuleCat.of R R ⟶ B.obj (Order.succ j) :=
    baerModuleIdealLift R (B.obj j) I ψ.hom ≫ ((Φ.iterationFunctorObjSuccIso j hj).app N).inv
  let g : ModuleCat.of R R ⟶ (Φ.iteration α.ToType).obj N :=
    gStage ≫ colimit.ι B (Order.succ j) ≫ e.inv
  refine ⟨g, ?_⟩
  have hlift :
      ModuleCat.ofHom I.subtype ≫ gStage = ψ ≫ B.map (homOfLE (Order.le_succ j)) := by
    simp [gStage, hsuccMap, Category.assoc]
    simpa [Category.assoc] using
      congrArg
        (fun k ↦ k ≫ ((Φ.iterationFunctorObjSuccIso j hj).app N).inv)
        (baerModuleIdealLift_comp_subtype R (B.obj j) I ψ.hom).w
  calc
    ModuleCat.ofHom I.subtype ≫ g =
        ψ ≫ B.map (homOfLE (Order.le_succ j)) ≫ colimit.ι B (Order.succ j) ≫ e.inv := by
          simpa [g, Category.assoc] using
            congrArg (fun k ↦ k ≫ colimit.ι B (Order.succ j) ≫ e.inv) hlift
    _ = ψ ≫ colimit.ι B j ≫ e.inv := by
          change ψ ≫ (B.map (homOfLE (Order.le_succ j)) ≫ colimit.ι B (Order.succ j)) ≫ e.inv =
            ψ ≫ colimit.ι B j ≫ e.inv
          rw [colimit.w B (homOfLE (Order.le_succ j))]

-- Proof sketch: use Baer's criterion. Given an ideal map `I ⟶ \mathbf{M}_α(N)`, apply
-- Proposition `19.2.5` to the module `I` to factor it through some earlier stage
-- `\mathbf{M}_β(N)` with `β < α`, then use Lemma `19.2.7 (3)` to extend it across
-- `I ↪ R` into `\mathbf{M}_{β + 1}(N) ⟶ \mathbf{M}_α(N)`.
/-- If the cofinality of `α` is larger than the cardinality of the set of ideals of `R`, then
`\mathbf{M}_α(N)` is an injective `R`-module. -/
theorem baerModuleTransfiniteFunctor_obj_injective
    (α : Ordinal.{u}) (hα : Cardinal.mk (Ideal R) < α.cof) (N : ModuleCat R) :
    Injective (𝐌_[α](N)) := by
  have hideals_ne_zero : Cardinal.mk (Ideal R) ≠ 0 :=
    Cardinal.mk_ne_zero_iff.2 ⟨⊥⟩
  have hcof_gt_one : 1 < α.cof := by
    exact lt_of_le_of_lt (Cardinal.one_le_iff_ne_zero.2 hideals_ne_zero) hα
  have hsucc : Order.IsSuccLimit α := (Ordinal.one_lt_cof_iff).1 hcof_gt_one
  have hα0 : α ≠ 0 := by
    intro hzero
    subst hzero
    simpa using hcof_gt_one
  let Φ : SuccStruct (ModuleCat R ⥤ ModuleCat R) := baerModuleTransfiniteSuccStruct R
  letI := Ordinal.toTypeOrderBot hα0
  let hobj :
      𝐌_[α](N) = (Φ.iteration α.ToType).obj N :=
    congrArg (fun F : ModuleCat R ⥤ ModuleCat R ↦ F.obj N)
      (baerModuleTransfiniteFunctor_eq_iteration R α hα0)
  have hmod : Module.Injective R ((Φ.iteration α.ToType).obj N) := by
    refine (Module.Baer.iff_injective).1 ?_
    intro I φ
    -- Factor the ideal map through a stage of the transfinite tower, then extend one step and
    -- compose into the top object.
    obtain ⟨j, ψ, hψ⟩ :=
      baerModuleStageFactorOfSmall R α hα0 hα N I (ModuleCat.ofHom φ)
    obtain ⟨g, hg⟩ :=
      baerModuleStageExtensionToTop R α hα0 hsucc N I (j := j) ψ
    refine ⟨g.hom, ?_⟩
    intro x hxI
    have hcomp : ModuleCat.ofHom I.subtype ≫ g = ModuleCat.ofHom φ := by
      simpa using hg.trans hψ
    have hcomp_hom : (ModuleCat.ofHom I.subtype ≫ g).hom = φ := by
      simpa using congrArg ModuleCat.Hom.hom hcomp
    exact LinearMap.congr_fun hcomp_hom ⟨x, hxI⟩
  have hinjectiveIter : Injective ((Φ.iteration α.ToType).obj N) :=
    (Module.injective_iff_injective_object R ((Φ.iteration α.ToType).obj N)).mp hmod
  simpa [hobj] using hinjectiveIter

/-- Theorem 19.2.8: if the cofinality of `α` is strictly larger than the cardinality of the set of
ideals of `R`, then the transfinite Baer construction `N ↦ \mathbf{M}_α(N)` together with the
canonical maps `N ⟶ \mathbf{M}_α(N)` yields functorial injective embeddings of `R`-modules. -/
@[reducible]
noncomputable def baerModule_hasFunctorialInjectiveEmbeddings
    (α : Ordinal.{u}) (hα : Cardinal.mk (Ideal R) < α.cof) :
    HasFunctorialInjectiveEmbeddings (ModuleCat R) where
  J := (baerModuleTransfiniteInclusion R α).arrowFunctor
  leftFunc_comp_J := NatTrans.arrowFunctor_leftFunc_comp _
  mono_obj N := (ModuleCat.mono_iff_injective _).mpr
    (baerModuleTransfiniteInclusion_app_injective R α N)
  injective_obj N := baerModuleTransfiniteFunctor_obj_injective R α hα N

end
