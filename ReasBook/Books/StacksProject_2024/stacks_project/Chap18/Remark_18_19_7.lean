import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap07.Lemma_7_23_1
import StacksProject_2024.Chap07.Remark_7_25_10
import StacksProject_2024.Chap18.Remark_18_19_6

open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u

section PresheafLevel

variable {C : Type u} [Category.{u} C] (𝒪 : Cᵒᵖ ⥤ RingCat.{u}) (U : C)

namespace PresheafLocalizedExtensionByZero

/-- Helper for Remark 18.19.7: the discrete family of terminal objects in the indexing category
computing the value of the left Kan extension at `V`. -/
private abbrev indexFunctor
    (U V : C) : Discrete (V ⟶ U) ⥤ CostructuredArrow (Over.forget U).op (op V) :=
  Discrete.functor fun φ ↦
    CostructuredArrow.mk
      (show (Over.forget U).op.obj (op (Over.mk φ)) ⟶ op V from 𝟙 (op V))

/-- Helper for Remark 18.19.7: the `Over U` object carried by a costructured arrow over `op V`. -/
private abbrev overObj
    {U V : C} (X : CostructuredArrow (Over.forget U).op (op V)) : Over U :=
  X.left.unop

/-- Helper for Remark 18.19.7: the leg `V ⟶ A` in the underlying triangle `V ⟶ A ⟶ U`. -/
private abbrev leg
    {U V : C} (X : CostructuredArrow (Over.forget U).op (op V)) :
    V ⟶ (overObj X).left :=
  X.hom.unop

/-- Helper for Remark 18.19.7: the composite arrow `V ⟶ U` attached to a costructured arrow. -/
private abbrev composite
    {U V : C} (X : CostructuredArrow (Over.forget U).op (op V)) : V ⟶ U :=
  leg X ≫ (overObj X).hom

/-- Helper for Remark 18.19.7: the discrete index remembered by a costructured arrow. -/
private abbrev index
    {U V : C} (X : CostructuredArrow (Over.forget U).op (op V)) : Discrete (V ⟶ U) :=
  Discrete.mk (composite X)

/-- Helper for Remark 18.19.7: the canonical morphism from an arbitrary indexing object to the
distinguished terminal object in its fiber. -/
private abbrev terminalHom
    (U V : C) {X : CostructuredArrow (Over.forget U).op (op V)} :
    X ⟶ (indexFunctor U V).obj (index X) :=
  CostructuredArrow.homMk
    ((show Over.mk (composite X) ⟶ overObj X from Over.homMk (leg X)).op)
    (by
      simp [indexFunctor, index, leg])

/-- Helper for Remark 18.19.7: any morphism in the costructured-arrow category preserves the
composite `V ⟶ U` of the underlying commutative triangle. -/
private lemma composite_eq_of_map
    (U V : C) {X Y : CostructuredArrow (Over.forget U).op (op V)} (hom : X ⟶ Y) :
    composite X = composite Y := by
  let triangle : overObj Y ⟶ overObj X := hom.left.unop
  have hleg : leg Y ≫ triangle.left = leg X := by
    have h := congrArg Quiver.Hom.unop (CostructuredArrow.w hom)
    simpa [triangle] using h
  have hw : triangle.left ≫ (overObj X).hom = (overObj Y).hom := Over.w triangle
  dsimp [composite]
  calc
    leg X ≫ (overObj X).hom = (leg Y ≫ triangle.left) ≫ (overObj X).hom := by
      rw [hleg]
    _ = leg Y ≫ (triangle.left ≫ (overObj X).hom) := by rw [Category.assoc]
    _ = leg Y ≫ (overObj Y).hom := by
      simpa [Category.assoc] using congrArg (fun k ↦ leg Y ≫ k) hw

/-- Helper for Remark 18.19.7: a morphism into the discrete inclusion is indexed by the composite
arrow of the source triangle. -/
private lemma composite_eq_of_hom
    (U V : C) {X : CostructuredArrow (Over.forget U).op (op V)}
    {φ : V ⟶ U} (hom : X ⟶ (indexFunctor U V).obj (Discrete.mk φ)) :
    composite X = φ := by
  simpa [indexFunctor, composite, leg, overObj] using composite_eq_of_map U V hom

/-- Helper for Remark 18.19.7: after fixing the composite `V ⟶ U`, the morphism into the chosen
terminal object is obtained by reindexing `terminalHom`. -/
private def homToIndex
    (U V : C) (X : CostructuredArrow (Over.forget U).op (op V))
    (φ : V ⟶ U) (hφ : composite X = φ) :
    X ⟶ (indexFunctor U V).obj (Discrete.mk φ) := by
  cases hφ
  exact terminalHom U V

/-- Helper for Remark 18.19.7: the chosen terminal morphism in each fiber is unique. -/
private lemma hom_eq_terminalHom
    (U V : C) (X : CostructuredArrow (Over.forget U).op (op V))
    (hom : X ⟶ (indexFunctor U V).obj (index X)) :
    hom = terminalHom U V := by
  ext
  exact by
    apply Quiver.Hom.unop_inj
    apply CommaMorphism.ext
    · have h := congrArg Quiver.Hom.unop (CostructuredArrow.w hom)
      simpa [indexFunctor] using h
    · simp [Over.homMk]

/-- Helper for Remark 18.19.7: the reindexed terminal morphism is also unique. -/
private lemma hom_eq_homToIndex
    (U V : C) (X : CostructuredArrow (Over.forget U).op (op V))
    (φ : V ⟶ U) (hφ : composite X = φ)
    (hom : X ⟶ (indexFunctor U V).obj (Discrete.mk φ)) :
    hom = homToIndex U V X φ hφ := by
  cases hφ
  simpa [homToIndex] using hom_eq_terminalHom U V X hom

/-- Helper for Remark 18.19.7: forgetting a costructured triangle keeps only its composite
`V ⟶ U`. -/
private abbrev compositeFunctor
    (U V : C) :
    CostructuredArrow (Over.forget U).op (op V) ⥤ Discrete (V ⟶ U) where
  obj X := Discrete.mk (composite X)
  map hom := Discrete.eqToHom (composite_eq_of_map U V hom)

/-- Helper for Remark 18.19.7: the discrete inclusion of the chosen terminal objects is right
adjoint to the functor remembering the composite `V ⟶ U`. -/
private def compositeIndexAdjunction (U V : C) :
    compositeFunctor U V ⊣ indexFunctor U V :=
  Adjunction.mkOfHomEquiv
    { homEquiv := by
        intro X φ
        cases φ with
        | mk ψ =>
            refine
              { toFun := fun hom ↦ homToIndex U V X ψ (Discrete.eq_of_hom hom)
                invFun := fun hom ↦ Discrete.eqToHom (composite_eq_of_hom U V hom)
                left_inv := ?_
                right_inv := ?_ }
            · intro hom
              apply Subsingleton.elim
            · intro hom
              simpa using
                (hom_eq_homToIndex U V X ψ (composite_eq_of_hom U V hom) hom).symm
      homEquiv_naturality_left_symm := by
        intro X' X φ hom k
        apply Subsingleton.elim
      homEquiv_naturality_right := by
        intro X Y Y' hom g
        cases Y with
        | mk ψ =>
            cases Y' with
            | mk ψ' =>
                have h :=
                  (hom_eq_homToIndex U V X ψ'
                    (by simpa using Discrete.eq_of_hom (hom ≫ g))
                    (homToIndex U V X ψ (Discrete.eq_of_hom hom) ≫
                      (indexFunctor U V).map g)).symm
                simpa [homToIndex] using congrArg CommaMorphism.left h }

/-- Helper for Remark 18.19.7: the discrete inclusion of the selected terminal objects is final. -/
private theorem indexFunctor_final (U V : C) : Functor.Final (indexFunctor U V) := by
  let _ : (indexFunctor U V).IsRightAdjoint :=
    ⟨⟨compositeFunctor U V, ⟨compositeIndexAdjunction U V⟩⟩⟩
  infer_instance

/-- Helper for Remark 18.19.7: after restricting to the final discrete subcategory, the colimit
diagram is literally the family `φ ↦ A(V \xrightarrow{φ} U)`. -/
private abbrev indexFunctorProjIso
    (U : C) (A : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}) (V : C) :
    indexFunctor U V ⋙ CostructuredArrow.proj (Over.forget U).op (op V) ⋙ A ≅
      Discrete.functor (fun φ : V ⟶ U ↦ A.obj (op (Over.mk φ))) := by
  refine Discrete.natIso ?_
  intro φ
  exact Iso.refl _

/-- Helper for Remark 18.19.7: the additive left Kan extension along `(Over.forget U).op`
evaluated at `V` is the coproduct over all arrows `V ⟶ U`. -/
noncomputable def localized_leftKanExtension_eval_iso_coproduct
    (A : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}) (V : C) :
    (((Over.forget U).op.lan.obj A).obj (op V)) ≅
      (∐ fun φ : V ⟶ U ↦ A.obj (op (Over.mk φ))) := by
  letI : Functor.Final (indexFunctor U V) := indexFunctor_final U V
  -- Proof comment: this repeats the source Remark 7.25.10 skeleton verbatim in
  -- `AddCommGrpCat`: evaluate the left Kan extension as a colimit over the costructured-arrow
  -- category, replace that category by the final discrete family indexed by `V ⟶ U`, and read the
  -- resulting colimit as the coproduct of the corresponding fibers.
  simpa using
    ((Over.forget U).op.leftKanExtensionObjIsoColimit A (op V) ≪≫
      (Functor.Final.colimitIso
        (indexFunctor U V)
        (CostructuredArrow.proj (Over.forget U).op (op V) ⋙ A)).symm ≪≫
      HasColimit.isoOfNatIso (indexFunctorProjIso U A V))

/-- Helper for Remark 18.19.7: forgetting the module coproduct at `V` gives the coproduct of the
underlying additive groups of the summands. -/
noncomputable def localized_coproduct_forget_matches_module_coproduct
    (𝒢 : PresheafOfModules ((Over.forget U).op ⋙ 𝒪)) (V : C) :
    (∐ fun φ : V ⟶ U ↦
      (forget₂ (ModuleCat (𝒪.obj (op V))) AddCommGrpCat).obj
        (𝒢.obj (op (Over.mk φ)))) ≅
      (forget₂ (ModuleCat (𝒪.obj (op V))) AddCommGrpCat).obj
        (∐ fun φ : V ⟶ U ↦ 𝒢.obj (op (Over.mk φ))) :=
  asIso <|
    sigmaComparison
      (forget₂ (ModuleCat (𝒪.obj (op V))) AddCommGrpCat)
      (fun φ : V ⟶ U ↦ 𝒢.obj (op (Over.mk φ)))

end PresheafLocalizedExtensionByZero

/- Domain-style sampling for Remark 18.19.7:
- primary domain: localization of presheaves of modules via restriction and its two Kan-extension
  adjoints along `Over.forget U`;
- sampled owner declarations:
  `PresheafOfModules.pullbackPushforwardAdjunction`,
  `PresheafOfModules.pullback`,
  `PresheafOfModules.pushforward`,
  `Functor.IsLeftAdjoint`,
  `Functor.rightAdjoint`,
  `SheafOfModules.forget`,
  `SheafOfModules.pushforward`;
- best owner abstraction:
  the direct canonical localized owners
  `PresheafOfModules.pushforward (𝟙 ((Over.forget U).op ⋙ 𝒪))`,
  `PresheafOfModules.pullback (𝟙 ((Over.forget U).op ⋙ 𝒪))`,
  the generic right-adjoint owner
  `(PresheafOfModules.pushforward (𝟙 ((Over.forget U).op ⋙ 𝒪))).rightAdjoint`,
  and, on the sheaf side below,
  `SheafOfModules.pushforward (SheafOfModules.pushforwardOver U)`;
- primitive data: the ring presheaf `𝒪` on `C` and the object `U : C`;
- derived API: the presheaf right adjoint `j_{U*}`, the objectwise coproduct formula for
  `j_{U!}` as a canonical isomorphism, the exactness of this presheaf-level lower shriek, and
  the sheaf-level commuting square relating forget, presheaf `j_{U!}`, and sheafification.

Source/core/bridge triage:
- `source-facing`: the presheaf localization adjoints `j_{U!} ⊣ j_U^* ⊣ j_{U*}`, the exactness
  of `j_{U!}`, and the objectwise formula for `j_{U!}`;
- `core/canonical`:
  `PresheafOfModules.pullbackPushforwardAdjunction (𝟙 ((Over.forget U).op ⋙ 𝒪))`,
  `PresheafOfModules.pullback (𝟙 ((Over.forget U).op ⋙ 𝒪))`,
  `PresheafOfModules.pushforward (𝟙 ((Over.forget U).op ⋙ 𝒪))`, and
  `Functor.IsLeftAdjoint` / `Functor.rightAdjoint` for that localized restriction,
  `SheafOfModules.pushforward (SheafOfModules.pushforwardOver U)`;
- `bridge/view`: the coproduct formula for `j_{U!}` and, below, the sheafification square for
  `j_{U!}` after forgetting to additive sheaves.

This file should therefore reuse the direct canonical localized owners instead of exporting local
aliases for them, expose `j_{U*}` through the generic `IsLeftAdjoint` / `.rightAdjoint` owner,
keep the source-facing exactness and coproduct statements for presheaf `j_{U!}`, and state the
sheaf-level `j_{U!}` comparison as the source square involving forget and sheafification.
-/

/- Remark 18.19.7: on presheaves, localized restriction `j_U^*` is the canonical pushforward
owner on modules over `𝒪_U`. -/
#check (PresheafOfModules.pushforward (𝟙 ((Over.forget U).op ⋙ 𝒪)) :
  PresheafOfModules 𝒪 ⥤ PresheafOfModules ((Over.forget U).op ⋙ 𝒪))

/- The presheaf lower shriek `j_{U!}` is the canonical left adjoint
`PresheafOfModules.pullback (𝟙 𝒪_U)` to this restriction functor. -/
#check (PresheafOfModules.pullbackPushforwardAdjunction (𝟙 ((Over.forget U).op ⋙ 𝒪)) :
  PresheafOfModules.pullback (𝟙 ((Over.forget U).op ⋙ 𝒪)) ⊣
    PresheafOfModules.pushforward (𝟙 ((Over.forget U).op ⋙ 𝒪)))

/-- Remark 18.19.7: the localized restriction functor `j_U^*` has a right adjoint. We keep this
at the theorem level here: the canonical owner is `Functor.IsLeftAdjoint` for
`PresheafOfModules.pushforward (𝟙 ((Over.forget U).op ⋙ 𝒪))`. -/
theorem presheafLocalizedRestriction_hasRightAdjoint :
    Functor.IsLeftAdjoint (PresheafOfModules.pushforward (𝟙 ((Over.forget U).op ⋙ 𝒪))) := by
  -- TODO: the missing owner bridge is the presheaf-module analogue of the sheaf-side
  -- `pushforwardOver` adjunction, packaging the right-Kan-extension/coextension functor that is
  -- right adjoint to localized restriction.
  sorry

-- Proof sketch: this is exactly Lemma `18.19.3` for the chaotic topology, where every presheaf is
-- already a sheaf. Equivalently, `j_{U!}` is the canonical pullback owner for the identity map on
-- the localized ring presheaf, and the source remark records that this lower shriek is exact.
/-- Remark 18.19.7 also records that the presheaf-level extension-by-zero functor
`j_{U!} = PresheafOfModules.pullback (𝟙 𝒪_U)` is exact. -/
theorem presheafLocalizedExtensionByZero_exact :
    exactFunctor _ _ (PresheafOfModules.pullback (𝟙 ((Over.forget U).op ⋙ 𝒪))) := by
  -- TODO: the missing owner theorem is the presheaf analogue of
  -- `sheafOfModules_pushforward_exact_of_isAlmostCocontinuous`, or an exactness bridge deduced
  -- from the explicit sigma formula once the additive left-Kan model is connected to modules.
  sorry

/-- Helper for Remark 18.19.7: forget the localized module presheaf to its underlying additive
presheaf on `Over U`. -/
private abbrev presheaf_localized_underlying_addCommGrp
    (𝒢 : PresheafOfModules ((Over.forget U).op ⋙ 𝒪)) :
    (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (PresheafOfModules.toPresheaf ((Over.forget U).op ⋙ 𝒪)).obj 𝒢

/-- Helper for Remark 18.19.7: the additive group underlying the value of `j_{U!} 𝒢` at `V`. -/
private abbrev presheaf_localized_pullback_eval_point
    (𝒢 : PresheafOfModules ((Over.forget U).op ⋙ 𝒪)) (V : C) :
    AddCommGrpCat.{u} :=
  (forget₂ (ModuleCat (𝒪.obj (op V))) AddCommGrpCat).obj
    (((PresheafOfModules.pullback (𝟙 ((Over.forget U).op ⋙ 𝒪))).obj 𝒢).obj (op V))

/-- Helper for Remark 18.19.7: the forgotten module-valued pullback at `V` is the additive
left-Kan extension value at `V`. This isolates the point-level transport mismatch before comparing
the explicit source cocone with the canonical colimit cocone. -/
private abbrev presheaf_localized_pullback_eval_point_iso_leftKanObj
    (𝒢 : PresheafOfModules ((Over.forget U).op ⋙ 𝒪)) (V : C) :
    presheaf_localized_pullback_eval_point (𝒪 := 𝒪) (U := U) 𝒢 V ≅
      (((Over.forget U).op.lan.obj
          (presheaf_localized_underlying_addCommGrp (𝒪 := 𝒪) (U := U) 𝒢)).obj (op V)) :=
  sorry

/-- Helper for Remark 18.19.7: the explicit pullback-evaluation cocone leg is the canonical
left-Kan leg, transported back along the point-level comparison isomorphism. -/
private noncomputable abbrev presheaf_localized_pullback_eval_cocone_leg
    (𝒢 : PresheafOfModules ((Over.forget U).op ⋙ 𝒪)) (V : C)
    (X : CostructuredArrow (Over.forget U).op (op V)) :
    ((CostructuredArrow.proj (Over.forget U).op (op V) ⋙
        presheaf_localized_underlying_addCommGrp (𝒪 := 𝒪) (U := U) 𝒢).obj X) ⟶
      presheaf_localized_pullback_eval_point (𝒪 := 𝒪) (U := U) 𝒢 V :=
  (((Over.forget U).op.leftKanExtensionUnit
      (presheaf_localized_underlying_addCommGrp (𝒪 := 𝒪) (U := U) 𝒢)).app X.left) ≫
    (((Over.forget U).op.lan.obj
        (presheaf_localized_underlying_addCommGrp (𝒪 := 𝒪) (U := U) 𝒢)).map X.hom) ≫
      (presheaf_localized_pullback_eval_point_iso_leftKanObj
        (𝒪 := 𝒪) (U := U) 𝒢 V).inv

/-- Helper for Remark 18.19.7: the transported left-Kan legs form a cocone over the
costructured-arrow indexing diagram. -/
private lemma presheaf_localized_pullback_eval_cocone_leg_naturality
    (𝒢 : PresheafOfModules ((Over.forget U).op ⋙ 𝒪)) (V : C)
    {X Y : CostructuredArrow (Over.forget U).op (op V)} (f : X ⟶ Y) :
    ((CostructuredArrow.proj (Over.forget U).op (op V) ⋙
        presheaf_localized_underlying_addCommGrp (𝒪 := 𝒪) (U := U) 𝒢).map f) ≫
      presheaf_localized_pullback_eval_cocone_leg (𝒪 := 𝒪) (U := U) 𝒢 V Y =
        presheaf_localized_pullback_eval_cocone_leg (𝒪 := 𝒪) (U := U) 𝒢 V X := by
  -- Proof comment: naturality is the naturality of the left-Kan unit, followed by the defining
  -- commutative-triangle relation in the costructured-arrow category.
  let F :=
    presheaf_localized_underlying_addCommGrp (𝒪 := 𝒪) (U := U) 𝒢
  let η := (Over.forget U).op.leftKanExtensionUnit F
  let lanF := (Over.forget U).op.lan.obj F
  let i := (presheaf_localized_pullback_eval_point_iso_leftKanObj
    (𝒪 := 𝒪) (U := U) 𝒢 V).inv
  have hw : ((Over.forget U).op.map f.left) ≫ Y.hom = X.hom := by
    simpa using CostructuredArrow.w f
  change
    F.map f.left ≫
        presheaf_localized_pullback_eval_cocone_leg (𝒪 := 𝒪) (U := U) 𝒢 V Y =
      presheaf_localized_pullback_eval_cocone_leg (𝒪 := 𝒪) (U := U) 𝒢 V X
  simp only [presheaf_localized_pullback_eval_cocone_leg, F]
  calc
    F.map f.left ≫ η.app Y.left ≫ lanF.map Y.hom ≫ i
        = η.app X.left ≫ lanF.map ((Over.forget U).op.map f.left) ≫ lanF.map Y.hom ≫ i := by
            simpa [Functor.comp_map, Category.assoc] using
              congrArg
                (fun k ↦ k ≫ lanF.map Y.hom ≫ i)
                (η.naturality f.left)
    _ = η.app X.left ≫ lanF.map (((Over.forget U).op.map f.left) ≫ Y.hom) ≫ i := by
          exact congrArg
            (fun k ↦ η.app X.left ≫ k ≫ i)
            (Functor.map_comp lanF ((Over.forget U).op.map f.left) Y.hom).symm
    _ = η.app X.left ≫ lanF.map X.hom ≫ i := by
          simpa using congrArg (fun k ↦ η.app X.left ≫ lanF.map k ≫ i) hw

/-- Helper for Remark 18.19.7: the point-level comparison extends to the colimit point of the
canonical costructured-arrow cocone. -/
private noncomputable abbrev presheaf_localized_pullback_eval_point_iso_colimit
    (𝒢 : PresheafOfModules ((Over.forget U).op ⋙ 𝒪)) (V : C) :
    presheaf_localized_pullback_eval_point (𝒪 := 𝒪) (U := U) 𝒢 V ≅
      colimit
        (CostructuredArrow.proj (Over.forget U).op (op V) ⋙
          presheaf_localized_underlying_addCommGrp (𝒪 := 𝒪) (U := U) 𝒢) :=
  presheaf_localized_pullback_eval_point_iso_leftKanObj (𝒪 := 𝒪) (U := U) 𝒢 V ≪≫
    (Over.forget U).op.leftKanExtensionObjIsoColimit
      (presheaf_localized_underlying_addCommGrp (𝒪 := 𝒪) (U := U) 𝒢) (op V)

/-- Helper for Remark 18.19.7: after composing with the point-to-colimit comparison, each
transported cocone leg is exactly the canonical colimit injection. -/
private lemma presheaf_localized_pullback_eval_cocone_leg_comp_point_iso_colimit_hom
    (𝒢 : PresheafOfModules ((Over.forget U).op ⋙ 𝒪)) (V : C)
    (X : CostructuredArrow (Over.forget U).op (op V)) :
    presheaf_localized_pullback_eval_cocone_leg (𝒪 := 𝒪) (U := U) 𝒢 V X ≫
      (presheaf_localized_pullback_eval_point_iso_colimit
        (𝒪 := 𝒪) (U := U) 𝒢 V).hom =
        colimit.ι
          (CostructuredArrow.proj (Over.forget U).op (op V) ⋙
            presheaf_localized_underlying_addCommGrp (𝒪 := 𝒪) (U := U) 𝒢) X := by
  -- Proof comment: this is exactly the owner formula for the cocone legs of
  -- `Functor.leftKanExtensionObjIsoColimit`, after canceling the inverse point transport.
  simp only [presheaf_localized_pullback_eval_cocone_leg,
    presheaf_localized_pullback_eval_point_iso_colimit, Category.assoc]
  simpa using
    ((Over.forget U).op.ι_leftKanExtensionObjIsoColimit_hom
      (presheaf_localized_underlying_addCommGrp (𝒪 := 𝒪) (U := U) 𝒢) (op V) X)

/-- Helper for Remark 18.19.7: evaluating the pushed-forward pullback presheaf at
`V \xrightarrow{\varphi} U` agrees with evaluating the pullback presheaf at `V`. -/
private lemma presheaf_localized_unit_component_codomain
    (𝒢 : PresheafOfModules ((Over.forget U).op ⋙ 𝒪)) (V : C) (φ : V ⟶ U) :
    ((PresheafOfModules.pushforward (𝟙 ((Over.forget U).op ⋙ 𝒪))).obj
        ((PresheafOfModules.pullback (𝟙 ((Over.forget U).op ⋙ 𝒪))).obj 𝒢)).obj
      (op (Over.mk φ)) =
      (((PresheafOfModules.pullback (𝟙 ((Over.forget U).op ⋙ 𝒪))).obj 𝒢).obj (op V)) :=
  rfl

/-- Helper for Remark 18.19.7: the unit component at `V \xrightarrow{\varphi} U` lands in the
evaluation of the localized pullback presheaf at `V` after the canonical codomain identification. -/
private noncomputable def presheaf_localized_unit_component
    (𝒢 : PresheafOfModules ((Over.forget U).op ⋙ 𝒪)) (V : C) (φ : V ⟶ U) :
    𝒢.obj (op (Over.mk φ)) ⟶
      (((PresheafOfModules.pullback (𝟙 ((Over.forget U).op ⋙ 𝒪))).obj 𝒢).obj (op V)) :=
  (((PresheafOfModules.pullbackPushforwardAdjunction
      (𝟙 ((Over.forget U).op ⋙ 𝒪))).unit.app 𝒢).app (op (Over.mk φ))) ≫
    eqToHom (presheaf_localized_unit_component_codomain (𝒪 := 𝒪) (U := U) 𝒢 V φ)

/-- Helper for Remark 18.19.7: the source coproduct map into the localized pullback value is
induced summandwise by the adjunction unit `𝒢 ⟶ j_U^* j_{U!} 𝒢`. -/
private noncomputable def presheaf_localized_extensionByZero_desc
    (𝒢 : PresheafOfModules ((Over.forget U).op ⋙ 𝒪)) (V : C) :
    (∐ fun φ : V ⟶ U ↦ 𝒢.obj (op (Over.mk φ))) ⟶
      (((PresheafOfModules.pullback (𝟙 ((Over.forget U).op ⋙ 𝒪))).obj 𝒢).obj (op V)) :=
  Limits.Sigma.desc fun φ ↦ presheaf_localized_unit_component (𝒪 := 𝒪) (U := U) 𝒢 V φ

/-- Helper for Remark 18.19.7: the source-proof cocone computing `j_{U!} 𝒢` at `V`. Its point is
the forgotten value of the pullback owner, and each leg is the adjunction-unit map followed by the
restriction to `V`. -/
private noncomputable def presheaf_localized_pullback_eval_cocone
    (𝒢 : PresheafOfModules ((Over.forget U).op ⋙ 𝒪)) (V : C) :
    Cocone
      (CostructuredArrow.proj (Over.forget U).op (op V) ⋙
        presheaf_localized_underlying_addCommGrp (𝒪 := 𝒪) (U := U) 𝒢) :=
  { pt := presheaf_localized_pullback_eval_point (𝒪 := 𝒪) (U := U) 𝒢 V
    ι :=
      { app := fun X ↦ presheaf_localized_pullback_eval_cocone_leg (𝒪 := 𝒪) (U := U) 𝒢 V X
        naturality := fun _ _ f ↦
          presheaf_localized_pullback_eval_cocone_leg_naturality
            (𝒪 := 𝒪) (U := U) 𝒢 V f } }

/-- Helper for Remark 18.19.7: the transported explicit cocone is canonically isomorphic to the
chosen colimit cocone for the costructured-arrow diagram. -/
private noncomputable def presheaf_localized_pullback_eval_cocone_iso_colimitCocone_spec
    (𝒢 : PresheafOfModules ((Over.forget U).op ⋙ 𝒪)) (V : C) :
    presheaf_localized_pullback_eval_cocone (𝒪 := 𝒪) (U := U) 𝒢 V ≅
      colimit.cocone
        (CostructuredArrow.proj (Over.forget U).op (op V) ⋙
          presheaf_localized_underlying_addCommGrp (𝒪 := 𝒪) (U := U) 𝒢) := by
  -- Proof comment: package the point comparison with the owner cocone-leg formula so that the
  -- entire source cocone is visibly the canonical colimit cocone.
  refine Cocone.ext
    (presheaf_localized_pullback_eval_point_iso_colimit (𝒪 := 𝒪) (U := U) 𝒢 V) ?_
  intro X
  exact presheaf_localized_pullback_eval_cocone_leg_comp_point_iso_colimit_hom
    (𝒪 := 𝒪) (U := U) 𝒢 V X

/-- Helper for Remark 18.19.7: the explicit pullback-evaluation cocone should be the colimit
computing the left Kan extension value at `V`. -/
private noncomputable def presheaf_localized_pullback_eval_cocone_iso_colimitCocone
    (𝒢 : PresheafOfModules ((Over.forget U).op ⋙ 𝒪)) (V : C) :
    presheaf_localized_pullback_eval_cocone (𝒪 := 𝒪) (U := U) 𝒢 V ≅
      colimit.cocone
        (CostructuredArrow.proj (Over.forget U).op (op V) ⋙
          presheaf_localized_underlying_addCommGrp (𝒪 := 𝒪) (U := U) 𝒢) :=
  presheaf_localized_pullback_eval_cocone_iso_colimitCocone_spec
    (𝒪 := 𝒪) (U := U) 𝒢 V

/-- Helper for Remark 18.19.7: once the explicit cocone is identified with the canonical colimit
cocone, its colimit property is transported directly from `colimit.isColimit`. -/
private noncomputable def presheaf_localized_pullback_eval_isColimit_spec
    (𝒢 : PresheafOfModules ((Over.forget U).op ⋙ 𝒪)) (V : C) :
    IsColimit (presheaf_localized_pullback_eval_cocone (𝒪 := 𝒪) (U := U) 𝒢 V) := by
  -- Proof comment: the cocone isomorphism above reduces the explicit source cocone to the chosen
  -- colimit cocone, so the universal property is inherited verbatim.
  refine (colimit.isColimit _).ofIsoColimit <|
    (presheaf_localized_pullback_eval_cocone_iso_colimitCocone
      (𝒪 := 𝒪) (U := U) 𝒢 V
    ).symm

/-- Helper for Remark 18.19.7: the explicit pullback-evaluation cocone should be the colimit
computing the left Kan extension value at `V`. -/
private noncomputable def presheaf_localized_pullback_eval_isColimit
    (𝒢 : PresheafOfModules ((Over.forget U).op ⋙ 𝒪)) (V : C) :
    IsColimit (presheaf_localized_pullback_eval_cocone (𝒪 := 𝒪) (U := U) 𝒢 V) :=
  presheaf_localized_pullback_eval_isColimit_spec (𝒪 := 𝒪) (U := U) 𝒢 V

/-- The value of presheaf extension by zero at `V` is canonically isomorphic to the coproduct of
the fibers over all arrows `V ⟶ U`. This is the module-valued counterpart of the Chapter 7
left-Kan-extension formula for localization. -/
noncomputable def presheafLocalizedExtensionByZero_objIsoSigma
    (𝒢 : PresheafOfModules ((Over.forget U).op ⋙ 𝒪)) (V : C) :
    (((PresheafOfModules.pullback (𝟙 ((Over.forget U).op ⋙ 𝒪))).obj 𝒢).obj (op V)) ≅
      (∐ fun φ : V ⟶ U ↦ 𝒢.obj (op (Over.mk φ))) := by
  -- TODO: once the forgotten coproduct comparison is proved, reflect the
  -- resulting additive-group isomorphism back along the forgetful functor
  -- `ModuleCat (𝒪.obj (op V)) ⥤ AddCommGrpCat`.
  sorry

end PresheafLevel

section SheafComparison

open SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] [HasBinaryProducts C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

/- In the final clause of Remark 18.19.7, the underlying additive-sheaf comparison for module
extension by zero is already the Chapter 18 owner `ringedSiteLocalizedExtensionByZero_toSheaf`
from Remark 18.19.6, so this file reuses that owner directly instead of a parallel comparison
wrapper. -/
#check (ringedSiteLocalizedExtensionByZero_toSheaf J 𝒪 U :
  ringedSiteLocalizedExtensionByZero J 𝒪 U ⋙
      SheafOfModules.toSheaf (ringSheaf J 𝒪) ≅
    SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U)) ⋙
      (Over.star U).sheafPushforwardContinuous AddCommGrpCat.{u} J (J.over U))

end SheafComparison
