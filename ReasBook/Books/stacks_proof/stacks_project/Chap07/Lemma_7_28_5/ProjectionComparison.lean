import Mathlib
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Limits.Types.Multiequalizer
import Mathlib.CategoryTheory.UnivLE
import stacks_proof.stacks_project.Chap07.Lemma_7_28_5.Topology
import stacks_proof.stacks_project.Chap07.Lemma_7_28_5.TypeSheafification

open CategoryTheory
open CategoryTheory.Limits
universe u₁ u₂ u₃ v₁ v₂ v₃ t w

noncomputable section

namespace CategoryTheory

attribute [local instance] Types.instConcreteCategory
attribute [local instance] Types.instFunLike

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (u : C ⥤ D) (V : D)

local notation "j" => CostructuredArrow.proj u V
local notation "uOver" => CostructuredArrow.toOver u V
local notation "J'" => cocontinuousOverTopologyCore J u V

noncomputable def cocontinuousOver_costructuredArrow_toOver_equivalence
    (Y : Over V) :
    CostructuredArrow uOver Y ≌ CostructuredArrow u Y.left :=
  CostructuredArrow.costructuredArrowToOverEquivalence u Y

/-- Helper for Lemma 7.28.5: restricting a sheaf along `j` evaluates on an object of
`CostructuredArrow u V` by forgetting to its underlying object of `C`. -/
theorem cocontinuousOver_projection_restrict_obj
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    (ℱ : Sheaf J (Type t)) (X : CostructuredArrow u V) :
    (((Functor.sheafPushforwardContinuous j (Type t) J' J).obj ℱ).obj.obj (Opposite.op X)) =
      ℱ.obj.obj (Opposite.op X.left) := by
  -- Continuous pushforward along `j` is restriction of the underlying presheaf along `j.op`.
  rfl

/-- Helper for Lemma 7.28.5: after restricting a sheaf on `D` along `u`, the only nontrivial
comparison on the `j`-side is the continuous sheafification map. -/
noncomputable def cocontinuousOver_projection_specializedComparison
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)] :
    sheafToPresheaf K (Type t) ⋙
        (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type t)).obj u.op ⋙
        (Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ Cᵒᵖ (Type t)).obj
          (CostructuredArrow.proj u V).op ⋙
        presheafToSheaf J' (Type t) ⟶
      sheafToPresheaf K (Type t) ⋙
        (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type t)).obj u.op ⋙
        presheafToSheaf J (Type t) ⋙
        Functor.sheafPushforwardContinuous j (Type t) J' J :=
  Functor.whiskerLeft
    (sheafToPresheaf K (Type t) ⋙
      (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type t)).obj u.op)
    ((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison J' J)

/-- Helper for Lemma 7.28.5: precomposing the source-facing `j`-comparison with `toSheafify`
recovers whiskering of the sheafification unit. -/
lemma cocontinuousOver_projection_comparison_precompose_toSheafify_app
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    (F : Cᵒᵖ ⥤ Type t)
    (X : (CostructuredArrow u V)ᵒᵖ) :
    ((toSheafify J' ((CostructuredArrow.proj u V).op ⋙ F)).app X ≫
        ((sheafToPresheaf J' (Type t)).map
          (((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison J' J).app
            F)).app X) =
      (Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J F)).app X := by
  -- This is the defining `sheafifyLift` relation for the source-facing comparison, evaluated at `X`.
  change
    ((toSheafify J' ((CostructuredArrow.proj u V).op ⋙ F)).app X ≫
        (sheafifyLift J'
          (Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J F))
          ((presheafToSheaf J (Type t) ⋙
              (CostructuredArrow.proj u V).sheafPushforwardContinuous (Type t) J' J).obj F).property).app
            X) =
      (Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J F)).app X
  exact
    congrArg (fun η => η.app X)
      (toSheafify_sheafifyLift J'
        (Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J F))
        ((presheafToSheaf J (Type t) ⋙
            (CostructuredArrow.proj u V).sheafPushforwardContinuous (Type t) J' J).obj F).property)

/-- Helper for Lemma 7.28.5: the source-facing `j`-comparison is characterized globally by the
expected `toSheafify` factorization. -/
lemma cocontinuousOver_projection_comparison_precompose_toSheafify
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    (F : Cᵒᵖ ⥤ Type t) :
    toSheafify J' ((CostructuredArrow.proj u V).op ⋙ F) ≫
        (sheafToPresheaf J' (Type t)).map
          (((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison J' J).app
            F) =
      Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J F) := by
  -- Compare the two owner morphisms pointwise on each object of `{}^u_V \mathcal I`.
  ext X x
  exact congrFun
    (cocontinuousOver_projection_comparison_precompose_toSheafify_app
      (J := J) (u := u) (V := V) F X)
    x

/-- Helper for Lemma 7.28.5: forgetting the image of a sheaf morphism under continuous
pushforward along `j` is just whiskering its underlying presheaf morphism by `j.op`. -/
lemma cocontinuousOver_projection_sheafPushforward_map_app_eq_whiskerLeft
    {A : Type*} [Category A]
    [HasWeakSheafify J A]
    [HasWeakSheafify J' A]
    {ℱ 𝒢 : Sheaf J A}
    (α : ℱ ⟶ 𝒢)
    (X : (CostructuredArrow u V)ᵒᵖ) :
    ((sheafToPresheaf J' A).map
        (((CostructuredArrow.proj u V).sheafPushforwardContinuous A J' J).map α)).app X =
      (Functor.whiskerLeft (CostructuredArrow.proj u V).op
        ((sheafToPresheaf J A).map α)).app X := by
  -- Continuous pushforward along `j` is defined by whiskering the underlying presheaf map.
  rfl

/-- Helper for Lemma 7.28.5: specializing the `j`-comparison precompose identity to a sheaf on
`D` rewrites the source component entirely in terms of the restricted presheaf `u.op ⋙ ℱ.1`. -/
lemma cocontinuousOver_projection_specializedComparison_precompose_toSheafify_app
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    (ℱ : Sheaf K (Type t))
    (X : (CostructuredArrow u V)ᵒᵖ) :
    let F : Cᵒᵖ ⥤ Type t :=
      ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type t)).obj u.op).obj
        ((sheafToPresheaf K (Type t)).obj ℱ)
    ((toSheafify J' ((CostructuredArrow.proj u V).op ⋙ F)).app X ≫
        ((sheafToPresheaf J' (Type t)).map
          ((cocontinuousOver_projection_specializedComparison
            (J := J) (K := K) (u := u) (V := V)).app ℱ)).app X) =
      (Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J F)).app X := by
  -- Unfold only the specialized comparison and reuse the generic precompose identity.
  dsimp [cocontinuousOver_projection_specializedComparison]
  simpa using
    cocontinuousOver_projection_comparison_precompose_toSheafify_app
      (J := J) (u := u) (V := V)
      (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type t)).obj u.op).obj
        ((sheafToPresheaf K (Type t)).obj ℱ))
      X

/-- Helper for Lemma 7.28.5: the specialized `j`-comparison is characterized owner-level by the
expected `toSheafify` factorization on the restricted presheaf `u.op ⋙ ℱ.1`. -/
lemma cocontinuousOver_projection_specializedComparison_precompose_toSheafify
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    (ℱ : Sheaf K (Type t)) :
    let F : Cᵒᵖ ⥤ Type t :=
      ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type t)).obj u.op).obj
        ((sheafToPresheaf K (Type t)).obj ℱ)
    toSheafify J' ((CostructuredArrow.proj u V).op ⋙ F) ≫
        (sheafToPresheaf J' (Type t)).map
          ((cocontinuousOver_projection_specializedComparison
            (J := J) (K := K) (u := u) (V := V)).app ℱ) =
      Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J F) := by
  let F : Cᵒᵖ ⥤ Type t :=
    ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type t)).obj u.op).obj
      ((sheafToPresheaf K (Type t)).obj ℱ)
  -- Compare the two owner maps pointwise on each object of `{}^u_V \mathcal I`.
  ext X x
  exact congrFun
    (cocontinuousOver_projection_specializedComparison_precompose_toSheafify_app
      (J := J) (K := K) (u := u) (V := V) ℱ X)
    x

/-- Helper for Lemma 7.28.5: precomposing by the `J'`-sheafification unit preserves an
owner-level forgotten equality of morphisms. -/
lemma cocontinuousOver_projection_toSheafify_comp_eq_of_eq
    [HasWeakSheafify J' (Type t)]
    {A B : (CostructuredArrow u V)ᵒᵖ ⥤ Type t}
    {f g : ((presheafToSheaf J' (Type t)).obj A).1 ⟶ B}
    (h : f = g) :
    toSheafify J' A ≫ f = toSheafify J' A ≫ g := by
  -- Precomposition by the sheafification unit preserves the normalized owner equality.
  simp [h]

/-- Helper for Lemma 7.28.5: after forgetting to presheaves, the specialized comparison at `X`
is definitionally the owner comparison for `j` evaluated on the restricted presheaf `u.op ⋙ ℱ.1`.
-/
lemma cocontinuousOver_projection_specializedComparison_underlying_app_eq_projectionComparison
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    (ℱ : Sheaf K (Type t))
    (X : CostructuredArrow u V) :
    let F : Cᵒᵖ ⥤ Type t :=
      ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type t)).obj u.op).obj
        ((sheafToPresheaf K (Type t)).obj ℱ)
    (((sheafToPresheaf J' (Type t)).map
        ((cocontinuousOver_projection_specializedComparison
          (J := J) (K := K) (u := u) (V := V)).app ℱ)).app (Opposite.op X)) =
      (((sheafToPresheaf J' (Type t)).map
      (((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison J' J).app
          F)).app (Opposite.op X)) := by
  -- The specialized comparison is definitionally the whiskered `j`-comparison on `F`.
  rfl

/-- Helper for Lemma 7.28.5: the source-proof indexing category over `X` is equivalent to the
comma category of arrows into `X` inside `{}^u_V \mathcal I`. -/
noncomputable def cocontinuousOver_projection_index_equivalence
    (X : C) :
    CostructuredArrow (Over.forget X ⋙ u) V ≌ CostructuredArrow j X :=
  { functor :=
      { obj := fun Y ↦
          let Z : CostructuredArrow u V := CostructuredArrow.mk Y.hom
          CostructuredArrow.mk (S := j) (Y := Z) Y.left.hom
        map := fun {Y₁ Y₂} φ ↦
          -- The source proof forgets only the `Over X` packaging and keeps the same
          -- underlying arrows `u(Y) ⟶ V` and `Y ⟶ X`.
          let φleft :
              (CostructuredArrow.mk (S := u) Y₁.hom : CostructuredArrow u V) ⟶
                (CostructuredArrow.mk (S := u) Y₂.hom : CostructuredArrow u V) :=
            CostructuredArrow.homMk φ.left.left (by
              simpa using CostructuredArrow.w φ)
          CostructuredArrow.homMk φleft (by
            show φ.left.left ≫ Y₂.left.hom = Y₁.left.hom
            simpa using Over.w φ.left)
        map_id := by
          intro Y
          apply CostructuredArrow.ext
          apply CostructuredArrow.ext
          simp
        map_comp := by
          intro Y₁ Y₂ Y₃ φ ψ
          apply CostructuredArrow.ext
          apply CostructuredArrow.ext
          simp }
    inverse :=
      { obj := fun Y ↦
          let Z : Over X := Over.mk Y.hom
          CostructuredArrow.mk (S := Over.forget X ⋙ u) (Y := Z) Y.left.hom
        map := fun {Y₁ Y₂} φ ↦
          -- Conversely, the arrow into `X` repackages the left object as an object of `Over X`.
          let φleft :
              Over.mk Y₁.hom ⟶ Over.mk Y₂.hom :=
            Over.homMk φ.left.left (by
              simpa using CostructuredArrow.w φ)
          CostructuredArrow.homMk φleft (by
            show u.map φ.left.left ≫ Y₂.left.hom = Y₁.left.hom
            simpa using CostructuredArrow.w φ.left)
        map_id := by
          intro Y
          apply CostructuredArrow.ext
          apply Over.OverMorphism.ext
          simp
        map_comp := by
          intro Y₁ Y₂ Y₃ φ ψ
          apply CostructuredArrow.ext
          apply Over.OverMorphism.ext
          simp }
    unitIso := NatIso.ofComponents (fun Y ↦
      -- Both composites are definitionally the identity after forgetting the comma packaging.
      let e : Y.left ≅ Over.mk Y.left.hom :=
        Over.isoMk (Iso.refl _) (by simp)
      CostructuredArrow.isoMk e (by simp [e]))
    counitIso := NatIso.ofComponents (fun Y ↦
      -- The target-side composite keeps the same object of `{}^u_V \mathcal I` and the same
      -- structure map to `X`, so only the nested comma packaging changes.
      let e : Y.left ≅ (CostructuredArrow.mk (S := u) Y.left.hom : CostructuredArrow u V) :=
        CostructuredArrow.isoMk (Iso.refl _) (by simp)
      CostructuredArrow.isoMk e (by simp [e])) }

/-- Helper for Lemma 7.28.5: the structured-arrow category used for pointwise right Kan
extensions is the opposite of the source-proof comma category. -/
noncomputable def cocontinuousOver_projection_structuredArrow_equivalence
    (X : C) :
    StructuredArrow (Opposite.op X) (CostructuredArrow.proj u V).op ≌
      (CostructuredArrow (Over.forget X ⋙ u) V)ᵒᵖ :=
  (((cocontinuousOver_projection_index_equivalence (u := u) (V := V) X).op).trans
    (costructuredArrowOpEquivalence (CostructuredArrow.proj u V) X)).symm

/-- Helper for Lemma 7.28.5: after identifying the sectionwise structured-arrow category with the
source-proof comma category, the projection functor is exactly the opposite of the canonical
precomposition functor `CostructuredArrow.pre`. -/
noncomputable def cocontinuousOver_projection_structuredArrow_proj_iso
    (X : C) :
    StructuredArrow.proj (Opposite.op X) (CostructuredArrow.proj u V).op ≅
      (cocontinuousOver_projection_structuredArrow_equivalence
        (u := u) (V := V) X).functor ⋙
        (CostructuredArrow.pre (Over.forget X) u V).op := by
  -- The explicit equivalence was chosen so that the textbook projection becomes definitional.
  exact Iso.refl _

/-- Helper for Lemma 7.28.5: each sectionwise structured-arrow diagram defining the pointwise
right Kan extension of `j.op` has a limit in the lifted universe where the source indexing
category is small enough for `Type`-limits. -/
theorem cocontinuousOver_projection_structuredArrow_hasLimit_lifted
    (X : C) (P : (CostructuredArrow u V)ᵒᵖ ⥤ Type (max (max (max (max t u₁) u₂) v₁) v₂)) :
    HasLimit (StructuredArrow.proj (Opposite.op X) (CostructuredArrow.proj u V).op ⋙ P) := by
  -- Route correction: compute the pointwise right Kan extension in the lifted universe, where
  -- the source indexing category from the textbook is small enough for the ambient `Type`.
  let e :=
    Functor.isoWhiskerRight
      (cocontinuousOver_projection_structuredArrow_proj_iso
        (u := u) (V := V) X) P
  -- After transporting along the explicit source-proof identification, the remaining diagram is
  -- an ordinary large-`Type` diagram and its limit is provided by the ambient `Type` instance.
  have htransport :
      HasLimit
        ((cocontinuousOver_projection_structuredArrow_equivalence
            (u := u) (V := V) X).functor ⋙
          (CostructuredArrow.pre (Over.forget X) u V).op ⋙ P) := by
    infer_instance
  exact hasLimit_of_iso e

/-- Helper for Lemma 7.28.5: in the lifted presheaf universe, the projection `j.op` admits the
pointwise right Kan extensions required by the owner comparison theorem. -/
theorem cocontinuousOver_projection_pointwiseRan_lifted
    (P : (CostructuredArrow u V)ᵒᵖ ⥤ Type (max (max (max (max t u₁) u₂) v₁) v₂)) :
    Functor.HasPointwiseRightKanExtension (CostructuredArrow.proj u V).op P := by
  intro X
  -- In the lifted universe, each structured-arrow diagram is small enough for the ambient
  -- `Type` limits instance, so the owner witness is available directly.
  infer_instance

/-- Helper for Lemma 7.28.5: the owner comparison for the projection `j` is already an
isomorphism, so the remaining source proof only needs the specialization rewrite. -/
theorem cocontinuousOver_projection_target_transport_underlying
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    (F : Cᵒᵖ ⥤ Type t) :
    let Tl := Type (max (max (max (max t u₁) u₂) v₁) v₂)
    let U : Type t ⥤ Tl := CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t}
    (sheafToPresheaf J' Tl).map
        (((CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J).map
          ((sheafComposeNatTrans J U
            (sheafificationAdjunction J (Type t))
            (sheafificationAdjunction J Tl)).app F)) =
      Functor.whiskerLeft (CostructuredArrow.proj u V).op
        ((sheafToPresheaf J Tl).map
          ((sheafComposeNatTrans J U
            (sheafificationAdjunction J (Type t))
            (sheafificationAdjunction J Tl)).app F)) := by
  -- Forgetting the target-side map along `j` is definitionally just whiskering the underlying
  -- presheaf map by `j.op`.
  ext X x
  rfl

/-- Helper for Lemma 7.28.5: in the lifted universe, precomposing the owner comparison with
`toSheafify` again recovers whiskering of the sheafification unit. -/
lemma cocontinuousOver_projection_comparison_precompose_toSheafify_lifted
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    (F : Cᵒᵖ ⥤ Type t) :
    let Tl := Type (max (max (max (max t u₁) u₂) v₁) v₂)
    let U : Type t ⥤ Tl := CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t}
    toSheafify J' (((CostructuredArrow.proj u V).op ⋙ F) ⋙ U) ≫
      (sheafToPresheaf J' Tl).map
        ((Functor.pushforwardContinuousSheafificationComparison.{max (max (max (max t u₁) u₂) v₁) v₂}
          (G := CostructuredArrow.proj u V) J' J).app (F ⋙ U)) =
      Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J (F ⋙ U)) := by
  -- The lifted comparison is again defined by `sheafifyLift`, so the defining unit factorization
  -- is unchanged after moving to the larger `Type` universe.
  ext X x
  change
    ((toSheafify J' (((CostructuredArrow.proj u V).op ⋙ F) ⋙
          CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t})).app X ≫
        (sheafifyLift J'
          (Functor.whiskerLeft (CostructuredArrow.proj u V).op
            (toSheafify J
              (F ⋙ CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t})))
          ((presheafToSheaf J
              (Type (max (max (max (max t u₁) u₂) v₁) v₂)) ⋙
            (CostructuredArrow.proj u V).sheafPushforwardContinuous
              (Type (max (max (max (max t u₁) u₂) v₁) v₂)) J' J).obj
              (F ⋙ CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t})).property).app
          X) x = _
  exact congrFun
    (congrArg (fun η => η.app X)
      (toSheafify_sheafifyLift J'
        (Functor.whiskerLeft (CostructuredArrow.proj u V).op
          (toSheafify J
            (F ⋙ CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t})))
        ((presheafToSheaf J
            (Type (max (max (max (max t u₁) u₂) v₁) v₂)) ⋙
          (CostructuredArrow.proj u V).sheafPushforwardContinuous
            (Type (max (max (max (max t u₁) u₂) v₁) v₂)) J' J).obj
            (F ⋙ CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t})).property))
    x

/-- Helper for Lemma 7.28.5: after moving the source comparison through `ULift`, the forgotten
comparison factors through the large-universe owner comparison and the target-side transport map. -/
lemma cocontinuousOver_projection_comparison_app_whisker_ulift_normalized
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    (F : Cᵒᵖ ⥤ Type t) :
    let Tl := Type (max (max (max (max t u₁) u₂) v₁) v₂)
    let U : Type t ⥤ Tl := CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t}
    let α :=
      ((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison J' J).app F
    let β :
        ((Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ Cᵒᵖ Tl).obj
            (CostructuredArrow.proj u V).op ⋙ presheafToSheaf J' Tl) ⟶
          presheafToSheaf J Tl ⋙
            (CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J :=
      Functor.pushforwardContinuousSheafificationComparison.{max (max (max (max t u₁) u₂) v₁) v₂}
        (G := CostructuredArrow.proj u V) J' J
    toSheafify J' (((CostructuredArrow.proj u V).op ⋙ F) ⋙ U) ≫
        (((sheafToPresheaf J' Tl).map
            ((sheafComposeNatTrans J' U
              (sheafificationAdjunction J' (Type t))
              (sheafificationAdjunction J' Tl)).app ((CostructuredArrow.proj u V).op ⋙ F))) ≫
          (Functor.whiskerRight ((sheafToPresheaf J' (Type t)).map α) U)) =
      toSheafify J' (((CostructuredArrow.proj u V).op ⋙ F) ⋙ U) ≫
        ((sheafToPresheaf J' Tl).map (β.app (F ⋙ U)) ≫
          (sheafToPresheaf J' Tl).map
            (((CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J).map
              ((sheafComposeNatTrans J U
                (sheafificationAdjunction J (Type t))
                (sheafificationAdjunction J Tl)).app F))) := by
  dsimp
  let Tl := Type (max (max (max (max t u₁) u₂) v₁) v₂)
  let U : Type t ⥤ Tl := CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t}
  let α :=
    (((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison J' J).app F)
  let common :=
    Functor.whiskerRight
      (toSheafify J' ((CostructuredArrow.proj u V).op ⋙ F) ≫
        (sheafToPresheaf J' (Type t)).map α)
      U
  have hsource :
      toSheafify J' (((CostructuredArrow.proj u V).op ⋙ F) ⋙ U) ≫
          (sheafToPresheaf J' Tl).map
            ((sheafComposeNatTrans J' U
                (sheafificationAdjunction J' (Type t))
                (sheafificationAdjunction J' Tl)).app
              ((CostructuredArrow.proj u V).op ⋙ F)) ≫
            Functor.whiskerRight ((sheafToPresheaf J' (Type t)).map α) U =
        common := by
    -- First expose the `J'`-sheafification unit for `sheafComposeNatTrans`, then repack the
    -- resulting composite as a whiskered precomposition.
    have hfac :=
      sheafComposeNatTrans_fac J' U
        (sheafificationAdjunction J' (Type t))
        (sheafificationAdjunction J' Tl)
        ((CostructuredArrow.proj u V).op ⋙ F)
    have hfac' :=
      congrArg (fun k ↦ k ≫ Functor.whiskerRight ((sheafToPresheaf J' (Type t)).map α) U) hfac
    calc
      toSheafify J' (((CostructuredArrow.proj u V).op ⋙ F) ⋙ U) ≫
          (sheafToPresheaf J' Tl).map
            ((sheafComposeNatTrans J' U
                (sheafificationAdjunction J' (Type t))
                (sheafificationAdjunction J' Tl)).app
              ((CostructuredArrow.proj u V).op ⋙ F)) ≫
            Functor.whiskerRight ((sheafToPresheaf J' (Type t)).map α) U =
          Functor.whiskerRight (toSheafify J' ((CostructuredArrow.proj u V).op ⋙ F)) U ≫
            Functor.whiskerRight ((sheafToPresheaf J' (Type t)).map α) U := by
        simpa [Category.assoc] using hfac'
      _ = Functor.whiskerRight
            (toSheafify J' ((CostructuredArrow.proj u V).op ⋙ F) ≫
              (sheafToPresheaf J' (Type t)).map α) U := by
        ext X x
        rfl
      _ = common := rfl
  have htarget :
      toSheafify J' (((CostructuredArrow.proj u V).op ⋙ F) ⋙ U) ≫
          (sheafToPresheaf J' Tl).map
            ((Functor.pushforwardContinuousSheafificationComparison.{max (max (max (max t u₁) u₂) v₁) v₂}
                (G := CostructuredArrow.proj u V) J' J).app (F ⋙ U)) ≫
          (sheafToPresheaf J' Tl).map
            (((CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J).map
              ((sheafComposeNatTrans J U
                  (sheafificationAdjunction J (Type t))
                  (sheafificationAdjunction J Tl)).app F)) =
        common := by
    -- Normalize the lifted owner comparison, then rewrite the transport term back to the same
    -- whiskered precomposition as on the source side.
    have hβ :
        toSheafify J' (((CostructuredArrow.proj u V).op ⋙ F) ⋙ U) ≫
            (sheafToPresheaf J' Tl).map
              ((Functor.pushforwardContinuousSheafificationComparison.{max (max (max (max t u₁) u₂) v₁) v₂}
                  (G := CostructuredArrow.proj u V) J' J).app (F ⋙ U)) =
          Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J (F ⋙ U)) := by
      simpa [Tl, U] using
        cocontinuousOver_projection_comparison_precompose_toSheafify_lifted
          (J := J) (u := u) (V := V) F
    have htransport :
        (sheafToPresheaf J' Tl).map
            (((CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J).map
              ((sheafComposeNatTrans J U
                  (sheafificationAdjunction J (Type t))
                  (sheafificationAdjunction J Tl)).app F)) =
          Functor.whiskerLeft (CostructuredArrow.proj u V).op
            ((sheafToPresheaf J Tl).map
              ((sheafComposeNatTrans J U
                  (sheafificationAdjunction J (Type t))
                  (sheafificationAdjunction J Tl)).app F)) := by
      simpa [Tl, U] using
        cocontinuousOver_projection_target_transport_underlying
          (J := J) (u := u) (V := V) F
    have hβ' :=
      congrArg
        (fun k ↦
          k ≫
            (sheafToPresheaf J' Tl).map
              (((CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J).map
                ((sheafComposeNatTrans J U
                    (sheafificationAdjunction J (Type t))
                    (sheafificationAdjunction J Tl)).app F)))
        hβ
    have hfac :=
      sheafComposeNatTrans_fac J U
        (sheafificationAdjunction J (Type t))
        (sheafificationAdjunction J Tl)
        F
    have hcompare :=
      cocontinuousOver_projection_comparison_precompose_toSheafify
        (J := J) (u := u) (V := V) F
    have hstep1 :
        toSheafify J' (((CostructuredArrow.proj u V).op ⋙ F) ⋙ U) ≫
            (sheafToPresheaf J' Tl).map
              ((Functor.pushforwardContinuousSheafificationComparison.{max (max (max (max t u₁) u₂) v₁) v₂}
                  (G := CostructuredArrow.proj u V) J' J).app (F ⋙ U)) ≫
            (sheafToPresheaf J' Tl).map
              (((CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J).map
                ((sheafComposeNatTrans J U
                    (sheafificationAdjunction J (Type t))
                    (sheafificationAdjunction J Tl)).app F)) =
          Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J (F ⋙ U)) ≫
            (sheafToPresheaf J' Tl).map
              (((CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J).map
                ((sheafComposeNatTrans J U
                    (sheafificationAdjunction J (Type t))
                    (sheafificationAdjunction J Tl)).app F)) := by
      simpa [Category.assoc] using hβ'
    have hstep2 :
        Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J (F ⋙ U)) ≫
            (sheafToPresheaf J' Tl).map
              (((CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J).map
                ((sheafComposeNatTrans J U
                    (sheafificationAdjunction J (Type t))
                    (sheafificationAdjunction J Tl)).app F)) =
          Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J (F ⋙ U)) ≫
            Functor.whiskerLeft (CostructuredArrow.proj u V).op
              ((sheafToPresheaf J Tl).map
                ((sheafComposeNatTrans J U
                    (sheafificationAdjunction J (Type t))
                    (sheafificationAdjunction J Tl)).app F)) := by
      ext X x
      let τ :=
        (Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J (F ⋙ U))).app X
      have htransportX := congrArg (fun η => η.app X) htransport
      simpa [τ, Category.assoc] using
        congrFun (congrArg (fun k ↦ τ ≫ k) htransportX) x
    have hstep3 :
        Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J (F ⋙ U)) ≫
            Functor.whiskerLeft (CostructuredArrow.proj u V).op
              ((sheafToPresheaf J Tl).map
                ((sheafComposeNatTrans J U
                    (sheafificationAdjunction J (Type t))
                    (sheafificationAdjunction J Tl)).app F)) =
          Functor.whiskerLeft (CostructuredArrow.proj u V).op
            (toSheafify J (F ⋙ U) ≫
              (sheafToPresheaf J Tl).map
                ((sheafComposeNatTrans J U
                    (sheafificationAdjunction J (Type t))
                    (sheafificationAdjunction J Tl)).app F)) := by
      rfl
    have hstep4 :
        Functor.whiskerLeft (CostructuredArrow.proj u V).op
            (toSheafify J (F ⋙ U) ≫
              (sheafToPresheaf J Tl).map
                ((sheafComposeNatTrans J U
                    (sheafificationAdjunction J (Type t))
                    (sheafificationAdjunction J Tl)).app F)) =
          Functor.whiskerLeft (CostructuredArrow.proj u V).op
            (Functor.whiskerRight (toSheafify J F) U) := by
      simpa using
        congrArg (fun η ↦ Functor.whiskerLeft (CostructuredArrow.proj u V).op η) hfac
    have hstep5 :
        Functor.whiskerLeft (CostructuredArrow.proj u V).op
            (Functor.whiskerRight (toSheafify J F) U) =
          Functor.whiskerRight
            (Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J F)) U := by
      ext X x
      rfl
    have hstep6 :
        Functor.whiskerRight
            (Functor.whiskerLeft (CostructuredArrow.proj u V).op (toSheafify J F)) U =
          common := by
      unfold common
      symm
      simpa using congrArg (fun η ↦ Functor.whiskerRight η U) hcompare
    exact hstep1.trans (hstep2.trans (hstep3.trans (hstep4.trans (hstep5.trans hstep6))))
  exact hsource.trans htarget.symm

/-- Helper for Lemma 7.28.5: the target-side lifted comparison is the unique sheaf morphism whose
precomposition with the `J'`-sheafification unit matches the normalized source-side candidate. -/
theorem cocontinuousOver_projection_comparison_target_candidate_eq
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    (F : Cᵒᵖ ⥤ Type t) :
    let Tl := Type (max (max (max (max t u₁) u₂) v₁) v₂)
    let U : Type t ⥤ Tl := CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t}
    let α :=
      ((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison J' J).app F
    let β :
        ((Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ Cᵒᵖ Tl).obj
            (CostructuredArrow.proj u V).op ⋙ presheafToSheaf J' Tl) ⟶
          presheafToSheaf J Tl ⋙
            (CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J :=
      Functor.pushforwardContinuousSheafificationComparison.{max (max (max (max t u₁) u₂) v₁) v₂}
        (G := CostructuredArrow.proj u V) J' J
    ((sheafComposeNatTrans J' U
        (sheafificationAdjunction J' (Type t))
        (sheafificationAdjunction J' Tl)).app ((CostructuredArrow.proj u V).op ⋙ F)) ≫
      ((sheafCompose J' U).map α) =
      (β.app (F ⋙ U)) ≫
        ((CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J).map
          ((sheafComposeNatTrans J U
            (sheafificationAdjunction J (Type t))
            (sheafificationAdjunction J Tl)).app F) := by
  dsimp
  let Tl := Type (max (max (max (max t u₁) u₂) v₁) v₂)
  let U : Type t ⥤ Tl := CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t}
  let α :=
    ((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison J' J).app F
  let β :
      ((Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ Cᵒᵖ Tl).obj
          (CostructuredArrow.proj u V).op ⋙ presheafToSheaf J' Tl) ⟶
        presheafToSheaf J Tl ⋙
          (CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J :=
    Functor.pushforwardContinuousSheafificationComparison.{max (max (max (max t u₁) u₂) v₁) v₂}
      (G := CostructuredArrow.proj u V) J' J
  -- The normalized owner equality already identifies the two candidates after precomposition by
  -- `toSheafify`, so injectivity of the sheafification adjunction closes the sheaf-level equality.
  apply (sheafificationAdjunction J' Tl).homEquiv _ _ |>.injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simpa [Functor.map_comp, Category.assoc, Tl, U, α, β] using
    cocontinuousOver_projection_comparison_app_whisker_ulift_normalized
      (J := J) (u := u) (V := V) F

/-- Helper for Lemma 7.28.5: after forgetting the target-candidate equality to presheaves,
the `ULift`-whiskered source comparison matches the transported large-universe comparison. -/
theorem cocontinuousOver_projection_comparison_app_whisker_ulift
    [HasWeakSheafify J (Type t)]
    [HasWeakSheafify J' (Type t)]
    (F : Cᵒᵖ ⥤ Type t) :
    let Tl := Type (max (max (max (max t u₁) u₂) v₁) v₂)
    let U : Type t ⥤ Tl := CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t}
    let α :=
      ((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison J' J).app F
    let β :
        ((Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ Cᵒᵖ Tl).obj
            (CostructuredArrow.proj u V).op ⋙ presheafToSheaf J' Tl) ⟶
          presheafToSheaf J Tl ⋙
            (CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J :=
      Functor.pushforwardContinuousSheafificationComparison.{max (max (max (max t u₁) u₂) v₁) v₂}
        (G := CostructuredArrow.proj u V) J' J
    ((sheafToPresheaf J' Tl).map
        ((sheafComposeNatTrans J' U
          (sheafificationAdjunction J' (Type t))
          (sheafificationAdjunction J' Tl)).app ((CostructuredArrow.proj u V).op ⋙ F))) ≫
      (Functor.whiskerRight ((sheafToPresheaf J' (Type t)).map α) U) =
      (sheafToPresheaf J' Tl).map (β.app (F ⋙ U)) ≫
        (sheafToPresheaf J' Tl).map
          (((CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J).map
            ((sheafComposeNatTrans J U
              (sheafificationAdjunction J (Type t))
              (sheafificationAdjunction J Tl)).app F)) := by
  -- Route correction: first identify the two sheaf morphisms upstairs, then forget that
  -- equality to the presheaf level where the displayed transport statement lives.
  dsimp
  let Tl := Type (max (max (max (max t u₁) u₂) v₁) v₂)
  let U : Type t ⥤ Tl := CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t}
  let α :=
    ((CostructuredArrow.proj u V).pushforwardContinuousSheafificationComparison J' J).app F
  let β :
      ((Functor.whiskeringLeft (CostructuredArrow u V)ᵒᵖ Cᵒᵖ Tl).obj
          (CostructuredArrow.proj u V).op ⋙ presheafToSheaf J' Tl) ⟶
        presheafToSheaf J Tl ⋙
          (CostructuredArrow.proj u V).sheafPushforwardContinuous Tl J' J :=
    Functor.pushforwardContinuousSheafificationComparison.{max (max (max (max t u₁) u₂) v₁) v₂}
      (G := CostructuredArrow.proj u V) J' J
  -- Forget the sheaf-level equality furnished by the owner uniqueness step.
  simpa [Functor.map_comp, Category.assoc, Tl, U, α, β] using
    congrArg
      (fun k ↦ (sheafToPresheaf J' Tl).map k)
      (cocontinuousOver_projection_comparison_target_candidate_eq
        (J := J) (u := u) (V := V) F)

end CategoryTheory
