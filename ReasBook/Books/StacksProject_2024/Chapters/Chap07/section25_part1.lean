import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_25_1 (from Chap07) -/
open CategoryTheory

universe u v

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)

/- Domain-style sampling for Definition 7.25.1:
- primary domain: localization of a site at an object and the induced localization morphism of
  topoi;
- sampled owner API:
  `GrothendieckTopology.over`,
  `GrothendieckTopology.instIsCocontinuousOverForgetOver`,
  `Functor.morphismOfTopoiInOfCocontinuous`,
  `Functor.morphismOfTopoiInOfCocontinuous_inverseImage`,
  `Functor.morphismOfTopoiInOfCocontinuous_pushforward`;
- source/core/bridge triage:
  `source-facing`: the localized site `(Over U, J.over U)` and the localization morphism
  `j_U : Sh(C/U, J.over U) ⟶ Sh(C, J)`;
  `core/canonical`: the owner construction `GrothendieckTopology.over` and the bundled morphism
  `(Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J :
    MorphismOfTopoiIn J (J.over U)`;
  `bridge/view`: the simp theorems identifying the inverse-image and direct-image fields of that
  morphism with the canonical cocontinuous sheaf pullback and pushforward owners.

Primitive data are just the ambient site `J` and the object `U`. The localized topology `J.over U`
is source-facing data, while the cocontinuity of `Over.forget U` and the resulting geometric
morphism are already owned upstream. This file therefore targets the `core/canonical` layer:
direct recall of those owners, with the inverse-image and direct-image functors left as derived
API rather than separate local declarations.
-/

/- Definition 7.25.1: for a site `(C, J)` and an object `U : C`, the localization of the site at
`U` is the slice site `C/U` endowed with the induced Grothendieck topology. This notion is
canonically owned by `GrothendieckTopology.over`. -/
recall GrothendieckTopology.over

/- Companion specialization: applied to `(J, U)`, the localized site is `J.over U` on `Over U`.
-/
#check (J.over U : GrothendieckTopology (Over U))

/- Companion recall: the localization morphism
`j_U : Sh(C/U, J.over U) ⟶ Sh(C, J)` is the canonical morphism of topoi attached to the
cocontinuous localization functor `Over.forget U`. -/
recall Functor.morphismOfTopoiInOfCocontinuous

/- Companion specialization: for localization at `U`, the bundled morphism is the cocontinuous
site morphism induced by `Over.forget U`. -/
#check
  ((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J :
    MorphismOfTopoiIn J (J.over U))

/- Companion recall: the inverse-image functor of `j_U` is canonically the cocontinuous sheaf
pullback along `Over.forget U`. -/
recall Functor.morphismOfTopoiInOfCocontinuous_inverseImage

/- Companion recall: the direct-image functor of `j_U` is canonically the cocontinuous sheaf
pushforward along `Over.forget U`. -/
recall Functor.morphismOfTopoiInOfCocontinuous_pushforward

end

/-! ### Lemma_7_25_2 (from Chap07) -/
open CategoryTheory Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

universe w v u

noncomputable section

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]

/-- The sheafification of the left Kan extension of the unit `toSheafify` is an isomorphism. -/
-- Proof sketch: the unit `toSheafify (J.over U) G` is a local equivalence for `J.over U`; apply
-- `W_map_of_adjunction_of_isContinuous` to its left Kan extension along `(Over.forget U).op`, then
-- use `J.W_iff` to convert the resulting `J`-local equivalence into an `IsIso` after sheafifying.
noncomputable instance localization_lowerShriek_toSheafify_map_isIso
    (J : GrothendieckTopology C) (U : C) (G : (Over U)ᵒᵖ ⥤ Type w)
    [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasLeftKanExtension F]
    [HasWeakSheafify (J.over U) (Type w)]
    [HasWeakSheafify J (Type w)] :
    IsIso ((presheafToSheaf J (Type w)).map
      (((Over.forget U).op.lan).map (toSheafify (J.over U) G))) := by
  -- Transport the slice-site local equivalence across the left Kan extension along
  -- `(Over.forget U).op`.
  have hW : J.W (((Over.forget U).op.lan).map (toSheafify (J.over U) G)) := by
    exact (Over.forget U).W_map_of_adjunction_of_isContinuous (J.over U) J ((Over.forget U).op.lan)
      ((Over.forget U).op.lanAdjunction (Type w)) (toSheafify (J.over U) G)
      ((J.over U).W_toSheafify G)
  -- Convert the transported `W`-statement into the required isomorphism after sheafification.
  exact (J.W_iff _).1 hW

/-- Lemma 7.25.2: for a site `C`, an object `U`, and a presheaf `G` on the slice site `C/U`, the
localization lower shriek `j_{U!}(G^#)` is canonically isomorphic to the sheaf associated to the
canonical left Kan extension of `G` along `(Over.forget U).op`, equivalently to the presheaf
`V ↦ ∐_{φ : V ⟶ U} G(V \xrightarrow{φ} U)`. -/
noncomputable def localization_lowerShriek_associatedSheafIso
    (J : GrothendieckTopology C) (U : C) (G : (Over U)ᵒᵖ ⥤ Type w)
    [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasLeftKanExtension F]
    [HasWeakSheafify (J.over U) (Type w)]
    [HasWeakSheafify J (Type w)] :
    (((Over.forget U).sheafPullback (Type w) (J.over U) J).obj
      ((presheafToSheaf (J.over U) (Type w)).obj G)) ≅
      (presheafToSheaf J (Type w)).obj ((Over.forget U).op.lan.obj G) :=
  let η := ((Over.forget U).op.lan).map (toSheafify (J.over U) G)
  letI : IsIso ((presheafToSheaf J (Type w)).map η) :=
    localization_lowerShriek_toSheafify_map_isIso J U G
  (sheafPullbackIso (Over.forget U) (Type w) (J.over U) J).app
      ((presheafToSheaf (J.over U) (Type w)).obj G) ≪≫
    eqToIso rfl ≪≫
    (asIso ((presheafToSheaf J (Type w)).map η)).symm

/-- The underlying morphism of `localization_lowerShriek_associatedSheafIso` is an isomorphism. -/
-- Proof sketch: this morphism is the forward map of the canonical isomorphism
-- `localization_lowerShriek_associatedSheafIso`.
theorem localization_lowerShriek_associatedSheafIso_hom_isIso
    (J : GrothendieckTopology C) (U : C) (G : (Over U)ᵒᵖ ⥤ Type w)
    [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasLeftKanExtension F]
    [HasWeakSheafify (J.over U) (Type w)]
    [HasWeakSheafify J (Type w)] :
    IsIso (localization_lowerShriek_associatedSheafIso J U G).hom := by
  -- The forward map of any isomorphism is an isomorphism.
  infer_instance

end

/-! ### Lemma_7_25_3 (from Chap07) -/
open CategoryTheory

universe u v

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
variable [∀ F : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.forget U).op.HasLeftKanExtension F]
variable [HasWeakSheafify (J.over U) (Type (max u v))]
variable [HasWeakSheafify J (Type (max u v))]

/- Domain-style sampling for Lemma 7.25.3:
- primary domain: localization lower shriek on sheaves and its action on sheafified representables;
- sampled owner API:
  `continuous_sheafified_representable_iso`,
  `(Over.forget U).sheafPullback`,
  `GrothendieckTopology.uliftSheafifiedRepresentable`;
- source/core/bridge triage:
  `source-facing`: the textbook identification `j_{U!}(h_{X/U}^#) ≅ h_X^#`;
  `core/canonical`: the general Chapter 7 owner
  `continuous_sheafified_representable_iso` for a continuous functor of sites;
  `bridge/view`: the exact localization specialization along `Over.forget U`.

Primitive data belong to the owner theorem from Lemma 7.13.5: a continuous functor of sites and
an object of the source site. In Lemma 7.25.3 the localization lower shriek and the sheafified
representables are derived from that owner, so this file should expose only the specialized
localization instance, not a parallel local wrapper and not the unspecialized theorem.
-/

/- Lemma 7.25.3: for a site `(C, J)`, an object `U : C`, and an object `X/U` of the localized
site, the localization lower shriek along `Over.forget U` sends `h_{X/U}^#` to `h_X^#`. This is
the exact specialization of `continuous_sheafified_representable_iso` to the localization functor.
-/
#check
  (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J :
    (X : Over U) →
      J.uliftSheafifiedRepresentable ((Over.forget U).obj X) ≅
        ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
          ((J.over U).uliftSheafifiedRepresentable X))

end
