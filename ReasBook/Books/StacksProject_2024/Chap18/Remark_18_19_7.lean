import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Tactic.Recall
import Mathlib.CategoryTheory.Sites.Over

open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u

section PresheafLevel

variable {C : Type u} [Category.{u} C] (𝒪 : Cᵒᵖ ⥤ RingCat.{u}) (U : C)

/- Domain-style sampling for Remark 18.19.7:
- primary domain: localization of presheaves of modules via restriction and its two Kan-extension
  adjoints along `Over.forget U`;
- sampled owner declarations:
  `PresheafOfModules.pullbackPushforwardAdjunction`,
  `Adjunction.ofIsLeftAdjoint`,
  `Functor.rightAdjoint`,
  `SheafOfModules.sheafificationCompPullback`,
  `Functor.ranAdjunction`;
- best owner abstraction:
  `PresheafOfModules.pullbackPushforwardAdjunction (𝟙 ((Over.forget U).op ⋙ 𝒪))`;
- primitive data: the ring presheaf `𝒪` on `C` and the localization object `U : C`;
- derived API: the presheaf right adjoint `j_{U*}`, the objectwise coproduct formula for
  `j_{U!}` as a canonical isomorphism, the exactness of this presheaf-level lower shriek, and,
  in the sheaf case below, the comparison showing that sheaf-level extension by zero is obtained
  by sheafifying presheaf-level extension by zero.

Source/core/bridge triage:
- `source-facing`: the presheaf localization adjoints `j_{U!} ⊣ j_U^* ⊣ j_{U*}`, the exactness
  of `j_{U!}`, and the objectwise formula for `j_{U!}`;
- `core/canonical`:
  `PresheafOfModules.pullbackPushforwardAdjunction (𝟙 ((Over.forget U).op ⋙ 𝒪))`;
- `bridge/view`: the coproduct formula and the sheafification comparison from the presheaf owner
  to the sheaf owner.

This file should therefore recall the canonical presheaf lower-shriek adjunction directly, record
the missing right adjunction for restriction, add the source-facing exactness statement for the
same owner, keep the coproduct formula as a canonical isomorphism, and use the upstream
sheafification/pullback comparison instead of a chapter-local wrapper square.
-/

/- Remark 18.19.7: for a presheaf of rings `𝒪` on `C` and an object `U : C`, restriction to the
slice category `C/U` is the canonical pushforward
`PresheafOfModules.pushforward (𝟙 ((Over.forget U).op ⋙ 𝒪))`, and its left adjoint
`j_{U!}` is exactly the owner adjunction
`PresheafOfModules.pullbackPushforwardAdjunction (𝟙 ((Over.forget U).op ⋙ 𝒪))`. -/
recall PresheafOfModules.pullbackPushforwardAdjunction

-- Proof sketch: the restriction functor is induced by precomposition with `(Over.forget U).op`,
-- so its right adjoint is the presheaf-module right Kan extension along `(Over.forget U).op`,
-- i.e. the presheaf-level `j_{U*}` from the source remark.
/-- Remark 18.19.7 also records that the restriction functor `j_U^*` on presheaves of modules is a
left adjoint, so its chosen right adjoint is the presheaf direct image `j_{U*}`. -/
instance presheafLocalizedRestriction_isLeftAdjoint :
    (PresheafOfModules.pushforward (𝟙 ((Over.forget U).op ⋙ 𝒪))).IsLeftAdjoint := sorry

/-- The source remark's presheaf direct image `j_{U*}` is the right adjoint of restriction, hence
the canonical adjunction below packages the source-facing statement `j_U^* ⊣ j_{U*}` directly. -/
noncomputable abbrev presheafLocalizedRestrictionRightAdjunction :
    PresheafOfModules.pushforward (𝟙 ((Over.forget U).op ⋙ 𝒪)) ⊣
      (PresheafOfModules.pushforward (𝟙 ((Over.forget U).op ⋙ 𝒪))).rightAdjoint :=
  Adjunction.ofIsLeftAdjoint
    (PresheafOfModules.pushforward (𝟙 ((Over.forget U).op ⋙ 𝒪)))

-- Proof sketch: this is exactly Lemma `18.19.3` for the chaotic topology, where every presheaf is
-- already a sheaf. Equivalently, `j_{U!}` is the canonical pullback owner for the identity map on
-- the localized ring presheaf, and the source remark records that this lower shriek is exact.
/-- Remark 18.19.7 also records that the presheaf-level extension-by-zero functor
`j_{U!} = PresheafOfModules.pullback (𝟙 ((Over.forget U).op ⋙ 𝒪))` is exact. -/
theorem presheafLocalizedExtensionByZero_exact :
    exactFunctor
      (PresheafOfModules ((Over.forget U).op ⋙ 𝒪))
      (PresheafOfModules 𝒪)
      (PresheafOfModules.pullback (𝟙 ((Over.forget U).op ⋙ 𝒪))) := by
  sorry

-- Proof sketch: compute the objectwise left Kan extension defining `j_{U!}` along
-- `(Over.forget U).op`; as in Remark `7.25.10`, the indexing category over `V` is final over the
-- discrete family of arrows `φ : V ⟶ U`, so the value at `V` is the coproduct of the fibers
-- `𝒢(V \xrightarrow{φ} U)`.
/-- The value of presheaf extension by zero at `V` is canonically the coproduct of the fibers over
all arrows `V ⟶ U`. This is the module-valued counterpart of the Chapter 7 left-Kan-extension
formula for localization. -/
noncomputable def presheafLocalizedExtensionByZero_objIsoSigma
    (𝒢 : PresheafOfModules ((Over.forget U).op ⋙ 𝒪)) (V : C) :
    (((PresheafOfModules.pullback (𝟙 ((Over.forget U).op ⋙ 𝒪))).obj 𝒢).obj (op V)) ≅
      (∐ fun φ : V ⟶ U ↦ 𝒢.obj (op (Over.mk φ))) := by
  sorry

end PresheafLevel

section SheafComparison

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J RingCat.{u}) (U : C)

/- The comparison square in Remark 18.19.7 is exactly the upstream pullback/sheafification
comparison specialized to the identity map of the localized ring sheaf `𝒪_U`. -/
recall SheafOfModules.sheafificationCompPullback

end SheafComparison
