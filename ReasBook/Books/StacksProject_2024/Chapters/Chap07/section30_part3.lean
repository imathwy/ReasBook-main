import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_30_4 (from Chap07) -/
open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (ℱ : Sheaf J (Type w))

/- Domain-style sampling for Definition 7.30.4:
- primary domain: localization of a sheaf topos at an object, expressed by the slice topos over
  that object;
- sampled owner API:
  `Over`,
  `Over.forgetAdjStar`,
  `Over.forget`,
  `Over.star`;
- source/core/bridge triage:
  `source-facing`: the localized topos `Sh(C, J) / ℱ`;
  `core/canonical`: the slice owner `Over ℱ`, together with the adjunction
  `Over.forget ℱ ⊣ Over.star ℱ`, packaged by `Over.forgetAdjStar ℱ`;
  `bridge/view`: the direct-image and inverse-image functors `Over.forget ℱ` and `Over.star ℱ`.

Primitive data are only the ambient site and the sheaf `ℱ`. The localization topos and its
geometric morphism are already owned canonically by `Over ℱ` and `Over.forgetAdjStar ℱ`, so this
file should stay at the `core/canonical` layer with direct recall rather than repeating the same
owner facts under parallel local names.
-/

/- Definition 7.30.4: the localization of the topos `Sh(C, J)` at a sheaf `ℱ` is the slice
topos `Sh(C, J) / ℱ`, represented in Lean by the over category `Over ℱ`. -/
#check Over ℱ

/- Companion recall: the localization morphism at `ℱ` is the canonical slice-topos adjunction
whose direct image is `Over.forget ℱ` and whose inverse image is `Over.star ℱ`. -/
recall Over.forgetAdjStar

/-! ### Lemma_7_30_5 (from Chap07) -/
open CategoryTheory
open CategoryTheory.GrothendieckTopology
open scoped SheafifiedRepresentable

universe u v

noncomputable section

namespace CategoryTheory.GrothendieckTopology

attribute [local instance] Types.instConcreteCategory
attribute [local instance] Types.instFunLike

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (U : C)

/- Lemma 7.30.5: if `ℱ = h_U^#`, then the localization morphism
`Sh(C, J)/ℱ ⥤ Sh(C, J)` from Lemma 7.30.1 agrees, via the equivalence
`Sh(C/U, J.over U) ≌ Sh(C, J)/h_U^#` of Lemma 7.25.4, with the localization morphism
`j_U : Sh(C/U, J.over U) ⥤ Sh(C, J)`. Equivalently, after identifying sheaves on `C/U` with
sheaves over `h_U^#`, the forgetful functor to `Sh(C, J)` is exactly `j_{U!}`.

This is the owner-level companion theorem
`GrothendieckTopology.representableLocalizationComparison_forget` attached to the comparison
functor of Lemma 7.25.4. -/
recall representableLocalizationComparison_forget

end CategoryTheory.GrothendieckTopology

/-! ### Lemma_7_30_6 (from Chap07) -/
open CategoryTheory CategoryTheory.Limits

universe u v w

noncomputable section

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒢 ℱ : Sheaf J (Type w)} (s : 𝒢 ⟶ ℱ)

/- Domain-style sampling for Lemma 7.30.6:
- primary domain: relocalization between slice topoi of sheaves, expressed through the canonical
  slice-category adjunction attached to a morphism `s : 𝒢 ⟶ ℱ`;
- sampled owner declarations:
  `Over.mapPullbackAdj`,
  `Over.map`,
  `Over.pullback`,
  `Over.starPullbackIsoStar`,
  `Over.map_obj_hom`,
  `Over.pullback_obj_hom`;
- best owner abstraction: the relocalization morphism `Sh(C, J)/𝒢 ⟶ Sh(C, J)/ℱ` is canonically
  organized by the adjunction `Over.mapPullbackAdj s : Over.map s ⊣ Over.pullback s`; the two
  slice functors are primitive components of that owner, and the compatibility of localization
  inverse-image functors is a derived companion owned by `Over.starPullbackIsoStar s`;
- primitive data: only the sheaf morphism `s`;
- derived API: the functor components `Over.map s`, `Over.pullback s`, their objectwise structure
  morphism formulas `Over.map_obj_hom`, `Over.pullback_obj_hom`, and the inverse-image comparison
  isomorphism `Over.starPullbackIsoStar s`.

Source/core/bridge triage:
- `source-facing`: the relocalization morphism `Sh(C, J)/𝒢 ⟶ Sh(C, J)/ℱ` and the induced
  commutative square of localization geometric morphisms;
- `core/canonical`: `Over.mapPullbackAdj s`;
- `bridge/view`: the component functors `Over.map s`, `Over.pullback s`, the inverse-image
  comparison `Over.starPullbackIsoStar s`, and the objectwise formulas
  `Over.map_obj_hom`, `Over.pullback_obj_hom`.

The file should therefore recall the relocalization through the canonical adjunction owner
`Over.mapPullbackAdj s` and keep the separate slice functors only as companion recalls.
-/

/- Lemma 7.30.6: the relocalization morphism `Sh(C, J)/𝒢 ⟶ Sh(C, J)/ℱ` induced by
`s : 𝒢 ⟶ ℱ` is canonically organized by the slice adjunction
`Over.mapPullbackAdj s : Over.map s ⊣ Over.pullback s`. -/
#check (Over.mapPullbackAdj s : Over.map s ⊣ Over.pullback s)

/- Companion recall: the relocalization direct-image functor is the left adjoint
`Over.map s : Over 𝒢 ⥤ Over ℱ`. -/
#check (Over.map s : Over 𝒢 ⥤ Over ℱ)

/- Companion recall: the relocalization inverse-image functor along `s` is the canonical slice
pullback functor `Over.pullback s : Over ℱ ⥤ Over 𝒢`. -/
#check (Over.pullback s : Over ℱ ⥤ Over 𝒢)

/- Companion recall: objectwise, `Over.map s` replaces the structure morphism by postcomposition
with `s`; this is the upstream owner theorem `Over.map_obj_hom`. -/
#check Over.map_obj_hom

/- Companion recall: objectwise, `Over.pullback s` is represented by the pullback projection
`pullback.snd`; this is the upstream owner theorem `Over.pullback_obj_hom`. -/
#check Over.pullback_obj_hom

/- Companion recall: the square of localization geometric morphisms induced by `s` commutes on
inverse-image functors via the canonical natural isomorphism
`Over.star ℱ ⋙ Over.pullback s ≅ Over.star 𝒢`. -/
#check (Over.starPullbackIsoStar s : Over.star ℱ ⋙ Over.pullback s ≅ Over.star 𝒢)

end

/-! ### Lemma_7_30_7 (from Chap07) -/
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.GrothendieckTopology.SheafifiedRepresentable

universe u v

noncomputable section

namespace CategoryTheory.GrothendieckTopology

attribute [local instance] Types.instConcreteCategory
attribute [local instance] Types.instFunLike

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/- Domain-style sampling for Lemma 7.30.7:
- primary domain: comparison between the localized inverse-image on the slice site `(C / U, J.over
  U)` and the canonical slice inverse-image functor on `Sh(C, J) / h[U]^#[J]`;
- sampled owner declarations:
  `GrothendieckTopology.representableLocalizationComparison_forget`,
  `Functor.sheafAdjunctionContinuous`,
  `Over.forgetAdjStar`,
  `Adjunction.rightAdjointUniq`;
- source/core/bridge triage:
  `source-facing`: the textbook identification of `j_U⁻¹` with the inverse-image functor of the
    localization at `h[U]^#[J]`;
  `core/canonical`: the adjunctions
    `(Over.forget U).sheafPullback ⊣ J.overPullback ... U` and
    `Over.forget h[U]^#[J] ⊣ Over.star h[U]^#[J]`;
  `bridge/view`: the transported comparison along
    `J.representableLocalizationComparison U`.

Primitive data are only the localized object `U` and the two owner adjunctions above. The object
formula is derived API; the canonical owner statement is the natural isomorphism of right adjoints
to the same forgetful functor, obtained via `Adjunction.rightAdjointUniq`. The public surface
should therefore live first at the functor level and only then specialize to objects through the
canonical restriction owner `ℱ.over U`.
-/

section

variable (U : C)
variable [∀ F : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.forget U).op.HasLeftKanExtension F]
variable [HasWeakSheafify (J.over U) (Type (max u v))]
variable [HasWeakSheafify J (Type (max u v))]

/-- Lemma 7.30.7, owner form: under the equivalence
`J.representableLocalizationComparison U : Sh(C/U, J.over U) ≌ Sh(C, J) / h[U]^#[J]`, the
localized
inverse-image functor `j_U⁻¹` is the canonical slice inverse-image functor
`Over.star h[U]^#[J]`. -/
noncomputable def representableLocalizationComparison_inverseImageIso :
    J.overPullback (Type (max u v)) U ⋙ J.representableLocalizationComparison U ≅
      Over.star h[U]^#[J] := by
  let comparison := J.representableLocalizationComparison U
  let hU := h[U]^#[J]
  haveI : comparison.IsEquivalence := J.representableLocalizationComparison_isEquivalence U
  let comparisonAdj := comparison.asEquivalence.toAdjunction
  let comparisonCounitIso := comparison.asEquivalence.counitIso
  let sliceAdj : comparison ⋙ Over.forget hU ⊣ Over.star hU ⋙ comparison.inv :=
    comparisonAdj.comp (Over.forgetAdjStar hU)
  let localizationAdj : comparison ⋙ Over.forget hU ⊣ J.overPullback (Type (max u v)) U :=
    ((Over.forget U).sheafAdjunctionContinuous (Type (max u v)) (J.over U) J).ofNatIsoLeft
      (eqToIso (J.representableLocalizationComparison_forget U).symm)
  let rightIso : Over.star hU ⋙ comparison.inv ≅ J.overPullback (Type (max u v)) U :=
    Adjunction.rightAdjointUniq sliceAdj localizationAdj
  let e' : Over.star hU ≅ J.overPullback (Type (max u v)) U ⋙ comparison :=
    (Functor.rightUnitor (Over.star hU)).symm ≪≫
      Functor.isoWhiskerLeft (Over.star hU) comparisonCounitIso.symm ≪≫
      (Functor.associator (Over.star hU) comparison.inv comparison).symm ≪≫
      Functor.isoWhiskerRight rightIso comparison
  exact e'.symm

/-- Objectwise form of Lemma 7.30.7, stated on the canonical restriction owner `ℱ.over U`. -/
noncomputable def representableLocalizationComparison_inverseImage_obj
    (ℱ : Sheaf J (Type (max u v))) :
    (J.representableLocalizationComparison U).obj (ℱ.over U) ≅
      (Over.star h[U]^#[J]).obj ℱ := by
  simpa [Sheaf.over] using
    (J.representableLocalizationComparison_inverseImageIso U).app ℱ

end

end CategoryTheory.GrothendieckTopology
