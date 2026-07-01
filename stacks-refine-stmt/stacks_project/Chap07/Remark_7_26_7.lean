import Mathlib
import stacks_project.Chap07.Lemma_7_25_8
import stacks_project.Chap07.Lemma_7_26_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

universe v u

noncomputable section

namespace CategoryTheory
namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/- Domain-style sampling for Remark 7.26.7:
- primary domain: glueing data for sheaves on the localized slice sites `U_τ ⊂ C/U`;
- sampled owner API:
  `GrothendieckTopology.overMapPullback`,
  `GrothendieckTopology.overMapPullbackId`,
  `GrothendieckTopology.overMapPullbackComp`,
  `Functor.sheafInducedTopologyEquivOfIsCoverDense`;
- source-facing owner: `LocalizedSliceGlueing J τ`, whose primitive data are the sheaves on the
  sites `U_τ` and the comparison morphisms `f_τ⁻¹ ℱ_U ⟶ ℱ_{U'}`;
- core/canonical owner for inverse image: the slice-site pullback
  `J.overMapPullback (Type (max u v)) f`;
- bridge/view: `LocalizedSliceSheaf.equiv`, the transported localized pullback
  `LocalizedSliceSheaf.pullback`, and `AbsoluteGlueing.toLocalizedSliceGlueing`, which restricts
  the stronger owner `AbsoluteGlueing J`.

Primitive data in this remark are the family `τ`, the induced topologies on the localized slice
sites, and the localized glueing morphisms. The owner-level pullback functor is obtained by
transporting `J.overMapPullback` across `LocalizedSliceSheaf.equiv`, so the file should not keep a
parallel localized inverse-image owner. Since Remark 7.26.7 weakens Lemma 7.26.6 by requiring the
comparison map `c_f` to be an isomorphism only when `f` is an object of `U_τ`, the main entry here
must stay source-facing rather than collapsing back to `AbsoluteGlueing J`.
-/

/-- A family `U ↦ U_τ ⊂ C/U` of full subcategories satisfying the hypotheses of
Remark 7.26.7. -/
class LocalizedSliceFamily (J : GrothendieckTopology C)
    (τ : ∀ U : C, ObjectProperty (Over U)) : Prop where
  /-- The identity object `U/U` belongs to `U_τ`. -/
  id_mem (U : C) : τ U (Over.mk (𝟙 U))
  /-- If `X/U` belongs to `U_τ`, then every member of a covering family of `X` again defines an
  object of `U_τ` by composition with `X ⟶ U`. -/
  cover_mem {U : C} {X : Over U} (_ : τ U X) {S : Sieve X.left} (_ : S ∈ J X.left)
      {Y : C} (g : Y ⟶ X.left) (_ : S g) : τ U (Over.mk (g ≫ X.hom))
  /-- The family is stable under base change. -/
  pullback_mem {U V : C} (f : V ⟶ U) {X : Over U} (_ : τ U X) :
      τ V ((Over.pullback f).obj X)

variable (J : GrothendieckTopology C) (τ : ∀ U : C, ObjectProperty (Over U))

/-- Under the hypotheses of Remark 7.26.7, the inclusion `U_τ ⥤ C/U` is cover-dense. -/
instance localizedSliceInclusion_isCoverDense [LocalizedSliceFamily J τ] (U : C) :
    ((τ U).ι).IsCoverDense (J.over U) := by
  sorry

/-- A sheaf of types on the induced topology of the localized slice site `U_τ`. -/
abbrev LocalizedSliceSheaf [LocalizedSliceFamily J τ] (U : C) :=
  Sheaf (((τ U).ι).inducedTopology (J.over U)) (Type (max u v))

namespace LocalizedSliceSheaf

/-- The canonical comparison equivalence between sheaves on `U_τ` with the induced topology and
sheaves on the full slice site `C/U`. -/
abbrev equiv [LocalizedSliceFamily J τ] (U : C) :
    LocalizedSliceSheaf J τ U ≌ Sheaf (J.over U) (Type (max u v)) :=
  ((τ U).ι).sheafInducedTopologyEquivOfIsCoverDense (J.over U) (Type (max u v))

/-- Pullback of localized sheaves along the morphism of sites attached to `f : V ⟶ U`. This is a
bridge/view obtained by transporting the canonical owner `J.overMapPullback` across
`LocalizedSliceSheaf.equiv`. -/
noncomputable abbrev pullback [LocalizedSliceFamily J τ] {U V : C} (f : V ⟶ U) :
    LocalizedSliceSheaf J τ U ⥤ LocalizedSliceSheaf J τ V :=
  ((equiv J τ U).functor ⋙ J.overMapPullback (Type (max u v)) f) ⋙
    (equiv J τ V).inverse

/-- Pullback on the localized subsite along `𝟙 U` is canonically the identity functor. This is
the localized bridge/view obtained from the owner isomorphism `J.overMapPullbackId`. -/
noncomputable def pullbackId [LocalizedSliceFamily J τ] (U : C) :
    pullback J τ (𝟙 U) ≅ 𝟭 (LocalizedSliceSheaf J τ U) :=
  let e := equiv J τ U
  (Functor.associator e.functor (J.overMapPullback (Type (max u v)) (𝟙 U)) e.inverse).symm ≪≫
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft e.functor (J.overMapPullbackId (Type (max u v)) U))
      e.inverse) ≪≫
    (Functor.isoWhiskerRight (Functor.rightUnitor e.functor) e.inverse) ≪≫
      e.unitIso.symm

/-- Pullback on the localized subsites along a composite is canonically the composite of the
pullback functors. -/
def pullbackComp [LocalizedSliceFamily J τ] {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    pullback J τ f ⋙ pullback J τ g ≅ pullback J τ (g ≫ f) :=
  let eU := equiv J τ U
  let eV := equiv J τ V
  let eW := equiv J τ W
  let Ff := J.overMapPullback (Type (max u v)) f
  let Fg := J.overMapPullback (Type (max u v)) g
  (Functor.associator (((eU.functor ⋙ Ff) ⋙ eV.inverse)) (eV.functor ⋙ Fg) eW.inverse).symm ≪≫
    (Functor.isoWhiskerRight
      (Functor.associator (eU.functor ⋙ Ff) eV.inverse (eV.functor ⋙ Fg))
      eW.inverse) ≪≫
      (Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft (eU.functor ⋙ Ff) (eV.invFunIdAssoc Fg))
        eW.inverse) ≪≫
        (Functor.isoWhiskerRight (Functor.associator eU.functor Ff Fg) eW.inverse) ≪≫
          (Functor.isoWhiskerRight
            (Functor.isoWhiskerLeft eU.functor (J.overMapPullbackComp (Type (max u v)) g f))
            eW.inverse)

end LocalizedSliceSheaf

/-- The source-facing localized glueing datum of Remark 7.26.7: sheaves on the induced sites
`U_τ`, comparison morphisms for every map in `C`, the identity and cocycle compatibilities, and
the requirement that the comparison is an isomorphism whenever the map itself is an object of
`U_τ`. -/
structure LocalizedSliceGlueing [LocalizedSliceFamily J τ] where
  /-- The sheaf on the induced site `U_τ`. -/
  obj (U : C) : LocalizedSliceSheaf J τ U
  /-- The comparison morphism `f_τ⁻¹ ℱ_U ⟶ ℱ_{U'}`. -/
  transition {U V : C} (f : V ⟶ U) :
      (LocalizedSliceSheaf.pullback J τ f).obj (obj U) ⟶ obj V
  /-- The comparison attached to an identity morphism is the canonical localized identity
  pullback comparison. -/
  transition_id (U : C) :
      transition (𝟙 U) = (LocalizedSliceSheaf.pullbackId J τ U).hom.app (obj U)
  /-- The comparison morphisms satisfy the source cocycle square expressing
  `c_g ∘ g_τ⁻¹(c_f) = c_{f ∘ g}`. -/
  transition_comp {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
      CommSq ((LocalizedSliceSheaf.pullbackComp J τ f g).hom.app (obj U))
        ((LocalizedSliceSheaf.pullback J τ g).map (transition f)) (transition (g ≫ f))
        (transition g)
  /-- If `f : V ⟶ U` is itself an object of `U_τ`, then the comparison map `c_f` is an
  isomorphism. -/
  isIso_transition_of_mem {U V : C} (f : V ⟶ U) (_ : τ U (Over.mk f)) :
      IsIso (transition f)

namespace LocalizedSliceGlueing

variable [LocalizedSliceFamily J τ]

/-- A morphism of localized glueings is a family of local sheaf morphisms compatible with the
transition morphisms. -/
@[ext] structure Hom (F G : LocalizedSliceGlueing J τ) where
  /-- The local component on `U_τ`. -/
  app (U : C) : F.obj U ⟶ G.obj U
  /-- Compatibility of the local components with localized pullback. -/
  naturality {U V : C} (f : V ⟶ U) :
      CommSq ((LocalizedSliceSheaf.pullback J τ f).map (app U))
        (F.transition f) (G.transition f) (app V)

private theorem localizedSliceGlueing_id_naturality (F : LocalizedSliceGlueing J τ) :
    ∀ {U V : C} (f : V ⟶ U),
      CommSq ((LocalizedSliceSheaf.pullback J τ f).map (𝟙 (F.obj U)))
        (F.transition f) (F.transition f) (𝟙 (F.obj V)) := by
  intro U V f
  exact .mk (by simp)

private def localizedSliceGlueingId (F : LocalizedSliceGlueing J τ) :
    LocalizedSliceGlueing.Hom J τ F F where
  app U := 𝟙 (F.obj U)
  naturality := localizedSliceGlueing_id_naturality J τ F

private theorem localizedSliceGlueing_comp_naturality
    {F G H : LocalizedSliceGlueing J τ} (α : LocalizedSliceGlueing.Hom J τ F G)
    (β : LocalizedSliceGlueing.Hom J τ G H) :
    ∀ {U V : C} (f : V ⟶ U),
      CommSq ((LocalizedSliceSheaf.pullback J τ f).map (α.app U ≫ β.app U))
        (F.transition f) (H.transition f) (α.app V ≫ β.app V) := by
  intro U V f
  exact .mk <| by
    rw [Functor.map_comp, Category.assoc, (β.naturality f).w]
    rw [← Category.assoc, (α.naturality f).w]
    simp [Category.assoc]

private def localizedSliceGlueingComp
    {F G H : LocalizedSliceGlueing J τ} (α : LocalizedSliceGlueing.Hom J τ F G)
    (β : LocalizedSliceGlueing.Hom J τ G H) :
    LocalizedSliceGlueing.Hom J τ F H where
  app U := α.app U ≫ β.app U
  naturality := localizedSliceGlueing_comp_naturality J τ α β

private theorem localizedSliceGlueing_id_comp
    {F G : LocalizedSliceGlueing J τ} (α : LocalizedSliceGlueing.Hom J τ F G) :
    localizedSliceGlueingComp J τ (localizedSliceGlueingId J τ F) α = α := by
  ext U
  simp [localizedSliceGlueingComp, localizedSliceGlueingId]

private theorem localizedSliceGlueing_comp_id
    {F G : LocalizedSliceGlueing J τ} (α : LocalizedSliceGlueing.Hom J τ F G) :
    localizedSliceGlueingComp J τ α (localizedSliceGlueingId J τ G) = α := by
  ext U
  simp [localizedSliceGlueingComp, localizedSliceGlueingId]

private theorem localizedSliceGlueing_assoc
    {F G H K : LocalizedSliceGlueing J τ} (α : LocalizedSliceGlueing.Hom J τ F G)
    (β : LocalizedSliceGlueing.Hom J τ G H) (γ : LocalizedSliceGlueing.Hom J τ H K) :
    localizedSliceGlueingComp J τ (localizedSliceGlueingComp J τ α β) γ =
      localizedSliceGlueingComp J τ α (localizedSliceGlueingComp J τ β γ) := by
  ext U
  simp [localizedSliceGlueingComp, Category.assoc]

/-- The category of localized glueing data from Remark 7.26.7. -/
instance : Category (LocalizedSliceGlueing J τ) where
  Hom F G := LocalizedSliceGlueing.Hom J τ F G
  id := localizedSliceGlueingId J τ
  comp α β := localizedSliceGlueingComp J τ α β
  id_comp := localizedSliceGlueing_id_comp J τ
  comp_id := localizedSliceGlueing_comp_id J τ
  assoc := localizedSliceGlueing_assoc J τ

end LocalizedSliceGlueing

namespace AbsoluteGlueing

/-- Any absolute glueing restricts to the localized source-facing glueing datum on the subsites
`U_τ`. -/
def toLocalizedSliceGlueing [LocalizedSliceFamily J τ] (F : AbsoluteGlueing J) :
    LocalizedSliceGlueing J τ where
  obj U := (LocalizedSliceSheaf.equiv J τ U).inverse.obj (F.obj U)
  transition {U V} f :=
    ((LocalizedSliceSheaf.equiv J τ V).inverse.mapIso
        ((J.overMapPullback (Type (max u v)) f).mapIso
          ((LocalizedSliceSheaf.equiv J τ U).counitIso.app (F.obj U))) ≪≫
      (LocalizedSliceSheaf.equiv J τ V).inverse.mapIso (F.transition f)).hom
  transition_id U := by
    let e := LocalizedSliceSheaf.equiv J τ U
    let ε := e.counitIso.hom
    let η := e.unitIso.inv
    rw [F.transition_id U]
    change e.inverse.map ((J.overMapPullback (Type (max u v)) (𝟙 U)).map (ε.app (F.obj U))) ≫
        e.inverse.map ((J.overMapPullbackId (Type (max u v)) U).hom.app (F.obj U)) =
      e.inverse.map
          ((J.overMapPullbackId (Type (max u v)) U).hom.app
            (e.functor.obj (e.inverse.obj (F.obj U)))) ≫
        η.app (e.inverse.obj (F.obj U))
    rw [show η.app (e.inverse.obj (F.obj U)) = e.inverse.map (e.counit.app (F.obj U)) by
      simpa [η] using e.unitInv_app_inverse (F.obj U)]
    rw [← e.inverse.map_comp]
    change e.inverse.map
        ((J.overMapPullback (Type (max u v)) (𝟙 U)).map (ε.app (F.obj U)) ≫
          (J.overMapPullbackId (Type (max u v)) U).hom.app (F.obj U)) =
      e.inverse.map
        ((J.overMapPullbackId (Type (max u v)) U).hom.app
            (e.functor.obj (e.inverse.obj (F.obj U))) ≫
          e.counit.app (F.obj U))
    exact congrArg e.inverse.map <|
      (J.overMapPullbackId (Type (max u v)) U).hom.naturality (ε.app (F.obj U))
  transition_comp f g := by
    sorry
  isIso_transition_of_mem f _ := by
    infer_instance

/-- The stronger absolute-glueing owner restricts functorially to the localized source-facing
glueing data. -/
def toLocalizedSliceGlueingFunctor [LocalizedSliceFamily J τ] :
    AbsoluteGlueing J ⥤ LocalizedSliceGlueing J τ where
  obj := toLocalizedSliceGlueing J τ
  map {F G} α :=
    { app := fun U ↦ (LocalizedSliceSheaf.equiv J τ U).inverse.map (α.app U)
      naturality := by
        intro U V f
        sorry }
  map_id F := by
    apply LocalizedSliceGlueing.Hom.ext
    funext U
    rfl
  map_comp α β := by
    apply LocalizedSliceGlueing.Hom.ext
    funext U
    rfl

end AbsoluteGlueing

/-- The sheaf on `(C, J)` determines the localized glueing datum of Remark 7.26.7 by first
forming its canonical absolute glueing and then restricting that stronger datum to the localized
slice subsites `U_τ`. -/
def sheafToLocalizedSliceGlueingFunctor [LocalizedSliceFamily J τ] :
    Sheaf J (Type (max u v)) ⥤ LocalizedSliceGlueing J τ :=
  sheafToAbsoluteGlueingFunctor J ⋙ AbsoluteGlueing.toLocalizedSliceGlueingFunctor J τ

/-- Remark 7.26.7 (tag `0GWL`): for a family `U ↦ U_τ ⊂ C/U` satisfying the localized-slice
hypotheses, the canonical functor from sheaves on `(C, J)` to localized glueing data is an
equivalence. This is the source-faithful localized variant of Lemma 7.26.6: the transition maps
are required to be isomorphisms only for arrows lying in the corresponding localized subsite. -/
instance sheafToLocalizedSliceGlueingFunctor_isEquivalence [LocalizedSliceFamily J τ] :
    Functor.IsEquivalence (sheafToLocalizedSliceGlueingFunctor J τ) := by
  sorry

end GrothendieckTopology
end CategoryTheory
