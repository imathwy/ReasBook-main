import Mathlib
import StacksProject_2024.Chap04.Definition_4_22_2
import StacksProject_2024.Chap04.Lemma_4_22_3
import StacksProject_2024.Chap04.Remark_4_22_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory

universe uI vI uC vC

section

variable {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
variable (M : I ⥤ C)

/- Domain-style sampling for Lemma 4.22.10:
- primary domain: cofiltered diagrams, their associated pro-objects, and corepresenting data for
  the Hom-colimit functor `X ↦ colim_i Hom(Mᵢ, X)`.
- inspected owner-level declarations:
  `IsEssentiallyConstantCofilteredDiagram`,
  `LimitCone`,
  `Functor.CorepresentableBy`,
  `proSystemHomColimitFunctor`,
  `Limits.colimitObjIsoColimitCompEvaluation`.
- best owner abstraction for the main proposition: `IsEssentiallyConstantCofilteredDiagram M`.
- best owner abstraction for fixed-object corepresenting data:
  `(proSystemHomColimitFunctor M).CorepresentableBy X`.

Primitive-vs-derived split:
- primitive source data: an essentially constant cone on `M`, or equivalently a corepresentation of
  the Hom-colimit functor of `M` by some fixed `X`.
- derived API: the resulting `LimitCone M`, and the Hom-colimit/stage-map comparison packages.
- the private proof layer may compare `Functor.CorepresentableBy` data for
  `proSystemHomColimitFunctor M` directly with the corresponding cone, limit-cone, and
  `CostructuredArrow M X` packages, but the public source-facing bridge statements should expose
  only proposition-level existence criteria unless a canonical witness is available.

Source/core/bridge triage:
- source-facing: the Hom-colimit and stage-map criteria from the textbook.
- core/canonical: `IsEssentiallyConstantCofilteredDiagram M`, `proSystemHomColimitFunctor M`, and
  `LimitCone M`.
- bridge/view: the equivalences below between corepresenting data and the cone/limit-cone/stage-map
  presentations. -/

namespace CategoryTheory.Limits.Cone

/-- Lemma 4.22.10, condition (2), as an owner-level criterion on a cone: the Hom-colimit
comparison for `c` is that every induced Yoneda test cocone on `c.op` is colimiting. -/
def HasHomColimitComparison (c : Cone M) : Prop :=
  ∀ W : C, Nonempty (IsColimit ((uliftYoneda.{uI}.obj W).mapCocone c.op))

end CategoryTheory.Limits.Cone

namespace CategoryTheory.Limits.CostructuredArrow

/-- Lemma 4.22.10, condition (4), as an owner-level criterion on a stage map: `p` satisfies the
Hom-colimit comparison when postcomposition with `p.hom` induces the canonical equivalence
`Hom(X, W) ≃ colimⱼ Hom(Mⱼ, W)` for every test object `W`. -/
def HasHomColimitComparison {X : C} (p : CostructuredArrow M X) : Prop :=
  ∀ W : C,
    Nonempty
      { e : (X ⟶ W) ≃ colimit (M.op ⋙ uliftYoneda.{uI}.obj W) //
          ∀ g : X ⟶ W,
            e g = colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj W) (op p.left)
              (ULift.up (p.hom ≫ g)) }

end CategoryTheory.Limits.CostructuredArrow

open CategoryTheory.Limits.CostructuredArrow

private noncomputable def stageClass (j : I) :
    (proSystemHomColimitFunctor M).obj (M.obj j) :=
  (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) (M.obj j)).inv <|
    colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj (M.obj j)) (op j) (ULift.up (𝟙 (M.obj j)))

private theorem exists_coneOfCorepresentableBy
    {X : C} (e : (proSystemHomColimitFunctor M).CorepresentableBy X) :
    Nonempty ((Functor.const I).obj X ⟶ M) := by
  sorry

private noncomputable def coneOfCorepresentableBy
    {X : C} (e : (proSystemHomColimitFunctor M).CorepresentableBy X) :
    (Functor.const I).obj X ⟶ M :=
  Classical.choice (exists_coneOfCorepresentableBy M e)

private noncomputable def coconePointIso
    {X W : C} (e : (proSystemHomColimitFunctor M).CorepresentableBy X) :
    ULift (X ⟶ W) ≅ colimit (M.op ⋙ uliftYoneda.{uI}.obj W) :=
  equivEquivIso <|
    Equiv.ulift.trans <|
      e.homEquiv.trans (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) W).toEquiv

private theorem coconePointIso_hom_ι
    {X W : C} (e : (proSystemHomColimitFunctor M).CorepresentableBy X)
    (j : I) (f : ULift (M.obj j ⟶ W)) :
    (coconePointIso M e).hom
        (((uliftYoneda.{uI}.obj W).mapCocone
          (Cone.mk X (coneOfCorepresentableBy M e)).op).ι.app (op j) f) =
      colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj W) (op j) f := by
  sorry

private noncomputable def homColimitComparisonIsColimit
    {X W : C} (e : (proSystemHomColimitFunctor M).CorepresentableBy X) :
    IsColimit ((uliftYoneda.{uI}.obj W).mapCocone
      (Cone.mk X (coneOfCorepresentableBy M e)).op) :=
  (colimit.isColimit (M.op ⋙ uliftYoneda.{uI}.obj W)).ofIsoColimit <|
    Cocone.ext (coconePointIso M e).symm <| by
      intro j
      ext f
      simpa using
        (congrArg (fun x ↦ (coconePointIso M e).inv x) (coconePointIso_hom_ι M e j.unop f)).symm

private theorem exists_corepresentableByOfCone_homColimitComparison
    (c : Cone M) (hc : c.HasHomColimitComparison) :
    Nonempty ((proSystemHomColimitFunctor M).CorepresentableBy c.pt) := by
  sorry

-- Proof sketch: this is the dual of Lemma 4.22.9. Pass from the cofiltered diagram to the
-- filtered colimit of the presheaves `Hom(Mᵢ, -)` and identify corepresentability with the
-- chapter owner `IsEssentiallyConstantCofilteredDiagram`.
section

variable [IsCofiltered I]

/-- Lemma 4.22.10, condition (1), expressed through the chapter owner
`IsEssentiallyConstantCofilteredDiagram`: a cofiltered diagram is essentially constant exactly
when its associated pro-object is corepresentable. The textbook Hom-colimit criteria are
companion bridge/view formulations of this canonical statement. -/
theorem essentiallyConstant_proObject_characterizations
    :
    (proSystemHomColimitFunctor M).IsCorepresentable ↔
      IsEssentiallyConstantCofilteredDiagram M := sorry

end

-- Proof sketch: dualize the corresponding representability criterion in Lemma 4.22.9. A
-- corepresentation of the formal pro-object by `X` is equivalent to a cone on `M` with vertex
-- `X` whose induced Yoneda test cocones on `c.op` are colimiting for every test object.
private theorem exists_corepresentableByEquivCone_homColimitComparison
    (X : C) :
    Nonempty
      ((proSystemHomColimitFunctor M).CorepresentableBy X ≃
        { c : Cone M // c.pt = X ∧ c.HasHomColimitComparison }) := by
  sorry

/-- Lemma 4.22.10, condition (2): the pro-object of `M` is corepresented by `X` exactly when `M`
admits a cone with vertex `X` whose canonical Hom-colimit comparison cocones are colimiting on all
test objects `W`. -/
theorem corepresentableBy_iff_exists_cone_homColimitComparison
    (X : C) :
    Nonempty ((proSystemHomColimitFunctor M).CorepresentableBy X) ↔
      ∃ c : Cone M, c.pt = X ∧ c.HasHomColimitComparison := by
  classical
  rcases exists_corepresentableByEquivCone_homColimitComparison M X with ⟨e⟩
  constructor
  · rintro ⟨h⟩
    exact ⟨(e h).1, (e h).2.1, (e h).2.2⟩
  · rintro ⟨c, hcpt, hc⟩
    exact ⟨e.symm ⟨c, hcpt, hc⟩⟩

-- Proof sketch: use Lemma 4.22.3 to pass from a corepresentable pro-object to a limit cone, and
-- conversely the vertex of an essentially constant limit cone already corepresents the pro-object.
/-- Lemma 4.22.10, condition (3), expressed through the limit-cone owner `LimitCone M`: the
pro-object of `M` is corepresented by `X` exactly when `M` admits an essentially constant
limit cone with vertex `X`. -/
private theorem exists_corepresentableByEquivEssentiallyConstant_limitCone
    (X : C) :
    Nonempty
      ((proSystemHomColimitFunctor M).CorepresentableBy X ≃
        { c : LimitCone M // c.cone.pt = X ∧ IsEssentiallyConstantCofilteredCone c.cone }) := by
  sorry

/-- Lemma 4.22.10, condition (3), expressed through the limit-cone owner `LimitCone M`: the
pro-object of `M` is corepresented by `X` exactly when `M` admits an essentially constant
limit cone with vertex `X`. -/
theorem corepresentableBy_iff_exists_essentiallyConstant_limitCone
    (X : C) :
    Nonempty ((proSystemHomColimitFunctor M).CorepresentableBy X) ↔
      ∃ c : LimitCone M, c.cone.pt = X ∧ IsEssentiallyConstantCofilteredCone c.cone := by
  classical
  rcases exists_corepresentableByEquivEssentiallyConstant_limitCone M X with ⟨e⟩
  constructor
  · rintro ⟨h⟩
    exact ⟨(e h).1, (e h).2.1, (e h).2.2⟩
  · rintro ⟨c, hcpt, hc⟩
    exact ⟨e.symm ⟨c, hcpt, hc⟩⟩

-- Proof sketch: dualize the stage-map criterion from Lemma 4.22.9. A distinguished stage map
-- `Mᵢ ⟶ X` determines the forward maps of the corepresenting equivalences
-- `Hom(X, W) ≃ colimⱼ Hom(Mⱼ, W)` for every test object `W`, and conversely those equivalences
-- identify `X` as the corepresenting object.
/-- Lemma 4.22.10, condition (4): the pro-object of `M` is corepresented by `X` exactly when some
stage map `Mᵢ ⟶ X` determines the usual comparison equivalences
`Hom(X, W) ≃ colimⱼ Hom(Mⱼ, W)` for all test objects `W`. -/
private theorem exists_corepresentableByEquivStageMap_homColimitComparison
    (X : C) :
    Nonempty
      ((proSystemHomColimitFunctor M).CorepresentableBy X ≃
        { p : CostructuredArrow M X // HasHomColimitComparison M p }) := by
  sorry

theorem corepresentableBy_iff_exists_stageMap_homColimitComparison
    (X : C) :
    Nonempty ((proSystemHomColimitFunctor M).CorepresentableBy X) ↔
      ∃ p : CostructuredArrow M X, HasHomColimitComparison M p := by
  classical
  rcases exists_corepresentableByEquivStageMap_homColimitComparison M X with ⟨e⟩
  constructor
  · rintro ⟨h⟩
    exact ⟨(e h).1, (e h).2⟩
  · rintro ⟨p, hp⟩
    exact ⟨e.symm ⟨p, hp⟩⟩

/-- Lemma 4.22.10, condition (4), in the chapter owner form `HasProObjectValue`: a diagram has
fixed pro-object value `X` exactly when some stage map into `X` satisfies the Hom-colimit
comparison. -/
theorem hasProObjectValue_iff_exists_stageMap_homColimitComparison
    (X : C) :
    HasProObjectValue M X ↔
      ∃ p : CostructuredArrow M X, HasHomColimitComparison M p := by
  simpa [HasProObjectValue] using
    (corepresentableBy_iff_exists_stageMap_homColimitComparison M X)

end
