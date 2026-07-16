import Mathlib
import StacksProject_2024.stacks_project.Chap04.Definition_4_22_2
import StacksProject_2024.stacks_project.Chap04.Lemma_4_22_3
import StacksProject_2024.stacks_project.Chap04.Remark_4_22_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open scoped CategoryTheory

universe uI vI uC vC

section

variable {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
variable [IsFiltered I] (M : I ⥤ C)

namespace CategoryTheory.Limits.Cocone

/-- Lemma 4.22.9, condition (2), as an owner-level criterion on a cocone: the Hom-colimit
comparison for `c` is that every induced co-Yoneda test cocone is colimiting. -/
abbrev HasHomColimitComparison (c : CategoryTheory.Limits.Cocone M) :=
  ∀ W : C, IsColimit ((uliftCoyoneda.{uI}.obj (Opposite.op W)).mapCocone c)

end CategoryTheory.Limits.Cocone

private noncomputable def coconeOfRepresentableBy
    {X : C} (e : (colimit (M ⋙ uliftYoneda.{uI})).RepresentableBy X) :
    Cocone M := by
  let eIso : uliftYoneda.obj X ≅ colimit (M ⋙ uliftYoneda.{uI}) :=
    RepresentableBy.equivUliftYonedaIso _ _ e
  let hYoneda :
      (uliftYoneda.{uI} : C ⥤ Cᵒᵖ ⥤ Type (max uI vC)).FullyFaithful :=
    ULiftYoneda.fullyFaithful C
  refine
    { pt := X
      ι :=
        { app := fun i ↦ hYoneda.preimage ((colimit.ι (M ⋙ uliftYoneda.{uI}) i) ≫ eIso.inv)
          naturality := ?_ } }
  intro i j f
  apply hYoneda.map_injective
  simp only [Functor.map_comp, hYoneda.map_preimage]
  simpa using congrArg (fun τ ↦ τ ≫ eIso.inv) (colimit.w (M ⋙ uliftYoneda.{uI}) f)

private noncomputable def coconePointIso
    {X W : C} (e : (colimit (M ⋙ uliftYoneda.{uI})).RepresentableBy X) :
    ULift (W ⟶ X) ≅ colimit (M ⋙ uliftCoyoneda.{uI}.obj (op W)) :=
  (RepresentableBy.equivUliftYonedaIso _ _ e).app (op W) ≪≫
    colimitObjIsoColimitCompEvaluation (M ⋙ uliftYoneda.{uI}) (op W)

omit [IsFiltered I] in
private theorem coconePointIso_hom_ι
    {X W : C} (e : (colimit (M ⋙ uliftYoneda.{uI})).RepresentableBy X)
    (j : I) (f : ULift (W ⟶ M.obj j)) :
    let pointIso : ULift (W ⟶ X) ≅ colimit (M ⋙ uliftCoyoneda.{uI}.obj (op W)) :=
      coconePointIso M e
    pointIso.hom
        (((uliftCoyoneda.{uI}.obj (op W)).mapCocone (coconeOfRepresentableBy M e)).ι.app j f) =
      colimit.ι (M ⋙ uliftCoyoneda.{uI}.obj (op W)) j f := by
  let eIso : uliftYoneda.obj X ≅ colimit (M ⋙ uliftYoneda.{uI}) :=
    RepresentableBy.equivUliftYonedaIso _ _ e
  let hYoneda :
      (uliftYoneda.{uI} : C ⥤ Cᵒᵖ ⥤ Type (max uI vC)).FullyFaithful :=
    ULiftYoneda.fullyFaithful C
  simp [coconePointIso, coconeOfRepresentableBy]
  simpa using congrArg (fun g ↦ g f)
    (colimitObjIsoColimitCompEvaluation_ι_app_hom (M ⋙ uliftYoneda.{uI}) j (op W))

private noncomputable def homColimitComparisonIsColimit
    {X W : C} (e : (colimit (M ⋙ uliftYoneda.{uI})).RepresentableBy X) :
    IsColimit ((uliftCoyoneda.{uI}.obj (op W)).mapCocone (coconeOfRepresentableBy M e)) := by
  let pointIso : ULift (W ⟶ X) ≅ colimit (M ⋙ uliftCoyoneda.{uI}.obj (op W)) :=
    coconePointIso M e
  refine (colimit.isColimit (M ⋙ uliftCoyoneda.{uI}.obj (op W))).ofIsoColimit <|
    Cocone.ext pointIso.symm <| ?_
  intro j
  ext f
  simpa [pointIso] using
    (congrArg (fun x ↦ pointIso.inv x)
      (coconePointIso_hom_ι M e j f)).symm

private noncomputable def uliftYonedaMapCoconeIsColimit
    (c : Cocone M)
    (h : c.HasHomColimitComparison) :
    IsColimit (uliftYoneda.mapCocone c) := by
  refine evaluationJointlyReflectsColimits _ ?_
  intro Y
  simpa using h Y.unop

private noncomputable def uliftYonedaIsoOfCocone_homColimitComparison
    (c : Cocone M)
    (h : c.HasHomColimitComparison) :
    uliftYoneda.obj c.pt ≅ colimit (M ⋙ uliftYoneda.{uI}) :=
  (uliftYonedaMapCoconeIsColimit M c h).coconePointUniqueUpToIso
    (colimit.isColimit (M ⋙ uliftYoneda.{uI}))

private noncomputable def representableByOfCocone_homColimitComparison
    (c : Cocone M)
    (h : c.HasHomColimitComparison) :
    (colimit (M ⋙ uliftYoneda.{uI})).RepresentableBy c.pt :=
  (RepresentableBy.equivUliftYonedaIso _ _).symm <|
    uliftYonedaIsoOfCocone_homColimitComparison M c h

private noncomputable def homColimitComparisonIsColimit_of_essentiallyConstant
    {c : Cocone M} (hc : IsEssentiallyConstantFilteredCocone c) (W : C) :
    IsColimit ((uliftCoyoneda.{uI}.obj (op W)).mapCocone c) :=
  let hc' := hc.mapCocone (uliftCoyoneda.{uI}.obj (op W))
  hc'.isColimit

omit [IsFiltered I] in
private theorem isEssentiallyConstantFilteredCocone_extend
    {c : Cocone M} (hc : IsEssentiallyConstantFilteredCocone c)
    {X : C} (e : c.pt ≅ X) :
    IsEssentiallyConstantFilteredCocone (c.extend e.hom) := by
  rcases hc with ⟨i, σ, hfac⟩
  refine ⟨i, SplitEpi.comp σ ⟨e.inv, by simp⟩, ?_⟩
  · intro j
    rcases hfac j with ⟨k, ik, jk, hjk⟩
    refine ⟨k, ik, jk, ?_⟩
    simpa [Category.assoc] using hjk

private noncomputable def colimitCoconeOfCocone_homColimitComparison
    (c : Cocone M)
    (h : c.HasHomColimitComparison) :
    ColimitCocone M :=
  ⟨c, isColimitOfReflects (uliftYoneda.{uI})
    (uliftYonedaMapCoconeIsColimit M c h)⟩

/- Domain-style sampling for Lemma 4.22.9:
- primary domain: filtered diagrams, their formal ind-objects, and representability/corepresenting
  data for the Hom-colimit presheaf.
- inspected owner-level declarations:
  `IsEssentiallyConstantFilteredDiagram`,
  `Cocone`,
  `ColimitCocone`,
  `StructuredArrow`,
  `Cocone.equivStructuredArrow`,
  `Functor.IsRepresentedBy`,
  `Functor.RepresentableBy`,
  `CategoryTheory.indLim_iso_yoneda_equiv_representableBy`.
- best owner abstraction in the target universe-general setting:
  `IsEssentiallyConstantFilteredDiagram M` for the source-facing predicate, and `ColimitCocone M`
  for actual colimit data; the cocone comparison criterion should be stated over `Cocone M`
  rather than a raw natural-transformation sigma package, and the stage-map criterion should be
  stated over `StructuredArrow X M` rather than a raw pair `(i, X ⟶ M.obj i)`; fixed-object
  representability is most canonically phrased through the owner structure
  `Functor.RepresentableBy`, while the stage-map criterion keeps `Functor.IsRepresentedBy` only
  for the specific universal element induced by that stage map.

Primitive-vs-derived split:
- primitive data: a cocone or colimit cocone on `M`, and representability data for the formal
  ind-object `colimit (M ⋙ uliftYoneda.{uI})`.
- derived API: `HasColimit M` together with the chosen `colimit.cocone M`, which should not be
  stored as primitive public data when `ColimitCocone M` is the real owner; raw sigma encodings
  of cocones and stage maps are likewise derived views once `Cocone M` and `StructuredArrow X M`
  are available; chosen universal elements and their pointwise bijectivity formulas are derived
  from `Functor.RepresentableBy`/`Functor.IsRepresentedBy`.

Source/core/bridge triage:
- `source-facing`: the Hom-colimit and stage-map criteria, which match the textbook conditions.
- `core/canonical`: `IsEssentiallyConstantFilteredDiagram M`, `Cocone M`,
  `ColimitCocone M`, and `StructuredArrow X M`.
- `bridge/view`: representability of `colimit (M ⋙ uliftYoneda.{uI})`; for small index
  categories this also compares to `Ind.lim`, but the present file stays universe-general; the
  left-hand owner is `Functor.RepresentableBy`, and the stage-map criterion uses
  `Functor.IsRepresentedBy` only for its specific universal element witness rather than a raw
  duplicated bijectivity package. The private proof layer may use equivalences between
  `Functor.RepresentableBy` data and owner-level packages on `Cocone M`, `ColimitCocone M`, and
  `StructuredArrow X M`, but the public bridge/view layer should expose only proposition-level
  existence criteria unless a canonical witness is available. -/

/-- Lemma 4.22.9, condition (1), expressed through the chapter owner
`IsEssentiallyConstantFilteredDiagram`: a filtered diagram is essentially constant exactly when
its associated ind-object is representable. The textbook Hom-colimit criteria are equivalent
bridge/view formulations of this canonical statement. -/
theorem essentiallyConstant_indObject_characterizations
    :
    (colimit (M ⋙ uliftYoneda.{uI})).IsRepresentable ↔
      IsEssentiallyConstantFilteredDiagram M := sorry

omit [IsFiltered I]

/- Lemma 4.22.9, condition (2), as a direct equivalence of representing data with cocone data:
the ind-object of `M` is represented by `X` exactly when `M` admits a cocone with vertex `X`
whose canonical Hom-colimit comparison cocones are colimiting on all co-Yoneda test functors. -/
private theorem exists_representableByEquivCocone_homColimitComparison
    (X : C) :
    Nonempty
      ((colimit (M ⋙ uliftYoneda.{uI})).RepresentableBy X ≃
        Σ c : { c : Cocone M // c.pt = X }, c.1.HasHomColimitComparison) := by
  classical
  refine ⟨
    { toFun := fun e ↦
        ⟨⟨coconeOfRepresentableBy M e, rfl⟩, fun W ↦ homColimitComparisonIsColimit M e⟩
      invFun := fun c ↦ by
        rcases c with ⟨⟨c, rfl⟩, hc⟩
        exact representableByOfCocone_homColimitComparison M c hc
      left_inv := by
        sorry
      right_inv := by
        sorry }⟩

/- Lemma 4.22.9, condition (2), as a direct equivalence of representing data with cocone data:
the ind-object of `M` is represented by `X` exactly when `M` admits a cocone with vertex `X`
whose canonical Hom-colimit comparison cocones are colimiting on all co-Yoneda test functors. -/
theorem representableBy_iff_exists_cocone_homColimitComparison
    (X : C) :
    Nonempty ((colimit (M ⋙ uliftYoneda.{uI})).RepresentableBy X) ↔
      ∃ c : Cocone M, c.pt = X ∧ Nonempty (c.HasHomColimitComparison) := by
  classical
  rcases exists_representableByEquivCocone_homColimitComparison M X with ⟨e⟩
  constructor
  · rintro ⟨h⟩
    exact ⟨(e h).1.1, (e h).1.2, ⟨(e h).2⟩⟩
  · rintro ⟨c, hcpt, ⟨hc⟩⟩
    exact ⟨e.symm ⟨⟨c, hcpt⟩, hc⟩⟩

/- Lemma 4.22.9, condition (3), as a direct equivalence of representing data with colimit-cocone
data: the ind-object of `M` is represented by `X` exactly when `M` admits an essentially constant
colimit cocone with vertex `X`. -/
private theorem exists_representableByEquivEssentiallyConstant_colimitCocone
    (X : C) :
    Nonempty
      ((colimit (M ⋙ uliftYoneda.{uI})).RepresentableBy X ≃
        { c : ColimitCocone M //
            c.cocone.pt = X ∧ IsEssentiallyConstantFilteredCocone c.cocone }) := by
  sorry

/- Lemma 4.22.9, condition (3), as a direct equivalence of representing data with colimit-cocone
data: the ind-object of `M` is represented by `X` exactly when `M` admits an essentially constant
colimit cocone with vertex `X`. -/
theorem representableBy_iff_exists_essentiallyConstant_colimitCocone
    (X : C) :
    Nonempty ((colimit (M ⋙ uliftYoneda.{uI})).RepresentableBy X) ↔
      ∃ c : ColimitCocone M,
        c.cocone.pt = X ∧ IsEssentiallyConstantFilteredCocone c.cocone := by
  classical
  rcases exists_representableByEquivEssentiallyConstant_colimitCocone M X with ⟨e⟩
  constructor
  · rintro ⟨h⟩
    exact ⟨(e h).1, (e h).2.1, (e h).2.2⟩
  · rintro ⟨c, hcpt, hc⟩
    exact ⟨e.symm ⟨c, hcpt, hc⟩⟩

/- Lemma 4.22.9, condition (4), as a direct equivalence of representing data with a stage map:
the ind-object of `M` is represented by `X` exactly when some stage map `X ⟶ M.obj i`
determines a universal element in the Hom-colimit presheaf. -/
private theorem exists_representableByEquivStageMap_homColimitComparison
    (X : C) :
    Nonempty
      ((colimit (M ⋙ uliftYoneda.{uI})).RepresentableBy X ≃
        { p : StructuredArrow X M //
            (colimit (M ⋙ uliftYoneda.{uI})).IsRepresentedBy
              ((colimit.ι (M ⋙ uliftYoneda.{uI}) p.right).app (op X) (ULift.up p.hom)) }) := by
  sorry

/- Lemma 4.22.9, condition (4), as a direct equivalence of representing data with a stage map:
the ind-object of `M` is represented by `X` exactly when some stage map `X ⟶ M.obj i`
determines a universal element in the Hom-colimit presheaf. -/
theorem representableBy_iff_exists_stageMap_homColimitComparison
    (X : C) :
    Nonempty ((colimit (M ⋙ uliftYoneda.{uI})).RepresentableBy X) ↔
      ∃ p : StructuredArrow X M,
        (colimit (M ⋙ uliftYoneda.{uI})).IsRepresentedBy
          ((colimit.ι (M ⋙ uliftYoneda.{uI}) p.right).app (op X) (ULift.up p.hom)) := by
  classical
  rcases exists_representableByEquivStageMap_homColimitComparison M X with ⟨e⟩
  constructor
  · rintro ⟨h⟩
    exact ⟨(e h).1, (e h).2⟩
  · rintro ⟨p, hp⟩
    exact ⟨e.symm ⟨p, hp⟩⟩

end
