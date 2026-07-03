import Mathlib
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_4_22_9 (from Chap04) -/
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

/-- Helper for Lemma 4.22.9: if the Hom-colimit comparison for a cocone is colimiting, then the
identity on the cocone point comes from one stage. -/
private theorem exists_section_of_homColimitComparison
    {c : Cocone M} (h : c.HasHomColimitComparison) :
    ∃ i : I, ∃ s : c.pt ⟶ M.obj i, s ≫ c.ι.app i = 𝟙 c.pt := by
  -- Evaluate the comparison at the cocone point and lift the identity through the colimit.
  obtain ⟨i, u, hu⟩ :=
    Types.jointly_surjective_of_isColimit (h c.pt) (ULift.up (𝟙 c.pt))
  refine ⟨i, u.down, ?_⟩
  -- Unwinding the co-Yoneda action turns the lifted element into a section of the chosen leg.
  simpa using congrArg ULift.down hu

/-- Helper for Lemma 4.22.9: a cocone satisfying the Hom-colimit comparison is essentially
constant in the sense of Definition 4.22.1. -/
private theorem essentiallyConstantFilteredCocone_of_homColimitComparison
    {c : Cocone M} (h : c.HasHomColimitComparison) :
    IsEssentiallyConstantFilteredCocone c := by
  -- Route correction: prove the textbook `(2) ⇒ (1)` directly from a stage retraction and the
  -- filtered-colimit equality criterion, rather than trying to package representability first.
  rw [isEssentiallyConstantFilteredCocone_iff]
  obtain ⟨i, s, hs⟩ := exists_section_of_homColimitComparison M h
  refine ⟨i, s, hs, ?_⟩
  intro j
  -- Compare the classes of `𝟙_{M_j}` and `c.ι.app j ≫ s` in the Hom-colimit for `W = M.obj j`.
  have hEq :
      ((uliftCoyoneda.{uI}.obj (op (M.obj j))).mapCocone c).ι.app i
          (ULift.up (c.ι.app j ≫ s)) =
        ((uliftCoyoneda.{uI}.obj (op (M.obj j))).mapCocone c).ι.app j
          (ULift.up (𝟙 (M.obj j))) := by
    change ULift.up ((c.ι.app j ≫ s) ≫ c.ι.app i) = ULift.up (𝟙 (M.obj j) ≫ c.ι.app j)
    apply congrArg ULift.up
    have hsj : c.ι.app j ≫ s ≫ c.ι.app i = c.ι.app j := by
      simpa using congrArg (fun f ↦ c.ι.app j ≫ f) hs
    simpa [hsj]
  obtain ⟨k, ik, jk, hk⟩ :=
    (CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff
      (F := M ⋙ uliftCoyoneda.{uI}.obj (op (M.obj j))) (h (M.obj j))).mp hEq
  refine ⟨k, ik, jk, ?_⟩
  -- Equality in the filtered colimit provides a common refinement where the desired factorization
  -- identity holds.
  simpa [FunctorToTypes.map_comp_apply, Category.assoc] using (congrArg ULift.down hk).symm

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
      IsEssentiallyConstantFilteredDiagram M := by
  constructor
  · intro hM
    -- Choose a representing object and convert it into the cocone supplied by the Yoneda colimit.
    rcases hM.has_representation with ⟨X, ⟨e⟩⟩
    refine ⟨coconeOfRepresentableBy M e, ?_⟩
    -- The source-proof core is that the Hom-colimit comparison forces eventual constancy.
    exact essentiallyConstantFilteredCocone_of_homColimitComparison M
      (fun W ↦ homColimitComparisonIsColimit M e)
  · rintro ⟨c, hc⟩
    -- An essentially constant cocone makes every co-Yoneda comparison cocone colimiting.
    exact
      (representableByOfCocone_homColimitComparison M c
        (fun W ↦ homColimitComparisonIsColimit_of_essentiallyConstant M hc W)).isRepresentable

/-- Helper for Lemma 4.22.9: rebuilding a cocone from the representability datum extracted from a
Hom-colimit comparison cocone recovers the original cocone. -/
private theorem coconeOfRepresentableBy_representableByOfCocone_homColimitComparison_eq
    (c : Cocone M)
    (h : c.HasHomColimitComparison) :
    coconeOfRepresentableBy M (representableByOfCocone_homColimitComparison M c h) = c := by
  -- The recovered representability datum is built from the cocone-point uniqueness iso, so each
  -- recovered leg is exactly the original leg after applying full faithfulness of `uliftYoneda`.
  cases c with
  | mk pt ι =>
      -- Once the cocone point is fixed, it remains to compare the natural-transformation legs.
      simp [coconeOfRepresentableBy, representableByOfCocone_homColimitComparison]
      ext i
      let hYoneda :
          (uliftYoneda.{uI} : C ⥤ Cᵒᵖ ⥤ Type (max uI vC)).FullyFaithful :=
        ULiftYoneda.fullyFaithful C
      apply hYoneda.map_injective
      simpa [hYoneda] using
        (IsColimit.comp_coconePointUniqueUpToIso_inv
          (uliftYonedaMapCoconeIsColimit M { pt := pt, ι := ι } h)
          (colimit.isColimit (M ⋙ uliftYoneda.{uI})) i)

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
        intro e
        -- Route correction: reduce the roundtrip on representing data to the universal element at
        -- `𝟙 X`, so the remaining comparison is exactly between the two canonical Yoneda isos.
        apply RepresentableBy.ext
        let c0 := coconeOfRepresentableBy M e
        let P := uliftYonedaMapCoconeIsColimit M c0 (fun W ↦ homColimitComparisonIsColimit M e)
        let uIso := uliftYonedaIsoOfCocone_homColimitComparison M c0
          (fun W ↦ homColimitComparisonIsColimit M e)
        let eIso : uliftYoneda.obj X ≅ colimit (M ⋙ uliftYoneda.{uI}) :=
          RepresentableBy.equivUliftYonedaIso _ _ e
        have hdesc :
            eIso.hom = P.desc (colimit.cocone (M ⋙ uliftYoneda.{uI})) := by
          apply (P.uniq _ eIso.hom)
          intro j
          ext W x
          simp [c0, coconeOfRepresentableBy, eIso, Category.assoc]
        have hhom : uIso.hom = eIso.hom := by
          have hu :
              uIso.hom = P.desc (colimit.cocone (M ⋙ uliftYoneda.{uI})) := by
            simpa [uIso, uliftYonedaIsoOfCocone_homColimitComparison] using
              (IsColimit.coconePointUniqueUpToIso_hom_desc
                (P := P) (Q := colimit.isColimit (M ⋙ uliftYoneda.{uI}))
                (r := colimit.cocone (M ⋙ uliftYoneda.{uI})))
          exact hu.trans hdesc.symm
        have happ := congrArg (fun η ↦ η.app (op X) (ULift.up (𝟙 X))) hhom
        simpa [representableByOfCocone_homColimitComparison, uIso, eIso] using happ
      right_inv := by
        rintro ⟨⟨c, rfl⟩, hc⟩
        -- Route correction: reduce the cocone roundtrip to equality of cocone legs; the
        -- `HasHomColimitComparison` witness is subsingleton once the cocone is fixed.
        have hcocone :
            coconeOfRepresentableBy M (representableByOfCocone_homColimitComparison M c hc) = c :=
          coconeOfRepresentableBy_representableByOfCocone_homColimitComparison_eq M c hc
        refine Sigma.ext (Subtype.ext hcocone) ?_
        exact Subsingleton.helim
          (congrArg (fun d : Cocone M ↦ d.HasHomColimitComparison) hcocone)
          (fun W ↦ homColimitComparisonIsColimit (M := M) (W := W)
            (representableByOfCocone_homColimitComparison M c hc))
          hc }⟩

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

variable [IsFiltered I]

theorem representableBy_iff_exists_essentiallyConstant_colimitCocone
    (X : C) :
    Nonempty ((colimit (M ⋙ uliftYoneda.{uI})).RepresentableBy X) ↔
      ∃ c : ColimitCocone M,
        c.cocone.pt = X ∧ IsEssentiallyConstantFilteredCocone c.cocone := by
  classical
  constructor
  · rintro ⟨e⟩
    -- Package the condition-(2) cocone as a colimit cocone and reuse the textbook `(2) ⇒ (1)`
    -- argument already formalized above.
    obtain ⟨c, hcpt, ⟨hc⟩⟩ :=
      (representableBy_iff_exists_cocone_homColimitComparison M X).mp ⟨e⟩
    exact ⟨colimitCoconeOfCocone_homColimitComparison M c hc, hcpt,
      essentiallyConstantFilteredCocone_of_homColimitComparison M hc⟩
  · rintro ⟨c, hcpt, hc⟩
    cases hcpt
    -- Forgetting the chosen colimit proof leaves an essentially constant cocone, which already
    -- gives the required representing datum.
    refine ⟨representableByOfCocone_homColimitComparison M c.cocone ?_⟩
    intro W
    exact homColimitComparisonIsColimit_of_essentiallyConstant M hc W

/-- Helper for Lemma 4.22.9: a section of one cocone leg represents the universal element of the
recovered representability datum by the corresponding stage class. -/
private theorem representableByOfCocone_homColimitComparison_homEquiv_id_eq_stageMap
    {c : Cocone M} (h : c.HasHomColimitComparison) {i : I} (s : c.pt ⟶ M.obj i)
    (hs : s ≫ c.ι.app i = 𝟙 c.pt) :
    (representableByOfCocone_homColimitComparison M c h).homEquiv (𝟙 c.pt) =
      ((colimit.ι (M ⋙ uliftYoneda.{uI}) i).app (op c.pt) (ULift.up s)) := by
  let uIso := uliftYonedaIsoOfCocone_homColimitComparison M c h
  -- Evaluate the cocone-point uniqueness relation on the chosen section to identify the
  -- universal element with its stage representative.
  have hcomp :
      (uIso.hom.app (op c.pt))
          (((uliftYoneda.mapCocone c).ι.app i).app (op c.pt) (ULift.up s)) =
        ((colimit.ι (M ⋙ uliftYoneda.{uI}) i).app (op c.pt) (ULift.up s)) := by
    have hcomp' :=
      congrArg (fun η ↦ η.app (op c.pt) (ULift.up s))
        (IsColimit.comp_coconePointUniqueUpToIso_hom
          (uliftYonedaMapCoconeIsColimit M c h)
          (colimit.isColimit (M ⋙ uliftYoneda.{uI})) i)
    simpa [uIso, uliftYonedaIsoOfCocone_homColimitComparison] using hcomp'
  have hs_app :
      (((uliftYoneda.mapCocone c).ι.app i).app (op c.pt) (ULift.up s)) = ULift.up (𝟙 c.pt) := by
    change ULift.up (s ≫ c.ι.app i) = ULift.up (𝟙 c.pt)
    simpa [hs]
  have hstage_id :
      (uIso.hom.app (op c.pt)) (ULift.up (𝟙 c.pt)) =
        ((colimit.ι (M ⋙ uliftYoneda.{uI}) i).app (op c.pt) (ULift.up s)) := by
    have hleft :
        (uIso.hom.app (op c.pt)) (ULift.up (𝟙 c.pt)) =
          (uIso.hom.app (op c.pt))
            (((uliftYoneda.mapCocone c).ι.app i).app (op c.pt) (ULift.up s)) := by
      exact congrArg (fun x ↦ (uIso.hom.app (op c.pt)) x) hs_app.symm
    exact hleft.trans hcomp
  -- Unfold the representability datum to read off its universal element at `𝟙`.
  simpa [representableByOfCocone_homColimitComparison, uIso] using hstage_id

/-- Helper for Lemma 4.22.9: a stage section obtained from the Hom-colimit comparison supplies
the stage-map witness in condition (4). -/
private theorem stageMap_isRepresentedBy_of_homColimitComparison
    {c : Cocone M} (h : c.HasHomColimitComparison) {i : I} (s : c.pt ⟶ M.obj i)
    (hs : s ≫ c.ι.app i = 𝟙 c.pt) :
    (colimit (M ⋙ uliftYoneda.{uI})).IsRepresentedBy
      ((colimit.ι (M ⋙ uliftYoneda.{uI}) i).app (op c.pt) (ULift.up s)) := by
  let R := representableByOfCocone_homColimitComparison M c h
  -- The previous identification lets us reuse the canonical representability witness.
  have hx :
      R.homEquiv (𝟙 c.pt) =
        ((colimit.ι (M ⋙ uliftYoneda.{uI}) i).app (op c.pt) (ULift.up s)) :=
    representableByOfCocone_homColimitComparison_homEquiv_id_eq_stageMap M h s hs
  exact hx ▸ R.isRepresentedBy

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
  constructor
  · rintro ⟨e⟩
    -- Route correction: use condition (2) to obtain a cocone, extract a section, and then read
    -- the corresponding stage class as the universal element.
    obtain ⟨c, hcpt, ⟨hc⟩⟩ :=
      (representableBy_iff_exists_cocone_homColimitComparison M X).mp ⟨e⟩
    subst hcpt
    obtain ⟨i, s, hs⟩ := exists_section_of_homColimitComparison M hc
    refine ⟨StructuredArrow.mk s, ?_⟩
    simpa using stageMap_isRepresentedBy_of_homColimitComparison M hc s hs
  · rintro ⟨p, hp⟩
    -- Any represented stage class yields a representing object by the canonical mathlib API.
    exact ⟨hp.representableBy⟩

end

/-! ### Lemma_4_22_10 (from Chap04) -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
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

private noncomputable def stageClass (j : I) :
    (proSystemHomColimitFunctor M).obj (M.obj j) :=
  (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) (M.obj j)).inv <|
    colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj (M.obj j)) (op j) (ULift.up (𝟙 (M.obj j)))

/-- Helper for Lemma 4.22.10: mapping the identity class at stage `j` along a morphism `f`
produces the corresponding class of `f` in the evaluated Hom-colimit. -/
private theorem stageClass_map
    {W : C} (j : I) (f : M.obj j ⟶ W) :
    (proSystemHomColimitFunctor M).map f (stageClass M j) =
      (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) W).inv
        (colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj W) (op j) (ULift.up f)) := by
  -- Move the functorial action across the evaluation/colimit comparison isomorphism.
  have hmap :=
    CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation_inv_colimit_map
      (F := M.op ⋙ uliftCoyoneda.{uI}) (f := f)
  have hmap' := congrFun hmap
    (colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj (M.obj j)) (op j) (ULift.up (𝟙 (M.obj j))))
  have hι := congrFun
    (CategoryTheory.Limits.colimit.ι_map
      ((M.op ⋙ uliftCoyoneda.{uI}).whiskerLeft
        ((evaluation C (Type (max uI vC))).map f))
      (op j))
    (ULift.up (𝟙 (M.obj j)))
  have hι' :
      colimMap ((M.op ⋙ uliftCoyoneda.{uI}).whiskerLeft
          ((evaluation C (Type (max uI vC))).map f))
          (colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj (M.obj j))
            (op j) (ULift.up (𝟙 (M.obj j)))) =
        colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj W) (op j) (ULift.up f) := by
    simpa using hι
  simpa [stageClass] using hmap'.trans
    (congrArg (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) W).inv hι')

/-- Helper for Lemma 4.22.10: mapping a represented stage class along `g` gives the class of the
composite stage map. -/
private theorem stageMap_class_map
    {X W : C} {i : I} (s : M.obj i ⟶ X) (g : X ⟶ W) :
    (proSystemHomColimitFunctor M).map g
      ((colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) X).inv
        (colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj X) (op i) (ULift.up s))) =
      (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) W).inv
        (colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj W) (op i) (ULift.up (s ≫ g))) := by
  -- Move the action of `g` across the evaluation/colimit comparison isomorphism.
  have hmap :=
    CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation_inv_colimit_map
      (F := M.op ⋙ uliftCoyoneda.{uI}) (f := g)
  have hmap' := congrFun hmap
    (colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj X) (op i) (ULift.up s))
  have hι := congrFun
    (CategoryTheory.Limits.colimit.ι_map
      ((M.op ⋙ uliftCoyoneda.{uI}).whiskerLeft
        ((evaluation C (Type (max uI vC))).map g))
      (op i))
    (ULift.up s)
  have hι' :
      colimMap ((M.op ⋙ uliftCoyoneda.{uI}).whiskerLeft
          ((evaluation C (Type (max uI vC))).map g))
          (colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj X) (op i) (ULift.up s)) =
        colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj W) (op i) (ULift.up (s ≫ g)) := by
    simpa [FunctorToTypes.map_comp_apply, Category.assoc] using hι
  simpa using hmap'.trans
    (congrArg (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) W).inv hι')

private theorem exists_coneOfCorepresentableBy
    {X : C} (e : (proSystemHomColimitFunctor M).CorepresentableBy X) :
    ∃ τ : (Functor.const I).obj X ⟶ M, ∀ j : I, e.homEquiv (τ.app j) = stageClass M j := by
  refine ⟨{ app := fun j ↦ e.homEquiv.symm (stageClass M j), naturality := ?_ }, ?_⟩
  · intro j j' f
    apply e.homEquiv.injective
    -- Both sides are the stage class of `j'`, written once through functoriality.
    have hleft :
        e.homEquiv (((Functor.const I).obj X).map f ≫ e.homEquiv.symm (stageClass M j')) =
          stageClass M j' := by
      simp
    have hcomp :
        e.homEquiv (e.homEquiv.symm (stageClass M j) ≫ M.map f) =
          (proSystemHomColimitFunctor M).map (M.map f) (stageClass M j) := by
      simpa using e.homEquiv_comp (M.map f) (e.homEquiv.symm (stageClass M j))
    have hmap :
        (proSystemHomColimitFunctor M).map (M.map f) (stageClass M j) =
          (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) (M.obj j')).inv
            (colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj (M.obj j')) (op j)
              (ULift.up (M.map f))) := by
      simpa using stageClass_map (M := M) j (M.map f)
    have hw := congrFun (colimit.w (M.op ⋙ uliftYoneda.{uI}.obj (M.obj j')) f.op)
      (ULift.up (𝟙 (M.obj j')))
    have hw' :
        colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj (M.obj j')) (op j) (ULift.up (M.map f)) =
          colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj (M.obj j')) (op j')
            (ULift.up (𝟙 (M.obj j'))) := by
      simpa using hw
    exact hleft.trans <| (hcomp.trans <| hmap.trans <|
      congrArg (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) (M.obj j')).inv hw').symm
  · intro j
    simp

private noncomputable def coneOfCorepresentableBy
    {X : C} (e : (proSystemHomColimitFunctor M).CorepresentableBy X) :
    (Functor.const I).obj X ⟶ M :=
  Classical.choose (exists_coneOfCorepresentableBy M e)

/-- Helper for Lemma 4.22.10: the chosen cone attached to a corepresentation has the prescribed
stage classes. -/
private theorem coneOfCorepresentableBy_homEquiv
    {X : C} (e : (proSystemHomColimitFunctor M).CorepresentableBy X) (j : I) :
    e.homEquiv ((coneOfCorepresentableBy M e).app j) = stageClass M j := by
  exact Classical.choose_spec (exists_coneOfCorepresentableBy M e) j

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
  -- Rewrite the chosen cone leg using its defining stage class.
  have hcomp :
      e.homEquiv ((coneOfCorepresentableBy M e).app j ≫ f.down) =
        (proSystemHomColimitFunctor M).map f.down (stageClass M j) := by
    rw [e.homEquiv_comp, coneOfCorepresentableBy_homEquiv]
  -- The evaluated stage class is exactly the image of the chosen element in the colimit.
  have hstage := stageClass_map (M := M) j f.down
  simpa [coconePointIso] using
    congrArg (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) W).hom
      (hcomp.trans hstage)

/-- Helper for Lemma 4.22.10: if a cone satisfies the Hom-colimit comparison, then the induced
co-Yoneda cocone is colimiting. -/
private noncomputable def uliftCoyonedaMapCoconeIsColimit
    (c : Cone M)
    (h : c.HasHomColimitComparison) :
    IsColimit (uliftCoyoneda.mapCocone c.op) := by
  refine evaluationJointlyReflectsColimits _ ?_
  intro Y
  simpa using Classical.choice (h Y)

/-- Helper for Lemma 4.22.10: a cone satisfying the Hom-colimit comparison determines the
canonical co-Yoneda realization of the pro-object. -/
private noncomputable def uliftCoyonedaIsoOfCone_homColimitComparison
    (c : Cone M)
    (h : c.HasHomColimitComparison) :
    uliftCoyoneda.obj (op c.pt) ≅ colimit (M.op ⋙ uliftCoyoneda.{uI}) :=
  (uliftCoyonedaMapCoconeIsColimit M c h).coconePointUniqueUpToIso
    (colimit.isColimit (M.op ⋙ uliftCoyoneda.{uI}))

/-- Helper for Lemma 4.22.10: a cone whose Hom-colimit comparisons are colimiting yields a
corepresentation of the pro-Hom functor by its cone point. -/
private noncomputable def corepresentableByOfCone_homColimitComparison
    (c : Cone M)
    (h : c.HasHomColimitComparison) :
    (proSystemHomColimitFunctor M).CorepresentableBy c.pt :=
  (Functor.CorepresentableBy.equivUliftCoyonedaIso _ _).symm <|
    uliftCoyonedaIsoOfCone_homColimitComparison M c h

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
  exact ⟨corepresentableByOfCone_homColimitComparison M c hc⟩

/-- Helper for Lemma 4.22.10: an essentially constant cofiltered cone makes every Yoneda test
cocone colimiting. -/
private noncomputable def homColimitComparisonIsColimit_of_essentiallyConstant
    {c : Cone M} (hc : IsEssentiallyConstantCofilteredCone c) (W : C) :
    IsColimit ((uliftYoneda.{uI}.obj W).mapCocone c.op) :=
  let hc' := (show IsEssentiallyConstantFilteredCocone c.op from hc).mapCocone
    (uliftYoneda.{uI}.obj W)
  hc'.isColimit

-- Proof sketch: this is the dual of Lemma 4.22.9. Pass from the cofiltered diagram to the
-- filtered colimit of the presheaves `Hom(Mᵢ, -)` and identify corepresentability with the
-- chapter owner `IsEssentiallyConstantCofilteredDiagram`.
section

variable [IsCofiltered I]

/-- Helper for Lemma 4.22.10: evaluating the Hom-colimit comparison at the cone point produces a
stage retraction to the cone point. -/
private theorem exists_retraction_of_homColimitComparison
    {c : Cone M} (h : c.HasHomColimitComparison) :
    ∃ i : I, ∃ s : M.obj i ⟶ c.pt, c.π.app i ≫ s = 𝟙 c.pt := by
  -- Lift the identity through the colimit presentation at the cone point.
  obtain ⟨i, u, hu⟩ :=
    Types.jointly_surjective_of_isColimit (Classical.choice (h c.pt)) (ULift.up (𝟙 c.pt))
  refine ⟨i.unop, u.down, ?_⟩
  simpa using congrArg ULift.down hu

/-- Helper for Lemma 4.22.10: the Hom-colimit comparison forces the eventual factorization data
of an essentially constant cofiltered cone. -/
private theorem essentiallyConstantCofilteredCone_of_homColimitComparison
    {c : Cone M} (h : c.HasHomColimitComparison) :
    IsEssentiallyConstantCofilteredCone c := by
  -- Route correction: extract a split cone leg first and then use equality in the filtered
  -- colimit over `Iᵒᵖ` to produce the eventual factorization witnesses.
  rw [isEssentiallyConstantCofilteredCone_iff]
  obtain ⟨i, s, hs⟩ := exists_retraction_of_homColimitComparison M h
  refine ⟨i, { retraction := s, id := hs }, ?_⟩
  intro j
  -- Compare the classes of `s ≫ c.π.app j` and `𝟙 (M.obj j)` in the Hom-colimit for `M.obj j`.
  have hEq :
      ((uliftYoneda.{uI}.obj (M.obj j)).mapCocone c.op).ι.app (op i)
          (ULift.up (s ≫ c.π.app j)) =
        ((uliftYoneda.{uI}.obj (M.obj j)).mapCocone c.op).ι.app (op j)
          (ULift.up (𝟙 (M.obj j))) := by
    have hsj : c.π.app i ≫ s ≫ c.π.app j = c.π.app j := by
      simpa using congrArg (fun f ↦ f ≫ c.π.app j) hs
    simpa [FunctorToTypes.map_comp_apply, Category.assoc, hsj]
  obtain ⟨k, ik, jk, hk⟩ :=
    (CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff
      (F := M.op ⋙ uliftYoneda.{uI}.obj (M.obj j))
      (Classical.choice (h (M.obj j)))).mp hEq
  refine ⟨k.unop, ik.unop, jk.unop, ?_⟩
  -- Equality in the filtered colimit becomes the desired factorization identity after unop.
  simpa [FunctorToTypes.map_comp_apply, Category.assoc] using (congrArg ULift.down hk).symm

/-- Lemma 4.22.10, condition (1), expressed through the chapter owner
`IsEssentiallyConstantCofilteredDiagram`: a cofiltered diagram is essentially constant exactly
when its associated pro-object is corepresentable. The textbook Hom-colimit criteria are
companion bridge/view formulations of this canonical statement. -/
theorem essentiallyConstant_proObject_characterizations
    :
    (proSystemHomColimitFunctor M).IsCorepresentable ↔
      IsEssentiallyConstantCofilteredDiagram M := by
  constructor
  · intro hM
    -- Choose a corepresenting object and recover the cone supplied by the corepresentability
    -- bridge.
    rcases hM.has_corepresentation with ⟨X, ⟨e⟩⟩
    refine ⟨Cone.mk X (coneOfCorepresentableBy M e), ?_⟩
    exact essentiallyConstantCofilteredCone_of_homColimitComparison M
      (fun W ↦ ⟨homColimitComparisonIsColimit M e⟩)
  · rintro ⟨c, hc⟩
    -- An essentially constant cone makes every Yoneda comparison cocone colimiting.
    exact
      (corepresentableByOfCone_homColimitComparison M c
        (fun W ↦ ⟨homColimitComparisonIsColimit_of_essentiallyConstant M hc W⟩)).isCorepresentable

end

-- Proof sketch: dualize the corresponding representability criterion in Lemma 4.22.9. A
-- corepresentation of the formal pro-object by `X` is equivalent to a cone on `M` with vertex
-- `X` whose induced Yoneda test cocones on `c.op` are colimiting for every test object.
private theorem exists_corepresentableByEquivCone_homColimitComparison
    (X : C) :
    Nonempty ((proSystemHomColimitFunctor M).CorepresentableBy X) ↔
      ∃ c : Cone M, c.pt = X ∧ c.HasHomColimitComparison := by
  constructor
  · rintro ⟨e⟩
    -- The chosen corepresenting datum supplies the canonical cone with Hom-colimit comparison.
    exact ⟨Cone.mk X (coneOfCorepresentableBy M e), rfl,
      fun W ↦ ⟨homColimitComparisonIsColimit M e⟩⟩
  · rintro ⟨c, hcpt, hc⟩
    -- Conversely, the cone point corepresents the pro-object by the comparison hypothesis.
    cases hcpt
    exact ⟨corepresentableByOfCone_homColimitComparison M c hc⟩

/-- Lemma 4.22.10, condition (2): the pro-object of `M` is corepresented by `X` exactly when `M`
admits a cone with vertex `X` whose canonical Hom-colimit comparison cocones are colimiting on all
test objects `W`. -/
theorem corepresentableBy_iff_exists_cone_homColimitComparison
    (X : C) :
    Nonempty ((proSystemHomColimitFunctor M).CorepresentableBy X) ↔
      ∃ c : Cone M, c.pt = X ∧ c.HasHomColimitComparison := by
  simpa using exists_corepresentableByEquivCone_homColimitComparison M X

section

variable [IsCofiltered I]

/-- Lemma 4.22.10, condition (3), expressed through the limit-cone owner `LimitCone M`: the
pro-object of `M` is corepresented by `X` exactly when `M` admits an essentially constant
limit cone with vertex `X`. -/
private theorem exists_corepresentableByEquivEssentiallyConstant_limitCone
    (X : C) :
    Nonempty ((proSystemHomColimitFunctor M).CorepresentableBy X) ↔
      ∃ c : LimitCone M, c.cone.pt = X ∧ IsEssentiallyConstantCofilteredCone c.cone := by
  constructor
  · rintro ⟨e⟩
    let c : Cone M := Cone.mk X (coneOfCorepresentableBy M e)
    have hc : IsEssentiallyConstantCofilteredCone c :=
      essentiallyConstantCofilteredCone_of_homColimitComparison M
        (fun W ↦ ⟨homColimitComparisonIsColimit M e⟩)
    -- Package the specific essentially constant cone on `X` as a limit cone.
    exact ⟨cofilteredConeToLimitCone hc, rfl, cofilteredConeToLimitCone_isEssentiallyConstant hc⟩
  · rintro ⟨c, hcpt, hc⟩
    cases hcpt
    -- Forgetting the chosen limit proof leaves an essentially constant cone, which already
    -- corepresents the pro-object.
    exact ⟨corepresentableByOfCone_homColimitComparison M c.cone
      (fun W ↦ ⟨homColimitComparisonIsColimit_of_essentiallyConstant M hc W⟩)⟩

/-- Lemma 4.22.10, condition (3), expressed through the limit-cone owner `LimitCone M`: the
pro-object of `M` is corepresented by `X` exactly when `M` admits an essentially constant
limit cone with vertex `X`. -/
theorem corepresentableBy_iff_exists_essentiallyConstant_limitCone
    (X : C) :
    Nonempty ((proSystemHomColimitFunctor M).CorepresentableBy X) ↔
      ∃ c : LimitCone M, c.cone.pt = X ∧ IsEssentiallyConstantCofilteredCone c.cone := by
  simpa using exists_corepresentableByEquivEssentiallyConstant_limitCone M X

end

/-- Helper for Lemma 4.22.10: a stage retraction of the canonical cone recovers the universal
element of the corepresenting equivalence. -/
private theorem corepresentableBy_homEquiv_id_eq_stageMap
    {X : C} (e : (proSystemHomColimitFunctor M).CorepresentableBy X)
    {i : I} (s : M.obj i ⟶ X)
    (hs : (coneOfCorepresentableBy M e).app i ≫ s = 𝟙 X) :
    e.homEquiv (𝟙 X) =
      (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) X).inv
        (colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj X) (op i) (ULift.up s)) := by
  -- Rewrite the identity via the chosen cone leg and transport the result through the
  -- corepresenting equivalence.
  have hleft :
      e.homEquiv (𝟙 X) = e.homEquiv ((coneOfCorepresentableBy M e).app i ≫ s) := by
    exact congrArg e.homEquiv hs.symm
  have hcomp :
      e.homEquiv ((coneOfCorepresentableBy M e).app i ≫ s) =
        (proSystemHomColimitFunctor M).map s (stageClass M i) := by
    rw [e.homEquiv_comp, coneOfCorepresentableBy_homEquiv]
  have hstage := stageClass_map (M := M) i s
  exact hleft.trans (hcomp.trans hstage)

-- Proof sketch: dualize the stage-map criterion from Lemma 4.22.9. A distinguished stage map
-- `Mᵢ ⟶ X` determines the forward maps of the corepresenting equivalences
-- `Hom(X, W) ≃ colimⱼ Hom(Mⱼ, W)` for every test object `W`, and conversely those equivalences
-- identify `X` as the corepresenting object.
/-- Lemma 4.22.10, condition (4): the pro-object of `M` is corepresented by `X` exactly when some
stage map `Mᵢ ⟶ X` determines the usual comparison equivalences
`Hom(X, W) ≃ colimⱼ Hom(Mⱼ, W)` for all test objects `W`. -/
private theorem exists_corepresentableByEquivStageMap_homColimitComparison
    (X : C) :
    Nonempty ((proSystemHomColimitFunctor M).CorepresentableBy X) ↔
      ∃ p : CostructuredArrow M X,
        ∀ W : C,
          Nonempty
            { e : (X ⟶ W) ≃ colimit (M.op ⋙ uliftYoneda.{uI}.obj W) //
                ∀ g : X ⟶ W,
                  e g = colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj W) (op p.left)
                    (ULift.up (p.hom ≫ g)) } := by
  classical
  constructor
  · rintro ⟨e⟩
    -- Represent the universal element at `𝟙 X` by a single stage map.
    obtain ⟨i, u, hu⟩ :=
      Types.jointly_surjective_of_isColimit
        (homColimitComparisonIsColimit (M := M) (e := e) (W := X))
        (ULift.up (𝟙 X))
    have hs : (coneOfCorepresentableBy M e).app i.unop ≫ u.down = 𝟙 X := by
      simpa using congrArg ULift.down hu
    let p : CostructuredArrow M X := CostructuredArrow.mk u.down
    refine ⟨p, ?_⟩
    intro W
    refine ⟨⟨e.homEquiv.trans
      (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) W).toEquiv, ?_⟩⟩
    intro g
    -- Every value of the equivalence is obtained by postcomposing the chosen universal element.
    change
      (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) W).hom
        (e.homEquiv g) =
      colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj W) (op p.left)
        (ULift.up (p.hom ≫ g))
    rw [e.homEquiv_eq, corepresentableBy_homEquiv_id_eq_stageMap (M := M) e u.down hs]
    simpa using congrArg
      (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) W).hom
      (stageMap_class_map (M := M) (s := u.down) g)
  · rintro ⟨p, hp⟩
    refine ⟨
      { homEquiv := fun {W} ↦
          ((Classical.choice (hp W)).1).trans
            (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) W).symm.toEquiv
        homEquiv_comp := ?_ }⟩
    intro W W' g f
    let eW := Classical.choice (hp W)
    let eW' := Classical.choice (hp W')
    -- Both sides are the same stage class after evaluating the colimit map along `g`.
    change
      (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) W').inv
        (eW'.1 (f ≫ g)) =
      (proSystemHomColimitFunctor M).map g
        ((colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) W).inv (eW.1 f))
    rw [eW'.2, eW.2]
    simpa [Category.assoc] using (stageMap_class_map (M := M) (s := p.hom ≫ f) g).symm

theorem corepresentableBy_iff_exists_stageMap_homColimitComparison
    (X : C) :
    Nonempty ((proSystemHomColimitFunctor M).CorepresentableBy X) ↔
      ∃ p : CostructuredArrow M X,
        ∀ W : C,
          Nonempty
            { e : (X ⟶ W) ≃ colimit (M.op ⋙ uliftYoneda.{uI}.obj W) //
                ∀ g : X ⟶ W,
                  e g = colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj W) (op p.left)
                    (ULift.up (p.hom ≫ g)) } := by
  simpa using exists_corepresentableByEquivStageMap_homColimitComparison M X

end

/-! ### Lemma_4_22_11 (from Chap04) -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor.Final

universe uI vI uJ vJ uC vC

/- Domain-style sampling for Lemma 4.22.11:
- primary domain: filtered diagrams, essential constancy, and invariance under pullback along a
  final functor.
- inspected owner-level declarations:
  `IsEssentiallyConstantFilteredDiagram`,
  `isEssentiallyConstantFilteredCocone_iff`,
  `Functor.Final.extendCocone`,
  `Functor.Final.final_iff_of_isFiltered`.
- best owner abstraction for the main proposition:
  `IsEssentiallyConstantFilteredDiagram M`.

Primitive-vs-derived split:
- primitive source data: an essentially constant cocone with a distinguished split leg and the
  eventual factorization data from `isEssentiallyConstantFilteredCocone_iff`.
- derived API: pullback of cocones by `Cocone.whisker`, extension along a final functor by
  `Functor.Final.extendCocone`, and the final-functor lifting/equalization data supplied by
  `Functor.Final.final_iff_of_isFiltered` and `Functor.Final.exists_coeq`.

Source/core/bridge triage:
- `source-facing`: the textbook claim that essential constancy is preserved and reflected by
  pullback along a cofinal functor.
- `core/canonical`: `IsEssentiallyConstantFilteredDiagram`.
- `bridge/view`: `Functor.Final.extendCocone`, `Functor.Final.extendCocone_obj_ι_app'`,
  `Functor.Final.colimit_cocone_comp_aux`, and the filtered-form finality criteria. -/

private theorem essentiallyConstantFilteredCocone_whisker_final
    {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
    [IsFiltered I] (H : I ⥤ J) [H.Final] {M : J ⥤ C} {c : Cocone M}
    (hc : IsEssentiallyConstantFilteredCocone c) :
    IsEssentiallyConstantFilteredCocone (c.whisker H) := by
  let _ : IsFiltered J := IsFiltered.of_final H
  rcases (isEssentiallyConstantFilteredCocone_iff c).mp hc with ⟨j₀, s, hs, hfac⟩
  obtain ⟨i₀, ⟨f₀⟩⟩ := ((Functor.final_iff_of_isFiltered H).mp
    (show H.Final from inferInstance)).1 j₀
  rw [isEssentiallyConstantFilteredCocone_iff]
  refine ⟨i₀, s ≫ M.map f₀, ?_, ?_⟩
  · change (s ≫ M.map f₀) ≫ c.ι.app (H.obj i₀) = 𝟙 c.pt
    have hw₀ : s ≫ M.map f₀ ≫ c.ι.app (H.obj i₀) = s ≫ c.ι.app j₀ := by
      have hw := congrArg (fun g ↦ s ≫ g) (c.w f₀)
      simpa only [Category.assoc] using hw
    simpa [Category.assoc] using hw₀.trans hs
  · intro j
    rcases hfac (H.obj j) with ⟨k, α, β, hβ⟩
    obtain ⟨i, ⟨u⟩⟩ := ((Functor.final_iff_of_isFiltered H).mp
      (show H.Final from inferInstance)).1 k
    let m := IsFiltered.max i₀ i
    let p : i₀ ⟶ m := IsFiltered.leftToMax i₀ i
    let q : i ⟶ m := IsFiltered.rightToMax i₀ i
    obtain ⟨n, r, hr⟩ := Functor.Final.exists_coeq H (f₀ ≫ H.map p) (α ≫ u ≫ H.map q)
    let m' := IsFiltered.max j n
    let a : j ⟶ m' := IsFiltered.leftToMax j n
    let b : n ⟶ m' := IsFiltered.rightToMax j n
    obtain ⟨n', r', hr'⟩ := Functor.Final.exists_coeq H (H.map a)
      (β ≫ u ≫ H.map q ≫ H.map r ≫ H.map b)
    refine ⟨n', p ≫ r ≫ b ≫ r', a ≫ r', ?_⟩
    change M.map (H.map (a ≫ r')) =
      c.ι.app (H.obj j) ≫ (s ≫ M.map f₀) ≫ M.map (H.map (p ≫ r ≫ b ≫ r'))
    calc
      M.map (H.map (a ≫ r')) = M.map (H.map a ≫ H.map r') := by
        simp [Functor.map_comp]
      _ = M.map (β ≫ u ≫ H.map q ≫ H.map r ≫ H.map b ≫ H.map r') := by
        simpa [Functor.map_comp, Category.assoc] using congrArg (fun f ↦ M.map f) hr'
      _ = M.map β ≫ M.map u ≫ M.map (H.map q) ≫ M.map (H.map r) ≫
          M.map (H.map b) ≫ M.map (H.map r') := by
        simp [Functor.map_comp]
      _ = c.ι.app (H.obj j) ≫ s ≫ M.map α ≫ M.map u ≫ M.map (H.map q) ≫
          M.map (H.map r) ≫ M.map (H.map b) ≫ M.map (H.map r') := by
        simpa [Functor.map_comp, Category.assoc] using congrArg
          (fun f ↦ f ≫ M.map u ≫ M.map (H.map q) ≫ M.map (H.map r) ≫
            M.map (H.map b) ≫ M.map (H.map r')) hβ
      _ = c.ι.app (H.obj j) ≫ (s ≫ M.map f₀) ≫ M.map (H.map (p ≫ r ≫ b ≫ r')) := by
        have hfr := congrArg (fun f ↦ M.map f ≫ M.map (H.map b) ≫ M.map (H.map r')) hr.symm
        simp only [Functor.const_obj_obj, Functor.map_comp, Category.assoc] at hfr ⊢
        rw [hfr]

private theorem essentiallyConstantFilteredCocone_of_whisker_final
    {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
    [IsFiltered I] (H : I ⥤ J) [H.Final] {M : J ⥤ C} {c : Cocone (H ⋙ M)}
    (hc : IsEssentiallyConstantFilteredCocone c) :
    IsEssentiallyConstantFilteredCocone (extendCocone.obj c) := by
  rw [isEssentiallyConstantFilteredCocone_iff] at hc ⊢
  rcases hc with ⟨i₀, s, hs, hfac⟩
  refine ⟨H.obj i₀, s, ?_, ?_⟩
  · have hw₀ : s ≫ (extendCocone.obj c).ι.app (H.obj i₀) = s ≫ c.ι.app i₀ := by
      simpa using congrArg (fun g ↦ s ≫ g) (colimit_cocone_comp_aux c i₀)
    simpa [hs] using hw₀.trans hs
  · intro j
    obtain ⟨i, ⟨f⟩⟩ := ((Functor.final_iff_of_isFiltered H).mp
      (show H.Final from inferInstance)).1 j
    rcases hfac i with ⟨k, α, β, hβ⟩
    refine ⟨H.obj k, H.map α, f ≫ H.map β, ?_⟩
    change M.map (f ≫ H.map β) =
      (extendCocone.obj c).ι.app j ≫ s ≫ M.map (H.map α)
    rw [extendCocone_obj_ι_app' c f]
    simpa [Functor.map_comp, Category.assoc] using congrArg (fun g ↦ M.map f ≫ g) hβ

-- Proof sketch: the source-facing data for an essentially constant cocone transport directly
-- along `Cocone.whisker` and `Functor.Final.extendCocone`. The only extra work is that, on the
-- whiskered side, the distinguished stage and the eventual factorization data must be moved into
-- the image of the final functor using the filtered-form criteria `Functor.final_iff_of_isFiltered`
-- and `Functor.Final.exists_coeq`.
/-- Lemma 4.22.11: for a cofinal functor `H : I ⥤ J` between filtered index categories, a diagram
`M : J ⥤ C` is essentially constant if and only if its pullback `H ⋙ M` is essentially constant. -/
theorem essentiallyConstantFilteredDiagram_iff_comp_final
    {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
    [IsFiltered I] (H : I ⥤ J) [H.Final] (M : J ⥤ C) :
    IsEssentiallyConstantFilteredDiagram M ↔
      IsEssentiallyConstantFilteredDiagram (H ⋙ M) := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c.whisker H, essentiallyConstantFilteredCocone_whisker_final H hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨extendCocone.obj c, essentiallyConstantFilteredCocone_of_whisker_final H hc⟩

/-! ### Lemma_4_22_12 (from Chap04) -/
universe uI vI uJ vJ uC vC

namespace CategoryTheory

variable {I : Type uI} {J : Type uJ} {C : Type uC}
variable [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]

/- Source/core/bridge triage for Lemma 4.22.12:
- `source-facing`: the product of filtered categories is filtered, and essential constancy is
  unchanged after pulling a diagram back along the second projection.
- `core/canonical`: the mathlib instance `IsFiltered (I × J)` and the chapter owner theorem
  `essentiallyConstantFilteredDiagram_iff_comp_final`.
- `bridge/view`: the final functor `Prod.snd I J : I × J ⥤ J`, whose finality is supplied by the
  filtered-domain instance `CategoryTheory.final_snd`.

Primary domain-style sampling:
- project owner recall: `IsFiltered` in `Definition_4_19_1`;
- mathlib owner instance: `IsFiltered (C × D)` in
  `Mathlib/CategoryTheory/Filtered/Basic.lean`;
- mathlib bridge/view instance: `final_snd` in
  `Mathlib/CategoryTheory/Filtered/Final.lean`;
- project final-functor invariance theorem:
  `essentiallyConstantFilteredDiagram_iff_comp_final` in `Lemma_4_22_11`.

Primitive-vs-derived split:
- primitive source data: filteredness of `I` and `J`, and the diagram `M : J ⥤ C`;
- derived API: filteredness of `I × J`, finality of `Prod.snd I J`, and the pullback invariance of
  `IsEssentiallyConstantFilteredDiagram`. -/

section

variable [IsFiltered I] [IsFiltered J]
variable (M : J ⥤ C)

/- Companion recall: if `I` and `J` are filtered, then the product category `I × J` is filtered.
This is exactly the canonical mathlib instance `IsFiltered (I × J)`. -/
#synth IsFiltered (I × J)

-- Proof sketch: the first clause is the canonical instance `IsFiltered (I × J)`, and the second
-- clause is the specialization of Lemma 4.22.11 to the final projection functor `Prod.snd I J`.
/-- Lemma 4.22.12: if `I` and `J` are filtered, then a diagram `M : J ⥤ C` is essentially
constant if and only if its pullback along the projection `Prod.snd I J : I × J ⥤ J` is
essentially constant. -/
theorem essentiallyConstantFilteredDiagram_iff_comp_snd :
    IsEssentiallyConstantFilteredDiagram M ↔
      IsEssentiallyConstantFilteredDiagram (Prod.snd I J ⋙ M) := by
  simpa using
    (essentiallyConstantFilteredDiagram_iff_comp_final (Prod.snd I J) M)

end

end CategoryTheory

/-! ### Lemma_4_22_13 (from Chap04) -/
open CategoryTheory

universe uI vI uJ vJ uC vC

/- Domain-style sampling for Lemma 4.22.13:
- primary domain: essentially constant cofiltered diagrams and their behavior under initial
  pullback.
- inspected owner-level declarations:
  `IsEssentiallyConstantCofilteredDiagram` in `Definition_4_22_2`,
  `isEssentiallyConstantCofilteredDiagram_iff_op` in `Definition_4_22_2`,
  `essentiallyConstantFilteredDiagram_iff_comp_final` in `Lemma_4_22_11`.
- inspected mathlib duality declaration:
  `CategoryTheory.final_op_of_initial` / instance `CategoryTheory.final_op_of_initial`,
  used through the canonical finality of `H.op`.
- best owner abstraction for the main proposition: `IsEssentiallyConstantCofilteredDiagram M`.

Primitive-vs-derived split:
- primitive source data: an essentially constant cone on the cofiltered diagram, equivalently the
  opposite filtered diagram being essentially constant.
- derived API: the initial-pullback invariance statement below, obtained by transporting the
  filtered result across the canonical opposite-category bridge.

Source/core/bridge triage:
- `source-facing`: the textbook claim that essential constancy is preserved and reflected by
  pullback along an initial functor.
- `core/canonical`: `IsEssentiallyConstantCofilteredDiagram`.
- `bridge/view`: passage to the opposite filtered diagram via
  the definition of `IsEssentiallyConstantCofilteredDiagram`, and then to the filtered
  invariance theorem `essentiallyConstantFilteredDiagram_iff_comp_final`. -/

-- Proof sketch: pass to the opposite diagram `M.op : Jᵒᵖ ⥤ Cᵒᵖ`, where `H.op` is final, apply
-- Lemma 4.22.11, and translate back through the canonical cone/cocone duality.
/-- Lemma 4.22.13: for an initial functor `H : I ⥤ J` from a cofiltered index category, a
diagram `M : J ⥤ C` is essentially constant if and only if its pullback `H ⋙ M` is essentially
constant. -/
theorem essentiallyConstantCofilteredDiagram_iff_comp_initial
    {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
    [IsCofiltered I] (H : I ⥤ J) [H.Initial] (M : J ⥤ C) :
    IsEssentiallyConstantCofilteredDiagram M ↔
      IsEssentiallyConstantCofilteredDiagram (H ⋙ M) := by
  simpa [isEssentiallyConstantCofilteredDiagram_iff_op] using
    (essentiallyConstantFilteredDiagram_iff_comp_final (H.op) M.op)
