import StacksProject_2024.stacks_project.Chap21.SiteAbelianDerived

open CategoryTheory Limits Opposite

noncomputable section

universe u v

namespace CategoryTheory.Sheaf

/-- Helper for Lemma 21.7.3: the degree-`p` right derived functor of the inclusion
`sheafToPresheaf J AddCommGrpCat` should agree with the canonical cohomology presheaf functor.
This is kept theorem-local so the target file no longer depends on the contaminated Chapter 20
wrapper import chain. -/
theorem cohomologyPresheafComparison
    {C : Type u} [Category.{max u v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v}]
    [HasExt (Sheaf J AddCommGrpCat.{max u v})]
    [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v})]
    (p : ℕ) :
    IsIsomorphic
      ((sheafToPresheaf J AddCommGrpCat.{max u v}).rightDerived p)
      (Sheaf.cohomologyPresheafFunctor J p :
        Sheaf J AddCommGrpCat.{max u v} ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) := by
  -- Route correction: isolate the forbidden later-item dependency here and keep the target proof
  -- on the intended objectwise transport route.
  -- TODO: prove the owner-level bridge without importing later item `Lemma_21_10_5`; either
  -- expose an earlier canonical theorem for
  -- `R^p(sheafToPresheaf J AddCommGrpCat) ≅ Sheaf.cohomologyPresheafFunctor J p`, or rebuild the
  -- same comparison from the generic `Ext`/right-derived API on the allowed import surface.
  sorry

/-- Helper for Lemma 21.7.3: evaluating the cohomology presheaf at `U` identifies `F.H' p U`
with the degree-`p` homology of the sections complex of a chosen injective resolution `I`. -/
theorem cohomologyAtObjectIsoHomologySections_isomorphic
    {C : Type u} [Category.{max u v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v}]
    [HasExt (Sheaf J AddCommGrpCat.{max u v})]
    [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v})]
    {F : Sheaf J AddCommGrpCat.{max u v}} (I : InjectiveResolution F) (U : C) (p : ℕ) :
    IsIsomorphic
      (F.H' p U)
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (ComplexShape.up ℕ) p).obj
        (((siteAbelianSectionsFunctor J U).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex)) := by
  rcases cohomologyPresheafComparison (J := J) p with ⟨e⟩
  let evalU := (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U)
  let eH' :
      F.H' p U ≅
        ((((sheafToPresheaf J AddCommGrpCat.{max u v}).rightDerived p).obj F).obj (op U)) := by
    -- Proof comment: evaluate the presheaf comparison at `U` and rewrite the target back to `H'`.
    simpa [Sheaf.H'] using (evalU.mapIso (e.app F)).symm
  -- Proof comment: compose the evaluated right-derived comparison with the sections-complex model.
  exact
    ⟨eH' ≪≫
      Sheaf.rightDerivedInclusion_app_obj_iso_homology_sections_complex J I U p⟩

/-- Helper for Lemma 21.7.3: evaluating the presheaf-level comparison at `U` identifies
`F.H' p U` with the evaluated degree-`p` right derived functor of the inclusion
`sheafToPresheaf J AddCommGrpCat`. -/
noncomputable def cohomologyAtObjectIsoRightDerivedValue
    {C : Type u} [Category.{max u v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v}]
    [HasExt (Sheaf J AddCommGrpCat.{max u v})]
    [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v})]
    {F : Sheaf J AddCommGrpCat.{max u v}} (U : C) (p : ℕ) :
    F.H' p U ≅
      ((((sheafToPresheaf J AddCommGrpCat.{max u v}).rightDerived p).obj F).obj (op U)) := by
  let e :=
    Classical.choice (cohomologyPresheafComparison (J := J) p)
  let evalU := (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U)
  -- Proof comment: the comparison is exactly the component of the chosen presheaf-level natural
  -- isomorphism evaluated at `U`, rewritten through the reducible owner `Sheaf.H'`.
  simpa [Sheaf.H'] using (evalU.mapIso (e.app F)).symm

/-- Helper for Lemma 21.7.3: the evaluated presheaf comparison is natural with respect to
restriction maps. -/
theorem cohomologyAtObjectIsoRightDerivedValue_naturality
    {C : Type u} [Category.{max u v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v}]
    [HasExt (Sheaf J AddCommGrpCat.{max u v})]
    [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v})]
    {F : Sheaf J AddCommGrpCat.{max u v}} {U V : C} (i : V ⟶ U) (p : ℕ) :
    ((F.cohomologyPresheaf p).map i.op) ≫
        (cohomologyAtObjectIsoRightDerivedValue (J := J) (F := F) V p).hom =
      (cohomologyAtObjectIsoRightDerivedValue (J := J) (F := F) U p).hom ≫
        ((((sheafToPresheaf J AddCommGrpCat.{max u v}).rightDerived p).obj F).map i.op) := by
  let e :=
    Classical.choice (cohomologyPresheafComparison (J := J) p)
  let evalU := (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U)
  let evalV := (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op V)
  have hnat :
      (e.app F).hom.app (op U) ≫ ((F.cohomologyPresheaf p).map i.op) =
        ((((sheafToPresheaf J AddCommGrpCat.{max u v}).rightDerived p).obj F).map i.op) ≫
          (e.app F).hom.app (op V) := by
    -- Proof comment: this is the naturality square of the presheaf component `e.app F` at `i.op`.
    simpa using NatTrans.naturality ((e.app F).hom) i.op
  -- Proof comment: invert the naturality square so the evaluated comparison is written in the
  -- direction used by the local-vanishing proof.
  simpa [cohomologyAtObjectIsoRightDerivedValue, evalU, evalV, Category.assoc] using
    Iso.eq_comp_inv (f := ((F.cohomologyPresheaf p).map i.op))
      (g := ((cohomologyAtObjectIsoRightDerivedValue (J := J) (F := F) U p).symm))
      (h := ((((sheafToPresheaf J AddCommGrpCat.{max u v}).rightDerived p).obj F).map i.op))
      (i := ((cohomologyAtObjectIsoRightDerivedValue (J := J) (F := F) V p).symm))
      hnat

/-- Helper for Lemma 21.7.3: an explicit `Iso` implementing the objectwise comparison between
cohomology and the sections-complex homology model. -/
noncomputable def cohomologyAtObjectIsoHomologySections
    {C : Type u} [Category.{max u v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v}]
    [HasExt (Sheaf J AddCommGrpCat.{max u v})]
    [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v})]
    {F : Sheaf J AddCommGrpCat.{max u v}} (I : InjectiveResolution F) (U : C) (p : ℕ) :
    F.H' p U ≅
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (ComplexShape.up ℕ) p).obj
        (((siteAbelianSectionsFunctor J U).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex)) := by
  -- Proof comment: the explicit objectwise comparison is the evaluated presheaf bridge followed
  -- by the standard sections-complex computation of the right-derived value.
  exact cohomologyAtObjectIsoRightDerivedValue (J := J) (F := F) U p ≪≫
    Sheaf.rightDerivedInclusion_app_obj_iso_homology_sections_complex J I U p

end CategoryTheory.Sheaf
