import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Monoidal.Tor
import StacksProject_2024.Chap04.Lemma_4_21_5
import StacksProject_2024.Chap10.Lemma_10_8_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

section

variable {R : Type u} [CommRing R]

/-- Helper for Lemma 10.76.2: tensor the fixed projective resolution of `N` termwise with the
varying left module. -/
private noncomputable def tor_fixed_right_resolution_complex_functor
    (N : ModuleCat.{u} R) :
    ModuleCat.{u} R ⥤ ChainComplex (ModuleCat.{u} R) ℕ where
  obj M :=
    ((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (projectiveResolution N).complex
  map f :=
    ((NatTrans.mapHomologicalComplex ((tensoringLeft (ModuleCat.{u} R)).map f)
      (ComplexShape.down ℕ)).app (projectiveResolution N).complex)
  map_id M := by
    -- The chain map induced by the identity tensor morphism is the identity.
    ext k
    simp
  map_comp f g := by
    -- Tensoring the fixed resolution is functorial in the left module.
    ext k
    simp

/-- Helper for Lemma 10.76.2: in degree `k`, the fixed-resolution complex functor is just right
tensoring with the `k`-th term of the projective resolution. -/
private noncomputable def tor_fixed_right_resolution_eval_iso
    (N : ModuleCat.{u} R) (k : ℕ) :
    tor_fixed_right_resolution_complex_functor (R := R) N ⋙
        HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) k ≅
      tensorRight ((projectiveResolution N).complex.X k) :=
  Iso.refl _

/-- Helper for Lemma 10.76.2: the canonical `Tor` functor with right variable fixed at `N`
identifies with homology of the fixed tensorized projective resolution. -/
private noncomputable def tor_fixed_right_resolution_homology_iso
    (N : ModuleCat.{u} R) (n : ℕ) :
    ((Tor (ModuleCat.{u} R) n).flip.obj N) ≅
      tor_fixed_right_resolution_complex_functor (R := R) N ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n :=
  NatIso.ofComponents
    (fun M ↦ (projectiveResolution N).isoLeftDerivedObj (tensorLeft M) n)
    (fun {X Y} f ↦ by
      -- Compute the `Tor` map from the chosen projective resolution of `N`.
      have h :=
        CategoryTheory.ProjectiveResolution.leftDerived_app_eq
          (((tensoringLeft (ModuleCat.{u} R)).map f))
          (projectiveResolution N) n
      have h' :=
        congrArg
          (fun z ↦ z ≫ ((projectiveResolution N).isoLeftDerivedObj (tensorLeft Y) n).hom)
          h
      simpa [Category.assoc, tor_fixed_right_resolution_complex_functor] using h')

/-- Helper for Lemma 10.76.2: tensoring a fixed projective resolution commutes with filtered
colimits because each degree is right tensoring with a fixed module. -/
private theorem tor_fixed_right_resolution_complex_functor_preserves_filtered_colimits
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (N : ModuleCat.{u} R) :
    PreservesColimitsOfShape J
      (tor_fixed_right_resolution_complex_functor (R := R) N) := by
  -- Check preservation degreewise, then transport from `tensorRight` to `tensorLeft` using the
  -- braiding so that the existing module-colimit instance applies.
  refine HomologicalComplex.preservesColimitsOfShape_of_eval _ ?_
  intro k
  let e :
      tensorLeft ((projectiveResolution N).complex.X k) ≅
        tor_fixed_right_resolution_complex_functor (R := R) N ⋙
          HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) k :=
    (BraidedCategory.tensorLeftIsoTensorRight ((projectiveResolution N).complex.X k)) ≪≫
      (tor_fixed_right_resolution_eval_iso (R := R) N k).symm
  exact preservesColimitsOfShape_of_natIso e

/-- Helper for Lemma 10.76.2: the filtered colimit of the tensorized fixed resolution identifies
with the tensorized fixed resolution of the filtered colimit module. -/
private noncomputable def tor_fixed_right_resolution_colimit_iso
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ModuleCat.{u} R) (N : ModuleCat.{u} R) :
    colimit (F ⋙ tor_fixed_right_resolution_complex_functor (R := R) N) ≅
      (tor_fixed_right_resolution_complex_functor (R := R) N).obj (colimit F) :=
  letI := tor_fixed_right_resolution_complex_functor_preserves_filtered_colimits
    (R := R) (J := J) N
  (preservesColimitIso
    (tor_fixed_right_resolution_complex_functor (R := R) N) F).symm

/-- Helper for Lemma 10.76.2: the colimit comparison map for the tensorized fixed resolution is
an isomorphism. -/
private theorem tor_fixed_right_resolution_post_isIso
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ModuleCat.{u} R) (N : ModuleCat.{u} R) :
    IsIso (colimit.post F (tor_fixed_right_resolution_complex_functor (R := R) N)) := by
  -- The explicit comparison isomorphism is the inverse of `preservesColimitIso`.
  letI := tor_fixed_right_resolution_complex_functor_preserves_filtered_colimits
    (R := R) (J := J) N
  infer_instance

/-- Helper for Lemma 10.76.2: the categorical colimit of a short-complex diagram agrees with the
short complex obtained by taking colimits componentwise. -/
private noncomputable def shortComplex_diagram_colimit_iso
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ShortComplex (ModuleCat.{u} R)) :
    colimit F ≅ (ShortComplex.colimitCocone F).pt :=
  IsColimit.coconePointUniqueUpToIso
    (colimit.isColimit F)
    (ShortComplex.isColimitColimitCocone F)

/-- Helper for Lemma 10.76.2: the comparison isomorphism from the categorical colimit of a
short-complex diagram to the pointwise-colimit short complex intertwines the cocone legs. -/
private theorem shortComplex_diagram_colimit_iso_hom_ι
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ShortComplex (ModuleCat.{u} R)) (j : J) :
    colimit.ι F j ≫ (shortComplex_diagram_colimit_iso (R := R) F).hom =
      (ShortComplex.colimitCocone F).ι.app j := by
  exact
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit F)
      (ShortComplex.isColimitColimitCocone F)
      j

/-- Helper for Lemma 10.76.2: the universal stage map into a module colimit is natural in the
diagram. -/
private theorem evaluation_to_colim_naturality
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{w} R)]
    (j : J) {F G : J ⥤ ModuleCat.{w} R} (α : F ⟶ G) :
    α.app j ≫ colimit.ι G j = colimit.ι F j ≫ colim.map α := by
  simpa using (colimit.ι_map α j).symm

/-- Helper for Lemma 10.76.2: the natural transformation from evaluation at `j` to the colimit
functor whose component on a diagram is the canonical map into its colimit. -/
private noncomputable def module_colimit_evaluation_to_colim
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{w} R)]
    (j : J) :
    (evaluation J (ModuleCat.{w} R)).obj j ⟶ colim (J := J) (C := ModuleCat.{w} R) where
  app F := colimit.ι F j
  naturality _ _ α := evaluation_to_colim_naturality (R := R) (J := J) j α

/-- Helper for Lemma 10.76.2: the stage cocone map into the pointwise-colimit short complex is
the map induced by the natural transformation from evaluation at `j` to colimit. -/
@[simp]
private theorem shortComplex_colimitCocone_ι_eq_mapNatTrans_module_colimit
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (T : ShortComplex (J ⥤ ModuleCat.{u} R)) (j : J) :
    (ShortComplex.colimitCocone
      ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T)).ι.app j =
      T.mapNatTrans (module_colimit_evaluation_to_colim (R := R) (J := J) j) := by
  ext <;> rfl

/-- Helper for Lemma 10.76.2: the categorical colimit of the short-complex diagram attached to an
owner short complex identifies with the short complex obtained by applying the module colimit
functor objectwise. -/
private noncomputable def shortComplex_owner_colimit_iso
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (T : ShortComplex (J ⥤ ModuleCat.{u} R)) :
    colimit ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T) ≅
      T.map (colim (J := J) (C := ModuleCat.{u} R)) :=
  IsColimit.coconePointUniqueUpToIso
    (colimit.isColimit ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T))
    (ShortComplex.isColimitColimitCocone
      ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T))

/-- Helper for Lemma 10.76.2: the owner-side colimit isomorphism intertwines stage cocone maps
with the short-complex maps induced by the canonical stage-to-colimit natural transformation. -/
private theorem shortComplex_owner_colimit_iso_hom_ι
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (T : ShortComplex (J ⥤ ModuleCat.{u} R)) (j : J) :
    colimit.ι ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T) j ≫
        (shortComplex_owner_colimit_iso (R := R) (J := J) T).hom =
      T.mapNatTrans (module_colimit_evaluation_to_colim (R := R) (J := J) j) := by
  have h₁ :
      colimit.ι ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T) j ≫
          (shortComplex_owner_colimit_iso (R := R) (J := J) T).hom =
        (ShortComplex.colimitCocone
          ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T)).ι.app j := by
    exact
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (colimit.isColimit
          ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T))
        (ShortComplex.isColimitColimitCocone
          ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T))
        j
  have h₂ :
      (ShortComplex.colimitCocone
        ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T)).ι.app j =
        T.mapNatTrans (module_colimit_evaluation_to_colim (R := R) (J := J) j) := by
    simpa using
      (shortComplex_colimitCocone_ι_eq_mapNatTrans_module_colimit
        (R := R) (J := J) T j)
  exact h₁.trans h₂

/-- Helper for Chap10 Lemma 10 76 2: homology of an owner short complex in a functor
category is naturally the diagram obtained by taking homology at each index. -/
private noncomputable def shortComplex_owner_homology_iso
    {J : Type v} [Category.{v} J]
    (T : ShortComplex (J ⥤ ModuleCat.{w} R)) :
    T.homology ≅
      (ShortComplex.functorEquivalence J (ModuleCat.{w} R)).functor.obj T ⋙
        ShortComplex.homologyFunctor (ModuleCat.{w} R) :=
  NatIso.ofComponents
    (fun j ↦
      ((T.mapHomologyIso ((evaluation J (ModuleCat.{w} R)).obj j)).symm))
    (fun {i j} f ↦ by
      -- Naturality is exactly `NatTrans.app_homology` for the evaluation morphism
      -- `evaluation i ⟶ evaluation j`, with the comparison isomorphisms inverted.
      simpa [Category.assoc] using
        congrArg
          (fun α ↦ α ≫
            (T.mapHomologyIso ((evaluation J (ModuleCat.{w} R)).obj j)).inv)
          (NatTrans.app_homology
            (τ := (evaluation J (ModuleCat.{w} R)).map f) (S := T)))

/-- Helper for Chap10 Lemma 10 76 2: once the module colimit functor preserves homology,
the owner-side short-complex homology functor preserves the corresponding colimit. -/
private theorem shortComplex_owner_preservesColimit_homologyFunctor_of_colim_preservesHomology
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{w} R)]
    [(colim (J := J) (C := ModuleCat.{w} R)).PreservesHomology]
    (T : ShortComplex (J ⥤ ModuleCat.{w} R)) :
    PreservesColimit
      ((ShortComplex.functorEquivalence J (ModuleCat.{w} R)).functor.obj T)
      (ShortComplex.homologyFunctor (ModuleCat.{w} R)) := by
  let S := (ShortComplex.functorEquivalence J (ModuleCat.{w} R)).functor.obj T
  let H : ShortComplex (ModuleCat.{w} R) ⥤ ModuleCat.{w} R :=
    ShortComplex.homologyFunctor (ModuleCat.{w} R)
  let α := shortComplex_owner_homology_iso (R := R) (J := J) T
  let β :=
    (ShortComplex.homologyFunctorIso (colim (J := J) (C := ModuleCat.{w} R))).app T
  -- Compare the homology cocone of the pointwise short-complex colimit with the ordinary
  -- module colimit cocone of the owner homology diagram.
  apply preservesColimit_of_preserves_colimit_cocone
    (ShortComplex.isColimitColimitCocone S)
  refine (IsColimit.precomposeHomEquiv α
    (H.mapCocone (ShortComplex.colimitCocone S))).1 ?_
  refine IsColimit.ofIsoColimit (colimit.isColimit T.homology) ?_
  refine Cocone.ext β.symm ?_
  intro j
  dsimp [S, H, α, β]
  -- The cocone-leg identity is `NatTrans.app_homology` for the stage-to-colimit
  -- natural transformation, with the target comparison isomorphism cancelled on the right.
  simpa [shortComplex_owner_homology_iso, Category.assoc] using
    congrArg
      (fun f ↦ f ≫ (T.mapHomologyIso (colim (J := J) (C := ModuleCat.{w} R))).inv)
      (NatTrans.app_homology
        (τ := module_colimit_evaluation_to_colim (R := R) (J := J) j) (S := T))

/-- Helper for Chap10 Lemma 10 76 2: homology-colimit preservation for an arbitrary
short-complex diagram follows from homology preservation by the module colimit functor. -/
private theorem shortComplexHomologyFunctor_preservesColimit_of_colim_preservesHomology
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{w} R)]
    [(colim (J := J) (C := ModuleCat.{w} R)).PreservesHomology]
    (S : J ⥤ ShortComplex (ModuleCat.{w} R)) :
    PreservesColimit S (ShortComplex.homologyFunctor (ModuleCat.{w} R)) := by
  let E := ShortComplex.functorEquivalence J (ModuleCat.{w} R)
  -- Move to the owner object under `ShortComplex.functorEquivalence`, prove preservation there,
  -- and transport it back across the counit isomorphism.
  letI : PreservesColimit ((E.inverse ⋙ E.functor).obj S)
      (ShortComplex.homologyFunctor (ModuleCat.{w} R)) := by
    dsimp [E]
    exact shortComplex_owner_preservesColimit_homologyFunctor_of_colim_preservesHomology
      (R := R) (J := J) (E.inverse.obj S)
  exact preservesColimit_of_iso_diagram
    (ShortComplex.homologyFunctor (ModuleCat.{w} R)) (E.counitIso.app S)

/-- Helper for Chap10 Lemma 10 76 2: after lifting modules to the universe large enough for the
filtered index category, `ModuleCat R` has exact filtered colimits of that shape. -/
private theorem moduleCatHasExactColimitsOfShapeLarge
    {J : Type v} [Category.{v} J] [IsFiltered J] :
    HasExactColimitsOfShape J (ModuleCat.{max u v} R) := by
  -- Exactness is pulled back from additive groups in the large universe, where `AB5OfSize_shrink`
  -- supplies the filtered-colimit exactness at the index-category size.
  haveI : AB5OfSize.{v, v} AddCommGrpCat.{max u v} :=
    AB5OfSize_shrink AddCommGrpCat.{max u v}
  exact HasExactColimitsOfShape.domain_of_functor J
    (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})

/-- Helper for Chap10 Lemma 10 76 2: the lifted large-universe module colimit functor preserves
homology of short complexes. -/
private theorem largeFilteredColimitFunctorPreservesHomology
    {J : Type v} [Category.{v} J] [IsFiltered J] :
    (colim (J := J) (C := ModuleCat.{max u v} R)).PreservesHomology := by
  -- The large exact-colimit bridge turns the standard exact-functor criterion into homology
  -- preservation for the large module category.
  letI : HasExactColimitsOfShape J (ModuleCat.{max u v} R) :=
    moduleCatHasExactColimitsOfShapeLarge (R := R) (J := J)
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  simpa using
    (colim.exact_mapShortComplex (J := J) (C := ModuleCat.{max u v} R)
      (S := S) (hS := hS)
      (hc₁ := colimit.isColimit S.X₁)
      (c₂ := colimit.cocone S.X₂) (hc₂ := colimit.isColimit S.X₂)
      (c₃ := colimit.cocone S.X₃) (hc₃ := colimit.isColimit S.X₃)
      (f := colim.map S.f) (g := colim.map S.g)
      (hf := by intro j; simp)
      (hg := by intro j; simp))

/-- Helper for Lemma 10.76.2: exactness of filtered colimits in `ModuleCat R` makes the module
colimit functor preserve homology of short complexes. -/
private theorem filtered_colimit_functor_preserves_homology
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    [HasExactColimitsOfShape J (ModuleCat.{u} R)] :
    (colim (J := J) (C := ModuleCat.{u} R)).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  simpa using
    (colim.exact_mapShortComplex (J := J) (C := ModuleCat.{u} R)
      (S := S) (hS := hS)
      (hc₁ := colimit.isColimit S.X₁)
      (c₂ := colimit.cocone S.X₂) (hc₂ := colimit.isColimit S.X₂)
      (c₃ := colimit.cocone S.X₃) (hc₃ := colimit.isColimit S.X₃)
      (f := colim.map S.f) (g := colim.map S.g)
      (hf := by intro j; simp)
      (hg := by intro j; simp))

/-- Helper for Chap10 Lemma 10 76 2: forgetting a lifted module to additive groups agrees with
lifting the forgotten additive group. -/
private noncomputable def moduleCatUliftForget₂Iso :
    forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{v, u} ≅
      ModuleCat.uliftFunctor.{v, u} R ⋙
        forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v} :=
  NatIso.ofComponents
    (fun _ ↦ Iso.refl _)
    (fun {X Y} f ↦ by
      -- Both routes act on a morphism by the same `ULift`-transport formula.
      ext x
      rfl)

/-- Helper for Chap10 Lemma 10 76 2: an additive `ULift` colimit witness transports to the
forgotten cocone of the lifted module cocone. -/
private noncomputable def addCommGrpUliftForgetMapCoconeIsColimit_toLargeForget
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (K : J ⥤ ModuleCat.{u} R) :
    IsColimit
        ((AddCommGrpCat.uliftFunctor.{v, u}).mapCocone
          ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapCocone (colimit.cocone K))) →
      IsColimit
        ((forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).mapCocone
          ((ModuleCat.uliftFunctor.{v, u} R).mapCocone (colimit.cocone K))) := by
  -- Transport the additive witness across the fixed comparison between forgetting after module
  -- `ULift` and applying additive `ULift` after forgetting.
  intro h
  exact IsColimit.mapCoconeEquiv (moduleCatUliftForget₂Iso (R := R)) h

/-- Helper for Chap10 Lemma 10 76 2: a colimit witness for the forgotten cocone of the lifted
module cocone transports back to the target additive `ULift` cocone. -/
private noncomputable def addCommGrpUliftForgetMapCoconeIsColimit_ofLargeForget
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (K : J ⥤ ModuleCat.{u} R) :
    IsColimit
        ((forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).mapCocone
          ((ModuleCat.uliftFunctor.{v, u} R).mapCocone (colimit.cocone K))) →
      IsColimit
        ((AddCommGrpCat.uliftFunctor.{v, u}).mapCocone
          ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapCocone (colimit.cocone K))) := by
  -- The same comparison transports a large-forget witness back to the additive `ULift` cocone.
  intro h
  exact IsColimit.mapCoconeEquiv (moduleCatUliftForget₂Iso (R := R)).symm h

/-- Helper for Chap10 Lemma 10 76 2: the ordinary forgetful functor from `ModuleCat.{u} R`
preserves filtered colimits in the source universe. -/
private theorem moduleCatForgetPreservesFilteredColimits :
    PreservesFilteredColimits (forget (ModuleCat.{u} R)) := by
  -- This is the imported filtered-colimit preservation instance, specialized for later reuse.
  simpa using
    (ModuleCat.FilteredColimits.forget_preservesFilteredColimits (R := R) :
      PreservesFilteredColimits (forget (ModuleCat.{u} R)))

/-- Helper for Chap10 Lemma 10 76 2: once the module diagram already lives in the large universe
`max u v`, the ordinary forgetful functor preserves its filtered colimit. -/
private theorem moduleCatLargeForgetPreservesColimitOfFilteredShape
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{max u v} R)]
    (K : J ⥤ ModuleCat.{max u v} R) :
    PreservesColimit K (forget (ModuleCat.{max u v} R)) := by
  -- In the large universe the additive forgetful package can be shrunk to the current shape size.
  letI : PreservesFilteredColimitsOfSize.{v, v} (forget AddCommGrpCat.{max u v}) :=
    preservesFilteredColimitsOfSize_shrink (forget AddCommGrpCat.{max u v})
  have hcomp : PreservesColimit K
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v} ⋙
        forget AddCommGrpCat.{max u v}) := by
    infer_instance
  simpa using hcomp

/-- Helper for Chap10 Lemma 10 76 2: the large ordinary forgetful functor also reflects filtered
colimits of the current shape. -/
private theorem moduleCatLargeForgetReflectsColimitOfFilteredShape
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{max u v} R)]
    (K : J ⥤ ModuleCat.{max u v} R) :
    ReflectsColimit K (forget (ModuleCat.{max u v} R)) := by
  -- This is the generic filtered-colimit reflection instance, specialized to the large universe.
  letI : ReflectsFilteredColimits (forget (ModuleCat.{max u v} R)) := by
    infer_instance
  infer_instance

/-- Helper for Chap10 Lemma 10 76 2: forgetting a lifted module to `Type` agrees with
first forgetting to `Type` and then applying the ordinary type-theoretic `ULift`. -/
private noncomputable def moduleCatUliftForgetIso :
    forget (ModuleCat.{u} R) ⋙ CategoryTheory.uliftFunctor.{v} ≅
      ModuleCat.uliftFunctor.{v, u} R ⋙ forget (ModuleCat.{max u v} R) :=
  (ModuleCat.uliftFunctorForgetIso (R := R) : _).symm

/-- Helper for Chap10 Lemma 10 76 2: filtered colimits commute with the module `ULift` functor
because the corresponding additive-group composite already preserves them. -/
private theorem moduleCatUliftPreservesColimitsOfShape_of_additiveColimits
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J AddCommGrpCat.{u}] :
    PreservesColimitsOfShape J (ModuleCat.uliftFunctor.{v, u} R) := by
  let e := moduleCatUliftForget₂Iso (R := R)
  -- When the small additive codomain already has `J`-colimits, the sibling additive `ULift`
  -- proof applies verbatim to the mixed-universe module lift.
  letI : PreservesColimitsOfShape J
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{v, u}) := by
    infer_instance
  letI : PreservesColimitsOfShape J
      (ModuleCat.uliftFunctor.{v, u} R ⋙
        forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}) :=
    preservesColimitsOfShape_of_natIso e
  -- Reflection along the large additive forgetful functor transports preservation back to
  -- modules.
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (ModuleCat.uliftFunctor.{v, u} R)
    (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})

/-- Helper for Chap10 Lemma 10 76 2: a `Type`-level `ULift` witness transports across the
comparison between `ModuleCat.uliftFunctor` and the ordinary type-theoretic `ULift`. -/
private noncomputable def moduleCatUliftUnderlyingMapCoconeIsColimit_of_smallForgetUlift
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (K : J ⥤ ModuleCat.{u} R)
    (h :
      IsColimit
        (((forget (ModuleCat.{u} R)) ⋙ CategoryTheory.uliftFunctor.{v}).mapCocone
          (colimit.cocone K))) :
    IsColimit
      ((forget (ModuleCat.{max u v} R)).mapCocone
        ((ModuleCat.uliftFunctor.{v, u} R).mapCocone (colimit.cocone K))) := by
  -- Transport the `Type`-level witness across the fixed comparison `moduleCatUliftForgetIso`.
  exact IsColimit.mapCoconeEquiv (moduleCatUliftForgetIso (R := R)) h

/-- Helper for Chap10 Lemma 10 76 2: the explicit filtered-colimit model of the lifted diagram
maps to the target lifted cocone. -/
private noncomputable def moduleCatUliftFilteredColimitDesc
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (K : J ⥤ ModuleCat.{u} R) :
    ModuleCat.FilteredColimits.colimit (K ⋙ ModuleCat.uliftFunctor.{v, u} R) ⟶
      (ModuleCat.uliftFunctor.{v, u} R).obj (colimit K) :=
  (ModuleCat.FilteredColimits.colimitCoconeIsColimit
      (K ⋙ ModuleCat.uliftFunctor.{v, u} R)).desc
    ((ModuleCat.uliftFunctor.{v, u} R).mapCocone (colimit.cocone K))

/-- Helper for Chap10 Lemma 10 76 2: the comparison map from the explicit lifted filtered colimit
agrees with the cocone legs on every stage. -/
private theorem moduleCatUliftFilteredColimitDesc_ι
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (K : J ⥤ ModuleCat.{u} R) (j : J) :
    (ModuleCat.FilteredColimits.colimitCocone
        (K ⋙ ModuleCat.uliftFunctor.{v, u} R)).ι.app j ≫
        moduleCatUliftFilteredColimitDesc (R := R) (J := J) K =
      ((ModuleCat.uliftFunctor.{v, u} R).mapCocone (colimit.cocone K)).ι.app j := by
  -- This is exactly the universal-property computation for the explicit filtered colimit model.
  exact
    (ModuleCat.FilteredColimits.colimitCoconeIsColimit
      (K ⋙ ModuleCat.uliftFunctor.{v, u} R)).fac
      ((ModuleCat.uliftFunctor.{v, u} R).mapCocone (colimit.cocone K))
      j

/-- Helper for Chap10 Lemma 10 76 2: the exact fixed-diagram colimit witness for
`ModuleCat.uliftFunctor`. -/
private noncomputable def moduleCatUliftMapCoconeIsColimit_direct
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (K : J ⥤ ModuleCat.{u} R) :
    IsColimit ((ModuleCat.uliftFunctor.{v, u} R).mapCocone (colimit.cocone K)) := by
  let U := ModuleCat.uliftFunctor.{v, u} R
  letI : ReflectsColimit (K ⋙ U) (forget (ModuleCat.{max u v} R)) :=
    moduleCatLargeForgetReflectsColimitOfFilteredShape (R := R) (J := J) (K := K ⋙ U)
  -- TODO: prove the large underlying `Type` cocone is colimiting by a direct filtered-colimit
  -- comparison for `K ⋙ U`; the naive small-universe `forget` route fails when `v > u`.
  have hLargeType :
      IsColimit
        ((forget (ModuleCat.{max u v} R)).mapCocone
          (U.mapCocone (colimit.cocone K))) := by
    sorry
  -- Reflection along the large ordinary forgetful functor upgrades the underlying witness back to
  -- the desired lifted module colimit witness.
  exact isColimitOfReflects (forget (ModuleCat.{max u v} R)) hLargeType

/-- Helper for Chap10 Lemma 10 76 2: forgetting a filtered module colimit to `Type` and then
applying the ordinary type-theoretic `ULift` still yields a colimiting cocone. -/
private noncomputable def smallForgetUliftMapCoconeIsColimit
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (K : J ⥤ ModuleCat.{u} R) :
    IsColimit
      (((forget (ModuleCat.{u} R)) ⋙ CategoryTheory.uliftFunctor.{v}).mapCocone
        (colimit.cocone K)) :=
by
  let U := ModuleCat.uliftFunctor.{v, u} R
  have hModule :
      IsColimit (U.mapCocone (colimit.cocone K)) :=
    moduleCatUliftMapCoconeIsColimit_direct (R := R) (J := J) K
  letI : PreservesColimit (K ⋙ U) (forget (ModuleCat.{max u v} R)) := by
    -- The large ordinary forgetful functor preserves filtered colimits once the lifted diagram
    -- already lives in the large module universe.
    exact moduleCatLargeForgetPreservesColimitOfFilteredShape
      (R := R) (J := J) (K := K ⋙ U)
  have hLargeType :
      IsColimit
        ((forget (ModuleCat.{max u v} R)).mapCocone
          (U.mapCocone (colimit.cocone K))) := by
    -- Forget the direct module witness to the large `Type` cocone.
    exact isColimitOfPreserves (forget (ModuleCat.{max u v} R)) hModule
  -- Transport the large underlying witness back across `moduleCatUliftForgetIso`.
  exact IsColimit.mapCoconeEquiv (moduleCatUliftForgetIso (R := R)).symm hLargeType

/-- Helper for Chap10 Lemma 10 76 2: once the underlying large `Type` cocone is colimiting,
reflection upgrades it to the corresponding large additive cocone. -/
private noncomputable def largeAdditiveForgetMapCoconeIsColimit_of_largeUnderlying
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (K : J ⥤ ModuleCat.{u} R)
    (h :
      IsColimit
        ((forget (ModuleCat.{max u v} R)).mapCocone
          ((ModuleCat.uliftFunctor.{v, u} R).mapCocone (colimit.cocone K)))) :
    IsColimit
      ((forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).mapCocone
        ((ModuleCat.uliftFunctor.{v, u} R).mapCocone (colimit.cocone K))) := by
  let U := ModuleCat.uliftFunctor.{v, u} R
  -- The large additive cocone is reflected from its underlying `Type` cocone.
  letI : PreservesFilteredColimitsOfSize.{v, v} (forget AddCommGrpCat.{max u v}) :=
    preservesFilteredColimitsOfSize_shrink (forget AddCommGrpCat.{max u v})
  letI : HasColimit
      (K ⋙ U ⋙ forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}) := by
    infer_instance
  letI : PreservesColimit
      (K ⋙ U ⋙ forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})
      (forget AddCommGrpCat.{max u v}) := by
    infer_instance
  let hReflect : ReflectsColimit
      (K ⋙ U ⋙ forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})
      (forget AddCommGrpCat.{max u v}) :=
    reflectsColimit_of_reflectsIsomorphisms
      (K ⋙ U ⋙ forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})
      (forget AddCommGrpCat.{max u v})
  exact (hReflect.reflects (by simpa [U] using h)).some

/-- Helper for Chap10 Lemma 10 76 2: an additive colimit witness for the forgotten lifted cocone
reflects back to a module colimit witness for the lifted cocone itself. -/
private noncomputable def moduleCatUliftMapCoconeIsColimit_of_additiveCocone
    {J : Type v} [Category.{v} J]
    {K : J ⥤ ModuleCat.{u} R} (c : Cocone K)
    (h :
      IsColimit
        ((AddCommGrpCat.uliftFunctor.{v, u}).mapCocone
          ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapCocone c))) :
    IsColimit ((ModuleCat.uliftFunctor.{v, u} R).mapCocone c) := by
  let U := ModuleCat.uliftFunctor.{v, u} R
  -- The additive `ULift` cocone is exactly the forgotten module `ULift` cocone up to the fixed
  -- comparison isomorphism `moduleCatUliftForget₂Iso`.
  have hforget :
      IsColimit
        ((forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).mapCocone
          (U.mapCocone c)) := by
    simpa [U] using
      IsColimit.mapCoconeEquiv (moduleCatUliftForget₂Iso (R := R)) h
  -- Reflection along the large additive forgetful functor upgrades the additive witness back to
  -- the desired module colimit witness.
  exact isColimitOfReflects
    (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})
    hforget

/-- Helper for Chap10 Lemma 10 76 2: an additive colimit witness for the forgotten lifted cocone
reflects back to a module colimit witness for the lifted cocone itself. -/
private noncomputable def moduleCatUliftMapCoconeIsColimit_of_additive
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (K : J ⥤ ModuleCat.{u} R)
    (h :
      IsColimit
        ((AddCommGrpCat.uliftFunctor.{v, u}).mapCocone
          ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapCocone (colimit.cocone K)))) :
    IsColimit ((ModuleCat.uliftFunctor.{v, u} R).mapCocone (colimit.cocone K)) := by
  exact moduleCatUliftMapCoconeIsColimit_of_additiveCocone
    (R := R) (c := colimit.cocone K) h

/-- Helper for Chap10 Lemma 10 76 2: the additive `ULift` of the forgotten module colimit cocone
is colimiting. -/
private noncomputable def addCommGrpUliftForgetMapCoconeIsColimit
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (K : J ⥤ ModuleCat.{u} R) :
    IsColimit
      ((AddCommGrpCat.uliftFunctor.{v, u}).mapCocone
        ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapCocone (colimit.cocone K))) := by
  let U := ModuleCat.uliftFunctor.{v, u} R
  -- Route correction: now that the fixed-diagram module witness is the main frontier, the
  -- additive claim is only one forgetful transport and one comparison isomorphism.
  have hModule :
      IsColimit (U.mapCocone (colimit.cocone K)) :=
    moduleCatUliftMapCoconeIsColimit_direct (R := R) (J := J) (K := K)
  have hLargeAdd :
      IsColimit
        ((forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).mapCocone
          (U.mapCocone (colimit.cocone K))) := by
    -- Forget the direct module witness to the large additive cocone.
    exact isColimitOfPreserves
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}) hModule
  -- Transport the large additive witness back across `moduleCatUliftForget₂Iso`.
  exact addCommGrpUliftForgetMapCoconeIsColimit_ofLargeForget
    (R := R) (J := J) K hLargeAdd

/-- Helper for Chap10 Lemma 10 76 2: the image of a filtered module colimit cocone under
`ModuleCat.uliftFunctor` is colimiting. -/
private noncomputable def moduleCatUliftMapCoconeIsColimit
    {J : Type v} [Category.{v} J]
    [IsFiltered J] [HasColimitsOfShape J (ModuleCat.{u} R)]
    (K : J ⥤ ModuleCat.{u} R) :
    IsColimit ((ModuleCat.uliftFunctor.{v, u} R).mapCocone (colimit.cocone K)) := by
  -- The direct fixed-diagram witness is now the canonical colimit proof for the lifted cocone.
  exact moduleCatUliftMapCoconeIsColimit_direct (R := R) (J := J) K

/-- Helper for Chap10 Lemma 10 76 2: the filtered-colimit comparison for
`ModuleCat.uliftFunctor.{v, u} R` is an isomorphism on any fixed diagram. -/
private theorem moduleCatUliftPost_isIso_of_filtered
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (K : J ⥤ ModuleCat.{u} R) :
    IsIso (colimit.post K (ModuleCat.uliftFunctor.{v, u} R)) := by
  let U := ModuleCat.uliftFunctor.{v, u} R
  letI : PreservesColimit K U := by
    -- The fixed-diagram mapped cocone is already colimiting, so recover local preservation from it.
    exact preservesColimit_of_preserves_colimit_cocone
      (colimit.isColimit K)
      (moduleCatUliftMapCoconeIsColimit (R := R) (J := J) K)
  -- The canonical comparison map is the `PreservesColimit` comparison for the fixed diagram `K`.
  infer_instance

/-- Helper for Chap10 Lemma 10 76 2: if the comparison map `colimit.post F G` is an isomorphism,
then the mapped cocone `G.mapCocone (colimit.cocone F)` is already a colimit cocone. -/
private noncomputable def isColimitOfMapCoconeOfPostIso
    {I : Type*} [Category I] {C : Type*} [Category C] {D : Type*} [Category D]
    [HasColimitsOfShape I C] [HasColimitsOfShape I D]
    (F : I ⥤ C) (G : C ⥤ D) [IsIso (colimit.post F G)] :
    IsColimit (G.mapCocone (colimit.cocone F)) := by
  -- The canonical comparison map identifies the colimit of `F ⋙ G` with the mapped cocone point.
  let e : colimit (F ⋙ G) ≅ G.obj (colimit F) := asIso (colimit.post F G)
  refine IsColimit.ofIsoColimit (colimit.isColimit (F ⋙ G)) ?_
  refine Cocone.ext e ?_
  intro i
  simpa using (colimit.ι_post (F := F) (G := G) i)

/-- Helper for Chap10 Lemma 10 76 2: applying `ModuleCat.uliftFunctor` to each term of a short
complex carries the fixed filtered-colimit comparison to an isomorphism. -/
private theorem moduleCatUliftMapShortComplexPost_isIso_of_filtered
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (S : J ⥤ ShortComplex (ModuleCat.{u} R)) :
    IsIso (colimit.post S ((ModuleCat.uliftFunctor.{v, u} R).mapShortComplex)) := by
  let U := ModuleCat.uliftFunctor.{v, u} R
  letI : HasColimitsOfShape J (ModuleCat.{max u v} R) := by
    infer_instance
  letI : IsIso (colimit.post (S ⋙ ShortComplex.π₁) U) :=
    moduleCatUliftPost_isIso_of_filtered (J := J) (S ⋙ ShortComplex.π₁)
  letI : PreservesColimit (S ⋙ ShortComplex.π₁) U := by
    exact preservesColimit_of_preserves_colimit_cocone
      (colimit.isColimit (S ⋙ ShortComplex.π₁))
      (isColimitOfMapCoconeOfPostIso (F := S ⋙ ShortComplex.π₁) (G := U))
  letI : IsIso (colimit.post (S ⋙ ShortComplex.π₂) U) :=
    moduleCatUliftPost_isIso_of_filtered (J := J) (S ⋙ ShortComplex.π₂)
  letI : PreservesColimit (S ⋙ ShortComplex.π₂) U := by
    exact preservesColimit_of_preserves_colimit_cocone
      (colimit.isColimit (S ⋙ ShortComplex.π₂))
      (isColimitOfMapCoconeOfPostIso (F := S ⋙ ShortComplex.π₂) (G := U))
  letI : IsIso (colimit.post (S ⋙ ShortComplex.π₃) U) :=
    moduleCatUliftPost_isIso_of_filtered (J := J) (S ⋙ ShortComplex.π₃)
  letI : PreservesColimit (S ⋙ ShortComplex.π₃) U := by
    exact preservesColimit_of_preserves_colimit_cocone
      (colimit.isColimit (S ⋙ ShortComplex.π₃))
      (isColimitOfMapCoconeOfPostIso (F := S ⋙ ShortComplex.π₃) (G := U))
  have hπ₁ :
      IsColimit (ShortComplex.π₁.mapCocone (U.mapShortComplex.mapCocone (colimit.cocone S))) := by
    -- The first projection is just the mapped cocone of `S ⋙ ShortComplex.π₁`.
    simpa using
      (isColimitOfPreserves U
        (isColimitOfPreserves ShortComplex.π₁ (colimit.isColimit S)))
  have hπ₂ :
      IsColimit (ShortComplex.π₂.mapCocone (U.mapShortComplex.mapCocone (colimit.cocone S))) := by
    -- The second projection is handled by the same fixed-diagram `ULift` comparison.
    simpa using
      (isColimitOfPreserves U
        (isColimitOfPreserves ShortComplex.π₂ (colimit.isColimit S)))
  have hπ₃ :
      IsColimit (ShortComplex.π₃.mapCocone (U.mapShortComplex.mapCocone (colimit.cocone S))) := by
    -- The third projection is again the mapped cocone of the corresponding module diagram.
    simpa using
      (isColimitOfPreserves U
        (isColimitOfPreserves ShortComplex.π₃ (colimit.isColimit S)))
  letI : PreservesColimit S U.mapShortComplex := by
    refine preservesColimit_of_preserves_colimit_cocone (colimit.isColimit S) ?_
    -- Rebuild the short-complex colimit from the three projected module colimits.
    exact ShortComplex.isColimitOfIsColimitπ
      (c := U.mapShortComplex.mapCocone (colimit.cocone S))
      hπ₁ hπ₂ hπ₃
  infer_instance

/-- Helper for Lemma 10.76.2: left-whiskering a functor isomorphism transports `colimit.post`
by naturality on each colimit leg. -/
private theorem colimit_post_whisker_left_iso_hom
    {I : Type*} [Category I] {C : Type*} [Category C] {D : Type*} [Category D]
    [HasColimitsOfShape I C] [HasColimitsOfShape I D]
    (F : I ⥤ C) {G H : C ⥤ D} (e : G ≅ H) :
    colim.map (Functor.isoWhiskerLeft F e).hom ≫ colimit.post F H =
      colimit.post F G ≫ (e.app (colimit F)).hom := by
  -- After precomposing with each cocone leg, the claim is exactly naturality of `e`.
  apply colimit.hom_ext
  intro i
  have h₁ :
      colimit.ι (F ⋙ G) i ≫ colim.map (Functor.isoWhiskerLeft F e).hom ≫ colimit.post F H =
        (Functor.isoWhiskerLeft F e).hom.app i ≫ H.map (colimit.ι F i) := by
    calc
      colimit.ι (F ⋙ G) i ≫ colim.map (Functor.isoWhiskerLeft F e).hom ≫ colimit.post F H =
          (Functor.isoWhiskerLeft F e).hom.app i ≫
            (colimit.ι (F ⋙ H) i ≫ colimit.post F H) := by
        simpa [Category.assoc] using
          (colimit.ι_map_assoc (α := (Functor.isoWhiskerLeft F e).hom)
            (h := colimit.post F H) i)
      _ = (Functor.isoWhiskerLeft F e).hom.app i ≫ H.map (colimit.ι F i) := by
        simpa using congrArg
          (fun k ↦ (Functor.isoWhiskerLeft F e).hom.app i ≫ k)
          (colimit.ι_post (F := F) (G := H) i)
  have h₂ :
      (Functor.isoWhiskerLeft F e).hom.app i ≫ H.map (colimit.ι F i) =
        G.map (colimit.ι F i) ≫ (e.app (colimit F)).hom := by
    simpa only [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc] using
      (e.hom.naturality (colimit.ι F i)).symm
  have h₃ :
      G.map (colimit.ι F i) ≫ (e.app (colimit F)).hom =
        colimit.ι (F ⋙ G) i ≫ colimit.post F G ≫ (e.app (colimit F)).hom := by
    simpa using congrArg
      (fun k ↦ k ≫ (e.app (colimit F)).hom)
      (colimit.ι_post (F := F) (G := G) i).symm
  exact h₁.trans (h₂.trans h₃)

/-- Helper for Chap10 Lemma 10 76 2: filtered homology comparisons for short-complex diagrams can
be proved after lifting modules to `ModuleCat.{max u v} R` and then reflected back. -/
private theorem uliftMap_shortComplexHomologyPost_isIso
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (S : J ⥤ ShortComplex (ModuleCat.{u} R)) :
    IsIso
      ((ModuleCat.uliftFunctor.{v, u} R).map
        (colimit.post S (ShortComplex.homologyFunctor (ModuleCat.{u} R)))) := by
  let U := ModuleCat.uliftFunctor.{v, u} R
  let Hsmall := ShortComplex.homologyFunctor (ModuleCat.{u} R)
  let Hlarge := ShortComplex.homologyFunctor (ModuleCat.{max u v} R)
  let e : U.mapShortComplex ⋙ Hlarge ≅ Hsmall ⋙ U :=
    ShortComplex.homologyFunctorIso U
  letI : HasColimitsOfShape J (ModuleCat.{max u v} R) := by
    infer_instance
  letI : (colim (J := J) (C := ModuleCat.{max u v} R)).PreservesHomology :=
    largeFilteredColimitFunctorPreservesHomology (R := R) (J := J)
  letI : IsIso (colimit.post (S ⋙ U.mapShortComplex) Hlarge) := by
    -- The large-universe homology functor preserves the colimit of the lifted diagram.
    letI : PreservesColimit (S ⋙ U.mapShortComplex) Hlarge :=
      shortComplexHomologyFunctor_preservesColimit_of_colim_preservesHomology
        (R := R) (J := J) (S := S ⋙ U.mapShortComplex)
    infer_instance
  letI : IsIso (colimit.post S U.mapShortComplex) :=
    moduleCatUliftMapShortComplexPost_isIso_of_filtered (R := R) (J := J) S
  have hLifted :
      IsIso (colimit.post S (U.mapShortComplex ⋙ Hlarge)) := by
    -- First move the lifted homology comparison into the standard `colimit.post_post` normal form.
    rw [← colimit.post_post (F := S) (G := U.mapShortComplex) Hlarge]
    have hpost :
        IsIso (colimit.post (S ⋙ U.mapShortComplex) Hlarge) := by
      infer_instance
    have hmap :
        IsIso (Hlarge.map (colimit.post S U.mapShortComplex)) := by
      infer_instance
    exact
      IsIso.comp_isIso'
        (f := colimit.post (S ⋙ U.mapShortComplex) Hlarge)
        (h := Hlarge.map (colimit.post S U.mapShortComplex))
        hpost hmap
  have hTransport :
      IsIso (colimit.post S (Hsmall ⋙ U)) := by
    -- Transport the lifted comparison across the canonical homology-commutation isomorphism.
    have hcomp :
        IsIso
          (colim.map (Functor.isoWhiskerLeft S e).hom ≫
            colimit.post S (Hsmall ⋙ U)) := by
      rw [colimit_post_whisker_left_iso_hom (F := S) (e := e)]
      have he :
          IsIso ((e.app (colimit S)).hom) := by
        infer_instance
      exact
        IsIso.comp_isIso'
          (f := colimit.post S (U.mapShortComplex ⋙ Hlarge))
          (h := (e.app (colimit S)).hom)
          hLifted he
    letI :
        IsIso
          (colim.map (Functor.isoWhiskerLeft S e).hom ≫
            colimit.post S (Hsmall ⋙ U)) := hcomp
    letI : IsIso (colim.map (Functor.isoWhiskerLeft S e).hom) := by
      infer_instance
    exact IsIso.of_isIso_comp_left
      (colim.map (Functor.isoWhiskerLeft S e).hom)
      (colimit.post S (Hsmall ⋙ U))
  letI : IsIso (colimit.post (S ⋙ Hsmall) U) :=
    moduleCatUliftPost_isIso_of_filtered (R := R) (J := J) (K := S ⋙ Hsmall)
  have hComposite :
      IsIso (colimit.post (S ⋙ Hsmall) U ≫ U.map (colimit.post S Hsmall)) := by
    -- The transported comparison factors through the fixed-diagram `ULift` comparison on homology.
    rw [colimit.post_post (F := S) (G := Hsmall) U]
    exact hTransport
  letI : IsIso (colimit.post (S ⋙ Hsmall) U ≫ U.map (colimit.post S Hsmall)) := hComposite
  exact IsIso.of_isIso_comp_left
    (colimit.post (S ⋙ Hsmall) U)
    (U.map (colimit.post S Hsmall))

/-- Helper for Chap10 Lemma 10 76 2: filtered homology comparisons for short-complex diagrams can
be proved after lifting modules to `ModuleCat.{max u v} R` and then reflected back. -/
private theorem shortComplexDiagramPost_isIso_viaUlift
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (S : J ⥤ ShortComplex (ModuleCat.{u} R)) :
    IsIso (colimit.post S (ShortComplex.homologyFunctor (ModuleCat.{u} R))) := by
  let U := ModuleCat.uliftFunctor.{v, u} R
  -- Route correction: prove the lifted comparison map is an isomorphism explicitly, then use the
  -- fully faithful `ULift` functor only for the final reflection step.
  letI :
      IsIso
        (U.map (colimit.post S (ShortComplex.homologyFunctor (ModuleCat.{u} R)))) :=
    uliftMap_shortComplexHomologyPost_isIso (R := R) (J := J) S
  -- The `ULift` functor is fully faithful, so isomorphisms detected after lifting descend.
  exact isIso_of_reflects_iso
    (colimit.post S (ShortComplex.homologyFunctor (ModuleCat.{u} R))) U

/-- Helper for Lemma 10.76.2: the owner-side comparison is the diagram-level comparison applied
to the concrete short-complex diagram underlying the owner object. -/
private theorem shortComplex_owner_post_isIso
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (T : ShortComplex (J ⥤ ModuleCat.{u} R)) :
    IsIso
      (colimit.post
        ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T)
        (ShortComplex.homologyFunctor (ModuleCat.{u} R))) := by
  -- Route correction: avoid a same-universe directed presentation and instead apply the
  -- large-universe `ulift` comparison directly to the displayed short-complex diagram.
  simpa using
    (shortComplexDiagramPost_isIso_viaUlift
      (R := R) (J := J)
      (S := (ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T))

/-- Helper for Lemma 10.76.2: the owner short complex attached to the degree-`n` window of the
fixed tensorized resolution satisfies `f ≫ g = 0` at each stage. -/
private theorem tor_fixed_right_resolution_window_owner_comp_eq_zero
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ ModuleCat.{u} R) (N : ModuleCat.{u} R) (n : ℕ) (i : I) :
    let S :=
      F ⋙ tor_fixed_right_resolution_complex_functor (R := R) N ⋙
        HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n
    let T := (ShortComplex.functorEquivalence I (ModuleCat.{u} R)).inverse.obj S
    T.f.app i ≫ T.g.app i = 0 := by
  -- Evaluate the short-complex relation carried by the owner object at the stage `i`.
  dsimp
  let S :=
    F ⋙ tor_fixed_right_resolution_complex_functor (R := R) N ⋙
      HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n
  let T := (ShortComplex.functorEquivalence I (ModuleCat.{u} R)).inverse.obj S
  simpa [T] using congrArg (fun α ↦ α.app i) T.zero

/-- Helper for Lemma 10.76.2: rebuilding the owner short complex from its maps recovers the
original owner object. -/
private theorem tor_fixed_right_resolution_window_owner_eq
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (T : ShortComplex (I ⥤ ModuleCat.{u} R))
    (_hcomp : ∀ i : I, T.f.app i ≫ T.g.app i = 0) :
    module_system_shortComplex (R := R) (I := I)
      (L := T.X₁) (M := T.X₂) (N := T.X₃) (φ := T.f) (ψ := T.g) _hcomp = T := by
  -- The `ShortComplex` structure is determined by its two maps; the proof field is propositional.
  cases T
  simp [module_system_shortComplex]

/-- Helper for Lemma 10.76.2: right-whiskering a diagram map transports `colimit.post` by the
standard `colimit.map_post` identity. -/
private theorem colimit_post_whisker_right_hom
    {I : Type*} [Category I] {C : Type*} [Category C] {D : Type*} [Category D]
    [HasColimitsOfShape I C] [HasColimitsOfShape I D]
    {A B : I ⥤ C} (ε : A ⟶ B) (H : C ⥤ D) :
    colim.map (Functor.whiskerRight ε H) ≫ colimit.post B H =
      colimit.post A H ≫ H.map (colim.map ε) := by
  -- This is exactly the right-whiskered naturality relation of `colimit.post`.
  simpa using (colimit.map_post (F := A) (G := B) (α := ε) H).symm

/-- Helper for Lemma 10.76.2: the canonical owner short complex can be rewritten back from a
concrete owner object `T` once the pointwise relation `f ≫ g = 0` is fixed. -/
private theorem tor_fixed_right_resolution_window_owner_eq_symm
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    [HasColimitsOfShape I (ModuleCat.{u} R)]
    (T : ShortComplex (I ⥤ ModuleCat.{u} R))
    (hcomp : ∀ i : I, T.f.app i ≫ T.g.app i = 0) :
    T =
      module_system_shortComplex
        (R := R) (I := I) (L := T.X₁) (M := T.X₂) (N := T.X₃) (φ := T.f) (ψ := T.g) hcomp := by
  -- This is exactly the symmetric form of the canonical owner reconstruction lemma.
  symm
  exact tor_fixed_right_resolution_window_owner_eq (R := R) (I := I) T hcomp

/-- Helper for Lemma 10.76.2: the directed-system comparison on the degree-`n` short-complex
window transports the owner-side `colimit.post` map to the concrete diagram using the counit of
`ShortComplex.functorEquivalence`. -/
private theorem tor_fixed_right_resolution_window_owner_transport_eq
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ModuleCat.{u} R) (N : ModuleCat.{u} R) (n : ℕ) :
    let S :=
      F ⋙ tor_fixed_right_resolution_complex_functor (R := R) N ⋙
        HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n
    let E := ShortComplex.functorEquivalence J (ModuleCat.{u} R)
    let T := E.inverse.obj S
    let H := ShortComplex.homologyFunctor (ModuleCat.{u} R)
    let ε : E.functor.obj T ≅ S := E.counitIso.app S
    colim.map (Functor.whiskerRight ε.hom H) ≫ colimit.post S H =
      colimit.post (E.functor.obj T) H ≫ H.map (colim.map ε.hom) := by
  -- Freeze the concrete short-complex diagram and transport the owner comparison in one step.
  dsimp
  let S :=
    F ⋙ tor_fixed_right_resolution_complex_functor (R := R) N ⋙
      HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n
  let E := ShortComplex.functorEquivalence J (ModuleCat R)
  let T := E.inverse.obj S
  let H := ShortComplex.homologyFunctor (ModuleCat.{u} R)
  let ε : E.functor.obj T ≅ S := E.counitIso.app S
  -- This is exactly the right-whiskered naturality identity for the typed counit.
  simpa only [S, E, T, H, ε]
    using
      (colimit_post_whisker_right_hom
        (I := J)
        (C := ShortComplex (ModuleCat.{u} R))
        (D := ModuleCat.{u} R)
        ε.hom H)

/-- Helper for Lemma 10.76.2: the directed-system comparison on the degree-`n` short-complex
window is an isomorphism. -/
private theorem tor_fixed_right_resolution_shortComplex_post_isIso
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ModuleCat.{u} R) (N : ModuleCat.{u} R) (n : ℕ) :
    IsIso
      (colimit.post
        (F ⋙ tor_fixed_right_resolution_complex_functor (R := R) N ⋙
          HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n)
        (ShortComplex.homologyFunctor (ModuleCat.{u} R))) := by
  let S :=
    F ⋙ tor_fixed_right_resolution_complex_functor (R := R) N ⋙
      HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n
  let E := ShortComplex.functorEquivalence J (ModuleCat.{u} R)
  let T : ShortComplex (J ⥤ ModuleCat.{u} R) := E.inverse.obj S
  let H : ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
    ShortComplex.homologyFunctor (ModuleCat.{u} R)
  let ε : E.functor.obj T ≅ S := E.counitIso.app S
  have howner :
      IsIso (colimit.post (E.functor.obj T) H) :=
    shortComplex_owner_post_isIso (R := R) (J := J) T
  have hmap :
      IsIso (H.map (colim.map ε.hom)) := by
    infer_instance
  have hcomp :
      IsIso (colim.map (Functor.whiskerRight ε.hom H) ≫ colimit.post S H) := by
    rw [tor_fixed_right_resolution_window_owner_transport_eq
      (R := R) (J := J) F N n]
    simpa [E, T, H, ε] using CategoryTheory.IsIso.comp_isIso' howner hmap
  exact IsIso.of_isIso_comp_left
    (colim.map (Functor.whiskerRight ε.hom H))
    (colimit.post S H)

/-- Helper for Lemma 10.76.2: the homology comparison after taking the degree-`n` short-complex
window factors through `colimit.post_post` for that window. -/
private theorem tor_fixed_right_resolution_homology_post_eq_post_post_window
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ModuleCat.{u} R) (N : ModuleCat.{u} R) (n : ℕ) :
    colimit.post
        (F ⋙ tor_fixed_right_resolution_complex_functor (R := R) N ⋙
          HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n)
        (ShortComplex.homologyFunctor (ModuleCat.{u} R)) ≫
      (ShortComplex.homologyFunctor (ModuleCat.{u} R)).map
        (colimit.post F
          (tor_fixed_right_resolution_complex_functor (R := R) N ⋙
            HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n)) =
    colimit.post F
      (tor_fixed_right_resolution_complex_functor (R := R) N ⋙
        HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n ⋙
          ShortComplex.homologyFunctor (ModuleCat.{u} R)) := by
  -- This is the standard `colimit.post_post` factorization for the degree-`n` short-complex
  -- window of the tensorized fixed resolution.
  simpa using
    (colimit.post_post
      (F := F)
      (G := tor_fixed_right_resolution_complex_functor (R := R) N ⋙
        HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n)
      (H := ShortComplex.homologyFunctor (ModuleCat.{u} R)))

/-- Helper for Lemma 10.76.2: a functor into `ShortComplex` preserves `J`-colimits once each of
its three projection functors does. -/
private theorem shortComplex_preservesColimitsOfShape_of_pi
    {D : Type*} [Category D]
    {J : Type*} [Category J]
    [HasColimitsOfShape J D]
    (G : D ⥤ ShortComplex (ModuleCat.{u} R))
    [PreservesColimitsOfShape J (G ⋙ ShortComplex.π₁)]
    [PreservesColimitsOfShape J (G ⋙ ShortComplex.π₂)]
    [PreservesColimitsOfShape J (G ⋙ ShortComplex.π₃)] :
    PreservesColimitsOfShape J G := by
  refine ⟨fun {F} => ?_⟩
  -- Rebuild the colimit in `ShortComplex` from the colimits of the three component diagrams.
  apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F)
  apply ShortComplex.isColimitOfIsColimitπ
  · exact isColimitOfPreserves (G ⋙ ShortComplex.π₁) (colimit.isColimit F)
  · exact isColimitOfPreserves (G ⋙ ShortComplex.π₂) (colimit.isColimit F)
  · exact isColimitOfPreserves (G ⋙ ShortComplex.π₃) (colimit.isColimit F)

/-- Helper for Lemma 10.76.2: the degree-`n` short-complex window on chain complexes preserves
filtered colimits of the current shape. -/
private theorem shortComplexFunctor_preserves_filtered_colimits
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (n : ℕ) :
    PreservesColimitsOfShape J
      (HomologicalComplex.shortComplexFunctor
        (ModuleCat.{u} R) (ComplexShape.down ℕ) n) := by
  letI : HasColimitsOfShape J
      (HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℕ)) := by
    infer_instance
  let W := HomologicalComplex.shortComplexFunctor
    (ModuleCat.{u} R) (ComplexShape.down ℕ) n
  -- Route correction: check the three components of the short-complex window separately.
  letI : PreservesColimitsOfShape J (W ⋙ ShortComplex.π₁) := by
    change PreservesColimitsOfShape J
      (HomologicalComplex.eval
        (ModuleCat.{u} R) (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev n))
    infer_instance
  letI : PreservesColimitsOfShape J (W ⋙ ShortComplex.π₂) := by
    change PreservesColimitsOfShape J
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n)
    infer_instance
  letI : PreservesColimitsOfShape J (W ⋙ ShortComplex.π₃) := by
    change PreservesColimitsOfShape J
      (HomologicalComplex.eval
        (ModuleCat.{u} R) (ComplexShape.down ℕ) ((ComplexShape.down ℕ).next n))
    infer_instance
  exact shortComplex_preservesColimitsOfShape_of_pi (R := R) W

/-- Helper for Lemma 10.76.2: filtered colimits commute with taking the degree-`n` short-complex
window of the fixed tensorized projective resolution. -/
private theorem tor_fixed_right_resolution_window_post_isIso
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ModuleCat.{u} R) (N : ModuleCat.{u} R) (n : ℕ) :
    IsIso
      (colimit.post F
        (tor_fixed_right_resolution_complex_functor (R := R) N ⋙
          HomologicalComplex.shortComplexFunctor
            (ModuleCat.{u} R) (ComplexShape.down ℕ) n)) := by
  let G := tor_fixed_right_resolution_complex_functor (R := R) N
  let W := HomologicalComplex.shortComplexFunctor
    (ModuleCat.{u} R) (ComplexShape.down ℕ) n
  -- Route correction: infer preservation for the composite functor directly instead of
  -- normalizing the comparison through `colimit.post_post`.
  letI : PreservesColimitsOfShape J G :=
    tor_fixed_right_resolution_complex_functor_preserves_filtered_colimits
      (R := R) (J := J) N
  letI : PreservesColimitsOfShape J W :=
    shortComplexFunctor_preserves_filtered_colimits (R := R) (J := J) n
  letI : PreservesColimitsOfShape J (G ⋙ W) := by
    infer_instance
  exact (show IsIso (colimit.post F (G ⋙ W)) by infer_instance)

/-- Helper for Lemma 10.76.2: after taking the degree-`n` short-complex window, filtered colimits
also commute with short-complex homology for the fixed tensorized resolution. -/
private theorem tor_fixed_right_resolution_window_homology_post_isIso
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ModuleCat.{u} R) (N : ModuleCat.{u} R) (n : ℕ) :
    IsIso
      (colimit.post F
        (tor_fixed_right_resolution_complex_functor (R := R) N ⋙
          HomologicalComplex.shortComplexFunctor
            (ModuleCat.{u} R) (ComplexShape.down ℕ) n ⋙
          ShortComplex.homologyFunctor (ModuleCat.{u} R))) := by
  let G := tor_fixed_right_resolution_complex_functor (R := R) N
  let W := HomologicalComplex.shortComplexFunctor
    (ModuleCat.{u} R) (ComplexShape.down ℕ) n
  let H := ShortComplex.homologyFunctor (ModuleCat.{u} R)
  let S := F ⋙ G ⋙ W
  have hwindow : IsIso (colimit.post F (G ⋙ W)) :=
    tor_fixed_right_resolution_window_post_isIso (R := R) (J := J) F N n
  have hshort : IsIso (colimit.post S H) :=
    tor_fixed_right_resolution_shortComplex_post_isIso (R := R) (J := J) F N n
  letI : IsIso (colimit.post F (G ⋙ W)) := hwindow
  have hmap : IsIso (H.map (colimit.post F (G ⋙ W))) := by
    infer_instance
  -- Route correction: use the already-named `post_post` factorization for this window once,
  -- then compose the two standard isomorphisms.
  rw [← tor_fixed_right_resolution_homology_post_eq_post_post_window
    (R := R) (J := J) F N n]
  simpa [G, W, H, S] using CategoryTheory.IsIso.comp_isIso' hshort hmap

/-- Helper for Lemma 10.76.2: degree-`n` chain-complex homology identifies with homology of the
degree-`n` short-complex window. -/
private noncomputable def homologyFunctor_shortComplexIso
    (n : ℕ) :
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n ≅
      HomologicalComplex.shortComplexFunctor
          (ModuleCat.{u} R) (ComplexShape.down ℕ) n ⋙
        ShortComplex.homologyFunctor (ModuleCat.{u} R) :=
  HomologicalComplex.homologyFunctorIso
    (ModuleCat.{u} R) (ComplexShape.down ℕ) n

/-- Helper for Lemma 10.76.2: whiskering the degree-`n` homology/window comparison by the fixed
tensorized resolution produces the comparison needed for the filtered-colimit transport step. -/
private noncomputable def tor_fixed_right_resolution_homology_window_whiskerIso
    (N : ModuleCat.{u} R) (n : ℕ) :
    tor_fixed_right_resolution_complex_functor (R := R) N ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n ≅
      tor_fixed_right_resolution_complex_functor (R := R) N ⋙
        HomologicalComplex.shortComplexFunctor
            (ModuleCat.{u} R) (ComplexShape.down ℕ) n ⋙
          ShortComplex.homologyFunctor (ModuleCat.{u} R) :=
  Functor.isoWhiskerLeft
    (tor_fixed_right_resolution_complex_functor (R := R) N)
    (homologyFunctor_shortComplexIso (R := R) n)

/-- Helper for Lemma 10.76.2: the whiskered homology/window comparison evaluated at `colimit F`
is the terminal transport morphism used in the filtered-colimit comparison. -/
private noncomputable def tor_fixed_right_resolution_homology_window_app
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ModuleCat.{u} R) (N : ModuleCat.{u} R) (n : ℕ) :
    (tor_fixed_right_resolution_complex_functor (R := R) N ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n).obj
        (colimit F) ⟶
      (tor_fixed_right_resolution_complex_functor (R := R) N ⋙
        HomologicalComplex.shortComplexFunctor
            (ModuleCat.{u} R) (ComplexShape.down ℕ) n ⋙
          ShortComplex.homologyFunctor (ModuleCat.{u} R)).obj
        (colimit F) :=
  ((tor_fixed_right_resolution_homology_window_whiskerIso
      (R := R) N n).app (colimit F)).hom

/-- Helper for Lemma 10.76.2: the filtered-colimit comparison for fixed-resolution homology in
degree `n`. -/
private noncomputable def tor_fixed_right_resolution_homology_post
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ModuleCat.{u} R) (N : ModuleCat.{u} R) (n : ℕ) :
    colimit
        (F ⋙ tor_fixed_right_resolution_complex_functor (R := R) N ⋙
          HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n) ⟶
      (tor_fixed_right_resolution_complex_functor (R := R) N ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n).obj
        (colimit F) :=
  colimit.post F
    (tor_fixed_right_resolution_complex_functor (R := R) N ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n)

/-- Helper for Lemma 10.76.2: transport the fixed-resolution homology comparison through the
comparison between chain-complex homology and the short-complex window in degree `n`. -/
private noncomputable def tor_fixed_right_resolution_homology_transport
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ModuleCat.{u} R) (N : ModuleCat.{u} R) (n : ℕ) :
    colimit
        (F ⋙ tor_fixed_right_resolution_complex_functor (R := R) N ⋙
          HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n) ⟶
      (tor_fixed_right_resolution_complex_functor (R := R) N ⋙
        HomologicalComplex.shortComplexFunctor
            (ModuleCat.{u} R) (ComplexShape.down ℕ) n ⋙
          ShortComplex.homologyFunctor (ModuleCat.{u} R)).obj
        (colimit F) :=
  tor_fixed_right_resolution_homology_post (R := R) F N n ≫
    tor_fixed_right_resolution_homology_window_app (R := R) F N n

/-- Helper for Lemma 10.76.2: the generic whisker-left transport identity specializes to the
fixed-resolution homology transport morphism without exposing its internal normal form. -/
private theorem tor_fixed_right_resolution_homology_transport_eq_whisker
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ModuleCat.{u} R) (N : ModuleCat.{u} R) (n : ℕ) :
    colim.map
        (Functor.isoWhiskerLeft F
          (tor_fixed_right_resolution_homology_window_whiskerIso
            (R := R) N n)).hom ≫
      colimit.post F
        (tor_fixed_right_resolution_complex_functor (R := R) N ⋙
          HomologicalComplex.shortComplexFunctor
            (ModuleCat.{u} R) (ComplexShape.down ℕ) n ⋙
          ShortComplex.homologyFunctor (ModuleCat.{u} R)) =
    tor_fixed_right_resolution_homology_transport (R := R) F N n := by
  -- Keep the terminal transport opaque by specializing the generic whisker-left formula once.
  simpa [tor_fixed_right_resolution_homology_transport,
    tor_fixed_right_resolution_homology_post,
    tor_fixed_right_resolution_homology_window_app] using
    (colimit_post_whisker_left_iso_hom
      (F := F)
      (e := tor_fixed_right_resolution_homology_window_whiskerIso
        (R := R) N n))

/-- Helper for Lemma 10.76.2: the fixed-resolution homology comparison becomes an isomorphism
after transporting from chain-complex homology to short-complex homology in degree `n`. -/
private theorem tor_fixed_right_resolution_homology_transport_isIso
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ModuleCat.{u} R) (N : ModuleCat.{u} R) (n : ℕ) :
    IsIso (tor_fixed_right_resolution_homology_transport (R := R) F N n) := by
  let e := tor_fixed_right_resolution_homology_window_whiskerIso (R := R) N n
  have hleft : IsIso (colim.map (Functor.isoWhiskerLeft F e).hom) := by
    infer_instance
  have hright :
      IsIso
        (colimit.post F
          (tor_fixed_right_resolution_complex_functor (R := R) N ⋙
            HomologicalComplex.shortComplexFunctor
              (ModuleCat.{u} R) (ComplexShape.down ℕ) n ⋙
            ShortComplex.homologyFunctor (ModuleCat.{u} R))) :=
    tor_fixed_right_resolution_window_homology_post_isIso
      (R := R) (J := J) F N n
  -- Route correction: rewrite the whiskered composite to the existing opaque transport morphism
  -- and compose the two known isomorphisms there.
  rw [← tor_fixed_right_resolution_homology_transport_eq_whisker
    (R := R) (J := J) F N n]
  exact CategoryTheory.IsIso.comp_isIso' hleft hright

/-- Helper for Lemma 10.76.2: the whiskered homology/window comparison remains an isomorphism when
evaluated at the colimit module. -/
private theorem tor_fixed_right_resolution_homology_window_app_isIso
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ModuleCat.{u} R) (N : ModuleCat.{u} R) (n : ℕ) :
    IsIso
      (tor_fixed_right_resolution_homology_window_app (R := R) F N n) := by
  -- Evaluating a natural isomorphism at the colimit object preserves the isomorphism.
  simpa [tor_fixed_right_resolution_homology_window_app]
    using
      (show
        IsIso
          (((tor_fixed_right_resolution_homology_window_whiskerIso
              (R := R) N n).app (colimit F)).hom) by
          infer_instance)

/-- Helper for Lemma 10.76.2: after passing to homology in degree `n`, the fixed-resolution
complex functor still sends the directed-colimit comparison morphism to an isomorphism. -/
private theorem tor_fixed_right_resolution_homology_post_isIso
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ModuleCat.{u} R) (N : ModuleCat.{u} R) (n : ℕ) :
    IsIso (tor_fixed_right_resolution_homology_post (R := R) F N n) := by
  letI : IsIso (tor_fixed_right_resolution_homology_transport (R := R) F N n) :=
    tor_fixed_right_resolution_homology_transport_isIso
      (R := R) (J := J) F N n
  letI : IsIso (tor_fixed_right_resolution_homology_window_app (R := R) F N n) :=
    tor_fixed_right_resolution_homology_window_app_isIso
      (R := R) (J := J) F N n
  have htransport :
      IsIso
        (tor_fixed_right_resolution_homology_post (R := R) F N n ≫
          tor_fixed_right_resolution_homology_window_app (R := R) F N n) := by
    simpa [tor_fixed_right_resolution_homology_transport] using
      (show
        IsIso (tor_fixed_right_resolution_homology_transport (R := R) F N n) by
          infer_instance)
  letI : IsIso
      (tor_fixed_right_resolution_homology_post (R := R) F N n ≫
        tor_fixed_right_resolution_homology_window_app (R := R) F N n) := htransport
  -- Once the transported comparison is invertible, peel off the terminal whisker isomorphism.
  exact IsIso.of_isIso_comp_right
    (tor_fixed_right_resolution_homology_post (R := R) F N n)
    (tor_fixed_right_resolution_homology_window_app (R := R) F N n)

end

/-- Helper for Lemma 10.76.2: the final Tor comparison is the whisker-left transport of the
fixed-resolution homology comparison along `tor_fixed_right_resolution_homology_iso`. -/
private theorem tor_filteredColimitComparison_transport_eq_whisker
    {R : Type u} [CommRing R]
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ModuleCat.{u} R)
    (N : ModuleCat.{u} R) (n : ℕ) :
    colim.map
        (Functor.isoWhiskerLeft F
          (tor_fixed_right_resolution_homology_iso (R := R) N n)).hom ≫
      tor_fixed_right_resolution_homology_post (R := R) F N n =
    colimit.post F ((Tor (ModuleCat.{u} R) n).flip.obj N) ≫
      ((tor_fixed_right_resolution_homology_iso (R := R) N n).app (colimit F)).hom := by
  -- This is the same whisker-left transport pattern used in the homology transport step.
  simpa [tor_fixed_right_resolution_homology_post] using
    (colimit_post_whisker_left_iso_hom
      (F := F)
      (e := tor_fixed_right_resolution_homology_iso (R := R) N n))

/-- Helper for Lemma 10.76.2: for a directed system, the canonical Tor comparison is obtained by
transporting the degree-`n` homology comparison of the fixed tensorized resolution. -/
private theorem tor_filteredColimitComparison_isIso_of_directed
    {R : Type u} [CommRing R]
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ModuleCat.{u} R)
    (N : ModuleCat.{u} R) (n : ℕ) :
    IsIso (colimit.post F ((Tor (ModuleCat.{u} R) n).flip.obj N)) := by
  let e := tor_fixed_right_resolution_homology_iso (R := R) N n
  have hleft : IsIso (colim.map (Functor.isoWhiskerLeft F e).hom) := by
    infer_instance
  have hright : IsIso (tor_fixed_right_resolution_homology_post (R := R) F N n) :=
    tor_fixed_right_resolution_homology_post_isIso
      (R := R) (J := J) F N n
  have hcomp :
      IsIso
        (colimit.post F ((Tor (ModuleCat.{u} R) n).flip.obj N) ≫
          (e.app (colimit F)).hom) := by
    -- Route correction: keep the final Tor transport in the opaque whisker-left normal form.
    rw [← tor_filteredColimitComparison_transport_eq_whisker
      (R := R) (J := J) F N n]
    exact CategoryTheory.IsIso.comp_isIso' hleft hright
  letI :
      IsIso
        (colimit.post F ((Tor (ModuleCat.{u} R) n).flip.obj N) ≫
          (e.app (colimit F)).hom) := hcomp
  letI : IsIso ((e.app (colimit F)).hom) := by
    infer_instance
  -- The transport target is an isomorphism, so the Tor comparison itself is already invertible.
  exact IsIso.of_isIso_comp_right
    (colimit.post F ((Tor (ModuleCat.{u} R) n).flip.obj N))
    ((e.app (colimit F)).hom)

end

-- Proof sketch: compute `Tor_n^R(-, N)` from a projective resolution of `N`. Tensoring that fixed
-- resolution termwise with the filtered diagram `F` commutes with filtered colimits by Lemma
-- `10.12.9`, and homology commutes with filtered colimits by Lemma `10.8.8`, so the canonical
-- comparison map is an isomorphism.
/-- Chap10 Lemma 10 76 2: for a filtered diagram `i ↦ M_i` of `R`-modules and a fixed
`R`-module `N`,
the canonical map
`\mathop{\mathrm{colim}}_i \operatorname{Tor}_n^R(M_i, N) \to
\operatorname{Tor}_n^R(\mathop{\mathrm{colim}}_i M_i, N)`
is an isomorphism. -/
@[stacks 0BNF]
theorem tor_filteredColimitComparison_isIso
    {R : Type u} [CommRing R]
    {J : Type v} [Category.{v} J] [IsFiltered J] [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ModuleCat.{u} R)
    (N : ModuleCat.{u} R) (n : ℕ) :
    IsIso (colimit.post F ((Tor (ModuleCat.{u} R) n).flip.obj N)) := by
  exact tor_filteredColimitComparison_isIso_of_directed
    (R := R) (J := J) F N n
