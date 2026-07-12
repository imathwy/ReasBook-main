import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Abelian.Exact
import StacksProject_2024.Chap10.Lemma_10_8_2
import StacksProject_2024.Chap10.Lemma_10_8_3
import StacksProject_2024.Chap10.Lemma_10_8_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open ShortComplex

universe u v w

noncomputable section

section

variable {R : Type u} [Ring R]
variable {I : Type v} [Preorder I]
variable {L M N : I ⥤ ModuleCat R}
variable {φ : L ⟶ M} {ψ : M ⟶ N}

-- Proof sketch: use `NatTrans.ext` and check equality objectwise; the hypothesis says exactly that
-- each component of `φ ≫ ψ` is zero.
private theorem module_system_comp_eq_zero
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    φ ≫ ψ = 0 := by
  -- Check the composite natural transformation objectwise, where the hypothesis gives the vanishing.
  ext i x
  change ((φ.app i ≫ ψ.app i).hom) x = 0
  simpa using LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (hcomp i)) x

/-- The short complex in the functor category attached to the composable system
`L ⟶ M ⟶ N`. This is the owner object from which the stagewise short complexes and their
homology are derived. -/
noncomputable def module_system_shortComplex
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    ShortComplex (I ⥤ ModuleCat R) :=
  .mk φ ψ (module_system_comp_eq_zero hcomp)

/-- Lemma 10.8.8 (1): if each stage `L_i ⟶ M_i ⟶ N_i` is a complex, then their homology modules
assemble into a system over `I`; in the directed case this is the system from the statement of
the lemma. -/
@[stacks 00DB]
noncomputable def module_system_homology
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    I ⥤ ModuleCat R :=
  (ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj
      (module_system_shortComplex hcomp) ⋙
    homologyFunctor (ModuleCat R)

-- Proof sketch: first rewrite `colim.map φ ≫ colim.map ψ` as `colim.map (φ ≫ ψ)` using
-- `colim.map_comp`, then substitute the vanishing natural transformation from
-- `module_system_comp_eq_zero`.
/-- Lemma 10.8.8 (2): the induced sequence on colimits
`colim L_i ⟶ colim M_i ⟶ colim N_i` is again a complex. -/
@[stacks 00DB]
theorem colimit_module_system_isComplex
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    colim.map φ ≫ colim.map ψ = 0 := by
  have h :=
    congrArg (fun α ↦ colim.map α)
      (module_system_comp_eq_zero hcomp)
  simpa only [Functor.map_comp, Functor.map_zero] using h

/-- The canonical comparison morphism from the colimit of the stagewise homology system to the
homology of the colimit short complex attached to `L ⟶ M ⟶ N`. -/
noncomputable def module_system_homology_comparison
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :=
  colimit.post
    ((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj
      (module_system_shortComplex hcomp))
    (homologyFunctor (ModuleCat R))

/-- Helper for Lemma 10.8.8: the transition maps in the stagewise homology system are literally
the homology maps induced by the corresponding morphisms of stage short complexes. -/
@[simp]
theorem module_system_homology_map_eq
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) {i j : I} (f : i ⟶ j) :
    (module_system_homology (R := R) (I := I) (L := L) (M := M) (N := N) hcomp).map f =
      (homologyFunctor (ModuleCat R)).map
        ((module_system_shortComplex hcomp).mapNatTrans
          ((evaluation I (ModuleCat R)).map f)) := by
  rfl

/-- Helper for Lemma 10.8.8: the universal stage map `X_i ⟶ colim X` is natural in the diagram
`X`. -/
private theorem evaluation_to_colim_naturality
    (i : I) {F G : I ⥤ ModuleCat R} (α : F ⟶ G) :
    α.app i ≫ colimit.ι G i = colimit.ι F i ≫ colim.map α := by
  simpa using (colimit.ι_map α i).symm

/-- Helper for Lemma 10.8.8: the natural transformation from evaluation at `i` to the colimit
functor whose component on `F` is the canonical map `F.obj i ⟶ colimit F`. -/
noncomputable def evaluation_to_colim
    (i : I) :
    (evaluation I (ModuleCat R)).obj i ⟶ colim (J := I) (C := ModuleCat R) where
  app F := colimit.ι F i
  naturality _ _ α := evaluation_to_colim_naturality (R := R) (I := I) i α

/-- Helper for Lemma 10.8.8: the colimit of an empty module diagram is a zero object. -/
private theorem module_colimit_isZero_of_isEmpty
    [IsEmpty I] (F : I ⥤ ModuleCat R) :
    IsZero (colimit F : ModuleCat R) := by
  -- Compare the empty colimit with the zero module, which is also initial in `ModuleCat`.
  have hinitial : IsInitial (colimit F : ModuleCat R) :=
    (isColimitEquivIsInitialOfIsEmpty (ModuleCat R) (colimit.cocone F))
      (colimit.isColimit F)
  have hzeroModule : IsZero (ModuleCat.of R PUnit) :=
    ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit)
  let e : (colimit F : ModuleCat R) ≅ ModuleCat.of R PUnit :=
    hinitial.coconePointUniqueUpToIso hzeroModule.isInitial
  exact IsZero.of_iso hzeroModule e

/-- Helper for Lemma 10.8.8: the categorical colimit of the stage short-complex diagram agrees
with the short complex obtained by taking colimits componentwise. -/
noncomputable def shortComplex_colimit_iso_map_colim
    (S : ShortComplex (I ⥤ ModuleCat R)) :
    colimit ((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj S) ≅
      S.map (colim (J := I) (C := ModuleCat R)) :=
  IsColimit.coconePointUniqueUpToIso
    (colimit.isColimit ((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj S))
    (ShortComplex.isColimitColimitCocone
      ((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj S))

/-- Helper for Lemma 10.8.8: the comparison isomorphism from the categorical colimit to the
componentwise colimit short complex matches the canonical cocone legs. -/
theorem shortComplex_colimit_iso_map_colim_ι
    (S : ShortComplex (I ⥤ ModuleCat R)) (i : I) :
    colimit.ι ((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj S) i ≫
        (shortComplex_colimit_iso_map_colim (R := R) (I := I) S).hom =
      (ShortComplex.colimitCocone
        ((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj S)).ι.app i := by
  -- Both cocones are colimiting, so the unique comparison iso intertwines the cocone maps.
  exact
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit ((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj S))
      (ShortComplex.isColimitColimitCocone
        ((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj S))
      i

/-- Helper for Lemma 10.8.8: the stage cocone map into the pointwise-colimit short complex is the
map induced by the natural transformation `evaluation i ⟶ colim`. -/
@[simp]
theorem shortComplex_colimitCocone_ι_eq_mapNatTrans_colimit_ι
    (S : ShortComplex (I ⥤ ModuleCat R)) (i : I) :
    (ShortComplex.colimitCocone
      ((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj S)).ι.app i =
      S.mapNatTrans (evaluation_to_colim (R := R) (I := I) i) := by
  -- This is the componentwise definition of `ShortComplex.colimitCocone`.
  ext <;> rfl

variable [IsDirectedOrder I]

/-- Helper for Chap10 Lemma 10 8 8: filtered colimits of `R`-modules are exact for the preorder
category underlying the directed system. -/
private theorem moduleCatHasExactFilteredColimitsOfShape :
    [Nonempty I] →
    HasExactColimitsOfShape I (ModuleCat.{max v w, u} R) := by
  intro
  let _ : SmallCategory I := inferInstance
  let _ : IsFiltered I := CategoryTheory.isFiltered_of_directed_le_nonempty I
  let _ : Limits.HasColimitsOfShape I AddCommGrpCat.{max v w} := by
    exact AddCommGrpCat.hasColimitsOfShape (J := I)
  let _ : Limits.HasColimitsOfShape I (ModuleCat.{max v w, u} R) :=
    ModuleCat.hasColimitsOfShape R I
  let _ : AB5OfSize.{v, v} AddCommGrpCat.{max v w} :=
    AB5OfSize_shrink AddCommGrpCat.{max v w}
  let _ : HasExactColimitsOfShape I AddCommGrpCat.{max v w} := inferInstance
  -- Exactness descends across the forgetful functor to additive groups.
  exact HasExactColimitsOfShape.domain_of_functor I
    (forget₂ (ModuleCat.{max v w, u} R) AddCommGrpCat.{max v w})

/-- Helper for Chap10 Lemma 10 8 8: exactness of filtered colimits in `ModuleCat R` makes the
module colimit functor preserve homology of short complexes. -/
private theorem filteredColimitFunctorPreservesHomology :
    [Nonempty I] →
    (colim (J := I) (C := ModuleCat.{max v w, u} R)).PreservesHomology := by
  intro
  let _ : HasExactColimitsOfShape I (ModuleCat.{max v w, u} R) :=
    moduleCatHasExactFilteredColimitsOfShape (R := R) (I := I)
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  -- The owner theorem `colim.exact_mapShortComplex` is the exactness input needed for
  -- `preservesHomology_of_map_exact`.
  simpa using
    (colim.exact_mapShortComplex (J := I) (C := ModuleCat.{max v w, u} R)
      (S := S) (hS := hS)
      (hc₁ := colimit.isColimit S.X₁)
      (c₂ := colimit.cocone S.X₂) (hc₂ := colimit.isColimit S.X₂)
      (c₃ := colimit.cocone S.X₃) (hc₃ := colimit.isColimit S.X₃)
      (f := colim.map S.f) (g := colim.map S.g)
      (hf := by intro i; simp)
      (hg := by intro i; simp))

omit [IsDirectedOrder I] in
/-- Helper for Chap10 Lemma 10 8 8: the objectwise homology isomorphisms for a short complex in
a functor category are natural in the index. -/
theorem shortComplexFunctorHomologyIso_naturality
    (S : ShortComplex (I ⥤ ModuleCat.{max v w, u} R)) {i j : I} (f : i ⟶ j) :
    S.homology.map f ≫
        (S.mapHomologyIso ((evaluation I (ModuleCat.{max v w, u} R)).obj j)).inv =
      (S.mapHomologyIso ((evaluation I (ModuleCat.{max v w, u} R)).obj i)).inv ≫
        (homologyFunctor (ModuleCat.{max v w, u} R)).map
          (S.mapNatTrans ((evaluation I (ModuleCat.{max v w, u} R)).map f)) := by
  -- The standard naturality formula for `app_homology` gives the square after composing with
  -- the inverse of the homology isomorphism at the target index.
  simpa [Category.assoc] using
    congrArg
      (fun α ↦ α ≫
        (S.mapHomologyIso ((evaluation I (ModuleCat.{max v w, u} R)).obj j)).inv)
      (NatTrans.app_homology
        (τ := (evaluation I (ModuleCat.{max v w, u} R)).map f) (S := S))

/-- Helper for Chap10 Lemma 10 8 8: functor-category homology is identified with the diagram
obtained by taking homology objectwise. -/
noncomputable def shortComplexFunctorHomologyIso
    (S : ShortComplex (I ⥤ ModuleCat.{max v w, u} R)) :
    S.homology ≅
      ((ShortComplex.functorEquivalence I (ModuleCat.{max v w, u} R)).functor.obj S ⋙
        homologyFunctor (ModuleCat.{max v w, u} R)) :=
  NatIso.ofComponents
    (fun i ↦ (S.mapHomologyIso ((evaluation I (ModuleCat.{max v w, u} R)).obj i)).symm)
    (fun {_ _} f ↦ shortComplexFunctorHomologyIso_naturality
      (R := R) (I := I) S f)

omit [IsDirectedOrder I] in
/-- Helper for Chap10 Lemma 10 8 8: if the module colimit functor preserves homology, then the
homology functor preserves the colimit of the associated diagram of short complexes. -/
theorem shortComplexHomologyFunctor_preservesColimit_of_colimPreservesHomology
    [(colim (J := I) (C := ModuleCat.{max v w, u} R)).PreservesHomology]
    (S : ShortComplex (I ⥤ ModuleCat.{max v w, u} R)) :
    PreservesColimit
      ((ShortComplex.functorEquivalence I (ModuleCat.{max v w, u} R)).functor.obj S)
      (homologyFunctor (ModuleCat.{max v w, u} R)) := by
  let K := (ShortComplex.functorEquivalence I (ModuleCat.{max v w, u} R)).functor.obj S
  let H := homologyFunctor (ModuleCat.{max v w, u} R)
  let α := shortComplexFunctorHomologyIso (R := R) (I := I) S
  -- First transport the ordinary colimit cocone for `S.homology` across the objectwise
  -- homology iso, giving a colimit cocone for the displayed homology diagram.
  let hpre : IsColimit ((Cocone.precompose α.symm.hom).obj (colimit.cocone S.homology)) :=
    (IsColimit.precomposeHomEquiv α.symm (colimit.cocone S.homology)).symm
      (colimit.isColimit S.homology)
  let cKH := colimit.cocone (K ⋙ H)
  let cH := H.mapCocone (ShortComplex.colimitCocone K)
  let e : cKH.pt ≅ cH.pt :=
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit (K ⋙ H)) hpre ≪≫
      ((ShortComplex.homologyFunctorIso
        (F := colim (J := I) (C := ModuleCat.{max v w, u} R))).app S).symm
  -- The mapped short-complex colimit cocone is isomorphic to the standard colimit cocone of
  -- objectwise homology; on legs this is exactly `NatTrans.app_homology`.
  refine preservesColimit_of_preserves_colimit_cocone (ShortComplex.isColimitColimitCocone K) ?_
  refine IsColimit.ofIsoColimit (colimit.isColimit (K ⋙ H)) (Cocone.ext e ?_)
  intro j
  dsimp [cKH, cH, e, H, K, α]
  have hunique :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit (K ⋙ H)) hpre j
  dsimp [K, H, α, shortComplexFunctorHomologyIso] at hunique
  rw [← Category.assoc]
  erw [hunique]
  simpa [Category.assoc] using
    congrArg
      (fun f ↦
        (S.mapHomologyIso ((evaluation I (ModuleCat.{max v w, u} R)).obj j)).hom ≫ f ≫
          (S.mapHomologyIso (colim (J := I) (C := ModuleCat.{max v w, u} R))).inv)
      (NatTrans.app_homology (τ := @evaluation_to_colim.{u, v, w} R _ I _ j) (S := S))

omit [IsDirectedOrder I] in
/-- Helper for Lemma 10.8.8: on the `i`-th cocone leg, the comparison map followed by the
transport to the pointwise-colimit short complex is the homology map induced by the stage-to-
colimit morphism of short complexes. This is the first source-faithful bridge from the abstract
comparison map to the representative chase on stages. -/
theorem module_system_homology_comparison_comp_pointwise_colimit_ι
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) (i : I) :
    colimit.ι (module_system_homology hcomp) i ≫
    module_system_homology_comparison hcomp ≫
        (homologyFunctor (ModuleCat R)).map
          (shortComplex_colimit_iso_map_colim (R := R) (I := I)
            (module_system_shortComplex hcomp)).hom =
      (homologyFunctor (ModuleCat R)).map
        ((module_system_shortComplex hcomp).mapNatTrans
          (evaluation_to_colim (R := R) (I := I) i)) := by
  -- Expand the universal comparison on the `i`-th cocone leg, then rewrite the short-complex
  -- cocone map into the pointwise colimit by the explicit `evaluation_to_colim` morphism.
  dsimp [module_system_homology, module_system_homology_comparison]
  let F :=
    ((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj
      (module_system_shortComplex hcomp))
  have hpost :
      colimit.ι (F ⋙ homologyFunctor (ModuleCat R)) i ≫
            colimit.post F (homologyFunctor (ModuleCat R)) ≫
          homologyMap
            (shortComplex_colimit_iso_map_colim (R := R) (I := I)
              (module_system_shortComplex hcomp)).hom =
        homologyMap
          (colimit.ι F i ≫
            (shortComplex_colimit_iso_map_colim (R := R) (I := I)
              (module_system_shortComplex hcomp)).hom) := by
    simpa [← Functor.map_comp] using
      congrArg
        (fun ζ ↦ ζ ≫
          homologyMap
            (shortComplex_colimit_iso_map_colim (R := R) (I := I)
              (module_system_shortComplex hcomp)).hom)
        (colimit.ι_post (F := F) (G := homologyFunctor (ModuleCat R)) i)
  have hpost' :
      colimit.ι
            (((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj
              (module_system_shortComplex hcomp)) ⋙ homologyFunctor (ModuleCat R))
            i ≫
          colimit.post
            (((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj
              (module_system_shortComplex hcomp)))
            (homologyFunctor (ModuleCat R)) ≫
            homologyMap
              (shortComplex_colimit_iso_map_colim (R := R) (I := I)
                (module_system_shortComplex hcomp)).hom =
        homologyMap
          (colimit.ι
              (((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj
                (module_system_shortComplex hcomp)))
              i ≫
            (shortComplex_colimit_iso_map_colim (R := R) (I := I)
              (module_system_shortComplex hcomp)).hom) := by
    simpa [F] using hpost
  refine hpost'.trans ?_
  congr 1
  rw [shortComplex_colimit_iso_map_colim_ι,
    shortComplex_colimitCocone_ι_eq_mapNatTrans_colimit_ι]

omit [IsDirectedOrder I] in
/-- Helper for Chap10 Lemma 10 8 8: the objectwise homology isomorphisms for the evaluation
functors are natural in the index, so they identify functor-category homology with the stagewise
homology diagram on maps. -/
theorem module_system_termwiseHomology_naturality
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) {i j : I} (f : i ⟶ j) :
    (module_system_shortComplex hcomp).homology.map f ≫
        ((module_system_shortComplex hcomp).mapHomologyIso
          ((evaluation I (ModuleCat R)).obj j)).inv =
      ((module_system_shortComplex hcomp).mapHomologyIso
        ((evaluation I (ModuleCat R)).obj i)).inv ≫
        (module_system_homology hcomp).map f := by
  let S := module_system_shortComplex hcomp
  -- Proof comment: the component at `i` is the standard homology comparison for the evaluation
  -- functor `(evaluation I (ModuleCat R)).obj i`, and `NatTrans.app_homology` gives the
  -- naturality square directly.
  -- Proof comment: `NatTrans.app_homology` for the evaluation morphism is exactly the naturality
  -- square of these objectwise homology isomorphisms.
  simpa [S, module_system_homology, Category.assoc] using
    congrArg
      (fun α ↦ α ≫ (S.mapHomologyIso ((evaluation I (ModuleCat R)).obj j)).inv)
      (NatTrans.app_homology
        (τ := (evaluation I (ModuleCat R)).map f) (S := S))

/-- Helper for Chap10 Lemma 10 8 8: the abstract homology object of the short complex in the
functor category is naturally isomorphic to the stagewise homology system. -/
noncomputable def module_system_homologyIso
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    (module_system_shortComplex hcomp).homology ≅ module_system_homology hcomp :=
  NatIso.ofComponents
    (fun i ↦
      ((module_system_shortComplex hcomp).mapHomologyIso
        ((evaluation I (ModuleCat R)).obj i)).symm)
    (fun {i j} f ↦ by
      -- Proof comment: the component maps are exactly the inverses of the objectwise evaluation
      -- homology isomorphisms, and the previous theorem gives their naturality square.
      simpa using module_system_termwiseHomology_naturality
        (R := R) (I := I) (φ := φ) (ψ := ψ) (i := i) (j := j) hcomp f)

/-- Chap10 Lemma 10 8 8 (3): in the nonempty directed case, the canonical comparison morphism
from the colimit of the stagewise homology modules `H_i` to the homology of the colimit complex
is an isomorphism. -/
theorem module_system_homology_comparison_isIso_of_nonempty
    [Nonempty I]
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    IsIso (module_system_homology_comparison hcomp) := by
  -- Route correction: install preservation of the displayed colimit by homology, avoiding the
  -- earlier direct `mapIso` transport across the stagewise homology isomorphism.
  letI : (colim (J := I) (C := ModuleCat R)).PreservesHomology :=
    filteredColimitFunctorPreservesHomology (R := R) (I := I)
  let S := module_system_shortComplex hcomp
  letI : PreservesColimit
      ((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj S)
      (homologyFunctor (ModuleCat R)) :=
    shortComplexHomologyFunctor_preservesColimit_of_colimPreservesHomology
      (R := R) (I := I) S
  -- With preservation installed, the comparison is the standard `colimit.post` map for the
  -- homology functor, hence an isomorphism by the colimit-preservation instance.
  dsimp [module_system_homology_comparison]
  change IsIso (colimit.post
    ((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj S)
    (homologyFunctor (ModuleCat R)))
  infer_instance

omit [IsDirectedOrder I] in
/-- Helper for Lemma 10.8.8: in the empty-index case, both sides of the comparison are zero
modules, so the comparison morphism is an isomorphism. -/
theorem module_system_homology_comparison_isIso_of_isEmpty
    [IsEmpty I]
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    IsIso (module_system_homology_comparison hcomp) := by
  -- The source is the colimit of an empty diagram of homology modules, hence zero.
  let hsource : IsZero (colimit (module_system_homology hcomp) : ModuleCat R) :=
    module_colimit_isZero_of_isEmpty
      (R := R) (I := I) (F := module_system_homology hcomp)
  -- The pointwise-colimit short complex has zero middle object, so its homology is zero.
  let Sinf := (module_system_shortComplex hcomp).map (colim (J := I) (C := ModuleCat R))
  have hpointwise : IsZero Sinf.homology := by
    -- The middle module is `colimit M`, which vanishes because the index category is empty.
    exact ShortComplex.isZero_homology_of_isZero_X₂
      (S := Sinf)
      (module_colimit_isZero_of_isEmpty (R := R) (I := I) (F := M))
  -- Transport that zero object back across the canonical iso from the categorical colimit short
  -- complex to the pointwise-colimit short complex.
  let htarget :
      IsZero
        (((homologyFunctor (ModuleCat R)).obj
          (colimit ((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj
            (module_system_shortComplex hcomp)))) : ModuleCat R) :=
    IsZero.of_iso hpointwise
      ((homologyFunctor (ModuleCat R)).mapIso
        (shortComplex_colimit_iso_map_colim (R := R) (I := I)
          (module_system_shortComplex hcomp)))
  -- Any morphism between zero objects is automatically an isomorphism.
  exact IsZero.isIso hsource htarget (module_system_homology_comparison hcomp)

/-- Helper for Chap10 Lemma 10 8 8: the unrestricted directed case follows by splitting the
index preorder into the empty and nonempty cases. -/
@[stacks 00DB]
theorem module_system_homology_comparison_isIso
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    IsIso (module_system_homology_comparison hcomp) := by
  -- Route correction: compare the categorical colimit short complex with the pointwise colimit
  -- short complex, then dispatch to the standard `mapHomologyIso` argument in the nonempty case.
  rcases isEmpty_or_nonempty I with hI | hI
  · letI : IsEmpty I := hI
    exact module_system_homology_comparison_isIso_of_isEmpty
      (R := R) (I := I) (L := L) (M := M) (N := N) hcomp
  · letI : Nonempty I := hI
    exact module_system_homology_comparison_isIso_of_nonempty
      (R := R) (I := I) (L := L) (M := M) (N := N) hcomp

noncomputable instance (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    IsIso (module_system_homology_comparison hcomp) :=
  module_system_homology_comparison_isIso hcomp

end
