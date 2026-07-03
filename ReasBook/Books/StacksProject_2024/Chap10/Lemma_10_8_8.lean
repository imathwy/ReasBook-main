import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Abelian.Exact
import StacksProject_2024.Chap10.Lemma_10_8_2
import StacksProject_2024.Chap10.Lemma_10_8_3
import StacksProject_2024.Chap10.Lemma_10_8_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open ShortComplex

universe u v

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

/-- Helper for Lemma 10.8.8: in the nonempty directed case, the homology comparison morphism is
an isomorphism. -/
theorem module_system_homology_comparison_isIso_of_nonempty
    [Nonempty I]
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    IsIso (module_system_homology_comparison hcomp) := by
  -- Route correction: the preserved-homology route asked for a global exactness instance that the
  -- source proof never uses. The remaining work is the source-faithful direct-limit chase: prove
  -- surjectivity and injectivity on representatives using Lemma 10.8.3 and Lemma 10.8.4, starting
  -- from `module_system_homology_comparison_comp_pointwise_colimit_ι`.
  -- TODO: transport the target through `ShortComplex.moduleCatHomologyIso`, identify the image of
  -- a stage class with the class of `colimit.ι M i m`, and finish by the explicit representative
  -- chase from the natural-language proof.
  sorry

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

/-- Lemma 10.8.8 (3): the canonical comparison morphism from the colimit of the stagewise homology
modules `H_i` to the homology of the colimit complex is an isomorphism. This formalizes the
textbook equality `H = colim_i H_i`. -/
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
