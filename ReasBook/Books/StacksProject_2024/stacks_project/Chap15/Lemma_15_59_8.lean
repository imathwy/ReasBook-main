import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.RingTheory.Flat.CategoryTheory
import StacksProject_2024.stacks_project.Chap15.Definition_15_59_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open CategoryTheory.MonoidalCategory
open scoped HomologicalComplex₂

noncomputable section

universe u v

namespace CochainComplex

variable {R : Type u} [CommRing R]

/- Domain sampling pass:
* primary domain: K-flat cochain complexes of `R`-modules and stability of the owner predicate
  under filtered colimits;
* sampled owner declarations:
  - `CochainComplex.IsKFlat` from `Definition_15_59_1`, the source-facing owner predicate;
  - `CochainComplex.isKFlat_iff` from `Definition_15_59_1`, the canonical eliminator exposing only
    the acyclicity-preservation content of `IsKFlat`;
  - `CategoryTheory.Limits.colimit`, the canonical owner of the filtered colimit object;
  - the ambient filtered-category typeclass `IsFiltered`, which is the canonical owner abstraction
    for the indexing hypothesis rather than a bespoke sequential-system wrapper.

Source/core/bridge triage:
* `source-facing`: the textbook closure of K-flatness under filtered colimits of module-valued
  cochain complexes;
* `core/canonical`: `CochainComplex.IsKFlat` on `CochainComplex (ModuleCat R) ℤ` together with the
  canonical colimit object `colimit F`;
* `bridge/view`: the sequential specialization obtained by instantiating the owner theorem at the
  preorder category `ℕ`; this file keeps that only as derived prose, not as a second public owner.

Primitive data are only the diagram `F`, the ambient colimit instance `[HasColimit F]`, and the
stagewise K-flatness hypotheses `hF`. The colimit complex and its K-flatness are derived from the
canonical colimit owner and the predicate `CochainComplex.IsKFlat`, so this file should not
introduce any auxiliary wrapper for sequential systems or filtered-colimit K-flat data.
-/

/-- Helper for Lemma 15.59.8: exactness of a short complex of `I`-indexed module systems can be
checked after evaluating at every stage `i : I`. -/
private theorem shortComplex_exact_iff_exact_app
    {I : Type v} [Category.{v} I]
    (S : ShortComplex (I ⥤ ModuleCat R)) :
    S.Exact ↔ ∀ i : I, (S.map ((evaluation I (ModuleCat R)).obj i)).Exact := by
  let hEval :
      JointlyReflectIsomorphisms
        ((evaluation I (ModuleCat R)).obj :
          I → (I ⥤ ModuleCat R) ⥤ ModuleCat R) := by
    refine ⟨fun {X Y} f _ ↦ ?_⟩
    rw [NatTrans.isIso_iff_isIso_app]
    intro i
    simpa using
      (inferInstance : IsIso (((evaluation I (ModuleCat R)).obj i).map f))
  -- Once the evaluation family is known to reflect isomorphisms, exactness is pointwise.
  exact hEval.exact_iff S

/-- Helper for Lemma 15.59.8: the differentials `X^{n-1} → X^n` in a diagram of cochain complexes
assemble into a natural transformation of module-valued diagrams. -/
private theorem prev_d_naturality
    {I : Type v} [Category.{v} I]
    (G : I ⥤ CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    ∀ ⦃i j : I⦄ (f : i ⟶ j),
      (G.map f).f (n - 1) ≫ (G.obj j).d (n - 1) n =
        (G.obj i).d (n - 1) n ≫ (G.map f).f n := by
  intro i j f
  -- This is exactly the degree-`n - 1 → n` commutativity relation for a morphism of complexes.
  simpa using (G.map f).comm (n - 1) n

/-- Helper for Lemma 15.59.8: the differentials `X^n → X^{n+1}` in a diagram of cochain complexes
assemble into a natural transformation of module-valued diagrams. -/
private theorem next_d_naturality
    {I : Type v} [Category.{v} I]
    (G : I ⥤ CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    ∀ ⦃i j : I⦄ (f : i ⟶ j),
      (G.map f).f n ≫ (G.obj j).d n (n + 1) =
        (G.obj i).d n (n + 1) ≫ (G.map f).f (n + 1) := by
  intro i j f
  -- This is the adjacent degree commutativity relation for a morphism of complexes.
  simpa using (G.map f).comm n (n + 1)

/-- Helper for Lemma 15.59.8: the degree-`n - 1 → n` differentials of a diagram of cochain
complexes form a natural transformation in the functor category. -/
private theorem prev_d_natTrans_naturality
    {I : Type v} [Category.{v} I]
    (G : I ⥤ CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    ∀ ⦃i j : I⦄ (f : i ⟶ j),
      (G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) (n - 1)).map f ≫
          (G.obj j).d (n - 1) n =
        (G.obj i).d (n - 1) n ≫
          (G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n).map f := by
  intro i j f
  exact prev_d_naturality (G := G) n f

/-- Helper for Lemma 15.59.8: the degree-`n → n + 1` differentials of a diagram of cochain
complexes satisfy the naturality condition required for a natural transformation. -/
private theorem next_d_natTrans_naturality
    {I : Type v} [Category.{v} I]
    (G : I ⥤ CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    ∀ ⦃i j : I⦄ (f : i ⟶ j),
      (G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n).map f ≫
          (G.obj j).d n (n + 1) =
        (G.obj i).d n (n + 1) ≫
          (G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) (n + 1)).map f := by
  intro i j f
  exact next_d_naturality (G := G) n f

/-- Helper for Lemma 15.59.8: the degree-`n - 1 → n` differentials of a diagram of cochain
complexes form a natural transformation in the functor category. -/
private def prev_d_natTrans
    {I : Type v} [Category.{v} I]
    (G : I ⥤ CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) (n - 1) ⟶
      G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n where
  app i := (G.obj i).d (n - 1) n
  naturality := prev_d_natTrans_naturality (G := G) n

/-- Helper for Lemma 15.59.8: the degree-`n → n + 1` differentials of a diagram of cochain
complexes form a natural transformation in the functor category. -/
private def next_d_natTrans
    {I : Type v} [Category.{v} I]
    (G : I ⥤ CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n ⟶
      G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) (n + 1) where
  app i := (G.obj i).d n (n + 1)
  naturality := next_d_natTrans_naturality (G := G) n

/-- Helper for Lemma 15.59.8: the consecutive degree differentials in a diagram of cochain
complexes compose to zero in the functor category. -/
private theorem degree_d_comp_eq_zero
    {I : Type v} [Category.{v} I]
    (G : I ⥤ CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    prev_d_natTrans (G := G) n ≫ next_d_natTrans (G := G) n = 0 := by
  -- Check the composite after evaluation at each stage `i`; it is the usual `d ≫ d = 0`.
  ext i x
  change
    (ModuleCat.Hom.hom (((G.obj i).d (n - 1) n) ≫ ((G.obj i).d n (n + 1))) x =
      ModuleCat.Hom.hom (0 : (G.obj i).X (n - 1) ⟶ (G.obj i).X (n + 1)) x)
  exact LinearMap.congr_fun
    (ModuleCat.hom_ext_iff.mp ((G.obj i).d_comp_d (n - 1) n (n + 1))) x

/-- Helper for Lemma 15.59.8: the degree-`n` short complex attached to a diagram of cochain
complexes, viewed inside the functor category `I ⥤ ModuleCat R`. -/
private def degree_shortComplex
    {I : Type v} [Category.{v} I]
    (G : I ⥤ CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    ShortComplex (I ⥤ ModuleCat R) :=
  ShortComplex.mk
    (prev_d_natTrans (G := G) n)
    (next_d_natTrans (G := G) n)
    (degree_d_comp_eq_zero (G := G) n)

/-- Helper for Lemma 15.59.8: evaluating the functor-category degree-`n` short complex at a
stage `i` recovers the ordinary degree-`n` short complex of `G.obj i`. -/
private def degree_shortComplex_app_iso
    {I : Type v} [Category.{v} I]
    (G : I ⥤ CochainComplex (ModuleCat R) ℤ) (n : ℤ) (i : I) :
    (degree_shortComplex (G := G) n).map ((evaluation I (ModuleCat R)).obj i) ≅
      (G.obj i).sc n :=
  -- Both short complexes have the same three terms and differentials after evaluation at `i`.
  (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)) ≪≫
    ((G.obj i).isoSc' (i := n - 1) (j := n) (k := n + 1)
      (CochainComplex.prev ℤ n) (CochainComplex.next ℤ n)).symm

/-- Helper for Lemma 15.59.8: if each stage of a diagram of cochain complexes is acyclic, then
the induced degree-`n` short complex in the functor category is exact. -/
private theorem degree_shortComplex_exact
    {I : Type v} [Category.{v} I]
    (G : I ⥤ CochainComplex (ModuleCat R) ℤ)
    (hG : ∀ i : I, (G.obj i).Acyclic) (n : ℤ) :
    (degree_shortComplex (G := G) n).Exact := by
  -- Reflect exactness through evaluation, where the short complex becomes the stagewise one.
  rw [shortComplex_exact_iff_exact_app]
  intro i
  have hExactAt : (G.obj i).ExactAt n := by
    exact (HomologicalComplex.acyclic_iff (G.obj i)).mp (hG i) n
  have hExactSc : ((G.obj i).sc n).Exact := by
    exact (HomologicalComplex.exactAt_iff (G.obj i) n).mp hExactAt
  -- Transport the stagewise exactness back across the evaluation identification.
  exact (ShortComplex.exact_iff_of_iso (degree_shortComplex_app_iso (G := G) n i)).mpr hExactSc

/-- Helper for Lemma 15.59.8: acyclicity is preserved under isomorphism of cochain complexes. -/
private theorem acyclic_of_iso
    {K L : CochainComplex (ModuleCat R) ℤ}
    (e : K ≅ L) (hK : K.Acyclic) :
    L.Acyclic := by
  -- Reduce to exactness of the degreewise short complexes and transport those along `e`.
  rw [HomologicalComplex.acyclic_iff] at hK ⊢
  intro n
  have hExactK : (K.sc n).Exact := by
    exact (HomologicalComplex.exactAt_iff K n).mp (hK n)
  let eSc : K.sc n ≅ L.sc n :=
    (HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) n).mapIso e
  -- The short complexes are isomorphic degreewise, so exactness transfers across that iso.
  exact (HomologicalComplex.exactAt_iff L n).mpr <| ShortComplex.exact_of_iso eSc hExactK

/-- Helper for Lemma 15.59.8: filtered colimits of `R`-modules are exact in the universe needed
for an arbitrary filtered indexing category `I`. -/
private theorem moduleCat_filtered_exact_colimits
    {I : Type v} [SmallCategory I] [IsFiltered I] :
    HasExactColimitsOfShape I (ModuleCat.{v, u} R) := by
  -- Route correction: descend exactness directly from `AddCommGrpCat` through `forget₂`, rather
  -- than transporting a native-universe `ModuleCat` owner across `ShrinkHoms`.
  let _ : HasColimitsOfShape I AddCommGrpCat.{v} := by
    let _ : Small.{v, v} I := inferInstance
    exact AddCommGrpCat.hasColimitsOfShape (J := I)
  let _ : HasColimitsOfShape I (ModuleCat.{v, u} R) := ModuleCat.hasColimitsOfShape R I
  let _ : AB5OfSize.{v, v} AddCommGrpCat.{v} := AB5OfSize_shrink AddCommGrpCat.{v}
  let _ : HasExactColimitsOfShape I AddCommGrpCat.{v} := by
    infer_instance
  -- Exactness is reflected by the forgetful functor because finite limits and filtered colimits
  -- are created on the underlying additive groups.
  exact HasExactColimitsOfShape.domain_of_functor I
    (forget₂ (ModuleCat.{v, u} R) AddCommGrpCat.{v})

/-- Helper for Lemma 15.59.8: the first `mapShortComplex` compatibility condition for
`degree_shortComplex G n` is exactly the canonical colimit comparison for `prev_d_natTrans`. -/
private theorem degree_shortComplex_colimit_map_prev
    {I : Type v} [SmallCategory I] [IsFiltered I]
    (G : I ⥤ CochainComplex (ModuleCat.{v, u} R) ℤ) (n : ℤ) (j : I) :
    colimit.ι (degree_shortComplex (G := G) n).X₁ j ≫ colim.map (prev_d_natTrans (G := G) n) =
      (degree_shortComplex (G := G) n).f.app j ≫
        colimit.ι (degree_shortComplex (G := G) n).X₂ j := by
  let _ : HasColimitsOfShape I (ModuleCat.{v, u} R) := ModuleCat.hasColimitsOfShape R I
  -- This is precisely the universal `ι_map` formula, after unfolding the short-complex fields.
  simpa [degree_shortComplex] using
    (colimit.ι_map (prev_d_natTrans (G := G) n) j)

/-- Helper for Lemma 15.59.8: the second `mapShortComplex` compatibility condition for
`degree_shortComplex G n` is exactly the canonical colimit comparison for `next_d_natTrans`. -/
private theorem degree_shortComplex_colimit_map_next
    {I : Type v} [SmallCategory I] [IsFiltered I]
    (G : I ⥤ CochainComplex (ModuleCat.{v, u} R) ℤ) (n : ℤ) (j : I) :
    colimit.ι (degree_shortComplex (G := G) n).X₂ j ≫ colim.map (next_d_natTrans (G := G) n) =
      (degree_shortComplex (G := G) n).g.app j ≫
        colimit.ι (degree_shortComplex (G := G) n).X₃ j := by
  let _ : HasColimitsOfShape I (ModuleCat.{v, u} R) := ModuleCat.hasColimitsOfShape R I
  -- This is the same `ι_map` identity for the second structure morphism.
  simpa [degree_shortComplex] using
    (colimit.ι_map (next_d_natTrans (G := G) n) j)

/-- Helper for Lemma 15.59.8: evaluating the chosen colimit cocone of `G` at degree `k` gives a
canonical cocone on the degree-`k` module diagram. -/
private def colimit_degree_term_cocone
    {I : Type v} [Category.{v} I] [IsFiltered I]
    (G : I ⥤ CochainComplex (ModuleCat.{v, u} R) ℤ) [HasColimit G] (k : ℤ) :
    Cocone (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) k) :=
  (HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) k).mapCocone (colimit.cocone G)

/-- Helper for Lemma 15.59.8: the evaluated cocone on the degree-`k` terms of `G` is colimiting,
because evaluation preserves colimits of cochain complexes. -/
private def colimit_degree_term_isColimit
    {I : Type v} [Category.{v} I] [IsFiltered I]
    (G : I ⥤ CochainComplex (ModuleCat.{v, u} R) ℤ) [HasColimit G] (k : ℤ) :
    IsColimit (colimit_degree_term_cocone (R := R) (G := G) k) :=
  Limits.isColimitOfPreserves
    (HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) k)
    (colimit.isColimit G)

/-- Helper for Lemma 15.59.8: the evaluated colimit cocone is also colimiting on the concrete
surface `ModuleCat R`, so later tensor-preservation arguments do not need extra universe
transport. -/
private noncomputable def colimit_degree_term_isColimit_concrete
    {I : Type v} [Category.{v} I] [IsFiltered I]
    (G : I ⥤ CochainComplex (ModuleCat R) ℤ) [HasColimit G] (k : ℤ) :
    IsColimit
      ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) k).mapCocone
        (colimit.cocone G)) :=
  -- This is the same `isColimitOfPreserves` argument, stated directly on the concrete owner.
  Limits.isColimitOfPreserves
    (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) k)
    (colimit.isColimit G)

/-- Helper for Lemma 15.59.8: the colimit of the degree-`k` terms is canonically identified with
the degree-`k` term of the colimit complex. -/
private noncomputable def colimit_degree_term_iso
    {I : Type v} [Category.{v} I] [IsFiltered I]
    (G : I ⥤ CochainComplex (ModuleCat.{v, u} R) ℤ) [HasColimit G] (k : ℤ) :
    colimit (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) k) ≅
      (colimit G).X k :=
  ((colimit_degree_term_isColimit (R := R) (G := G) k).coconePointUniqueUpToIso
    (colimit.isColimit
      (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) k))).symm

/-- Helper for Lemma 15.59.8: on the `j`-th cocone leg, the degreewise colimit comparison is the
canonical map from `G.obj j` into the colimit complex, evaluated at degree `k`. -/
private theorem colimit_degree_term_iso_hom_ι
    {I : Type v} [Category.{v} I] [IsFiltered I]
    (G : I ⥤ CochainComplex (ModuleCat.{v, u} R) ℤ) [HasColimit G] (k : ℤ) (j : I) :
    colimit.ι
        (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) k) j ≫
          (colimit_degree_term_iso (R := R) (G := G) k).hom =
      (colimit.ι G j).f k := by
  let e :
      (colimit G).X k ≅
        colimit (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) k) :=
    (colimit_degree_term_isColimit (R := R) (G := G) k).coconePointUniqueUpToIso
      (colimit.isColimit
        (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) k))
  have h :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit_degree_term_isColimit (R := R) (G := G) k)
      (colimit.isColimit
        (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) k)) j
  -- Compose the cocone-leg formula with the inverse comparison to recover the desired direction.
  simpa [colimit_degree_term_iso, colimit_degree_term_cocone, e] using
    (congrArg (fun f ↦ f ≫ e.inv) h).symm

/-- Helper for Lemma 15.59.8: the degreewise colimit comparison intertwines
`colim.map (prev_d_natTrans G n)` with the differential of the colimit complex. -/
private theorem colimit_degree_term_iso_prev_comm
    {I : Type v} [Category.{v} I] [IsFiltered I]
    (G : I ⥤ CochainComplex (ModuleCat.{v, u} R) ℤ) [HasColimit G] (n : ℤ) :
    (colimit_degree_term_iso (R := R) (G := G) (n - 1)).hom ≫ (colimit G).d (n - 1) n =
      colim.map (prev_d_natTrans (G := G) n) ≫
        (colimit_degree_term_iso (R := R) (G := G) n).hom := by
  -- Compare both morphisms after precomposing with each cocone leg of the source colimit.
  apply colimit.hom_ext
  intro j
  have h1 :
      colimit.ι (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) (n - 1)) j ≫
          (colimit_degree_term_iso (R := R) (G := G) (n - 1)).hom ≫ (colimit G).d (n - 1) n =
        (colimit.ι G j).f (n - 1) ≫ (colimit G).d (n - 1) n := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦ k ≫ (colimit G).d (n - 1) n)
        (colimit_degree_term_iso_hom_ι (R := R) (G := G) (n - 1) j)
  have h2 :
      (colimit.ι G j).f (n - 1) ≫ (colimit G).d (n - 1) n =
        (G.obj j).d (n - 1) n ≫ (colimit.ι G j).f n := by
    simpa using (colimit.ι G j).comm (n - 1) n
  have h3 :
      (G.obj j).d (n - 1) n ≫ (colimit.ι G j).f n =
        (prev_d_natTrans (G := G) n).app j ≫
          (colimit.ι (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) n) j ≫
            (colimit_degree_term_iso (R := R) (G := G) n).hom) := by
    simpa [prev_d_natTrans, Category.assoc] using
      (congrArg
        (fun k ↦ (prev_d_natTrans (G := G) n).app j ≫ k)
        (colimit_degree_term_iso_hom_ι (R := R) (G := G) n j)).symm
  have h4 :
      (prev_d_natTrans (G := G) n).app j ≫
          (colimit.ι (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) n) j ≫
            (colimit_degree_term_iso (R := R) (G := G) n).hom) =
        ((prev_d_natTrans (G := G) n).app j ≫
          colimit.ι (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) n) j) ≫
            (colimit_degree_term_iso (R := R) (G := G) n).hom := by
    simp [Category.assoc]
  have h5 :
      ((prev_d_natTrans (G := G) n).app j ≫
          colimit.ι (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) n) j) ≫
            (colimit_degree_term_iso (R := R) (G := G) n).hom =
        (colimit.ι
            (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) (n - 1)) j ≫
          colim.map (prev_d_natTrans (G := G) n)) ≫
            (colimit_degree_term_iso (R := R) (G := G) n).hom := by
    rw [colimit.ι_map]
    simp [Category.assoc]
  have h6 :
      (colimit.ι
          (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) (n - 1)) j ≫
        colim.map (prev_d_natTrans (G := G) n)) ≫
          (colimit_degree_term_iso (R := R) (G := G) n).hom =
        colimit.ι
          (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) (n - 1)) j ≫
          (colim.map (prev_d_natTrans (G := G) n) ≫
            (colimit_degree_term_iso (R := R) (G := G) n).hom) := by
    simp [Category.assoc]
  exact h1.trans <| h2.trans <| h3.trans <| h4.trans <| h5.trans h6

/-- Helper for Lemma 15.59.8: the degreewise colimit comparison intertwines
`colim.map (next_d_natTrans G n)` with the next differential of the colimit complex. -/
private theorem colimit_degree_term_iso_next_comm
    {I : Type v} [Category.{v} I] [IsFiltered I]
    (G : I ⥤ CochainComplex (ModuleCat.{v, u} R) ℤ) [HasColimit G] (n : ℤ) :
    (colimit_degree_term_iso (R := R) (G := G) n).hom ≫ (colimit G).d n (n + 1) =
      colim.map (next_d_natTrans (G := G) n) ≫
        (colimit_degree_term_iso (R := R) (G := G) (n + 1)).hom := by
  -- The same cocone-leg calculation identifies the next differential after passing to colimits.
  apply colimit.hom_ext
  intro j
  have h1 :
      colimit.ι (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) n) j ≫
          (colimit_degree_term_iso (R := R) (G := G) n).hom ≫ (colimit G).d n (n + 1) =
        (colimit.ι G j).f n ≫ (colimit G).d n (n + 1) := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦ k ≫ (colimit G).d n (n + 1))
        (colimit_degree_term_iso_hom_ι (R := R) (G := G) n j)
  have h2 :
      (colimit.ι G j).f n ≫ (colimit G).d n (n + 1) =
        (G.obj j).d n (n + 1) ≫ (colimit.ι G j).f (n + 1) := by
    simpa using (colimit.ι G j).comm n (n + 1)
  have h3 :
      (G.obj j).d n (n + 1) ≫ (colimit.ι G j).f (n + 1) =
        (next_d_natTrans (G := G) n).app j ≫
          (colimit.ι
              (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) (n + 1)) j ≫
            (colimit_degree_term_iso (R := R) (G := G) (n + 1)).hom) := by
    simpa [next_d_natTrans, Category.assoc] using
      (congrArg
        (fun k ↦ (next_d_natTrans (G := G) n).app j ≫ k)
        (colimit_degree_term_iso_hom_ι (R := R) (G := G) (n + 1) j)).symm
  have h4 :
      (next_d_natTrans (G := G) n).app j ≫
          (colimit.ι
              (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) (n + 1)) j ≫
            (colimit_degree_term_iso (R := R) (G := G) (n + 1)).hom) =
        ((next_d_natTrans (G := G) n).app j ≫
          colimit.ι (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) (n + 1)) j) ≫
            (colimit_degree_term_iso (R := R) (G := G) (n + 1)).hom := by
    simp [Category.assoc]
  have h5 :
      ((next_d_natTrans (G := G) n).app j ≫
          colimit.ι (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) (n + 1)) j) ≫
            (colimit_degree_term_iso (R := R) (G := G) (n + 1)).hom =
        (colimit.ι
            (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) n) j ≫
          colim.map (next_d_natTrans (G := G) n)) ≫
            (colimit_degree_term_iso (R := R) (G := G) (n + 1)).hom := by
    rw [colimit.ι_map]
    simp [Category.assoc]
  have h6 :
      (colimit.ι
          (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) n) j ≫
        colim.map (next_d_natTrans (G := G) n)) ≫
          (colimit_degree_term_iso (R := R) (G := G) (n + 1)).hom =
        colimit.ι
          (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) n) j ≫
          (colim.map (next_d_natTrans (G := G) n) ≫
            (colimit_degree_term_iso (R := R) (G := G) (n + 1)).hom) := by
    simp [Category.assoc]
  exact h1.trans <| h2.trans <| h3.trans <| h4.trans <| h5.trans h6

/-- Helper for Lemma 15.59.8: the canonical colimit short complex of `degree_shortComplex G n`
identifies with the degree-`n` short complex of the colimit complex. -/
private noncomputable def colimit_degree_shortComplex_iso
    {I : Type v} [Category.{v} I] [IsFiltered I]
    (G : I ⥤ CochainComplex (ModuleCat.{v, u} R) ℤ) [HasColimit G] (n : ℤ) :
    colim.mapShortComplex (degree_shortComplex (G := G) n)
      (colimit.isColimit _)
      (colimit.cocone _)
      (colimit.cocone _)
      (colim.map (prev_d_natTrans (G := G) n))
      (colim.map (next_d_natTrans (G := G) n))
      (degree_shortComplex_colimit_map_prev (G := G) n)
      (degree_shortComplex_colimit_map_next (G := G) n) ≅
        (colimit G).sc n :=
  -- Assemble the three degreewise colimit comparisons into a short-complex isomorphism.
  (ShortComplex.isoMk
      (colimit_degree_term_iso (R := R) (G := G) (n - 1))
      (colimit_degree_term_iso (R := R) (G := G) n)
      (colimit_degree_term_iso (R := R) (G := G) (n + 1))
      (colimit_degree_term_iso_prev_comm (R := R) (G := G) n)
      (colimit_degree_term_iso_next_comm (R := R) (G := G) n)) ≪≫
    ((colimit G).isoSc' (i := n - 1) (j := n) (k := n + 1)
      (CochainComplex.prev ℤ n) (CochainComplex.next ℤ n)).symm

/-- Helper for Lemma 15.59.8: exactness of a filtered short-complex diagram of `R`-modules
descends to the short complex obtained by taking colimits termwise. -/
private theorem colimit_mapShortComplex_exact_of_isFiltered
    {I : Type v} [SmallCategory I] [IsFiltered I]
    (S : ShortComplex (I ⥤ ModuleCat.{v, u} R)) (hS : S.Exact) :
    (colim.mapShortComplex S
      (colimit.isColimit S.X₁)
      (colimit.cocone S.X₂)
      (colimit.cocone S.X₃)
      (colim.map S.f)
      (colim.map S.g)
      (fun j ↦ by simp)
      (fun j ↦ by simp)).Exact := by
  let _ : HasExactColimitsOfShape I (ModuleCat.{v, u} R) :=
    moduleCat_filtered_exact_colimits (R := R) (I := I)
  have hf :
      ∀ j : I,
        colimit.ι S.X₁ j ≫ colim.map S.f = S.f.app j ≫ colimit.ι S.X₂ j := by
    intro j
    simpa using (colimit.ι_map S.f j)
  have hg :
      ∀ j : I,
        colimit.ι S.X₂ j ≫ colim.map S.g = S.g.app j ≫ colimit.ι S.X₃ j := by
    intro j
    simpa using (colimit.ι_map S.g j)
  -- Once filtered exactness is installed on `ModuleCat R`, the canonical colimit short complex
  -- is exact by the generic `colim.exact_mapShortComplex` theorem.
  exact Limits.colim.exact_mapShortComplex hS
    (colimit.isColimit S.X₁)
    (colimit.isColimit S.X₂)
    (colimit.isColimit S.X₃)
    (colim.map S.f)
    (colim.map S.g)
    hf
    hg

/-- Helper for Lemma 15.59.8: a filtered colimit of acyclic cochain complexes of `R`-modules is
acyclic. -/
lemma acyclic_colimit_of_isFiltered
    {I : Type v} [Category.{v} I] [IsFiltered I]
    (G : I ⥤ CochainComplex (ModuleCat.{v, u} R) ℤ)
    [HasColimit G]
    (hG : ∀ i : I, (G.obj i).Acyclic) :
    (colimit G).Acyclic := by
  let _ : SmallCategory I := inferInstance
  let _ : HasColimitsOfShape I (ModuleCat.{v, u} R) := ModuleCat.hasColimitsOfShape R I
  -- Prove acyclicity degreewise by exactness of the canonical degree-`n` short complexes.
  rw [HomologicalComplex.acyclic_iff]
  intro n
  have hExactSource :=
    colimit_mapShortComplex_exact_of_isFiltered (R := R) (I := I)
      (degree_shortComplex (G := G) n)
      (degree_shortComplex_exact (G := G) hG n)
  have hExactTarget : ((colimit G).sc n).Exact := by
    -- Transport exactness across the canonical identification of the colimit short complex.
    exact (ShortComplex.exact_iff_of_iso
      (colimit_degree_shortComplex_iso (R := R) (G := G) n)).mp hExactSource
  exact (HomologicalComplex.exactAt_iff (colimit G) n).mpr hExactTarget

/-- Helper for Lemma 15.59.8: filtered-colimit acyclicity can be invoked directly for diagrams
valued in the concrete owner `ModuleCat R`. -/
private theorem acyclic_colimit_of_isFiltered_concrete
    {I : Type v} [Category.{v} I] [IsFiltered I]
    (G : I ⥤ CochainComplex (ModuleCat R) ℤ)
    [HasColimit G]
    (hG : ∀ i : I, (G.obj i).Acyclic) :
    (colimit G).Acyclic := by
  -- TODO: the concrete replay of `acyclic_colimit_of_isFiltered` still needs a stable universe
  -- normalization for the native owner `ModuleCat R`; the direct `HasExactColimitsOfShape` and
  -- `degree_shortComplex` surfaces elaborate with incompatible hidden universes.
  sorry

/-- Helper for Lemma 15.59.8: after tensoring an acyclic test complex with a filtered diagram of
K-flat complexes, every stage of the tensorized diagram is acyclic. -/
private theorem tensorized_stage_acyclic
    {I : Type v} [Category.{v} I]
    {M : CochainComplex (ModuleCat R) ℤ}
    (hM : M.Acyclic)
    (F : I ⥤ CochainComplex (ModuleCat R) ℤ)
    (hF : ∀ i : I, (F.obj i).IsKFlat) :
    ∀ i : I, (HomologicalComplex.tensorObj M (F.obj i)).Acyclic := by
  intro i
  -- Each stage is acyclic because the source hypothesis says tensoring by `F.obj i` preserves
  -- acyclic complexes.
  exact CochainComplex.acyclic_tensorObj_of_isKFlat (hF i) hM

/-- Helper for Lemma 15.59.8: tensoring on the left by a fixed complex preserves identity maps in
the right factor. -/
private theorem tensorHom_id_right
    (M K : CochainComplex (ModuleCat R) ℤ) :
    HomologicalComplex.tensorHom (𝟙 M) (𝟙 K) = 𝟙 (HomologicalComplex.tensorObj M K) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simpa [HomologicalComplex.ιTensorObj, HomologicalComplex.tensorHom, HomologicalComplex.id_f] using
    (HomologicalComplex.ι_mapBifunctorMap
      (K₁ := M) (K₂ := K) (L₁ := M) (L₂ := K)
      (f₁ := 𝟙 M) (f₂ := 𝟙 K) (F := curriedTensor (ModuleCat R))
      (c := ComplexShape.up ℤ) p q n h)

/-- Helper for Lemma 15.59.8: tensoring on the left by a fixed complex preserves compositions in
the right factor. -/
private theorem tensorHom_comp_right
    (M : CochainComplex (ModuleCat R) ℤ)
    {K L P : CochainComplex (ModuleCat R) ℤ}
    (f : K ⟶ L) (g : L ⟶ P) :
    HomologicalComplex.tensorHom (𝟙 M) (f ≫ g) =
      HomologicalComplex.tensorHom (𝟙 M) f ≫ HomologicalComplex.tensorHom (𝟙 M) g := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have hfg :
      HomologicalComplex.ιTensorObj M K p q n h ≫
          (HomologicalComplex.tensorHom (𝟙 M) (f ≫ g)).f n =
        (M.X p ◁ ((f ≫ g).f q)) ≫ HomologicalComplex.ιTensorObj M P p q n h := by
    simpa [HomologicalComplex.ιTensorObj, HomologicalComplex.tensorHom,
      HomologicalComplex.id_f] using
      (HomologicalComplex.ι_mapBifunctorMap
        (K₁ := M) (K₂ := K) (L₁ := M) (L₂ := P)
        (f₁ := 𝟙 M) (f₂ := f ≫ g) (F := curriedTensor (ModuleCat R))
        (c := ComplexShape.up ℤ) p q n h)
  have hf :
      HomologicalComplex.ιTensorObj M K p q n h ≫
          (HomologicalComplex.tensorHom (𝟙 M) f).f n =
        (M.X p ◁ f.f q) ≫ HomologicalComplex.ιTensorObj M L p q n h := by
    simpa [HomologicalComplex.ιTensorObj, HomologicalComplex.tensorHom,
      HomologicalComplex.id_f] using
      (HomologicalComplex.ι_mapBifunctorMap
        (K₁ := M) (K₂ := K) (L₁ := M) (L₂ := L)
        (f₁ := 𝟙 M) (f₂ := f) (F := curriedTensor (ModuleCat R))
        (c := ComplexShape.up ℤ) p q n h)
  have hg :
      HomologicalComplex.ιTensorObj M L p q n h ≫
          (HomologicalComplex.tensorHom (𝟙 M) g).f n =
        (M.X p ◁ g.f q) ≫ HomologicalComplex.ιTensorObj M P p q n h := by
    simpa [HomologicalComplex.ιTensorObj, HomologicalComplex.tensorHom,
      HomologicalComplex.id_f] using
      (HomologicalComplex.ι_mapBifunctorMap
        (K₁ := M) (K₂ := L) (L₁ := M) (L₂ := P)
        (f₁ := 𝟙 M) (f₂ := g) (F := curriedTensor (ModuleCat R))
        (c := ComplexShape.up ℤ) p q n h)
  calc
    HomologicalComplex.ιTensorObj M K p q n h ≫
        (HomologicalComplex.tensorHom (𝟙 M) (f ≫ g)).f n
      = (M.X p ◁ ((f ≫ g).f q)) ≫ HomologicalComplex.ιTensorObj M P p q n h := hfg
    _ = (M.X p ◁ (f.f q ≫ g.f q)) ≫ HomologicalComplex.ιTensorObj M P p q n h := by
          simp [HomologicalComplex.comp_f]
    _ = ((M.X p ◁ f.f q) ≫ (M.X p ◁ g.f q)) ≫ HomologicalComplex.ιTensorObj M P p q n h := by
          rw [← whiskerLeft_comp]
    _ = (M.X p ◁ f.f q) ≫ ((M.X p ◁ g.f q) ≫ HomologicalComplex.ιTensorObj M P p q n h) := by
          simp [Category.assoc]
    _ = (M.X p ◁ f.f q) ≫
          (HomologicalComplex.ιTensorObj M L p q n h ≫
            (HomologicalComplex.tensorHom (𝟙 M) g).f n) := by
          rw [← hg]
    _ = (HomologicalComplex.ιTensorObj M K p q n h ≫
          (HomologicalComplex.tensorHom (𝟙 M) f).f n) ≫
            (HomologicalComplex.tensorHom (𝟙 M) g).f n := by
          rw [hf]
          simp [Category.assoc]
    _ = HomologicalComplex.ιTensorObj M K p q n h ≫
          ((HomologicalComplex.tensorHom (𝟙 M) f ≫
            HomologicalComplex.tensorHom (𝟙 M) g).f n) := by
          simp [HomologicalComplex.comp_f, Category.assoc]

/-- Helper for Lemma 15.59.8: the explicit filtered diagram obtained by tensoring every stage of
`F` on the left with the fixed acyclic test complex `M`. -/
private noncomputable def tensorized_filtered_diagram
    {I : Type v} [Category.{v} I]
    (M : CochainComplex (ModuleCat R) ℤ)
    (F : I ⥤ CochainComplex (ModuleCat R) ℤ) :
    I ⥤ CochainComplex (ModuleCat R) ℤ :=
  F ⋙ MonoidalCategory.tensorLeft M

/-- Helper for Lemma 15.59.8: the canonical cocone from the explicit tensorized filtered diagram
to the tensor product with the colimit complex. -/
private noncomputable def tensorized_filtered_cocone
    {I : Type v} [Category.{v} I]
    (M : CochainComplex (ModuleCat R) ℤ)
    (F : I ⥤ CochainComplex (ModuleCat R) ℤ) [HasColimit F] :
    Cocone (tensorized_filtered_diagram (R := R) M F) :=
  (MonoidalCategory.tensorLeft M).mapCocone (colimit.cocone F)

/-- Helper for Lemma 15.59.8: tensoring the degree-`q` colimit cocone on the left by `M.X p`
gives the canonical cocone on the `(p,q)`-summand system. -/
private noncomputable def tensorized_filtered_summand_cocone
    {I : Type v} [Category.{v} I]
    (M : CochainComplex (ModuleCat R) ℤ)
    (F : I ⥤ CochainComplex (ModuleCat R) ℤ) [HasColimit F]
    (p q : ℤ) :
    Cocone
      (((F ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) q) ⋙
        MonoidalCategory.tensorLeft (M.X p))) :=
  (MonoidalCategory.tensorLeft (M.X p)).mapCocone
    ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) q).mapCocone (colimit.cocone F))

/-- Helper for Lemma 15.59.8: the `(p,q)`-summand cocone is colimiting because left tensoring by
`M.X p` preserves colimits of module diagrams. -/
private noncomputable def tensorized_filtered_summand_isColimit
    {I : Type v} [Category.{v} I] [IsFiltered I]
    (M : CochainComplex (ModuleCat R) ℤ)
    (F : I ⥤ CochainComplex (ModuleCat R) ℤ) [HasColimit F]
    (p q : ℤ) :
    IsColimit (tensorized_filtered_summand_cocone (R := R) (M := M) (F := F) p q) := by
  -- TODO: the native-owner proof of termwise tensor-colimit commutation still needs a single
  -- universe-stable owner for `F ⋙ eval q` and `tensorLeft (M.X p)`; the direct concrete proof
  -- hits the same hidden-universe mismatch as the acyclicity replay.
  sorry

/-- Helper for Lemma 15.59.8: on each `(p,q)` summand, the map induced by a morphism in the
tensorized filtered diagram is the expected whiskered degree map. -/
@[reassoc]
private theorem tensorized_filtered_diagram_map_comp_ιTensorObj
    {I : Type v} [Category.{v} I]
    (M : CochainComplex (ModuleCat R) ℤ)
    (F : I ⥤ CochainComplex (ModuleCat R) ℤ)
    {i j : I} (f : i ⟶ j) (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫
        ((tensorized_filtered_diagram (R := R) M F).map f).f n =
      (M.X p ◁ (F.map f).f q) ≫ HomologicalComplex.ιTensorObj M (F.obj j) p q n h := by
  -- This is the canonical `ι_mapBifunctorMap` formula for the fixed-left tensor functor.
  simpa [tensorized_filtered_diagram, HomologicalComplex.ιTensorObj] using
    (HomologicalComplex.ι_mapBifunctorMap
      (K₁ := M) (K₂ := F.obj i) (L₁ := M) (L₂ := F.obj j)
      (f₁ := 𝟙 M) (f₂ := F.map f) (F := curriedTensor (ModuleCat R))
      (c := ComplexShape.up ℤ) p q n h)

/-- Helper for Lemma 15.59.8: on each `(p,q)` summand, the `i`-th leg of the explicit tensorized
cocone is given by whiskering the degree-`q` colimit map and then including that summand. -/
@[reassoc]
private theorem tensorized_filtered_cocone_leg_comp_ιTensorObj
    {I : Type v} [Category.{v} I]
    (M : CochainComplex (ModuleCat R) ℤ)
    (F : I ⥤ CochainComplex (ModuleCat R) ℤ) [HasColimit F]
    (i : I) (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫
        ((tensorized_filtered_cocone (R := R) M F).ι.app i).f n =
      (M.X p ◁ (colimit.ι F i).f q) ≫ HomologicalComplex.ιTensorObj M (colimit F) p q n h := by
  -- This is the same summand formula specialized to the cocone leg `colimit.ι F i`.
  simpa [tensorized_filtered_cocone, HomologicalComplex.ιTensorObj] using
    (HomologicalComplex.ι_mapBifunctorMap
      (K₁ := M) (K₂ := F.obj i) (L₁ := M) (L₂ := colimit F)
      (f₁ := 𝟙 M) (f₂ := colimit.ι F i) (F := curriedTensor (ModuleCat R))
      (c := ComplexShape.up ℤ) p q n h)

/-- Helper for Lemma 15.59.8: a cocone over the evaluated tensorized diagram induces, for each
`(p,q)` summand of total degree `n`, a cocone over the corresponding tensorized degree system. -/
private theorem tensorized_filtered_branch_cocone_naturality
    {I : Type v} [Category.{v} I]
    (M : CochainComplex (ModuleCat R) ℤ)
    (F : I ⥤ CochainComplex (ModuleCat R) ℤ)
    (n : ℤ)
    (s : Cocone
      ((tensorized_filtered_diagram (R := R) M F) ⋙
        HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n))
    (p q : ℤ) (h : p + q = n) :
    ∀ ⦃i j : I⦄ (f : i ⟶ j),
      (((F ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) q) ⋙
          MonoidalCategory.tensorLeft (M.X p)).map f) ≫
          (HomologicalComplex.ιTensorObj M (F.obj j) p q n h ≫ s.ι.app j) =
        HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫ s.ι.app i := by
  intro i j f
  -- Rewrite the branch map as the degree-`n` tensorized diagram map, then use cocone naturality.
  have hmap :
      (((F ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) q) ⋙
          MonoidalCategory.tensorLeft (M.X p)).map f) ≫
          (HomologicalComplex.ιTensorObj M (F.obj j) p q n h ≫ s.ι.app j) =
        HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫
          (((tensorized_filtered_diagram (R := R) M F).map f).f n ≫ s.ι.app j) := by
    simpa [tensorized_filtered_diagram, Functor.comp_map, Category.assoc] using
      congrArg (fun k ↦ k ≫ s.ι.app j)
        (tensorized_filtered_diagram_map_comp_ιTensorObj
          (R := R) M F f p q n h).symm
  have hs :
      HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫
          (((tensorized_filtered_diagram (R := R) M F).map f).f n ≫ s.ι.app j) =
        HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫ s.ι.app i := by
    simpa [tensorized_filtered_diagram, Functor.comp_map, Category.assoc] using
      congrArg (fun k ↦ HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫ k) (s.w f)
  exact hmap.trans hs

/-- Helper for Lemma 15.59.8: the branch maps coming from an evaluated cocone assemble to a cocone
on the `(p,q)` summand diagram. -/
private def tensorized_filtered_branch_cocone
    {I : Type v} [Category.{v} I]
    (M : CochainComplex (ModuleCat R) ℤ)
    (F : I ⥤ CochainComplex (ModuleCat R) ℤ)
    (n : ℤ)
    (s : Cocone
      ((tensorized_filtered_diagram (R := R) M F) ⋙
        HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n))
    (p q : ℤ) (h : p + q = n) :
    Cocone
      (((F ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) q) ⋙
        MonoidalCategory.tensorLeft (M.X p))) where
  pt := s.pt
  ι.app i := HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫ s.ι.app i
  ι.naturality := tensorized_filtered_branch_cocone_naturality
    (R := R) M F n s p q h

/-- Helper for Lemma 15.59.8: after evaluation at degree `n`, the explicit tensorized cocone is
colimiting. -/
private noncomputable def tensorized_filtered_eval_desc
    {I : Type v} [Category.{v} I] [IsFiltered I]
    (M : CochainComplex (ModuleCat R) ℤ)
    (F : I ⥤ CochainComplex (ModuleCat R) ℤ) [HasColimit F]
    (n : ℤ)
    (s : Cocone
      ((tensorized_filtered_diagram (R := R) M F) ⋙
        HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n)) :
    (HomologicalComplex.tensorObj M (colimit F)).X n ⟶ s.pt :=
  -- Descend each `(p,q)` summand through its filtered colimit, then reassemble the branches.
  HomologicalComplex.mapBifunctorDesc
    (fun p q h ↦
      (tensorized_filtered_summand_isColimit (R := R) M F p q).desc
        (tensorized_filtered_branch_cocone (R := R) M F n s p q h))

/-- Helper for Lemma 15.59.8: restricting `tensorized_filtered_eval_desc` to one `(p,q)` summand
recovers the descended map from the corresponding summand colimit cocone. -/
@[reassoc]
private theorem iTensorObj_tensorized_filtered_eval_desc_assoc
    {I : Type v} [Category.{v} I] [IsFiltered I]
    (M : CochainComplex (ModuleCat R) ℤ)
    (F : I ⥤ CochainComplex (ModuleCat R) ℤ) [HasColimit F]
    (n : ℤ)
    (s : Cocone
      ((tensorized_filtered_diagram (R := R) M F) ⋙
        HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n))
    (p q : ℤ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj M (colimit F) p q n h ≫
        tensorized_filtered_eval_desc (R := R) M F n s =
      (tensorized_filtered_summand_isColimit (R := R) M F p q).desc
        (tensorized_filtered_branch_cocone (R := R) M F n s p q h) := by
  -- Evaluate `mapBifunctorDesc` once and isolate the chosen summand via `ι_mapBifunctorDesc`.
  simpa [tensorized_filtered_eval_desc, HomologicalComplex.ιTensorObj] using
    (HomologicalComplex.ι_mapBifunctorDesc
      (K₁ := M) (K₂ := colimit F) (F := curriedTensor (ModuleCat R))
      (c := ComplexShape.up ℤ) (A := s.pt) (j := n)
      (f := fun p q h ↦
        (tensorized_filtered_summand_isColimit (R := R) M F p q).desc
          (tensorized_filtered_branch_cocone (R := R) M F n s p q h))
      p q h)

/-- Helper for Lemma 15.59.8: the branchwise descender from the tensorized summand colimits
commutes with each cocone leg after evaluation in degree `n`. -/
private theorem tensorized_filtered_eval_desc_fac
    {I : Type v} [Category.{v} I] [IsFiltered I]
    (M : CochainComplex (ModuleCat R) ℤ)
    (F : I ⥤ CochainComplex (ModuleCat R) ℤ) [HasColimit F]
    (n : ℤ)
    (s : Cocone
      ((tensorized_filtered_diagram (R := R) M F) ⋙
        HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n))
    (i : I) :
    ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n).mapCocone
        (tensorized_filtered_cocone (R := R) M F)).ι.app i ≫
        tensorized_filtered_eval_desc (R := R) M F n s =
      s.ι.app i := by
  -- It is enough to test after precomposing with each summand inclusion `ιTensorObj`.
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have hleg :
      HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫
          (((HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n).mapCocone
            (tensorized_filtered_cocone (R := R) M F)).ι.app i ≫
              tensorized_filtered_eval_desc (R := R) M F n s) =
        (M.X p ◁ (colimit.ι F i).f q) ≫
          (HomologicalComplex.ιTensorObj M (colimit F) p q n h ≫
            tensorized_filtered_eval_desc (R := R) M F n s) := by
    simpa [Category.assoc] using
      congrArg (fun k ↦ k ≫ tensorized_filtered_eval_desc (R := R) M F n s)
        (tensorized_filtered_cocone_leg_comp_ιTensorObj (R := R) M F i p q n h)
  have hdesc :
      (M.X p ◁ (colimit.ι F i).f q) ≫
          (HomologicalComplex.ιTensorObj M (colimit F) p q n h ≫
            tensorized_filtered_eval_desc (R := R) M F n s) =
        (M.X p ◁ (colimit.ι F i).f q) ≫
          (tensorized_filtered_summand_isColimit (R := R) M F p q).desc
            (tensorized_filtered_branch_cocone (R := R) M F n s p q h) := by
    simpa [Category.assoc] using
      congrArg (fun k ↦ (M.X p ◁ (colimit.ι F i).f q) ≫ k)
        (iTensorObj_tensorized_filtered_eval_desc_assoc
          (R := R) M F n s p q h)
  have hfac :
      (M.X p ◁ (colimit.ι F i).f q) ≫
          (tensorized_filtered_summand_isColimit (R := R) M F p q).desc
            (tensorized_filtered_branch_cocone (R := R) M F n s p q h) =
        HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫ s.ι.app i := by
    -- The descended branch map satisfies the cocone-leg equation for the `(p,q)` summand system.
    simpa [tensorized_filtered_summand_cocone, tensorized_filtered_branch_cocone,
      Category.assoc] using
      (tensorized_filtered_summand_isColimit (R := R) M F p q).fac
        (tensorized_filtered_branch_cocone (R := R) M F n s p q h) i
  exact hleg.trans (hdesc.trans hfac)

/-- Helper for Lemma 15.59.8: the branchwise descender on the evaluated tensorized cocone is the
unique morphism compatible with all cocone legs. -/
private theorem tensorized_filtered_eval_desc_uniq
    {I : Type v} [Category.{v} I] [IsFiltered I]
    (M : CochainComplex (ModuleCat R) ℤ)
    (F : I ⥤ CochainComplex (ModuleCat R) ℤ) [HasColimit F]
    (n : ℤ)
    (s : Cocone
      ((tensorized_filtered_diagram (R := R) M F) ⋙
        HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n))
    (m : ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n).mapCocone
        (tensorized_filtered_cocone (R := R) M F)).pt ⟶ s.pt)
    (hm : ∀ i : I,
      ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n).mapCocone
          (tensorized_filtered_cocone (R := R) M F)).ι.app i ≫ m =
        s.ι.app i) :
    m = tensorized_filtered_eval_desc (R := R) M F n s := by
  -- Two maps from the tensor degree agree once they agree on every `(p,q)` summand.
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have hbranch :
      ∀ i : I,
        (tensorized_filtered_summand_cocone (R := R) (M := M) (F := F) p q).ι.app i ≫
            (HomologicalComplex.ιTensorObj M (colimit F) p q n h ≫ m) =
          (tensorized_filtered_branch_cocone (R := R) M F n s p q h).ι.app i := by
    intro i
    -- Normalize the summand leg through the ambient tensorized cocone, then use the hypothesis
    -- that `m` is cocone-compatible with the evaluated tensorized diagram.
    have hleg :
        (tensorized_filtered_summand_cocone (R := R) (M := M) (F := F) p q).ι.app i ≫
            (HomologicalComplex.ιTensorObj M (colimit F) p q n h ≫ m) =
          HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫
            (((HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n).mapCocone
              (tensorized_filtered_cocone (R := R) M F)).ι.app i ≫ m) := by
      simpa [tensorized_filtered_summand_cocone, Category.assoc] using
        congrArg (fun k ↦ k ≫ m)
          (tensorized_filtered_cocone_leg_comp_ιTensorObj
            (R := R) M F i p q n h).symm
    have hm' :
        HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫
            (((HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n).mapCocone
              (tensorized_filtered_cocone (R := R) M F)).ι.app i ≫ m) =
          HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫ s.ι.app i := by
      simpa [Category.assoc] using
        congrArg (fun k ↦ HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫ k) (hm i)
    have hbranchLeg :
        HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫ s.ι.app i =
          (tensorized_filtered_branch_cocone (R := R) M F n s p q h).ι.app i := by
      rfl
    exact hleg.trans (hm'.trans hbranchLeg)
  have hdesc :
      HomologicalComplex.ιTensorObj M (colimit F) p q n h ≫ m =
        (tensorized_filtered_summand_isColimit (R := R) M F p q).desc
          (tensorized_filtered_branch_cocone (R := R) M F n s p q h) := by
    exact (tensorized_filtered_summand_isColimit (R := R) M F p q).uniq
      (tensorized_filtered_branch_cocone (R := R) M F n s p q h)
      (HomologicalComplex.ιTensorObj M (colimit F) p q n h ≫ m)
      hbranch
  exact hdesc.trans (iTensorObj_tensorized_filtered_eval_desc_assoc
    (R := R) M F n s p q h).symm

/-- Helper for Lemma 15.59.8: after evaluation at degree `n`, the explicit tensorized cocone is
colimiting. -/
private noncomputable def tensorized_filtered_eval_isColimit
    {I : Type v} [Category.{v} I] [IsFiltered I]
    (M : CochainComplex (ModuleCat R) ℤ)
    (F : I ⥤ CochainComplex (ModuleCat R) ℤ) [HasColimit F]
    (n : ℤ) :
    IsColimit
      ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n).mapCocone
        (tensorized_filtered_cocone (R := R) M F)) :=
  -- Package the explicit descender together with its branchwise `fac` and `uniq` proofs.
  { desc := tensorized_filtered_eval_desc (R := R) M F n
    fac := tensorized_filtered_eval_desc_fac (R := R) M F n
    uniq := tensorized_filtered_eval_desc_uniq (R := R) M F n }

/-- Helper for Lemma 15.59.8: the explicit tensorized cocone should be colimiting. -/
private noncomputable def tensorized_filtered_isColimit
    {I : Type v} [Category.{v} I] [IsFiltered I]
    (M : CochainComplex (ModuleCat R) ℤ)
    (F : I ⥤ CochainComplex (ModuleCat R) ℤ) [HasColimit F] :
    IsColimit (tensorized_filtered_cocone (R := R) M F) := by
  -- The source proof is degreewise, and the evaluation functors jointly reflect colimits.
  refine HomologicalComplex.isColimitOfEval
    (F := tensorized_filtered_diagram (R := R) M F)
    (s := tensorized_filtered_cocone (R := R) M F) ?_
  intro n
  exact tensorized_filtered_eval_isColimit (R := R) M F n

/-- Helper for Lemma 15.59.8: once the explicit tensorized cocone is known to be colimiting, the
colimit of the tensorized filtered diagram identifies with `M ⊗ colimit F`. -/
private noncomputable def tensorized_filtered_diagram_colimit_iso
    {I : Type v} [Category.{v} I] [IsFiltered I]
    (M : CochainComplex (ModuleCat R) ℤ)
    (F : I ⥤ CochainComplex (ModuleCat R) ℤ) [HasColimit F]
    [HasColimit (tensorized_filtered_diagram (R := R) M F)] :
    colimit (tensorized_filtered_diagram (R := R) M F) ≅
      HomologicalComplex.tensorObj M (colimit F) := by
  let hcolim := tensorized_filtered_isColimit (R := R) M F
  -- Compare the chosen colimit of the tensorized diagram with the explicit source cocone.
  exact (hcolim.coconePointUniqueUpToIso
    (colimit.isColimit (tensorized_filtered_diagram (R := R) M F))).symm

-- Proof sketch: let `M^•` be any acyclic complex. Tensoring with the filtered colimit identifies
-- `HomologicalComplex.tensorObj M (colimit F)` with the filtered colimit of the tensor products
-- `HomologicalComplex.tensorObj M (F.obj i)` by Lemma `10.12.9`, and each stage is acyclic by the
-- assumed K-flatness. Exactness of filtered colimits from Lemma `10.8.8` then gives acyclicity of
-- the colimit tensor complex.
/-- Lemma 15.59.8: any filtered colimit of K-flat cochain complexes of `R`-modules is K-flat.
Specializing to the preorder category `ℕ` recovers the sequential-colimit case. -/
theorem isKFlat_colimit_of_isFiltered
    {I : Type v} [Category.{v} I] [IsFiltered I]
    (F : I ⥤ CochainComplex (ModuleCat R) ℤ)
    [HasColimit F]
    (hF : ∀ i : I, (F.obj i).IsKFlat) :
    (colimit F).IsKFlat := by
  -- Route correction: follow the source proof on the explicit tensorized diagram instead of using
  -- an unavailable global `tensorLeft`-preserves-colimits owner on cochain complexes.
  -- Unfold K-flatness and run the source argument on the explicit filtered tensor diagram.
  rw [CochainComplex.isKFlat_iff]
  intro M _ hM
  let _ : HasColimit (tensorized_filtered_diagram (R := R) M F) :=
    HasColimit.mk ⟨tensorized_filtered_cocone (R := R) M F,
      tensorized_filtered_isColimit (R := R) M F⟩
  have hTensorStages :
      ∀ i : I, (HomologicalComplex.tensorObj M (F.obj i)).Acyclic :=
    tensorized_stage_acyclic (R := R) hM F hF
  have hTensorColim :
      (colimit (tensorized_filtered_diagram (R := R) M F)).Acyclic :=
    acyclic_colimit_of_isFiltered_concrete
      (R := R)
      (G := tensorized_filtered_diagram (R := R) M F)
      hTensorStages
  -- Transport the filtered-colimit acyclicity statement across the explicit comparison iso.
  exact
    acyclic_of_iso
      (tensorized_filtered_diagram_colimit_iso (R := R) M F)
      hTensorColim

end CochainComplex
