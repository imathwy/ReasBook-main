import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_21_42_1_Computing_cohomology (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v})]

-- Proof sketch: the example identifies the explicit complex attached to
-- `(GrothendieckTopology.pointBot U).skyscraperSheafFunctor.obj A` with the cochains of a
-- contractible simplicial set. The resulting chain homotopy makes the associated cohomology
-- groups vanish in every positive degree, which is exactly the acyclicity input used later in the
-- computation theorem.
/-- Point skyscraper sheaves for the chaotic topology are acyclic for positive global
cohomology. -/
theorem pointBot_skyscraperSheaf_H_isZero_of_pos
    [LocallySmall.{max u v} C]
    (U : C) (A : AddCommGrpCat.{max u v}) {n : ℕ} (hn : 0 < n) :
    IsZero
      (AddCommGrpCat.of
        (((GrothendieckTopology.pointBot U).skyscraperSheafFunctor.obj A).H n)) := sorry

-- Proof sketch: replace the explicit complex `K^•(F)` from the text by a chosen injective
-- resolution `I` of `F` in the abelian sheaf category for the chaotic topology. The global
-- sections complex `Γ(I^•)` computes the right derived functors of `Γ`, hence its degree-`n`
-- cohomology is canonically `H^n(C, F)`. The example's acyclicity argument for products of point
-- skyscraper sheaves explains why the ad hoc complex `K^•(F)` is another model for the same
-- derived functor computation.
/-- Example 21.42.1 (Computing cohomology): for an abelian sheaf `\mathcal F` on the chaotic site
associated to a category `\mathcal C`, the cohomology object `H^n(\mathcal C, \mathcal F)` is
computed by the degree-`n` cohomology of the global-sections complex of any injective resolution
of `\mathcal F`. This is the canonical injective-resolution form of the explicit cochain complex
`K^\bullet(\mathcal F)` constructed in the text. -/
theorem categoryCohomology_iso_homology_of_injectiveResolution
    (F : Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v})
    (I : InjectiveResolution F) (n : ℕ) :
    IsIsomorphic (AddCommGrpCat.of (F.H n))
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (ComplexShape.up ℕ) n).obj
        (((Sheaf.Γ (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex)) := sorry

end

end CategoryTheory

/-! ### Example_21_42_2_Computing_Exts (from Chap21) -/
open CategoryTheory

noncomputable section

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{u}}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]

-- Proof sketch: replace the explicit complex `K^\bullet(\mathcal G, \mathcal F)` from the text
-- by the canonical Hom complex from a projective resolution `P` of `\mathcal G` to the single
-- cochain complex concentrated in degree zero at `\mathcal F`. The standard projective-resolution
-- computation of `Ext` identifies `Ext^n_{\mathcal O}(\mathcal G, \mathcal F)` with
-- cohomology classes in that Hom complex, and `CochainComplex.HomComplex.homologyAddEquiv`
-- turns those classes into degree-`n` homology.
/-- Example 21.42.2 (Computing Exts): for `\mathcal O`-modules `\mathcal G` and `\mathcal F` on a
ringed site, the canonical projective-resolution computation of
`Ext^n_{\mathrm{Mod}(\mathcal O)}(\mathcal G, \mathcal F)` is the degree-`n` homology of the Hom
complex from a projective resolution of `\mathcal G` to the single-term complex on
`\mathcal F`. This is the library-facing replacement for the explicit complex
`K^\bullet(\mathcal G, \mathcal F)` used in the source under the objectwise-projective hypothesis
on `\mathcal G`. -/
theorem ext_isomorphic_homology_homComplex_of_projectiveResolution
    [Abelian (SheafOfModules (ringSheaf J 𝒪))]
    [HasExt (SheafOfModules (ringSheaf J 𝒪))]
    [HasProjectiveResolutions (SheafOfModules (ringSheaf J 𝒪))]
    (𝒢 ℱ : SheafOfModules (ringSheaf J 𝒪)) (P : ProjectiveResolution 𝒢) (n : ℕ) :
    IsIsomorphic
      (AddCommGrpCat.of (Abelian.Ext 𝒢 ℱ n))
      (AddCommGrpCat.of
        ((CochainComplex.HomComplex P.cochainComplex
          ((CochainComplex.singleFunctor (SheafOfModules (ringSheaf J 𝒪)) 0).obj ℱ)).homology
            n)) := sorry

-- Proof sketch: dually, resolve `\mathcal F` by an injective resolution `I` and replace the
-- source by the single cochain complex concentrated in degree zero at `\mathcal G`. The standard
-- injective-resolution computation identifies `Ext^n_{\mathcal O}(\mathcal G, \mathcal F)` with
-- cohomology classes in the Hom complex into `I`, and `homologyAddEquiv` converts those classes
-- into degree-`n` homology.
/-- The dual injective-resolution computation of `Ext^n_{\mathrm{Mod}(\mathcal O)}(\mathcal G,
\mathcal F)` as the degree-`n` homology of the Hom complex into an injective resolution of
`\mathcal F`. -/
theorem ext_isomorphic_homology_homComplex_of_injectiveResolution
    [Abelian (SheafOfModules (ringSheaf J 𝒪))]
    [HasExt (SheafOfModules (ringSheaf J 𝒪))]
    [HasInjectiveResolutions (SheafOfModules (ringSheaf J 𝒪))]
    (𝒢 ℱ : SheafOfModules (ringSheaf J 𝒪)) (I : InjectiveResolution ℱ) (n : ℕ) :
    IsIsomorphic
      (AddCommGrpCat.of (Abelian.Ext 𝒢 ℱ n))
      (AddCommGrpCat.of
        ((CochainComplex.HomComplex
          ((CochainComplex.singleFunctor (SheafOfModules (ringSheaf J 𝒪)) 0).obj 𝒢)
            I.cochainComplex).homology n)) := sorry

end

end SheafOfModules.RingedSite
