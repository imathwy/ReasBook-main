import Mathlib
import stacks_project.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

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
