import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import StacksProject_2024.Chap10.Definition_10_82_1

open CategoryTheory Limits MonoidalCategory
open LinearMap

universe u

namespace CategoryTheory
namespace ShortComplex

variable {R : Type u} [CommRing R]

namespace Splitting

-- Proof sketch: a splitting is preserved by the additive tensor functor `tensorLeft N`; applying
-- `ShortComplex.Splitting.shortExact` after tensoring gives short exactness for every `N`.
/-- A splitting of a short complex of `R`-modules makes it universally exact. -/
theorem universallyExact {S : ShortComplex (ModuleCat.{u} R)}
    (s : S.Splitting) : S.UniversallyExact := by
  refine ⟨s.shortExact, ?_⟩
  intro Q _ _
  let N : ModuleCat.{u} R := ModuleCat.of R Q
  -- Tensor the chosen splitting and read off injectivity from the tensorized split exact sequence.
  have hShortExact : (S.map (tensorLeft N)).ShortExact := (s.map (tensorLeft N)).shortExact
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
  simpa [N, ModuleCat.hom_whiskerLeft] using
    (ModuleCat.mono_iff_injective ((S.map (tensorLeft N)).f)).1 hShortExact.mono_f

end Splitting

variable {J : Type u} [Category.{u} J] [IsFiltered J]

omit [IsFiltered J] in
/-- Helper for Example 10.82.2: evaluation functors jointly reflect isomorphisms on a module-valued
functor category. -/
theorem evaluation_jointly_reflects_isomorphisms :
    JointlyReflectIsomorphisms (fun j : J ↦ (evaluation J (ModuleCat.{u} R)).obj j) := by
  refine ⟨?_⟩
  intro X Y f hf
  -- A natural transformation is an isomorphism exactly when all of its components are.
  rw [NatTrans.isIso_iff_isIso_app]
  intro j
  simpa using hf j

namespace UniversallyExact

/-- Helper for Example 10.82.2: tensoring a universally exact short complex on the left preserves
short exactness. -/
theorem tensorLeft_shortExact {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.UniversallyExact) (N : ModuleCat.{u} R) :
    (S.map (tensorLeft N)).ShortExact := by
  have hShortExact : S.ShortExact := hS.shortExact
  have hExact : Function.Exact S.f.hom S.g.hom := by
    simpa using (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hShortExact.exact
  have hSurj : Function.Surjective S.g.hom := hShortExact.moduleCat_surjective_g
  have hTensorExact : Function.Exact (S.f.hom.lTensor N) (S.g.hom.lTensor N) :=
    lTensor_exact N hExact hSurj
  -- Universal injectivity supplies the missing injectivity of the left tensor map.
  have hTensorInj : Function.Injective (S.f.hom.lTensor N) := by
    rw [LinearMap.lTensor_inj_iff_rTensor_inj]
    exact hS.universallyInjective_f N inferInstance inferInstance
  refine ModuleCat.shortComplex_shortExact (S.map (tensorLeft N)) ?_ ?_ ?_
  · simpa [ModuleCat.hom_whiskerLeft] using hTensorExact
  · simpa [ModuleCat.hom_whiskerLeft] using hTensorInj
  · simpa [ModuleCat.hom_whiskerLeft] using LinearMap.lTensor_surjective N hSurj

end UniversallyExact

/-- Helper for Example 10.82.2: tensoring the colimit cocone of a diagram of short complexes by a
fixed module again yields a colimit cocone. -/
noncomputable def tensorLeft_mapCocone_isColimit
    (F : J ⥤ ShortComplex (ModuleCat.{u} R)) (N : ModuleCat.{u} R) :
    IsColimit (((tensorLeft N).mapShortComplex).mapCocone (colimit.cocone F)) :=
  ShortComplex.isColimitOfIsColimitπ _
    (Limits.isColimitOfPreserves (tensorLeft N)
      (Limits.isColimitOfPreserves
        (ShortComplex.π₁ : ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R)
        (colimit.isColimit F)))
    (Limits.isColimitOfPreserves (tensorLeft N)
      (Limits.isColimitOfPreserves
        (ShortComplex.π₂ : ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R)
        (colimit.isColimit F)))
    (Limits.isColimitOfPreserves (tensorLeft N)
      (Limits.isColimitOfPreserves
        (ShortComplex.π₃ : ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R)
        (colimit.isColimit F)))

/-- Helper for Example 10.82.2: a colimit cocone of stagewise short exact short complexes has a
short exact cocone point. -/
theorem shortExact_of_isColimit_of_stagewise_shortExact
    (G : J ⥤ ShortComplex (ModuleCat.{u} R))
    (c : Cocone G) (hc : IsColimit c)
    (hG : ∀ j, (G.obj j).ShortExact) :
    c.pt.ShortExact := by
  let S : ShortComplex (J ⥤ ModuleCat.{u} R) :=
    (ShortComplex.functorEquivalence J (ModuleCat.{u} R)).inverse.obj G
  have hS : S.ShortExact := by
    let hEval := evaluation_jointly_reflects_isomorphisms (R := R) (J := J)
    -- Reflect short exactness from the family of componentwise evaluations.
    refine (hEval.shortExact_iff S).2 ?_
    intro j
    simpa [S] using hG j
  letI : Mono S.f := hS.mono_f
  letI : Epi S.g := hS.epi_g
  have hπ₁ : IsColimit (ShortComplex.π₁.mapCocone c) :=
    Limits.isColimitOfPreserves
      (ShortComplex.π₁ : ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R) hc
  have hπ₂ : IsColimit (ShortComplex.π₂.mapCocone c) :=
    Limits.isColimitOfPreserves
      (ShortComplex.π₂ : ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R) hc
  have hπ₃ : IsColimit (ShortComplex.π₃.mapCocone c) :=
    Limits.isColimitOfPreserves
      (ShortComplex.π₃ : ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R) hc
  -- Exactness, monicity, and epimorphicity all pass to the colimit point.
  have hExactColim : c.pt.Exact := by
    simpa [S] using
      (Limits.colim.exact_mapShortComplex (S := S) hS.exact hπ₁ hπ₂ hπ₃ c.pt.f c.pt.g
        (fun j ↦ by simpa [S] using (c.ι.app j).comm₁₂)
        (fun j ↦ by simpa [S] using (c.ι.app j).comm₂₃))
  refine ModuleCat.shortComplex_shortExact c.pt ?_ ?_ ?_
  · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact c.pt).mp hExactColim
  · exact (ModuleCat.mono_iff_injective _).1 <|
      Limits.colim.map_mono' S.f hπ₁ hπ₂ c.pt.f
        (fun j ↦ by simpa [S] using (c.ι.app j).comm₁₂)
  · exact (ModuleCat.epi_iff_surjective _).1 <|
      Limits.colim.map_epi' S.g (ShortComplex.π₂.mapCocone c) hπ₃ c.pt.g
        (fun j ↦ by simpa [S] using (c.ι.app j).comm₂₃)

-- Proof sketch: for each `N`, tensor-left by `N` preserves colimits, so
-- `(colimit F).map (tensorLeft N)` identifies with the colimit of the tensorized diagram; exact
-- filtered colimits in `ModuleCat R` then preserve the short exactness supplied by `hF`.
/-- Example 10.82.2: the colimit of a directed system of universally exact short exact sequences of
`R`-modules is universally exact. -/
theorem universallyExact_colimit_of_isFiltered
    (F : J ⥤ ShortComplex (ModuleCat.{u} R))
    (hF : ∀ j, (F.obj j).UniversallyExact) :
    (colimit F).UniversallyExact := by
  refine ⟨?_, ?_⟩
  · -- First forget the universal injectivity and keep only the stagewise short exactness.
    exact shortExact_of_isColimit_of_stagewise_shortExact F (colimit.cocone F)
      (colimit.isColimit F) (fun j ↦ (hF j).shortExact)
  · intro Q _ _
    let N : ModuleCat.{u} R := ModuleCat.of R Q
    have hTensorShortExact : ((colimit F).map (tensorLeft N)).ShortExact := by
      -- Tensor the entire filtered system, then pass short exactness through the tensorized colimit.
      simpa [N] using
        shortExact_of_isColimit_of_stagewise_shortExact
          (F ⋙ (tensorLeft N).mapShortComplex)
          (((tensorLeft N).mapShortComplex).mapCocone (colimit.cocone F))
          (tensorLeft_mapCocone_isColimit F N)
          (fun j ↦ (hF j).tensorLeft_shortExact N)
    -- Universal injectivity is the monomorphism statement for the tensorized first map.
    rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
    simpa [N, ModuleCat.hom_whiskerLeft] using
      (ModuleCat.mono_iff_injective (((colimit F).map (tensorLeft N)).f)).1
        hTensorShortExact.mono_f

-- Proof sketch: each stage is universally exact by `Splitting.universallyExact`, applied to a
-- chosen stagewise splitting, and the previous theorem preserves universal exactness under
-- filtered colimits.
/-- A directed colimit of split short exact sequences of `R`-modules is universally exact. -/
theorem universallyExact_colimit_of_split_system
    (F : J ⥤ ShortComplex (ModuleCat.{u} R))
    (hF : ∀ j, Nonempty ((F.obj j).Splitting)) :
    (colimit F).UniversallyExact := by
  apply universallyExact_colimit_of_isFiltered
  intro j
  obtain ⟨s⟩ := hF j
  -- Each stage is universally exact because its splitting survives tensoring.
  exact s.universallyExact

end ShortComplex
end CategoryTheory
