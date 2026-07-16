import Mathlib.CategoryTheory.Sites.LocallySurjective
import StacksProject_2024.stacks_project.Chap12.Lemma_12_24_11
import StacksProject_2024.stacks_project.Chap12.Definition_12_24_9
import StacksProject_2024.stacks_project.Chap21.Definition_21_13_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Abelian
open scoped CategoryTheory.Sheaf

noncomputable section

universe v u

namespace CategoryTheory
namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J (Type (max u v))]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf J AddCommGrpCat.{max u v})]

/-- The sheafified Čech `p`-simplex of a presheaf morphism `φ`. This is the `p`-th object of the
Čech nerve of the sheafified map associated to `φ`, i.e. the sheafified form of the iterated
fiber product `K' ×_K ⋯ ×_K K'` with `p + 1` factors. -/
abbrev sheafifiedCechLevel {K K' : Cᵒᵖ ⥤ Type (max u v)} (φ : K' ⟶ K) (p : ℕ) :
    Sheaf J (Type (max u v)) :=
  (Arrow.mk ((presheafToSheaf J (Type (max u v))).map φ)).cechNerve.obj (op (SimplexCategory.mk p))

/- Domain-style sampling for Lemma 21.13.2:
- primary domain: Čech nerves of sheafified presheaf maps and first-quadrant cohomological
  spectral sequences on a site;
- sampled owner declarations:
  `Arrow.cechNerve`,
  `Presheaf.IsLocallySurjective`,
  `Sheaf.composeAndSheafify`,
  `FilteredComplex`,
  `IsAssociatedToFilteredComplex`,
  `FilteredComplex.cohomologyFiltrationIsFinite`,
  `FilteredComplex.convergesToCohomology`;
- best owner abstraction: the source-facing theorem should quantify directly over the canonical
  filtered-complex package for a chosen associated cohomological spectral sequence, with the
  sheafified Čech simplices expressed through `Arrow.cechNerve` on the sheafified map and their
  cohomology expressed through the chapter owner `H^q(K, F)`;
- primitive data: the presheaf map `φ`, its local-surjectivity hypothesis, the sheaf `F`, the
  filtered complex, the associated spectral sequence, and the page-one and target comparison
  isomorphisms;
- derived API: boundedness of the chosen spectral sequence together with its convergence to
  the filtered-complex cohomology identified with the cohomology over `K^#`, packaged in the
  canonical Chapter `12` convergence owner and the finite-filtration companion used by nearby
  Chapter `21` spectral-sequence statements.

Source/core/bridge triage:
- `source-facing`: the existence of the Čech spectral sequence attached to a locally surjective
  presheaf map;
- `core/canonical`: `Arrow.cechNerve`, `Presheaf.IsLocallySurjective`,
  `cohomologyOverSheaf`, `FilteredComplex`, `IsAssociatedToFilteredComplex`, and
  `FilteredComplex.cohomologyFiltrationIsFinite`, and
  `FilteredComplex.convergesToCohomology`;
- `bridge/view`: the source-facing stage family `sheafifiedCechLevel` together with the page-one
  and target comparison isomorphisms.

The deleted detached abutment family did not say that the displayed spectral sequence actually
abutted to the identified cohomology groups. The source-facing stage family `sheafifiedCechLevel`
is kept, while the theorem itself now uses the canonical filtered-complex owner package that
records the chosen spectral sequence, its finite cohomology filtration, and its convergence to
cohomology directly. -/
-- Proof sketch: replace the map of presheaves by its sheafification, using left exactness of
-- sheafification to identify the sheafified Čech nerve levels with the sheafifications of the
-- iterated fiber products `K'_p`. After enlarging the site as in Lemma `7.29.5`, represent the
-- sheafified map by a covering of an object and apply the Čech-to-cohomology spectral sequence of
-- Lemma `21.10.6` on the localized site.
--
-- The cohomology owners `H^q(K, F)` and `cohomologyOverPresheaf K F n` are canonically built from
-- sheafification on abelian-group-valued presheaves, so the theorem keeps the owner-level
-- assumption `[HasSheafify J AddCommGrpCat.{max u v}]`. The exactness class
-- `[J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]` is only used by the Chapter 21 proof
-- route and is omitted from the public theorem surface.
omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- Lemma 21.13.2: let `φ : K' ⟶ K` be a map of presheaves of sets on a site whose sheafification
is surjective, formalized here by `Presheaf.IsLocallySurjective J φ`. Then for every abelian sheaf `F`
there is a bounded associated cohomological spectral sequence whose nonnegative `E_1^{p,q}` terms
are the cohomology of `F` over the sheafified Čech `p`-simplex of `φ`, i.e. the sheafified form
of `K'_p = K' ×_K ⋯ ×_K K'`, and which converges to the cohomology of `F` over the
sheafification of `K`, with finite induced cohomology filtration. -/
@[stacks 079Z]
theorem exists_cechSpectralSequence_of_isLocallySurjective
    {K K' : Cᵒᵖ ⥤ Type (max u v)} (φ : K' ⟶ K)
    (hφ : Presheaf.IsLocallySurjective J φ)
    (F : Sheaf J AddCommGrpCat.{max u v}) :
    ∃ (filteredComplex : FilteredComplex AddCommGrpCat.{max u v})
      (spectralSequence : CohomologicalSpectralSequence AddCommGrpCat.{max u v} 0)
      (hAssoc : IsAssociatedToFilteredComplex filteredComplex spectralSequence)
      (pageOneIso :
        ∀ p q : ℕ,
          (spectralSequence.page 1).X (Int.ofNat p, Int.ofNat q) ≅
            H^q(sheafifiedCechLevel φ p, F))
      (targetIso :
        ∀ n : ℕ,
          filteredComplex.underlying.homology (Int.ofNat n) ≅
            cohomologyOverPresheaf K F n),
      CohomologicalSpectralSequence.IsBounded spectralSequence ∧
        filteredComplex.cohomologyFiltrationIsFinite ∧
        filteredComplex.convergesToCohomology spectralSequence := sorry

end Sheaf
end CategoryTheory
