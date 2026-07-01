import Mathlib
import stacks_project.Chap13.Lemma_13_26_6

open CategoryTheory
open CategoryTheory.Limits
open CochainComplex
open CategoryTheory.ObjectProperty

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]

local instance instCategoryWithHomologyGradedObjectInt_13_26_9 :
    CategoryWithHomology (GradedObject ℤ 𝒜) := by
  have hzero : (Preadditive.preadditiveHasZeroMorphisms :
      HasZeroMorphisms (GradedObject ℤ 𝒜)) = GradedObject.hasZeroMorphisms ℤ :=
    HasZeroMorphisms.ext _ _
  exact hzero ▸
    (@_root_.CategoryTheory.categoryWithHomology_of_abelian (GradedObject ℤ 𝒜) _ _)

namespace FilteredComplex

local notation "FilF" => Fil^f(𝒜)
local notation "FiltInjPlus" => CochainComplex.FilteredInjectivePlus 𝒜
local notation "ιFilF" =>
  Functor.mapHomologicalComplex
    (ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜))))
    (ComplexShape.up ℤ)

/- Domain-style sampling for Lemma `13.26.9`.
- primary domain: bounded-below filtered complexes with finite filtrations and their filtered
  quasi-isomorphisms into bounded-below complexes of filtered injective objects;
- sampled owner declarations:
  `FilteredComplex`,
  `FilteredComplex.HasFiniteFiltrations`,
  `FilteredComplex.toFiniteCochain`,
  `FilteredComplex.toFiniteCochainMap`,
  `FilteredComplex.associatedGradedMap`,
  `CochainComplex.FilteredInjectivePlus`,
  `CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso`,
  `((ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜)))).mapHomologicalComplex
    (ComplexShape.up ℤ))`;
- best owner abstraction: the source object remains the intrinsic Chapter `12` owner
  `FilteredComplex 𝒜`, while the target bounded-below filtered-injective complex is canonically
  owned by `CochainComplex.FilteredInjectivePlus 𝒜`; the comparison map data should be expressed
  by the chapter owner `CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso` after the
  canonical bridge `FilteredComplex.toFiniteCochain` from a finite filtered complex to a cochain
  complex in `Fil^f(𝒜)`;
- primitive data: a filtered complex `K : FilteredComplex 𝒜` together with a lower bound
  `hKge : K.underlying.IsStrictlyGE a` and the finiteness witness `hKfin : K.HasFiniteFiltrations`;
- derived API: the bridge declarations `toFiniteCochain` and `toFiniteCochainMap`, and the
  existence theorem below, whose public comparison datum is the intrinsic filtered-complex
  morphism `f : K ⟶ (ιFilF).obj I`;
- source/core/bridge triage:
  `source-facing`: the existence theorem below, formulated on `FilteredComplex 𝒜`;
  `core/canonical`: `CochainComplex.FilteredInjectivePlus` and
    `CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso`;
  `bridge/view`: `FilteredComplex.toFiniteCochain`, `FilteredComplex.toFiniteCochainMap`, and
    the canonical inclusion
    `((ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜))))
      .mapHomologicalComplex (ComplexShape.up ℤ))`, which translates the intrinsic
    finite-filtration hypothesis into the canonical full-subcategory owner `Fil^f(𝒜)`. -/

/-- Bridge/view layer: a filtered complex with finite filtrations is canonically a cochain complex
in `Fil^f(𝒜)`. -/
abbrev toFiniteCochain (K : FilteredComplex 𝒜) (hKfin : K.HasFiniteFiltrations) :
    CochainComplex FilF ℤ :=
  { X n := ⟨K.X n, hKfin n⟩
    d i j := ObjectProperty.homMk (K.d i j)
    shape i j hij := by
      simp [K.shape i j hij]
    d_comp_d' i j k hij hjk := by
      ext
      simp [K.d_comp_d' i j k hij hjk] }

/-- Bridge/view layer: a morphism from a filtered complex with finite filtrations into the
canonical image of a cochain complex in `Fil^f(𝒜)` lifts to a morphism in
`CochainComplex (Fil^f(𝒜)) ℤ`. -/
abbrev toFiniteCochainMap {K : FilteredComplex 𝒜} (hKfin : K.HasFiniteFiltrations)
    {I : CochainComplex FilF ℤ} (f : K ⟶ (ιFilF).obj I) :
    K.toFiniteCochain hKfin ⟶ I :=
  { f n := ObjectProperty.homMk (f.f n)
    comm' i j hij := by
      ext
      simpa using f.comm' i j hij }

-- Proof sketch: shift a bounded-below filtered complex so that it is concentrated in degrees
-- `≥ 0`, and resolve the kernels and coimages of the differentials
-- termwise by Lemma
-- `13.26.6`. Use Lemma `13.26.7` to lift the connecting morphisms and Lemma `13.26.8` to splice
-- the resulting resolutions into a double complex whose total complex gives the desired target.
-- The degreewise maps are strict monomorphisms by construction, and the total map is a filtered
-- quasi-isomorphism because associated graded commutes with totalization and Lemma `12.25.4`
-- applies to the graded double complex.
/-- Lemma 13.26.9: a bounded-below filtered complex with finite filtrations admits a filtered
quasi-isomorphism to a bounded-below filtered complex of filtered injective objects such that each
degree map is a strict monomorphism in `Fil^f(𝒜)`. -/
theorem exists_filteredQuasiIso_to_termwiseStrictMono_termwiseFilteredInjective_of_boundedBelow
    (a : ℤ) (K : FilteredComplex 𝒜) (hKge : K.underlying.IsStrictlyGE a)
    (hKfin : K.HasFiniteFiltrations) :
    ∃ (I : FiltInjPlus) (f : K ⟶ (ιFilF).obj I),
      CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso a I
        (toFiniteCochainMap hKfin f) := sorry

end FilteredComplex

end CategoryTheory
