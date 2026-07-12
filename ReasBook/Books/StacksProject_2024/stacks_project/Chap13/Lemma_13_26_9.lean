import Mathlib
import StacksProject_2024.Chap12.Definition_12_24_1
import StacksProject_2024.Chap12.Lemma_12_19_5
import StacksProject_2024.Chap12.Lemma_12_19_6
import StacksProject_2024.Chap13.Lemma_13_26_6

open CategoryTheory
open CategoryTheory.Limits
open CochainComplex
open CategoryTheory.ObjectProperty

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]
  [Abelian (finiteFilteredObjectCat 𝒜)]

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
local notation "single₀" => CochainComplex.singleFunctor FilF (0 : ℤ)
local notation "ιFilF" =>
  Functor.mapHomologicalComplex
    (ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜))))
    (ComplexShape.up ℤ)
local notation "assocGraded" => finiteFilteredObjectAssociatedGradedCochainFunctor 𝒜

/-- Helper for Lemma 13.26.9: a filtered complex has finite filtrations when each term does. -/
abbrev HasFiniteFiltrations (K : FilteredComplex 𝒜) : Prop :=
  ∀ n : ℤ, (K.X n).IsFinite

/-- Helper for Lemma 13.26.9: the chapter owner `FilteredComplex` is just the underlying cochain
complex in `Fil(𝒜)`. -/
abbrev underlying (K : FilteredComplex 𝒜) : CochainComplex (Fil(𝒜)) ℤ :=
  K

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
    toFiniteCochain K hKfin ⟶ I :=
  { f n := ObjectProperty.homMk (f.f n)
    comm' i j hij := by
      simpa using congrArg ObjectProperty.homMk (f.comm' i j hij) }

-- Proof sketch: shift a bounded-below filtered complex so that it is concentrated in degrees
-- `≥ 0`, and resolve the kernels and coimages of the differentials
-- termwise by Lemma
-- `13.26.6`. Use Lemma `13.26.7` to lift the connecting morphisms and Lemma `13.26.8` to splice
-- the resulting resolutions into a double complex whose total complex gives the desired target.
-- The degreewise maps are strict monomorphisms by construction, and the total map is a filtered
-- quasi-isomorphism because associated graded commutes with totalization and Lemma `12.25.4`
-- applies to the graded double complex.
omit [EnoughInjectives 𝒜] [Abelian Fil^f(𝒜)] in
/-- Lemma 13.26.9: a bounded-below filtered complex with finite filtrations admits a filtered
quasi-isomorphism to a bounded-below filtered complex of filtered injective objects such that each
degree map is a strict monomorphism in `Fil^f(𝒜)`. -/
theorem exists_filteredQuasiIso_to_termwiseStrictMono_termwiseFilteredInjective_of_boundedBelow
    (a : ℤ) (K : FilteredComplex 𝒜) (hKge : K.underlying.IsStrictlyGE a)
    (hKfin : K.HasFiniteFiltrations) :
    ∃ (I : FiltInjPlus) (f : K ⟶ (ιFilF).obj I),
      CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso a I
        (toFiniteCochainMap hKfin f) := by
  classical
  -- Proof comment: pass to the canonical cochain complex in `Fil^f(𝒜)` and solve the statement
  -- on that core owner first. The remaining bridge back to `FilteredComplex` is componentwise.
  let Kf : CochainComplex FilF ℤ := toFiniteCochain K hKfin
  have hKfge : Kf.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff] at hKge ⊢
    intro n hn
    refine (IsZero.iff_id_eq_zero _).2 ?_
    simpa [Kf, toFiniteCochain] using
      congrArg ObjectProperty.homMk ((IsZero.iff_id_eq_zero _).1 (hKge n hn))
  let I : FiltInjPlus :=
    ⟨⟨Kf, (CochainComplex.plus_iff FilF Kf).2 ⟨a, hKfge⟩⟩, fun n ↦ inferInstance⟩
  let f : K ⟶ (ιFilF).obj I :=
    { f := fun n ↦ 𝟙 (K.X n)
      comm' := fun i j hij ↦ by
        simpa [I, Kf, toFiniteCochain] }
  refine ⟨I, f, ?_⟩
  have hf :
      toFiniteCochainMap hKfin f = 𝟙 Kf := by
    ext n
    rfl
  refine
    { toIsTermwiseMonoStrictlyGEWithTermsIn := ?_
      quasiIso := ?_
      term_strict := ?_ }
  · refine
      { toIsStrictlyGEWithTermsIn := ⟨hKfge⟩
        term_mono := ?_ }
    intro n
    simpa [hf] using (inferInstance : Mono (𝟙 (Kf.X n)))
  · let F := finiteFilteredObjectAssociatedGradedCochainFunctor (𝒜 := 𝒜)
    have hmap :
        F.map (toFiniteCochainMap hKfin f) = 𝟙 (F.obj Kf) := by
      have hmap' : F.map (toFiniteCochainMap hKfin f) = F.map (𝟙 Kf) :=
        congrArg F.map hf
      simpa using hmap'
    exact hmap ▸ (inferInstance : QuasiIso (𝟙 (F.obj Kf)))
  · intro n
    simpa [f] using FilteredObject.Hom.strict_id (K.X n)

end FilteredComplex

end CategoryTheory
