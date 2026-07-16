import Mathlib
import StacksProject_2024.stacks_project.Chap12.Definition_12_24_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open FilteredObject
open FilteredComplex

noncomputable section

universe w v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- Helper for Lemma 19.13.7: the quotient complex is obtained by applying the filtered quotient
functor degreewise. -/
noncomputable abbrev FilteredComplex.quotient (K : FilteredComplex 𝒜) (p : ℤ) :
    CochainComplex 𝒜 ℤ :=
  ((FilteredObject.quotientFunctor (C := 𝒜) p).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K

/-- Helper for Lemma 19.13.7: the induced map on quotient complexes comes from applying the
filtered quotient functor degreewise. -/
noncomputable abbrev FilteredComplex.quotientMap {K L : FilteredComplex 𝒜}
    (f : K ⟶ L) (p : ℤ) :
    K.quotient p ⟶ L.quotient p :=
  ((FilteredObject.quotientFunctor (C := 𝒜) p).mapHomologicalComplex
    (ComplexShape.up ℤ)).map f

/-- Helper for Lemma 19.13.7: the filtration subquotient `F^p K^• / F^{p'} K^•` is the canonical
subquotient complex attached to the stage comparison. -/
noncomputable abbrev FilteredComplex.subquotient (K : FilteredComplex 𝒜)
    {p p' : ℤ} (hpp' : p ≤ p') :
    CochainComplex 𝒜 ℤ :=
  cokernel (K.stageMapOfLE hpp')

/-- Helper for Lemma 19.13.7: a filtered-complex morphism commutes with the canonical stage
comparison maps, which is the square needed to map cokernel-defined subquotients. -/
lemma subquotientMap_square {K L : FilteredComplex 𝒜}
    (f : K ⟶ L) {p p' : ℤ} (hpp' : p ≤ p') :
    K.stageMapOfLE hpp' ≫ FilteredComplex.stageMap f p =
      FilteredComplex.stageMap f p' ≫ L.stageMapOfLE hpp' := by
  -- Proof comment: this is the naturality square of the stage-comparison transformation
  -- `stageFunctor p' ⟶ stageFunctor p` lifted to cochain complexes.
  simpa [FilteredComplex.stageMap, FilteredComplex.stageMapOfLE] using
    (NatTrans.mapHomologicalComplex (FilteredObject.stageFunctorMapOfLE hpp')
      (ComplexShape.up ℤ)).naturality f

/-- Helper for Lemma 19.13.7: the induced map on filtration subquotients is the image of the
filtered-complex morphism under the subquotient construction. -/
noncomputable abbrev FilteredComplex.subquotientMap {K L : FilteredComplex 𝒜}
    (f : K ⟶ L) {p p' : ℤ} (hpp' : p ≤ p') :
    K.subquotient hpp' ⟶ L.subquotient hpp' :=
  cokernel.map (K.stageMapOfLE hpp') (L.stageMapOfLE hpp')
    (FilteredComplex.stageMap f p') (FilteredComplex.stageMap f p)
    (subquotientMap_square f hpp')

/- Domain-style sampling for Lemma 19.13.7:
- primary domain: filtered cochain complexes in a Grothendieck abelian category and their
  K-injective replacements;
- sampled owner declarations:
  `FilteredComplex`,
  `FilteredComplex.underlying`,
  `FilteredComplex.stage`,
  `FilteredComplex.stageMapOfLE`,
  `FilteredObject.quotientFunctor`;
- best owner abstraction: the canonical filtered-complex owner `FilteredComplex 𝒜`, together with
  the stage, quotient, and subquotient bridge constructions obtained from the filtered-object
  functors lifted along `mapHomologicalComplex`;
- primitive data: a filtered-complex morphism `j : K ⟶ J`;
- derived API retained here: quotient and subquotient complexes and the induced comparison maps;
- source/core/bridge triage:
  `source-facing`: `exists_filteredComplex_kInjectiveReplacement`;
  `core/canonical`: `FilteredComplex 𝒜`, `underlying`, `stage`, `stageMapOfLE`, and
  `quotientFunctor`;
  `bridge/view`: `FilteredComplex.quotient`, `FilteredComplex.quotientMap`,
    `FilteredComplex.underlyingToQuotient`, `FilteredComplex.subquotient`, and
    `FilteredComplex.subquotientMap`. -/

-- Proof sketch: apply Theorem 19.12.6 functorially to the underlying complex and to each stage
-- complex `F^p K^•`, then correct the comparison maps by acyclic K-injective summands so that the
-- stagewise maps become termwise monomorphisms inside one filtered target complex. Products of
-- injectives remain injective in a Grothendieck abelian category, and the standard two-out-of-three
-- arguments for K-injective complexes and long exact cohomology sequences give the quotient and
-- subquotient quasi-isomorphisms and K-injectivity statements.
/-- Helper for Lemma 19.13.7: quotient maps are computed by the degreewise quotient functor. -/
lemma quotientMap_def {K L : FilteredComplex 𝒜} (f : K ⟶ L) (p : ℤ) :
    FilteredComplex.quotientMap f p =
      ((FilteredObject.quotientFunctor (C := 𝒜) p).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f := rfl

/-- Helper for Lemma 19.13.7: once a termwise injective model for the chosen filtration
subquotient is available, we can read off injectivity degreewise. -/
lemma subquotientX_injective (J : FilteredComplex 𝒜)
    {p p' : ℤ} (hpp' : p ≤ p') (hJ : ∀ n : ℤ, Injective ((J.subquotient hpp').X n))
    (n : ℤ) :
    Injective ((J.subquotient hpp').X n) := by
  -- Proof comment: the product-tail model constructed in the main theorem will supply `hJ`.
  exact hJ n

/-- Helper for Lemma 19.13.7: filtration subquotients of a resolved filtered complex are
K-injective once a K-injective model for the chosen subquotient has been established. -/
lemma subquotientIsKInjective (J : FilteredComplex 𝒜)
    {p p' : ℤ} (hpp' : p ≤ p') (hJ : (J.subquotient hpp').IsKInjective) :
    (J.subquotient hpp').IsKInjective := by
  -- Proof comment: the main theorem will prove the premise `hJ` from the split short exact rows
  -- of the product-tail construction.
  exact hJ

/-- Lemma 19.13.7: every filtered complex in a Grothendieck abelian category admits a morphism to
a filtered complex whose terms, stage complexes, quotient complexes, and filtration-subquotient
complexes are injective and K-injective in the appropriate sense, and such that the induced maps
on the underlying complex, every stage, every quotient, and every filtration subquotient are
quasi-isomorphisms. -/
theorem exists_filteredComplex_kInjectiveReplacement
    [IsGrothendieckAbelian.{w} 𝒜]
    (K : FilteredComplex 𝒜) :
    ∃ (J : FilteredComplex 𝒜) (j : K ⟶ J),
      (∀ n : ℤ, Injective (J.underlying.X n)) ∧
        (∀ p n : ℤ, Injective ((J.stage p).X n)) ∧
        (∀ p n : ℤ, Injective ((J.quotient p).X n)) ∧
        (∀ {p p' : ℤ} (hpp' : p ≤ p') (n : ℤ),
          Injective ((J.subquotient hpp').X n)) ∧
        J.underlying.IsKInjective ∧
        (∀ p : ℤ, (J.stage p).IsKInjective) ∧
        (∀ p : ℤ, (J.quotient p).IsKInjective) ∧
        (∀ {p p' : ℤ} (hpp' : p ≤ p'), (J.subquotient hpp').IsKInjective) ∧
        QuasiIso ((FilteredObject.forget.mapHomologicalComplex (ComplexShape.up ℤ)).map j) ∧
        (∀ p : ℤ, QuasiIso (((stageFunctor p).mapHomologicalComplex (ComplexShape.up ℤ)).map j)) ∧
        (∀ p : ℤ, QuasiIso (FilteredComplex.quotientMap j p)) ∧
        (∀ {p p' : ℤ} (hpp' : p ≤ p'), QuasiIso (FilteredComplex.subquotientMap j hpp')) := by
  -- Route correction: the previous filtered-object replacement route was wrong for this file.
  -- TODO: rebuild the textbook proof from the repaired Chapter 19 owner theorem supplying
  -- stagewise K-injective replacements, together with the local subquotient API placeholders
  -- introduced above.
  sorry

end CategoryTheory
