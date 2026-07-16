import Mathlib
import stacks_proof.stacks_project.Chap12.Definition_12_24_5

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

/-- Helper for Lemma 19.13.7: a filtered-complex morphism commutes with the inclusion of the
`p`-th stage into the underlying complex. -/
lemma FilteredComplex.stageMap_stageInclusion_square
    {K L : FilteredComplex 𝒜} (f : K ⟶ L) (p : ℤ) :
    FilteredComplex.stageMap f p ≫ L.stageInclusion p =
      K.stageInclusion p ≫ FilteredComplex.underlyingMap f := by
  -- Proof comment: this is the degreewise naturality square for filtered morphisms on the
  -- `p`-th stage and the ambient object.
  ext n
  exact FilteredObject.Hom.stageMap_comm (f.f n) p

/-- Helper for Lemma 19.13.7: the quotient map is the canonical `cokernel.map` attached to the
stage-inclusion square. -/
lemma quotientMap_cokernelMap {K L : FilteredComplex 𝒜} (f : K ⟶ L) (p : ℤ) :
    FilteredComplex.quotientMap f p =
      cokernel.map (K.stageInclusion p) (L.stageInclusion p)
        (FilteredComplex.stageMap f p) (FilteredComplex.underlyingMap f)
        (FilteredComplex.stageMap_stageInclusion_square f p).symm := rfl

/-- Helper for Lemma 19.13.7: in a morphism of short exact rows whose first two vertical maps are
quasi-isomorphisms, the induced map on cokernels is also a quasi-isomorphism. -/
lemma quasiIso_cokernelMap_of_monoSquare
    {A₁ B₁ A₂ B₂ : CochainComplex 𝒜 ℤ}
    (u₁ : A₁ ⟶ B₁) (u₂ : A₂ ⟶ B₂)
    [Mono u₁] [Mono u₂]
    (a : A₁ ⟶ A₂) (b : B₁ ⟶ B₂)
    (hsq : u₁ ≫ b = a ≫ u₂)
    [QuasiIso a] [QuasiIso b] :
    QuasiIso (cokernel.map u₁ u₂ a b hsq) := by
  let S₁ : ShortComplex (CochainComplex 𝒜 ℤ) := ShortComplex.cokernelSequence u₁
  let hS₁ : S₁.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact u₁)
      (inferInstance : Mono u₁) (inferInstance : Epi (cokernel.π u₁))
  let S₂ : ShortComplex (CochainComplex 𝒜 ℤ) := ShortComplex.cokernelSequence u₂
  let hS₂ : S₂.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact u₂)
      (inferInstance : Mono u₂) (inferInstance : Epi (cokernel.π u₂))
  let c : cokernel u₁ ⟶ cokernel u₂ := cokernel.map u₁ u₂ a b hsq
  let φ : S₁ ⟶ S₂ :=
    ShortComplex.Hom.mk a b c
      (by simpa using hsq.symm)
      (by simp [S₁, S₂, c, cokernel.map])
  -- Proof comment: the two quasi-isomorphism hypotheses occupy the first two terms of the
  -- cokernel rows, so the canonical homology-sequence lemma upgrades the cokernel map.
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ hS₁ hS₂ inferInstance inferInstance

/-- Helper for Lemma 19.13.7: once the underlying map and the `p`-th stage map are
quasi-isomorphisms, the induced quotient map at level `p` is also a quasi-isomorphism. -/
lemma quasiIso_quotientMap_of_underlying_stageMap
    {K L : FilteredComplex 𝒜} (f : K ⟶ L) (p : ℤ)
    [QuasiIso (FilteredComplex.underlyingMap f)]
    [QuasiIso (FilteredComplex.stageMap f p)] :
    QuasiIso (FilteredComplex.quotientMap f p) := by
  -- Proof comment: identify the quotient map with the canonical cokernel map of the stage
  -- inclusion square, then apply the short-exact-row transport lemma.
  rw [quotientMap_cokernelMap]
  exact
    quasiIso_cokernelMap_of_monoSquare
      (K.stageInclusion p) (L.stageInclusion p)
      (FilteredComplex.stageMap f p) (FilteredComplex.underlyingMap f)
      (FilteredComplex.stageMap_stageInclusion_square f p).symm

/-- Helper for Lemma 19.13.7: once the stage maps at `p'` and `p` are quasi-isomorphisms, the
induced map on the filtration subquotient `F^p/F^{p'}` is also a quasi-isomorphism. -/
lemma quasiIso_subquotientMap_of_stageMaps
    {K L : FilteredComplex 𝒜} (f : K ⟶ L) {p p' : ℤ} (hpp' : p ≤ p')
    [QuasiIso (FilteredComplex.stageMap f p)]
    [QuasiIso (FilteredComplex.stageMap f p')] :
    QuasiIso (FilteredComplex.subquotientMap f hpp') := by
  -- Proof comment: `FilteredComplex.subquotient` is defined as a cokernel, so the same
  -- short-exact-row transport applies to the stage-comparison square.
  exact
    quasiIso_cokernelMap_of_monoSquare
      (K.stageMapOfLE hpp') (L.stageMapOfLE hpp')
      (FilteredComplex.stageMap f p') (FilteredComplex.stageMap f p)
      (subquotientMap_square f hpp')

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

/-- Helper for Chap19 Lemma 19 13 7: once a filtered-complex morphism already lands in a target
with the required injective and K-injective models, the quotient and subquotient quasi-isomorphism
clauses follow formally from the underlying and stage quasi-isomorphisms. -/
lemma filteredComplexReplacementDataSuffices
    {K J : FilteredComplex 𝒜} (j : K ⟶ J)
    (hUnderlyingX : ∀ n : ℤ, Injective (J.underlying.X n))
    (hStageX : ∀ p n : ℤ, Injective ((J.stage p).X n))
    (hQuotientX : ∀ p n : ℤ, Injective ((J.quotient p).X n))
    (hSubquotientX : ∀ {p p' : ℤ} (hpp' : p ≤ p') (n : ℤ),
      Injective ((J.subquotient hpp').X n))
    (hUnderlyingK : J.underlying.IsKInjective)
    (hStageK : ∀ p : ℤ, (J.stage p).IsKInjective)
    (hQuotientK : ∀ p : ℤ, (J.quotient p).IsKInjective)
    (hSubquotientK : ∀ {p p' : ℤ} (hpp' : p ≤ p'), (J.subquotient hpp').IsKInjective)
    (hUnderlyingQ : QuasiIso (FilteredComplex.underlyingMap j))
    (hStageQ : ∀ p : ℤ, QuasiIso (FilteredComplex.stageMap j p)) :
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
  -- Proof comment: all objectwise injectivity and K-injectivity clauses are assumptions, so the
  -- remaining work is to transport quasi-isomorphisms from the underlying complex and stages to
  -- quotients and subquotients via the two local cokernel lemmas.
  refine ⟨hUnderlyingX, hStageX, hQuotientX, hSubquotientX, hUnderlyingK, hStageK, hQuotientK,
    hSubquotientK, ?_, ?_, ?_, ?_⟩
  · -- Proof comment: the theorem statement spells out the underlying map via the forgetful
    -- functor, which is definitionally the same as `FilteredComplex.underlyingMap`.
    simpa [FilteredComplex.underlyingMap] using hUnderlyingQ
  · -- Proof comment: each stage map in the statement is definitionally the corresponding
    -- `FilteredComplex.stageMap`.
    intro p
    simpa [FilteredComplex.stageMap] using hStageQ p
  · intro p
    -- Proof comment: the quotient map is a cokernel map of the stage inclusion square, so the
    -- local two-out-of-three lemma upgrades the underlying and stage quasi-isomorphisms.
    letI : QuasiIso (FilteredComplex.underlyingMap j) := hUnderlyingQ
    letI : QuasiIso (FilteredComplex.stageMap j p) := hStageQ p
    exact quasiIso_quotientMap_of_underlying_stageMap j p
  · intro p p' hpp'
    -- Proof comment: the subquotient map is the corresponding cokernel map of stage-comparison
    -- morphisms, so the stagewise quasi-isomorphisms suffice.
    letI : QuasiIso (FilteredComplex.stageMap j p) := hStageQ p
    letI : QuasiIso (FilteredComplex.stageMap j p') := hStageQ p'
    exact quasiIso_subquotientMap_of_stageMaps j hpp'

/-- Helper for Chap19 Lemma 19 13 7: the remaining source-level task is to construct a filtered
K-injective replacement whose underlying and stage maps are quasi-isomorphisms; the final quotient
and subquotient quasi-isomorphism clauses are then handled by
`filteredComplexReplacementDataSuffices`. -/
lemma existsFilteredComplexReplacementData
    [IsGrothendieckAbelian.{w} 𝒜] (K : FilteredComplex 𝒜) :
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
        QuasiIso (FilteredComplex.underlyingMap j) ∧
        (∀ p : ℤ, QuasiIso (FilteredComplex.stageMap j p)) := by
  -- Route correction: the filtered-object category is not abelian in general, so the missing step
  -- is not a direct application of the ordinary Chapter 19 replacement theorem in `Fil(𝒜)`.
  -- TODO: build one filtered target by strictifying compatible stagewise K-injective resolutions
  -- inside a common ambient complex, then read off the quotient and subquotient models degreewise.
  sorry

/-- Lemma 19.13.7: every filtered complex in a Grothendieck abelian category admits a morphism to
a filtered complex whose terms, stage complexes, quotient complexes, and filtration-subquotient
complexes are injective and K-injective in the appropriate sense, and such that the induced maps
on the underlying complex, every stage, every quotient, and every filtration subquotient are
quasi-isomorphisms. -/
@[stacks 0BKI]
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
  -- Proof comment: the theorem now reduces to one structural existence lemma constructing the
  -- filtered replacement data; the quotient and subquotient quasi-isomorphism clauses are closed
  -- formally by `filteredComplexReplacementDataSuffices`.
  obtain ⟨J, j, hUnderlyingX, hStageX, hQuotientX, hSubquotientX, hUnderlyingK, hStageK,
    hQuotientK, hSubquotientK, hUnderlyingQ, hStageQ⟩ :=
    existsFilteredComplexReplacementData (𝒜 := 𝒜) K
  refine ⟨J, j, ?_⟩
  exact
    filteredComplexReplacementDataSuffices j
      hUnderlyingX hStageX hQuotientX hSubquotientX
      hUnderlyingK hStageK hQuotientK hSubquotientK
      hUnderlyingQ hStageQ

end CategoryTheory
