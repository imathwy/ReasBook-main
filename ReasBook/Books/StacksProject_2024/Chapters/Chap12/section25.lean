import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_12_25_1 (from Chap12) -/
open CategoryTheory ComplexShape HomologicalComplex
open HomologicalComplex₂

noncomputable section

universe v u

/- Domain-style sampling for Lemma 12.25.1:
- primary domain: cohomological double complexes and the page identifications of the two spectral
  sequences attached to them;
- inspected owner declarations:
  `HomologicalComplex₂.flip`,
  `HomologicalComplex.homologyFunctor`,
  `CochainComplex.of`,
  `ComplexShape.ε_up_ℤ`;
- owner abstraction: the double-complex owner `HomologicalComplex₂`, with row/column and homology
  views derived from `flip` and `HomologicalComplex.homologyFunctor`;
- primitive data: the bicomplex `K` and its owner differentials;
- derived API in this file: the source-facing `E₀`, `E₁`, and `E₂` page terms and differentials,
  together with the canonical first `E₁`-page complex and its signed flipped companion for the
  second `E₁`-page;
- triage:
  `source-facing`: the page-term and differential declarations below;
  `core/canonical`: `HomologicalComplex₂`, `flip`, and `HomologicalComplex.homologyFunctor`;
  `bridge/view`: the first `E₁`-page cochain complex in the horizontal direction, together with
  its sign-twisted flipped variant for the second `E₁`-page; both should use canonical
  `CochainComplex` owners rather than coordinate-only projections.
-/

section SignTwist

variable {C : Type u} [Category.{v} C] [Preadditive C]

-- Proof sketch: `CochainComplex.of` is the canonical owner for an explicitly defined cochain
-- complex, so it is enough to verify square-zero on consecutive differentials.
private theorem cochainComplexUnitsSMul_sq
    (L : CochainComplex C ℤ) (ε : ℤˣ) (p : ℤ) :
    (ε • L.d p (p + 1)) ≫ (ε • L.d (p + 1) ((p + 1) + 1)) = 0 := by
  calc
    (ε • L.d p (p + 1)) ≫ (ε • L.d (p + 1) ((p + 1) + 1)) =
        ε • (ε • (L.d p (p + 1) ≫ L.d (p + 1) ((p + 1) + 1))) := by
      simp [Linear.units_smul_comp, Linear.comp_units_smul]
    _ = 0 := by simp [L.d_comp_d p (p + 1) ((p + 1) + 1)]

end SignTwist

section

variable {C : Type u} [Category.{v} C] [Preadditive C]
local notation "DoubleComplex" => HomologicalComplex₂ C (up ℤ) (up ℤ)

/-- Lemma 12.25.1 (1): the first spectral sequence attached to a cohomological double complex has
term `{}'E_0^{p,q} = K^{p,q}`. -/
abbrev firstDoubleComplexPageZero
    (K : DoubleComplex) (p q : ℤ) : C :=
  (K.X p).X q

/-- Lemma 12.25.1 (2): the differential on the first `E₀`-page is
`{}'d_0^{p,q} = (-1)^p d_2^{p,q} : K^{p,q} ⟶ K^{p,q + 1}`. -/
abbrev firstDoubleComplexPageZeroDifferential
    (K : DoubleComplex) (p q : ℤ) :
    firstDoubleComplexPageZero K p q ⟶ firstDoubleComplexPageZero K p (q + 1) :=
  p.negOnePow • (K.X p).d q (q + 1)

/-- Lemma 12.25.1 (3): the second spectral sequence attached to a cohomological double complex has
term `{}''E_0^{p,q} = K^{q,p}`. -/
abbrev secondDoubleComplexPageZero
    (K : DoubleComplex) (p q : ℤ) : C :=
  (K.flip.X p).X q

-- Proof sketch: this is the defining abbreviation of the second `E₀`-page term.
/-- The second `E₀`-page object is definitionally the transposed `(q,p)`-entry of the double
complex. -/
theorem secondDoubleComplexPageZero_def
    (K : DoubleComplex) (p q : ℤ) :
    secondDoubleComplexPageZero K p q = (K.X q).X p := rfl

/-- Lemma 12.25.1 (4): the differential on the second `E₀`-page is
`{}''d_0^{p,q} = d_1^{q,p} : K^{q,p} ⟶ K^{q + 1,p}`. -/
abbrev secondDoubleComplexPageZeroDifferential
    (K : DoubleComplex) (p q : ℤ) :
    secondDoubleComplexPageZero K p q ⟶ secondDoubleComplexPageZero K p (q + 1) :=
  (K.flip.X p).d q (q + 1)

-- Proof sketch: unfold the abbreviation for the second `E₀`-page differential.
/-- The second `E₀`-page differential is definitionally the horizontal differential of the double
complex. -/
theorem secondDoubleComplexPageZeroDifferential_def
    (K : DoubleComplex) (p q : ℤ) :
    secondDoubleComplexPageZeroDifferential K p q = (K.d q (q + 1)).f p := rfl

variable [CategoryWithHomology C]
local notation "homologyFunctor" => HomologicalComplex.homologyFunctor C (up ℤ)

/-- The first `E₁`-page cochain complex obtained by taking vertical homology in degree `q` along
the columns of a cohomological double complex. -/
abbrev firstDoubleComplexPageOneComplex
    (K : DoubleComplex) (q : ℤ) : CochainComplex C ℤ :=
  ((homologyFunctor q).mapHomologicalComplex (up ℤ)).obj K

/-- The `p`-th object of the first `E₁`-page complex is the vertical homology of the `p`-th
column. -/
@[simp] theorem firstDoubleComplexPageOneComplex_X
    (K : DoubleComplex) (p q : ℤ) :
    (firstDoubleComplexPageOneComplex K q).X p = (K.X p).homology q := rfl

/-- The differential of the first `E₁`-page complex is the homology map induced by the horizontal
differential. -/
@[simp] theorem firstDoubleComplexPageOneComplex_d
    (K : DoubleComplex) (p q : ℤ) :
    (firstDoubleComplexPageOneComplex K q).d p (p + 1) =
      homologyMap (K.d p (p + 1)) q := rfl

/-- The second `E₁`-page cochain complex: its objects are the horizontal homology groups
`H^q(K^{\bullet,p})`, and its differential is the sign-twisted map
`(-1)^q H^q(d_2^{\bullet,p})`. Equivalently, it is the sign twist of
`firstDoubleComplexPageOneComplex K.flip q`. -/
abbrev secondDoubleComplexPageOneComplex
    (K : DoubleComplex) (q : ℤ) : CochainComplex C ℤ :=
  CochainComplex.of
    (firstDoubleComplexPageOneComplex K.flip q).X
    (fun p ↦ q.negOnePow • (firstDoubleComplexPageOneComplex K.flip q).d p (p + 1))
    (cochainComplexUnitsSMul_sq (firstDoubleComplexPageOneComplex K.flip q) q.negOnePow)

/-- The `p`-th object of the second `E₁`-page complex is the horizontal homology of the `p`-th
row. -/
@[simp] theorem secondDoubleComplexPageOneComplex_X
    (K : DoubleComplex) (p q : ℤ) :
    (secondDoubleComplexPageOneComplex K q).X p = (K.flip.X p).homology q := rfl

/-- The differential of the second `E₁`-page complex is the signed homology map induced by the
vertical differential on the flipped double complex. -/
@[simp] theorem secondDoubleComplexPageOneComplex_d
    (K : DoubleComplex) (q p : ℤ) :
    (secondDoubleComplexPageOneComplex K q).d p (p + 1) =
      q.negOnePow • (firstDoubleComplexPageOneComplex K.flip q).d p (p + 1) := by
  exact
    CochainComplex.of_d
      (firstDoubleComplexPageOneComplex K.flip q).X
      (fun p ↦ q.negOnePow • (firstDoubleComplexPageOneComplex K.flip q).d p (p + 1))
      (cochainComplexUnitsSMul_sq (firstDoubleComplexPageOneComplex K.flip q) q.negOnePow)
      p

/-- Lemma 12.25.1 (5): the first `E₁`-page is the vertical homology
`{}'E_1^{p,q} = H^q(K^{p,\bullet})`. -/
abbrev firstDoubleComplexPageOne
    (K : DoubleComplex) (p q : ℤ) : C :=
  (firstDoubleComplexPageOneComplex K q).X p

/-- The first `E₁`-page object is definitionally the vertical homology of the `p`-th column. -/
theorem firstDoubleComplexPageOne_def
    (K : DoubleComplex) (p q : ℤ) :
    firstDoubleComplexPageOne K p q = (K.X p).homology q := by
  simpa [firstDoubleComplexPageOne] using firstDoubleComplexPageOneComplex_X K p q

/-- Lemma 12.25.1 (6): the differential on the first `E₁`-page is
`{}'d_1^{p,q} = H^q(d_1^{p,\bullet})`. -/
abbrev firstDoubleComplexPageOneDifferential
    (K : DoubleComplex) (p q : ℤ) :
    firstDoubleComplexPageOne K p q ⟶ firstDoubleComplexPageOne K (p + 1) q :=
  (firstDoubleComplexPageOneComplex K q).d p (p + 1)

/-- The first `E₁`-page differential is definitionally the homology map induced by the horizontal
differential. -/
theorem firstDoubleComplexPageOneDifferential_def
    (K : DoubleComplex) (p q : ℤ) :
    firstDoubleComplexPageOneDifferential K p q =
      homologyMap (K.d p (p + 1)) q := by
  simpa [firstDoubleComplexPageOneDifferential] using firstDoubleComplexPageOneComplex_d K p q

/-- Lemma 12.25.1 (7): the second `E₁`-page is the horizontal homology
`{}''E_1^{p,q} = H^q(K^{\bullet,p})`. -/
abbrev secondDoubleComplexPageOne
    (K : DoubleComplex) (p q : ℤ) : C :=
  (secondDoubleComplexPageOneComplex K q).X p

/-- The second `E₁`-page object is definitionally the horizontal homology of the `p`-th row. -/
theorem secondDoubleComplexPageOne_def
    (K : DoubleComplex) (p q : ℤ) :
    secondDoubleComplexPageOne K p q = (K.flip.X p).homology q := by
  simpa [secondDoubleComplexPageOne] using secondDoubleComplexPageOneComplex_X K p q

/-- Lemma 12.25.1 (8): the differential on the second `E₁`-page is
`{}''d_1^{p,q} = (-1)^q H^q(d_2^{\bullet,p})`. -/
abbrev secondDoubleComplexPageOneDifferential
    (K : DoubleComplex) (p q : ℤ) :
    secondDoubleComplexPageOne K p q ⟶ secondDoubleComplexPageOne K (p + 1) q :=
  (secondDoubleComplexPageOneComplex K q).d p (p + 1)

/-- The second `E₁`-page differential is definitionally the signed homology map induced by the
vertical differential on the flipped double complex. -/
theorem secondDoubleComplexPageOneDifferential_def
    (K : DoubleComplex) (p q : ℤ) :
    secondDoubleComplexPageOneDifferential K p q =
      q.negOnePow • homologyMap (K.flip.d p (p + 1)) q := by
  rw [secondDoubleComplexPageOneDifferential, secondDoubleComplexPageOneComplex_d]
  rfl

/-- Lemma 12.25.1 (9): the first `E₂`-page is the horizontal homology of the vertical homology
complex, namely `{}'E_2^{p,q} = H_I^p(H_{II}^q(K^{\bullet,\bullet}))`. -/
abbrev firstDoubleComplexPageTwo
    (K : DoubleComplex) (p q : ℤ) : C :=
  (firstDoubleComplexPageOneComplex K q).homology p

/-- The first `E₂`-page object is definitionally the horizontal homology of the vertical homology
complex. -/
theorem firstDoubleComplexPageTwo_def
    (K : DoubleComplex) (p q : ℤ) :
    firstDoubleComplexPageTwo K p q =
      (firstDoubleComplexPageOneComplex K q).homology p := rfl

/-- Lemma 12.25.1 (10): the second `E₂`-page is the vertical homology of the horizontal homology
complex, namely `{}''E_2^{p,q} = H_{II}^p(H_I^q(K^{\bullet,\bullet}))`. -/
abbrev secondDoubleComplexPageTwo
    (K : DoubleComplex) (p q : ℤ) : C :=
  (secondDoubleComplexPageOneComplex K q).homology p

-- Proof sketch: this is the defining abbreviation of the second `E₂`-page term.
/-- The second `E₂`-page object is definitionally the vertical homology of the horizontal
homology complex. -/
theorem secondDoubleComplexPageTwo_def
    (K : DoubleComplex) (p q : ℤ) :
    secondDoubleComplexPageTwo K p q = (secondDoubleComplexPageOneComplex K q).homology p := rfl

end

/-! ### Definition_12_25_2 (from Chap12) -/
universe u v

namespace CategoryTheory

open ComplexShape
open CategoryTheory.Limits

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [LocallySmall 𝒜] [WellPowered 𝒜]
  [HasWidePullbacks 𝒜] [HasCoproducts 𝒜] [InitialMonoClass 𝒜]

/- Domain-style sampling for Definition `12.25.2`.
- primary domain: convergence of the two spectral sequences attached to a double complex, expressed
  through the canonical first and second filtered complexes on `Tot(K)`;
- sampled owner/canonical declarations:
  `FilteredComplex.weaklyConvergesToCohomology`,
  `FilteredComplex.abutsToCohomology`,
  `FilteredComplex.convergesToCohomology`,
  `firstDoubleComplexFilteredComplex`,
  `secondDoubleComplexFilteredComplex`;
- best owner abstraction: the canonical filtered-complex owners
  `firstDoubleComplexFilteredComplex K` and `secondDoubleComplexFilteredComplex K`, with an
  associated spectral sequence `E` only when the full convergence predicate is needed;
- primitive data: a double complex `K`, and optionally an associated spectral sequence `E` of one
  of the two canonical filtrations on `Tot(K)`;
- derived API: the convergence predicates on those two canonical filtered-complex owners;
- source/core/bridge triage:
  `source-facing`: the first and second spectral sequences of a double complex;
  `core/canonical`: the filtered-complex convergence owners on
    `firstDoubleComplexFilteredComplex K` and `secondDoubleComplexFilteredComplex K`;
  `bridge/view`: the two canonical filtered-complex constructions on `Tot(K)`.

This item is recall-only: once the filtered-complex model is fixed, the chapter's canonical
filtered-complex convergence owners already express exactly the textbook notions. -/

section First

variable (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]

/- Definition 12.25.2 (1): for the canonical first filtered complex on `Tot(K)`, weak
convergence of the first spectral sequence to `H^*(Tot(K))` is recalled canonically by
`(firstDoubleComplexFilteredComplex K).weaklyConvergesToCohomology`. -/
#check (firstDoubleComplexFilteredComplex K).weaklyConvergesToCohomology

/- Definition 12.25.2 (2): for the same canonical first filtered complex, abutment of the first
spectral sequence to `H^*(Tot(K))` is recalled canonically by
`(firstDoubleComplexFilteredComplex K).abutsToCohomology`. -/
#check (firstDoubleComplexFilteredComplex K).abutsToCohomology

variable (E : CohomologicalSpectralSequence 𝒜 0)
variable [IsAssociatedToFilteredComplex (firstDoubleComplexFilteredComplex K) E]

/- Definition 12.25.2 (3): for an associated spectral sequence `E` of the canonical first
filtered complex, convergence to `H^*(Tot(K))` is recalled canonically by
`(firstDoubleComplexFilteredComplex K).convergesToCohomology E`. -/
#check (firstDoubleComplexFilteredComplex K).convergesToCohomology E

end First

section Second

variable (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]

/- Definition 12.25.2 (4): for the canonical second filtered complex on `Tot(K)`, weak
convergence of the second spectral sequence to `H^*(Tot(K))` is recalled canonically by
`(secondDoubleComplexFilteredComplex K).weaklyConvergesToCohomology`. -/
#check (secondDoubleComplexFilteredComplex K).weaklyConvergesToCohomology

/- Definition 12.25.2 (5): for the same canonical second filtered complex, abutment of the
second spectral sequence to `H^*(Tot(K))` is recalled canonically by
`(secondDoubleComplexFilteredComplex K).abutsToCohomology`. -/
#check (secondDoubleComplexFilteredComplex K).abutsToCohomology

variable (E : CohomologicalSpectralSequence 𝒜 0)
variable [IsAssociatedToFilteredComplex (secondDoubleComplexFilteredComplex K) E]

/- Definition 12.25.2 (6): for an associated spectral sequence `E` of the canonical second
filtered complex, convergence to `H^*(Tot(K))` is recalled canonically by
`(secondDoubleComplexFilteredComplex K).convergesToCohomology E`. -/
#check (secondDoubleComplexFilteredComplex K).convergesToCohomology E

end Second

end CategoryTheory

/-! ### Lemma_12_25_3 (from Chap12) -/
open CategoryTheory ComplexShape
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open scoped HomologicalComplex₂

noncomputable section

universe u v

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜]

/-- The finiteness hypothesis on a cohomological double complex: on each total degree `n`, only
finitely many terms `K^{p,n-p}` are nonzero. -/
def doubleComplexHasFiniteAntidiagonalSupport
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) : Prop :=
  ∀ n : ℤ, { p : ℤ | ¬ IsZero ((K.X p).X (n - p)) }.Finite

end

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [CategoryWithHomology 𝒜]
  [LocallySmall 𝒜] [WellPowered 𝒜] [HasWidePullbacks 𝒜] [HasCoproducts 𝒜] [InitialMonoClass 𝒜]

local notation "FilteredComplex" => CategoryTheory.FilteredComplex 𝒜

/- Domain-style sampling for Lemma `12.25.3`.
- primary domain: cohomological double complexes, their total complexes, and the two filtered
  complexes realizing the standard first and second filtrations on `Tot(K^{•,•})`;
- sampled owner/canonical declarations in this domain:
  `HomologicalComplex₂.HasTotal`,
  `HomologicalComplex₂.total`,
  `FilteredObject`,
  `FilteredComplex.underlying`,
  `IsAssociatedToFilteredComplex`,
  `FilteredComplex.convergesToCohomology`;
- best owner abstraction: the actual first and second filtered complexes on `Tot(K)`, exposed
  below as `firstDoubleComplexFilteredComplex K` and `secondDoubleComplexFilteredComplex K`;
- primitive data: a double complex `K`, its total complex, and the degreewise filtration stages
  obtained as the images of the partial antidiagonal coproduct maps;
- derived API: finite-filtration consequences from finite antidiagonal support, boundedness of an
  associated spectral sequence, finiteness of the induced cohomology filtration, convergence, and
  the weak-LinearRepresentations_Serre_1977 consequence for total cohomology;
- source/core/bridge triage:
  `source-facing`: the finiteness hypothesis on the antidiagonal support and the eight conclusions
    of the lemma, together with the first and second filtrations on `Tot(K)`;
  `core/canonical`: `HomologicalComplex₂.total`, `FilteredComplex.underlying`,
    `IsAssociatedToFilteredComplex`, `CohomologicalSpectralSequence.IsBounded`, and
    `FilteredComplex.convergesToCohomology`;
  `bridge/view`: the degreewise antidiagonal coproduct maps whose images define the filtration
    stages.

The correct public layer here is therefore the actual filtered-complex owners on `Tot(K)`, not a
wrapper predicate around an arbitrary filtered-complex model. -/

private abbrev TailIndices (p : ℤ) := {i : ℤ // p ≤ i}

private noncomputable def firstDoubleComplexFiltrationMap
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] (n p : ℤ) :
    ∐ (fun i : TailIndices p ↦ (K.X i.1).X (n - i.1)) ⟶ (Tot(K)).X n :=
  Limits.Sigma.desc fun i : TailIndices p ↦
    K.ιTotal (up ℤ) i.1 (n - i.1) n (by
      change i.1 + (n - i.1) = n
      omega)

private noncomputable def secondDoubleComplexFiltrationMap
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] (n p : ℤ) :
    ∐ (fun i : TailIndices p ↦ (K.X (n - i.1)).X i.1) ⟶ (Tot(K)).X n :=
  Limits.Sigma.desc fun i : TailIndices p ↦
    K.ιTotal (up ℤ) (n - i.1) i.1 n (by
      change (n - i.1) + i.1 = n
      omega)

private noncomputable abbrev firstDoubleComplexFiltrationStage
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] (n p : ℤ) :
    Subobject ((Tot(K)).X n) :=
  imageSubobject (firstDoubleComplexFiltrationMap K n p)

private noncomputable abbrev secondDoubleComplexFiltrationStage
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] (n p : ℤ) :
    Subobject ((Tot(K)).X n) :=
  imageSubobject (secondDoubleComplexFiltrationMap K n p)

private noncomputable def firstDoubleComplexFilteredObject
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] (n : ℤ) :
    FilteredObject 𝒜 where
  obj := (Tot(K)).X n
  filtration :=
    { toFun := firstDoubleComplexFiltrationStage K n
      monotone' := by
        intro p q hpq
        sorry }

private noncomputable def secondDoubleComplexFilteredObject
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] (n : ℤ) :
    FilteredObject 𝒜 where
  obj := (Tot(K)).X n
  filtration :=
    { toFun := secondDoubleComplexFiltrationStage K n
      monotone' := by
        intro p q hpq
        sorry }

/-- The filtered complex on `Tot(K^{\bullet,\bullet})` defined by the first filtration
`F_I^p Tot^n(K) = \operatorname{im}(\bigoplus_{i \ge p} K^{i,n-i} \to Tot^n(K))`. -/
noncomputable def firstDoubleComplexFilteredComplex
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] :
    FilteredComplex :=
  { X := firstDoubleComplexFilteredObject K
    d i j :=
      { hom := (Tot(K)).d i j
        preserves := by
          intro p
          sorry }
    shape i j hij := by
      exact FilteredObject.forget.map_injective ((Tot(K)).shape i j hij)
    d_comp_d' i j k hij hjk := by
      exact FilteredObject.forget.map_injective ((Tot(K)).d_comp_d' i j k hij hjk) }

/-- The filtered complex on `Tot(K^{\bullet,\bullet})` defined by the second filtration
`F_{II}^p Tot^n(K) = \operatorname{im}(\bigoplus_{j \ge p} K^{n-j,j} \to Tot^n(K))`. -/
noncomputable def secondDoubleComplexFilteredComplex
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] :
    FilteredComplex :=
  { X := secondDoubleComplexFilteredObject K
    d i j :=
      { hom := (Tot(K)).d i j
        preserves := by
          intro p
          sorry }
    shape i j hij := by
      exact FilteredObject.forget.map_injective ((Tot(K)).shape i j hij)
    d_comp_d' i j k hij hjk := by
      exact FilteredObject.forget.map_injective ((Tot(K)).d_comp_d' i j k hij hjk) }

omit [CategoryWithHomology 𝒜] [LocallySmall 𝒜] [WellPowered 𝒜] [HasWidePullbacks 𝒜]
  [InitialMonoClass 𝒜] in
@[simp] theorem firstDoubleComplexFilteredComplex_underlying
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] :
    (firstDoubleComplexFilteredComplex K).underlying = Tot(K) := rfl

omit [CategoryWithHomology 𝒜] [LocallySmall 𝒜] [WellPowered 𝒜] [HasWidePullbacks 𝒜]
  [InitialMonoClass 𝒜] in
@[simp] theorem secondDoubleComplexFilteredComplex_underlying
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] :
    (secondDoubleComplexFilteredComplex K).underlying = Tot(K) := rfl

-- Proof sketch: on total degree `n`, finite antidiagonal support makes the tail-image filtration
-- on `Tot^n(K)` eventually equal to the whole antidiagonal sum and eventually zero.
/-- Finite antidiagonal support on `K` makes the first filtration on `Tot(K)` finite in each
degree. -/
theorem firstDoubleComplexFilteredComplex_hasFiniteFiltrations_of_finiteAntidiagonalSupport
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]
    (hfin : doubleComplexHasFiniteAntidiagonalSupport K) :
    (firstDoubleComplexFilteredComplex K).HasFiniteFiltrations := sorry

-- Proof sketch: the same finite antidiagonal support controls the row-tail filtration defining
-- the second filtration on `Tot(K)`.
/-- Finite antidiagonal support on `K` makes the second filtration on `Tot(K)` finite in each
degree. -/
theorem secondDoubleComplexFilteredComplex_hasFiniteFiltrations_of_finiteAntidiagonalSupport
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]
    (hfin : doubleComplexHasFiniteAntidiagonalSupport K) :
    (secondDoubleComplexFilteredComplex K).HasFiniteFiltrations := sorry

-- Proof sketch: finite support on each antidiagonal makes the initial page of the first spectral
-- sequence finite on every total degree, so the associated filtered-complex spectral sequence is
-- bounded by the filtered-complex criterion of Lemma `12.24.11`.
/-- Lemma 12.25.3 (1): if each antidiagonal of the double complex has only finitely many nonzero
terms, then the first spectral sequence associated to `K^{\bullet,\bullet}` is bounded. -/
theorem firstDoubleComplex_associatedSpectralSequence_isBounded_of_finiteAntidiagonalSupport
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]
    (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex (firstDoubleComplexFilteredComplex K) E]
    (hfin : doubleComplexHasFiniteAntidiagonalSupport K) :
    CohomologicalSpectralSequence.IsBounded E := sorry

-- Proof sketch: the same finiteness hypothesis is invariant under exchanging the two indices, so
-- the second spectral sequence is bounded for the identical reason as the first.
/-- Lemma 12.25.3 (2): if each antidiagonal of the double complex has only finitely many nonzero
terms, then the second spectral sequence associated to `K^{\bullet,\bullet}` is bounded. -/
theorem secondDoubleComplex_associatedSpectralSequence_isBounded_of_finiteAntidiagonalSupport
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]
    (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex (secondDoubleComplexFilteredComplex K) E]
    (hfin : doubleComplexHasFiniteAntidiagonalSupport K) :
    CohomologicalSpectralSequence.IsBounded E := sorry

-- Proof sketch: identify the first filtration `F_I` on `H^n(Tot(K))` with the cohomology
-- filtration induced by the first filtered complex attached to `K`, then apply the finite
-- filtration criterion coming from finite antidiagonal support.
/-- Lemma 12.25.3 (3): under the same finiteness hypothesis, the first filtration `F_I` on each
`H^n(\mathrm{Tot}(K^{\bullet,\bullet}))` is finite. In this file it is recorded by the canonical
filtered-complex owner `firstDoubleComplexFilteredComplex K`. -/
theorem firstDoubleComplex_cohomologyFiltrationIsFinite_of_finiteAntidiagonalSupport
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]
    (hfin : doubleComplexHasFiniteAntidiagonalSupport K) :
    (firstDoubleComplexFilteredComplex K).cohomologyFiltrationIsFinite := sorry

-- Proof sketch: repeat the preceding argument for the second filtration `F_{II}` coming from the
-- second filtered-complex realization of the total complex.
/-- Lemma 12.25.3 (4): under the same finiteness hypothesis, the second filtration `F_{II}` on
each `H^n(\mathrm{Tot}(K^{\bullet,\bullet}))` is finite. In this file it is recorded by the
canonical filtered-complex owner `secondDoubleComplexFilteredComplex K`. -/
theorem secondDoubleComplex_cohomologyFiltrationIsFinite_of_finiteAntidiagonalSupport
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]
    (hfin : doubleComplexHasFiniteAntidiagonalSupport K) :
    (secondDoubleComplexFilteredComplex K).cohomologyFiltrationIsFinite := sorry

-- Proof sketch: boundedness together with finiteness of the first induced cohomology filtration
-- gives convergence of the first associated spectral sequence to the cohomology of the total
-- complex.
/-- Lemma 12.25.3 (5): under the same finiteness hypothesis, the first spectral sequence
associated to `K^{\bullet,\bullet}` converges to the cohomology of `\mathrm{Tot}(K^{\bullet,
\bullet})`. In this file the convergence package is recorded by
`(firstDoubleComplexFilteredComplex K).convergesToCohomology E` for an associated spectral
sequence `E` of the canonical first filtration. -/
theorem firstDoubleComplex_convergesToTotalCohomology_of_finiteAntidiagonalSupport
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]
    (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex (firstDoubleComplexFilteredComplex K) E]
    (hfin : doubleComplexHasFiniteAntidiagonalSupport K) :
    (firstDoubleComplexFilteredComplex K).convergesToCohomology E := sorry

-- Proof sketch: apply the same filtered-complex convergence argument to the second filtration on
-- the total complex.
/-- Lemma 12.25.3 (6): under the same finiteness hypothesis, the second spectral sequence
associated to `K^{\bullet,\bullet}` converges to the cohomology of `\mathrm{Tot}(K^{\bullet,
\bullet})`. In this file the convergence package is recorded by
`(secondDoubleComplexFilteredComplex K).convergesToCohomology E` for an associated spectral
sequence `E` of the canonical second filtration. -/
theorem secondDoubleComplex_convergesToTotalCohomology_of_finiteAntidiagonalSupport
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]
    (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex (secondDoubleComplexFilteredComplex K) E]
    (hfin : doubleComplexHasFiniteAntidiagonalSupport K) :
    (secondDoubleComplexFilteredComplex K).convergesToCohomology E := sorry

-- Proof sketch: boundedness lets one pass from a page `E_r` lying in a weak LinearRepresentations_Serre_1977 subcategory to
-- the limiting graded pieces of the first filtration; finiteness of that filtration then implies
-- that the total cohomology objects belong to the same weak LinearRepresentations_Serre_1977 subcategory by closure under
-- extensions.
/-- Lemma 12.25.3 (7): let `\mathcal C` be a weak LinearRepresentations_Serre_1977 subcategory of `\mathcal A`. If for some
page `r` every term of the first spectral sequence associated to `K^{\bullet,\bullet}` lies in
`\mathcal C`, then every cohomology object `H^n(\mathrm{Tot}(K^{\bullet,\bullet}))` lies in
`\mathcal C`. -/
theorem firstDoubleComplex_totalCohomologyObject_mem_of_page_mem_of_finiteAntidiagonalSupport
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]
    (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex (firstDoubleComplexFilteredComplex K) E]
    (P : ObjectProperty 𝒜) [IsWeakSerreClass P]
    (hfin : doubleComplexHasFiniteAntidiagonalSupport K)
    (r : ℤ) (hr : 0 ≤ r)
    (hpage : ∀ p q : ℤ, P ((E.page r hr).X (p, q))) :
    ∀ n : ℤ, P ((Tot(K)).homology n) := sorry

-- Proof sketch: the same argument applied to the second filtration shows that a page of the
-- second spectral sequence lying in a weak LinearRepresentations_Serre_1977 subcategory forces the cohomology of the total
-- complex to lie there as well.
/-- Lemma 12.25.3 (8): let `\mathcal C` be a weak LinearRepresentations_Serre_1977 subcategory of `\mathcal A`. If for some
page `r` every term of the second spectral sequence associated to `K^{\bullet,\bullet}` lies in
`\mathcal C`, then every cohomology object `H^n(\mathrm{Tot}(K^{\bullet,\bullet}))` lies in
`\mathcal C`. -/
theorem secondDoubleComplex_totalCohomologyObject_mem_of_page_mem_of_finiteAntidiagonalSupport
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]
    (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex (secondDoubleComplexFilteredComplex K) E]
    (P : ObjectProperty 𝒜) [IsWeakSerreClass P]
    (hfin : doubleComplexHasFiniteAntidiagonalSupport K)
    (r : ℤ) (hr : 0 ≤ r)
    (hpage : ∀ p q : ℤ, P ((E.page r hr).X (p, q))) :
    ∀ n : ℤ, P ((Tot(K)).homology n) := sorry

end

end CategoryTheory

/-! ### Lemma_12_25_4 (from Chap12) -/
open CategoryTheory Limits ComplexShape HomologicalComplex HomologicalComplex₂
open scoped HomologicalComplex₂

noncomputable section

universe v u

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [HasZeroObject 𝒜]

local notation "ev₀" => HomologicalComplex.eval 𝒜 (up ℤ) (0 : ℤ)

/- Domain-style sampling for Lemma 12.25.4:
- primary domain: cohomological double complexes, their total complexes, and quasi-isomorphism
  criteria detected on one filtration line;
- sampled owner declarations:
  `HomologicalComplex₂.total`,
  `HomologicalComplex₂.totalFlipIso`,
  `HomologicalComplex₂.flip`,
  `HomologicalComplex.ExactAt`,
  `doubleComplexHasFiniteAntidiagonalSupport`,
  `QuasiIso`;
- best owner abstraction: the canonical comparison morphisms from the zero row or zero column into
  the owner total complex `Tot(A)`;
- primitive data: a morphism into the zero row `A^{•,0}` or zero column `A^{0,•}`, together with
  the corresponding cycle condition on its components;
- derived API: the induced maps to the column or row cycles and the resulting `QuasiIso`
  criterion under finite antidiagonal support and exactness off the chosen axis;
- source/core/bridge triage:
  `source-facing`: the comparison maps from the zero row or zero column into
    `Tot(A^{•,•})` and the two quasi-isomorphism theorems;
  `core/canonical`: `Tot(_)`, `HomologicalComplex.ExactAt`, `QuasiIso`, and
    `doubleComplexHasFiniteAntidiagonalSupport`, together with the flip symmetry of totalization;
  `bridge/view`: `HomologicalComplex₂.zeroColumnIsoZeroRowFlip`,
    `doubleComplexZeroRowCyclesMap`, and `doubleComplexZeroColumnCyclesMap`, which record the
    identifications of `K^p` or `K^q` with the corresponding cycles on the chosen axis.

The public theorems below should therefore be stated directly in terms of these owners. In each
orientation, exactness on the negative side is derived from the vanishing hypothesis, so the
nontrivial primitive exactness input is only the positive-degree part away from the chosen axis.
-/

namespace HomologicalComplex₂

/-- The zeroth column `A^{0,\bullet}` is canonically the zeroth row of the flipped bicomplex
`(A.flip)^{\bullet,0}`. -/
noncomputable def zeroColumnIsoZeroRowFlip
    (A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) :
    A.X 0 ≅ ((ev₀).mapHomologicalComplex (up ℤ)).obj A.flip :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ Iso.refl _)
    (fun p q hpq ↦ by
      have h : p + 1 = q := by
        simpa [ComplexShape.up, ComplexShape.up'] using hpq
      subst h
      simp)

end HomologicalComplex₂

/-- The degree-`n` component of the canonical map `K^\bullet ⟶ \mathrm{Tot}(A^{\bullet,\bullet})`
attached to a morphism `α : K^\bullet ⟶ A^{\bullet,0}`. -/
noncomputable def doubleComplexZeroRowToTotalComponent
    {K : CochainComplex 𝒜 ℤ} {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (α : K ⟶ ((ev₀).mapHomologicalComplex (up ℤ)).obj A) (n : ℤ) :
    K.X n ⟶ (Tot(A)).X n :=
  α.f n ≫ A.ιTotal (up ℤ) n 0 n (Int.add_zero n)

-- Proof sketch: expand the total differential as the sum of its horizontal and vertical parts.
-- The horizontal part is the row differential and is handled by the cochain-map condition on `α`;
-- the vertical part vanishes because each `α^p` lands in the cycles of the `p`-th column.
/-- The row-zero comparison components define a morphism of cochain complexes into the total
complex. -/
theorem doubleComplexZeroRowToTotal_comm
    {K : CochainComplex 𝒜 ℤ} {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (α : K ⟶ ((ev₀).mapHomologicalComplex (up ℤ)).obj A)
    (hαcycles : ∀ p : ℤ, α.f p ≫ (A.X p).d 0 1 = 0)
    (n n' : ℤ) (_ : (up ℤ).Rel n n') :
    doubleComplexZeroRowToTotalComponent α n ≫ (Tot(A)).d n n' =
      K.d n n' ≫ doubleComplexZeroRowToTotalComponent α n' := sorry

/-- The canonical morphism `K^\bullet ⟶ \mathrm{Tot}(A^{\bullet,\bullet})` induced by a morphism
`α : K^\bullet ⟶ A^{\bullet,0}` whose components land in the cycles of the columns. -/
noncomputable def doubleComplexZeroRowToTotal
    {K : CochainComplex 𝒜 ℤ} {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (α : K ⟶ ((ev₀).mapHomologicalComplex (up ℤ)).obj A)
    (hαcycles : ∀ p : ℤ, α.f p ≫ (A.X p).d 0 1 = 0) :
    K ⟶ Tot(A) where
  f := doubleComplexZeroRowToTotalComponent α
  comm' := doubleComplexZeroRowToTotal_comm α hαcycles

/-- The canonical morphism from the zeroth column into the zeroth row of the flipped bicomplex. -/
noncomputable def doubleComplexZeroColumnToZeroRowFlip
    {K : CochainComplex 𝒜 ℤ} {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (α : K ⟶ A.X 0) :
    K ⟶ ((ev₀).mapHomologicalComplex (up ℤ)).obj A.flip :=
  α ≫ (A.zeroColumnIsoZeroRowFlip).hom

/-- The zero-column cycle condition is exactly the row-zero cycle condition on the flipped
bicomplex. -/
theorem doubleComplexZeroColumnToZeroRowFlip_comp_d
    {K : CochainComplex 𝒜 ℤ} {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (α : K ⟶ A.X 0)
    (hαcycles : ∀ q : ℤ, α.f q ≫ (A.d 0 1).f q = 0) :
    ∀ q : ℤ, (doubleComplexZeroColumnToZeroRowFlip α).f q ≫ (A.flip.X q).d 0 1 = 0 := by
  sorry

/-- The canonical morphism `K^\bullet ⟶ \mathrm{Tot}(A^{\bullet,\bullet})` induced by a morphism
`α : K^\bullet ⟶ A^{0,\bullet}` whose components land in the cycles of the rows. -/
noncomputable def doubleComplexZeroColumnToTotal
    {K : CochainComplex 𝒜 ℤ} {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (α : K ⟶ A.X 0)
    (hαcycles : ∀ q : ℤ, α.f q ≫ (A.d 0 1).f q = 0) :
    K ⟶ Tot(A) :=
  doubleComplexZeroRowToTotal
      (doubleComplexZeroColumnToZeroRowFlip α)
      (doubleComplexZeroColumnToZeroRowFlip_comp_d α hαcycles) ≫
    (A.totalFlipIso (up ℤ)).hom

end

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [Abelian 𝒜] [CategoryWithHomology 𝒜]

local notation "ev₀" => HomologicalComplex.eval 𝒜 (up ℤ) (0 : ℤ)

/-- The morphism from `K^p` to the cycles `\ker(d_2^{p,0})` induced by the component
`α^p : K^p ⟶ A^{p,0}`. -/
noncomputable def doubleComplexZeroRowCyclesMap
    {K : CochainComplex 𝒜 ℤ} {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (α : K ⟶ ((ev₀).mapHomologicalComplex (up ℤ)).obj A)
    (hαcycles : ∀ p : ℤ, α.f p ≫ (A.X p).d 0 1 = 0) (p : ℤ) :
    K.X p ⟶ (A.X p).cycles 0 :=
  (A.X p).liftCycles' (α.f p) 1 rfl (hαcycles p)

/-- The morphism from `K^q` to the cycles `\ker(d_1^{0,q})` induced by the component
`α^q : K^q ⟶ A^{0,q}`. -/
noncomputable def doubleComplexZeroColumnCyclesMap
    {K : CochainComplex 𝒜 ℤ} {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (α : K ⟶ A.X 0)
    (hαcycles : ∀ q : ℤ, α.f q ≫ (A.d 0 1).f q = 0) (q : ℤ) :
    K.X q ⟶ (A.flip.X q).cycles 0 :=
  doubleComplexZeroRowCyclesMap
      (doubleComplexZeroColumnToZeroRowFlip α)
      (doubleComplexZeroColumnToZeroRowFlip_comp_d α hαcycles) q

-- Proof sketch: apply the second spectral sequence of the double complex. The hypotheses imply
-- that the `E₁`-page is concentrated on the row `q = 0`, where it identifies with `K^\bullet`
-- via the maps to cycles. The vanishing hypothesis makes the negative rows automatically exact,
-- so only positive vertical degrees need to be assumed exact. Finite antidiagonal support gives
-- convergence to
-- `H^\ast(\mathrm{Tot}(A^{\bullet,\bullet}))`, so the induced map from `K^\bullet` to the total
-- complex is a quasi-isomorphism.
/-- Lemma 12.25.4: if `A^{p,q}` vanishes for `q < 0`, every column `A^{p,\bullet}` is exact in
every positive degree `q > 0`, and a morphism `α : K^\bullet ⟶ A^{\bullet,0}` identifies each
`K^p` with the cycles `\ker(d_2^{p,0})`, then under finite antidiagonal support the induced
comparison map `K^\bullet ⟶ \mathrm{Tot}(A^{\bullet,\bullet})` is a quasi-isomorphism. -/
theorem zeroRowToTotal_quasiIso_of_exact_columns_and_cycles
    {K : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (hfin : doubleComplexHasFiniteAntidiagonalSupport A)
    (hvanish : ∀ p q : ℤ, q < 0 → IsZero ((A.X p).X q))
    (hexact : ∀ p q : ℤ, 0 < q → (A.X p).ExactAt q)
    (α : K ⟶ ((ev₀).mapHomologicalComplex (up ℤ)).obj A)
    (hαcycles : ∀ p : ℤ, α.f p ≫ (A.X p).d 0 1 = 0)
    (hαiso : ∀ p : ℤ, IsIso (doubleComplexZeroRowCyclesMap α hαcycles p)) :
    QuasiIso (doubleComplexZeroRowToTotal α hαcycles) := sorry

private theorem doubleComplexHasFiniteAntidiagonalSupport_flip
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (hfin : doubleComplexHasFiniteAntidiagonalSupport A) :
    doubleComplexHasFiniteAntidiagonalSupport A.flip := by
  sorry

-- Proof sketch: apply the previous theorem to the flipped bicomplex. The hypotheses become the
-- zero-row hypotheses for `A.flip`, and `A.totalFlipIso (up ℤ)` transports the resulting
-- quasi-isomorphism back to `Tot(A)`.
/-- Lemma 12.25.4 (moreover): if `A^{p,q}` vanishes for `p < 0`, every row `A^{\bullet,q}` is
exact in every positive degree `p > 0`, and a morphism `α : K^\bullet ⟶ A^{0,\bullet}`
identifies each `K^q` with the cycles `\ker(d_1^{0,q})`, then under finite antidiagonal support
the induced comparison map `K^\bullet ⟶ \mathrm{Tot}(A^{\bullet,\bullet})` is a
quasi-isomorphism. -/
theorem zeroColumnToTotal_quasiIso_of_exact_rows_and_cycles
    {K : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (hfin : doubleComplexHasFiniteAntidiagonalSupport A)
    (hvanish : ∀ p q : ℤ, p < 0 → IsZero ((A.X p).X q))
    (hexact : ∀ p q : ℤ, 0 < p → (A.flip.X q).ExactAt p)
    (α : K ⟶ A.X 0)
    (hαcycles : ∀ q : ℤ, α.f q ≫ (A.d 0 1).f q = 0)
    (hαiso : ∀ q : ℤ, IsIso (doubleComplexZeroColumnCyclesMap α hαcycles q)) :
    QuasiIso (doubleComplexZeroColumnToTotal α hαcycles) := by
  let α' := doubleComplexZeroColumnToZeroRowFlip α
  let hα'cycles := doubleComplexZeroColumnToZeroRowFlip_comp_d α hαcycles
  have hvanishFlip : ∀ p q : ℤ, q < 0 → IsZero ((A.flip.X p).X q) := by
    intro p q hq
    simpa using hvanish q p hq
  have hexactFlip : ∀ p q : ℤ, 0 < q → (A.flip.X p).ExactAt q := by
    intro p q hq
    simpa using hexact q p hq
  have hα'iso : ∀ p : ℤ, IsIso (doubleComplexZeroRowCyclesMap α' hα'cycles p) := by
    intro p
    simpa [doubleComplexZeroColumnCyclesMap, α', hα'cycles] using hαiso p
  letI : QuasiIso (doubleComplexZeroRowToTotal α' hα'cycles) :=
    zeroRowToTotal_quasiIso_of_exact_columns_and_cycles
      (doubleComplexHasFiniteAntidiagonalSupport_flip hfin)
      hvanishFlip hexactFlip α' hα'cycles hα'iso
  simpa [doubleComplexZeroColumnToTotal, α', hα'cycles] using
    (inferInstance : QuasiIso (doubleComplexZeroRowToTotal α' hα'cycles ≫
      (A.totalFlipIso (up ℤ)).hom))

end

end

/-! ### Lemma_12_25_5 (from Chap12) -/
open CategoryTheory ComplexShape HomologicalComplex HomologicalComplex₂
open scoped HomologicalComplex₂

universe v u

noncomputable section

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [CategoryTheory.Limits.HasZeroObject 𝒜]

local notation "single₀" => CochainComplex.singleFunctor (CochainComplex 𝒜 ℤ) (0 : ℤ)

/- Domain-style sampling for Lemma 12.25.5:
- primary domain: cohomological bicomplexes, total complexes, and homotopy equivalences;
- sampled owner declarations:
  `doubleComplexZeroColumnToTotal`,
  `HomologicalComplex₂.total`,
  `HomologicalComplex₂.totalFunctor`,
  `Functor.mapHomotopyEquiv`,
  `HomotopyEquiv`;
- source/core/bridge triage:
  `source-facing`: the comparison map induced by `a : M^•[0] ⟶ A^{•,•}`;
  `core/canonical`: `Tot(A)` / `totalFunctor 𝒜 (up ℤ) (up ℤ) (up ℤ)` together with
    `doubleComplexZeroColumnToTotal` and `Functor.mapHomotopyEquiv`;
  `bridge/view`: the degree-zero column map extracted from `a`.

Primitive data:
- a bicomplex morphism `a : (single₀).obj M ⟶ A`;
- its degree-zero column map `M^• ⟶ A.X 0`.

Derived API:
- the source-facing comparison map `M^• ⟶ Tot(A)`,
- its compatibility with the owner morphism `total.map`.
-/

/-- The degree-zero column map extracted from `a : M^•[0] ⟶ A^{•,•}`. -/
noncomputable def singleZeroToZeroColumn
    {M : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (a : (single₀).obj M ⟶ A) :
    M ⟶ A.X 0 :=
  (singleObjXSelf (up ℤ) 0 M).inv ≫ a.f 0

/-- The cycle condition on the degree-zero column induced by `a`. -/
private theorem singleZeroToZeroColumn_comp_d
    {M : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (a : (single₀).obj M ⟶ A) :
    ∀ p : ℤ, (singleZeroToZeroColumn a).f p ≫ (A.d 0 1).f p = 0 := by
  sorry

/-- The comparison map `α : M^• ⟶ \mathrm{Tot}(A^{•,•})` attached to a bicomplex morphism
`a : M^•[0] ⟶ A^{•,•}`. -/
noncomputable def singleZeroToTotal
    {M : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (a : (single₀).obj M ⟶ A) :
    M ⟶ Tot(A) :=
  doubleComplexZeroColumnToTotal (singleZeroToZeroColumn a) (singleZeroToZeroColumn_comp_d a)

/-- The source-facing comparison map is functorial in the target bicomplex map, and the
comparison with the owner totalization functor is the canonical map `total.map`. -/
theorem singleZeroToTotal_comp_map
    {M : CochainComplex 𝒜 ℤ}
    {A B : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)] [B.HasTotal (up ℤ)]
    (a : (single₀).obj M ⟶ A) (b : A ⟶ B) :
    singleZeroToTotal (a ≫ b) =
      singleZeroToTotal a ≫ total.map b (up ℤ) := by
  sorry

-- Proof sketch: transport `a` through the owner totalization functor, use
-- `Functor.mapHomotopyEquiv` on a homotopy inverse of `a`, and compare the resulting map
-- `Tot(M^•[0]) ⟶ Tot(A)` with the canonical zero-column comparison `singleZeroToTotal a`.
/-- Lemma 12.25.5: if `a : M^•[0] ⟶ A^{•,•}` is a homotopy equivalence of cohomological
complexes of cochain complexes, then the induced comparison map
`α : M^• ⟶ \mathrm{Tot}(A^{•,•})` coming from the degree-zero column `M^• ⟶ A^{0,•}` is a
homotopy equivalence. -/
theorem singleZeroToTotal_homotopyEquivalence_of_homotopyEquivalence
    {M : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    {a : (single₀).obj M ⟶ A}
    (ha : homotopyEquivalences (CochainComplex 𝒜 ℤ) (up ℤ) a) :
    homotopyEquivalences 𝒜 (up ℤ) (singleZeroToTotal a) := sorry

end
