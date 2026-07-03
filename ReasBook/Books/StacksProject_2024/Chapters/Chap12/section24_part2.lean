import Mathlib
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_12_24_9 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜]

/-
Domain-style sampling for Definition `12.24.9`.
- primary domain: convergence of the spectral sequence associated to a filtered cochain complex,
  with the extra clause that the induced cohomology filtration is complete in the inverse-limit
  sense;
- sampled owner/canonical declarations in this domain:
  `DecreasingFiltration`,
  `FilteredComplex.inducedCohomologyFiltration`,
  `FilteredComplex.weaklyConvergesToCohomology`,
  `FilteredComplex.abutsToCohomology`,
  `FilteredObject.quotientFunctor`;
- best owner abstraction: for completeness, a single decreasing filtration
  `F : DecreasingFiltration A`, viewed through the canonical filtered-object quotient API; for the
  spectral-sequence clauses, the filtered-complex owner `K : FilteredComplex 𝒜` together with its
  induced cohomology filtrations and the existing chapter owners for weak convergence and
  abutment;
- primitive data: a filtered complex `K`, a chosen associated spectral sequence `E`, and for the
  completeness clause only a decreasing filtration `F` on a single object;
- derived API: the completeness predicate on `F`, the completeness predicate on the induced
  cohomology filtrations of `K`, the chosen-`E` bridge predicates for weak convergence and
  abutment, and the final convergence predicate for `E`;
- source/core/bridge triage:
  `source-facing`: `DecreasingFiltration.IsComplete`,
    `FilteredComplex.cohomologyFiltrationIsComplete`,
    `FilteredComplex.convergesToCohomology`;
  `core/canonical`: `DecreasingFiltration`, `FilteredComplex.inducedCohomologyFiltration`,
    `FilteredComplex.weaklyConvergesToCohomology`,
    `FilteredComplex.abutsToCohomology`,
    `FilteredObject.quotientFunctor`;
  `bridge/view`: the quotient inverse system `A / F^p A`, its canonical cone from `A`, and the
    chosen-`E` comparison predicates that keep Definition `12.24.9 (3)` tied to the same
    associated spectral sequence.

The completeness clause is genuine new source-facing content here, but its owner is only the
quotient tower of a single decreasing filtration, so it should live in the weakest quotient-level
context and reuse the existing filtered-object quotient owner rather than restating pointwise
quotient objects as new public API. -/

section CompleteFiltration

variable [HasZeroMorphisms 𝒜] [HasCokernels 𝒜]

namespace DecreasingFiltration

/-- The filtered-object owner carrying the ambient object together with its decreasing
filtration. -/
private abbrev toFilteredObject {A : 𝒜} (F : DecreasingFiltration A) : FilteredObject 𝒜 :=
  ⟨A, F⟩

/-- The quotient object `A / F^p A`, expressed through the canonical filtered-object owner. -/
private noncomputable abbrev quotientObj {A : 𝒜} (F : DecreasingFiltration A)
    (p : ℤᵒᵖ) : 𝒜 :=
  (toFilteredObject F).quotient (unop p)

private noncomputable def quotientSystemMap {A : 𝒜} (F : DecreasingFiltration A)
    {p q : ℤᵒᵖ} (f : p ⟶ q) : quotientObj F p ⟶ quotientObj F q :=
  by
    change cokernel (F.obj (unop p)).arrow ⟶ cokernel (F.obj (unop q)).arrow
    exact subobjectQuotientMap (F.antitone_obj (leOfHom f.unop))

-- Proof sketch: for the identity morphism of `op p`, the induced inclusion of filtration stages is
-- the identity `F^p A ≤ F^p A`, so the corresponding quotient map is the identity on `A / F^p A`.
private theorem quotientSystemMap_id {A : 𝒜} (F : DecreasingFiltration A) (p : ℤᵒᵖ) :
    quotientSystemMap F (𝟙 p) = 𝟙 (quotientObj F p) := sorry

-- Proof sketch: both sides are the canonical quotient map induced by the composite inclusion
-- `F^r A ≤ F^q A ≤ F^p A`; compare them using the universal property of cokernels.
private theorem quotientSystemMap_comp {A : 𝒜} (F : DecreasingFiltration A)
    {p q r : ℤᵒᵖ} (f : p ⟶ q) (g : q ⟶ r) :
    quotientSystemMap F (f ≫ g) = quotientSystemMap F f ≫ quotientSystemMap F g := sorry

private noncomputable def quotientSystem {A : 𝒜} (F : DecreasingFiltration A) : ℤᵒᵖ ⥤ 𝒜 where
  obj := quotientObj F
  map f := quotientSystemMap F f
  map_id p := quotientSystemMap_id F p
  map_comp f g := quotientSystemMap_comp F f g

private noncomputable def quotientSystemCone {A : 𝒜} (F : DecreasingFiltration A) :
    Cone (quotientSystem F) where
  pt := A
  π :=
    { app := fun p ↦ by
        change A ⟶ cokernel (F.obj (unop p)).arrow
        exact cokernel.π (F.obj (unop p)).arrow
      naturality := fun p q f ↦ by
        let h := F.antitone_obj (leOfHom f.unop)
        have hzero : (F.obj (unop p)).arrow ≫ cokernel.π (F.obj (unop q)).arrow = 0 := by
          calc
            (F.obj (unop p)).arrow ≫ cokernel.π (F.obj (unop q)).arrow =
                Subobject.ofLE (F.obj (unop p)) (F.obj (unop q)) h ≫
                  (F.obj (unop q)).arrow ≫ cokernel.π (F.obj (unop q)).arrow := by
                    rw [← Subobject.ofLE_arrow h, Category.assoc]
            _ = 0 := by simp
        change 𝟙 A ≫ cokernel.π (F.obj (unop q)).arrow =
          cokernel.π (F.obj (unop p)).arrow ≫ subobjectQuotientMap h
        simpa [Category.id_comp, subobjectQuotientMap] using
          (cokernel.π_desc (F.obj (unop p)).arrow (cokernel.π (F.obj (unop q)).arrow) hzero).symm }

/-- A decreasing filtration is complete if the canonical cone from the ambient object to its
quotient inverse system `A / F^p A` is a limit cone. -/
def IsComplete {A : 𝒜} (F : DecreasingFiltration A) : Prop :=
  Nonempty (IsLimit (quotientSystemCone F))

end DecreasingFiltration

end CompleteFiltration

namespace FilteredComplex

section AssociatedSpectralSequence

variable [Abelian 𝒜] [LocallySmall 𝒜] [WellPowered 𝒜] [HasWidePullbacks 𝒜] [HasCoproducts 𝒜]
  [InitialMonoClass 𝒜]

/-- The induced filtration on the cohomology of a filtered complex is complete if every
cohomology object is the inverse limit of its quotient tower by the induced filtration stages. -/
def cohomologyFiltrationIsComplete (K : FilteredComplex 𝒜) : Prop :=
  ∀ n : ℤ, DecreasingFiltration.IsComplete (K.inducedCohomologyFiltration n)

/- Definition 12.24.9 (1): the spectral sequence associated to a filtered complex weakly
converges to `H^*(K^•)` exactly when the owner predicate
`FilteredComplex.weaklyConvergesToCohomology` holds. -/
recall weaklyConvergesToCohomology

/- Definition 12.24.9 (2): the spectral sequence associated to a filtered complex abuts to
`H^*(K^•)` exactly when the owner predicate `FilteredComplex.abutsToCohomology` holds. -/
recall abutsToCohomology

/-- Bridge/view layer: the chosen associated spectral sequence `E` weakly converges to the
cohomology of `K` when its `E_\infty`-terms recover the graded pieces of the induced
cohomology filtration in every bidegree. -/
def weaklyConvergesToCohomologyWith
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [CategoryTheory.IsAssociatedToFilteredComplex K E] : Prop :=
  ∀ n p : ℤ,
    Nonempty
      ((K.inducedCohomologyFiltration n).gradedPiece p ≅
        E.toPageOneSpectralSequence.infinityPage (p, n - p))

/-- Bridge/view layer: the chosen associated spectral sequence `E` abuts to the cohomology of
`K` when that same `E` weakly converges and the induced cohomology filtration is separated and
exhaustive in every degree. -/
def abutsToCohomologyWith
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [CategoryTheory.IsAssociatedToFilteredComplex K E] : Prop :=
  K.weaklyConvergesToCohomologyWith E ∧
    ∀ n : ℤ,
      DecreasingFiltration.IsSeparated (K.inducedCohomologyFiltration n) ∧
        DecreasingFiltration.IsExhaustive (K.inducedCohomologyFiltration n)

/-- Definition 12.24.9 (3): the associated spectral sequence of a filtered complex
converges to `H^*(K^•)` when the chosen associated spectral sequence is regular, it abuts to
cohomology, and each cohomology object is the inverse limit of the quotient tower by its induced
filtration. -/
def convergesToCohomology
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [CategoryTheory.IsAssociatedToFilteredComplex K E] : Prop :=
  CohomologicalSpectralSequence.IsRegular E ∧
    K.abutsToCohomologyWith E ∧
    K.cohomologyFiltrationIsComplete

end AssociatedSpectralSequence

end FilteredComplex
end CategoryTheory

/-! ### Lemma_12_24_10 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

namespace FilteredComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

section

variable [LocallySmall 𝒜] [WellPowered 𝒜]
  [HasWidePullbacks 𝒜] [HasCoproducts 𝒜] [InitialMonoClass 𝒜]
variable (K : FilteredComplex 𝒜)

local notation "HFil" n => inducedCohomologyFiltration K n

private abbrev filtrationStage (n p : ℤ) : Subobject ((K.X n).obj) :=
  (K.X n).filtration.obj p

private abbrev cyclesSubobject (n : ℤ) : Subobject ((K.X n).obj) :=
  kernelSubobject ((K.d n (n + 1)).hom)

private abbrev boundariesSubobject (n : ℤ) : Subobject ((K.X n).obj) :=
  imageSubobject ((K.d (n - 1) n).hom)

/- Domain-style sampling for Lemma `12.24.10`.
- primary domain: weak convergence and abutment for the spectral sequence associated to a filtered
  cochain complex in an abelian category;
- sampled core/canonical declarations:
  `FilteredComplex.inducedCohomologyFiltration`,
  `DecreasingFiltration.IsSeparated`,
  `DecreasingFiltration.IsExhaustive`,
  `SpectralSequence.infinityPage`;
- best owner abstraction: the induced filtration `inducedCohomologyFiltration K n` on
  `H^n(K^•)` together with the canonical limit term
  `E.toPageOneSpectralSequence.infinityPage (p, n - p)`;
- primitive data: the filtered complex `K`, the stage subobjects of `K^{n-1}`, `K^n`, and
  `K^{n+1}`, and an associated spectral sequence `E`;
- derived API: the source-facing pagewise equalities `(12.24.6.2)` and `(12.24.6.1)`, the
  graded-piece / `E_∞` comparison, and the intersection/union criterion for the induced
  cohomology filtration;
- source/core/bridge triage:
  `source-facing`: `weaklyConvergesToCohomology`, `abutsToCohomology`,
    `weakConvergenceCriterion`, `cohomologyFiltrationCriterion`;
  `core/canonical`: `inducedCohomologyFiltration` and `SpectralSequence.infinityPage`;
  `bridge/view`: the representative-level subobject equalities inside `K^n` that compare the
    source formulas to those owner objects.

Only the source-facing predicates and their two bridge criteria stay public here; the auxiliary
comparison and representative wrappers remain internal. -/

/-- The eventual boundary representative
`⋃_r (F^p K^n ∩ im(F^{p-r+1} K^{n-1} ⟶ K^n)) + F^{p+1} K^n`
appearing in equation `(12.24.6.2)`. -/
def eventualBoundaryStep (n p : ℤ) :
    Subobject ((K.X n).obj) :=
  ⨆ r : ℕ,
    (filtrationStage K n p ⊓
        imageSubobject
          ((filtrationStage K (n - 1) (p - r + 1)).arrow ≫ (K.d (n - 1) n).hom)) ⊔
      filtrationStage K n (p + 1)

/-- The eventual cycle representative
`⋂_r (F^p K^n ∩ (d^n)⁻¹(F^{p+r} K^{n+1})) + F^{p+1} K^n`
appearing in equation `(12.24.6.1)`. -/
def eventualCycleStep (n p : ℤ) :
    Subobject ((K.X n).obj) :=
  ⨅ r : ℕ,
    (filtrationStage K n p ⊓
        (Subobject.pullback ((K.d n (n + 1)).hom)).obj
          (filtrationStage K (n + 1) (p + r))) ⊔
      filtrationStage K n (p + 1)

/-- The cycle representative
`(\ker d^n ∩ F^p K^n) + F^{p+1} K^n` for the `p`-th graded piece of cohomology. -/
def cohomologyCycleStep (n p : ℤ) :
    Subobject ((K.X n).obj) :=
  (cyclesSubobject K n ⊓ filtrationStage K n p) ⊔ filtrationStage K n (p + 1)

/-- The boundary representative
`(\operatorname{im} d^{n-1} ∩ F^p K^n) + F^{p+1} K^n` for the `p`-th graded piece of
cohomology. -/
def cohomologyBoundaryStep (n p : ℤ) :
    Subobject ((K.X n).obj) :=
  (boundariesSubobject K n ⊓ filtrationStage K n p) ⊔ filtrationStage K n (p + 1)

/-- The equalities of `(12.24.6.2)` and `(12.24.6.1)` for every degree and every filtration
index. This is the concrete pagewise criterion appearing in Lemma `12.24.10 (1)`. -/
def weakConvergenceCriterion : Prop :=
  ∀ n p : ℤ,
    eventualBoundaryStep K n p = cohomologyBoundaryStep K n p ∧
      cohomologyCycleStep K n p = eventualCycleStep K n p

-- For a chosen associated spectral sequence `E`, weak convergence to cohomology is the
-- identification of each graded piece `gr^p H^n(K^•)` with the antidiagonal limit term
-- `E_∞^{p, n - p}`. This comparison remains internal; the public owner is
-- `weaklyConvergesToCohomology`.
private abbrev weakConvergenceComparison (E : CohomologicalSpectralSequence 𝒜 0) : Prop :=
  ∀ n p : ℤ,
    Nonempty
      ((HFil n).gradedPiece p ≅
        E.toPageOneSpectralSequence.infinityPage (p, n - p))

/-- Definition 12.24.9 (1): the associated spectral sequence of a filtered complex weakly
converges to `H^*(K^•)` when some associated cohomological spectral sequence has
`E_∞^{p, n - p} ≅ gr^p H^n(K^•)` in every bidegree. Lemma `12.24.10 (1)` supplies the equivalent
pagewise criterion `(12.24.6.2)` and `(12.24.6.1)`. -/
def weaklyConvergesToCohomology : Prop :=
  ∃ (E : CohomologicalSpectralSequence 𝒜 0) (_ : IsAssociatedToFilteredComplex K E),
    weakConvergenceComparison K E

-- The representative `\ker(d^n) ∩ F^p K^n + \operatorname{im}(d^{n-1})` of the `p`-th step of
-- the filtration induced on `H^n(K^•)` is only auxiliary here, so it remains internal.
private abbrev cohomologyFiltrationRepresentative (n p : ℤ) :
    Subobject ((K.X n).obj) :=
  (cyclesSubobject K n ⊓ filtrationStage K n p) ⊔ boundariesSubobject K n

/-- The concrete intersection/union criterion on the representatives
`\ker(d^n) ∩ F^p K^n + \operatorname{im}(d^{n-1})` from Lemma `12.24.10 (2)`. -/
def cohomologyFiltrationCriterion : Prop :=
  ∀ n : ℤ,
    (⨅ p : ℤ, cohomologyFiltrationRepresentative K n p) =
        boundariesSubobject K n ∧
      (⨆ p : ℤ, cohomologyFiltrationRepresentative K n p) =
        cyclesSubobject K n

/-- Definition 12.24.9 (2): the associated spectral sequence of a filtered complex abuts to
`H^*(K^•)` if it weakly converges and the induced cohomology filtration is separated and
exhaustive in every degree. -/
def abutsToCohomology : Prop :=
  weaklyConvergesToCohomology K ∧
    ∀ n : ℤ,
      DecreasingFiltration.IsSeparated (HFil n) ∧
        DecreasingFiltration.IsExhaustive (HFil n)

-- Proof sketch: compare the intrinsic filtration on `H^n(K^•)` with its textbook representatives
-- `\ker(d^n) ∩ F^p K^n + \operatorname{im}(d^{n-1})` inside `K^n`, using the quotient description
-- from Definition `12.24.5`.
/-- The induced cohomology filtration is separated and exhaustive exactly when the representatives
`\ker(d^n) ∩ F^p K^n + \operatorname{im}(d^{n-1})` have intersection `\operatorname{im}(d^{n-1})`
and union `\ker(d^n)` in every degree. -/
theorem cohomologyFiltrationCriterion_iff_separatedExhaustive
    :
    (∀ n : ℤ,
      DecreasingFiltration.IsSeparated (HFil n) ∧
        DecreasingFiltration.IsExhaustive (HFil n)) ↔
      cohomologyFiltrationCriterion K := by
  sorry

-- Proof sketch: weak convergence is source-facingly the identification
-- `\mathrm{gr}^p H^n(K^•) \cong E_\infty^{p,n-p}`, while equations `(12.24.6.2)` and
-- `(12.24.6.1)` are the pagewise criterion forcing that identification.
/-- Lemma 12.24.10 (1): for a filtered complex in an abelian category, the associated spectral
sequence weakly converges to the cohomology of the underlying complex exactly when the equalities
of `(12.24.6.2)` and `(12.24.6.1)` hold in every degree and filtration step. -/
theorem weaklyConvergesToCohomology_iff
    :
    weaklyConvergesToCohomology K ↔
      weakConvergenceCriterion K := by
  sorry

-- Proof sketch: abutment means weak convergence together with separatedness and exhaustiveness of
-- the induced filtration, and the previous bridge identifies those intrinsic properties with the
-- textbook intersection/union criterion on
-- `\ker(d^n) ∩ F^p K^n + \operatorname{im}(d^{n-1})`.
/-- Lemma 12.24.10 (2): for a filtered complex in an abelian category, the associated spectral
sequence abuts to the cohomology of the underlying complex exactly when it weakly converges and
the representatives `\ker(d^n) ∩ F^p K^n + \operatorname{im}(d^{n-1})` have intersection
`\operatorname{im}(d^{n-1})` and union `\ker(d^n)` in every degree. -/
theorem abutsToCohomology_iff
    :
    abutsToCohomology K ↔
      weaklyConvergesToCohomology K ∧
        cohomologyFiltrationCriterion K := by
  rw [abutsToCohomology]
  exact and_congr_right fun _ ↦ cohomologyFiltrationCriterion_iff_separatedExhaustive K

end

end FilteredComplex
end CategoryTheory

/-! ### Lemma_12_24_11 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u v

namespace CategoryTheory
namespace FilteredComplex

section FiniteFiltrations

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜] [HasZeroObject 𝒜]

/- Domain-style sampling for Lemma `12.24.11`.
- primary domain: filtered complexes in an abelian category, their associated cohomological
  spectral sequences, and the induced filtrations on cohomology;
- sampled owner/canonical declarations in this domain:
  `FilteredObject.IsFinite`,
  `FilteredComplex.inducedCohomologyFiltration`,
  `FilteredComplex.abutsToCohomology`,
  `FilteredComplex.convergesToCohomology`,
  `CohomologicalSpectralSequence.IsBounded`;
- best owner abstraction: the filtered-complex owner `K : FilteredComplex 𝒜`, with termwise
  finiteness and cohomology-filtration finiteness attached directly to that owner;
- primitive data: only the filtered complex `K`, a chosen associated spectral sequence `E`, and
  the object property `P`;
- derived API: boundedness of `E`, finiteness of the induced cohomology filtration, and the weak
  LinearRepresentations_Serre_1977 membership and convergence consequences for the cohomology objects.
Source/core/bridge triage:
- `source-facing`: `HasFiniteFiltrations` and the four lemmas below;
- `core/canonical`: `FilteredComplex`, `FilteredObject.IsFinite`,
  `FilteredComplex.inducedCohomologyFiltration`, and
  `FilteredComplex.convergesToCohomology`,
  `CohomologicalSpectralSequence.IsBounded`;
- `bridge/view`: the passage from a page of an associated spectral sequence to the cohomology
  objects of the underlying complex via the induced filtration.

The file therefore keeps the source-facing hypotheses and consequences, but it places them on the
canonical `FilteredComplex` owner instead of a parallel root-level wrapper vocabulary. -/

/-- Each term `K^n` of a filtered complex has a finite filtration when some stage is the whole
object and some stage is zero. -/
abbrev HasFiniteFiltrations (K : FilteredComplex 𝒜) : Prop :=
  ∀ n : ℤ, (K.X n).IsFinite

end FiniteFiltrations

section Abelian

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- The induced filtration on the cohomology in degree `n` is finite when the owner filtration on
`H^n(K^•)` has a top stage and a bottom stage. -/
abbrev cohomologyFiltrationIsFinite (K : FilteredComplex 𝒜) : Prop :=
  ∀ n : ℤ, (K.inducedCohomologyFiltration n).IsFinite

variable (K : FilteredComplex 𝒜)

section AssociatedSpectralSequence

variable (E : CohomologicalSpectralSequence 𝒜 0) [IsAssociatedToFilteredComplex K E]

-- Proof sketch: on the initial page of total degree `n`, the entry `E₀^{p,n-p}` is the graded
-- piece `gr^p K^n`; finite filtrations on each `K^n` therefore give only finitely many nonzero
-- terms on every antidiagonal.
/-- Lemma 12.24.11 (1): if every term `K^n` of a filtered complex has a finite filtration, then
the associated spectral sequence is bounded. -/
theorem associatedSpectralSequence_isBounded_of_hasFiniteFiltrations
    (hfin : K.HasFiniteFiltrations) :
    CohomologicalSpectralSequence.IsBounded E := sorry

-- Proof sketch: Equation `(12.24.5.1)` identifies the induced filtration on cohomology with the
-- images of the finite stages of the filtration on `K^n`; once the filtration on `K^n` is finite,
-- the induced one has top stage the cycles and bottom stage the boundaries.
/-- Lemma 12.24.11 (2): if every term `K^n` has a finite filtration, then the induced filtration
on each cohomology object `H^n(K^•)` is finite. -/
theorem cohomologyFiltrationIsFinite_of_hasFiniteFiltrations
    (hfin : K.HasFiniteFiltrations) :
    K.cohomologyFiltrationIsFinite := sorry

section Convergence

variable [LocallySmall 𝒜] [WellPowered 𝒜] [HasWidePullbacks 𝒜] [HasCoproducts 𝒜]
  [InitialMonoClass 𝒜]

-- Proof sketch: finite filtrations on the terms of `K` force boundedness of the associated
-- spectral sequence, hence regularity; part (2) gives the corresponding finiteness of the induced
-- cohomology filtration, which yields the completeness required in Definition `12.24.9`.
/-- Lemma 12.24.11 (3): if every term `K^n` of a filtered complex has a finite filtration, then
the associated spectral sequence converges to the cohomology of the underlying complex in the
sense of Definition `12.24.9`. -/
theorem convergesToCohomology_of_hasFiniteFiltrations
    (hfin : K.HasFiniteFiltrations) :
    K.convergesToCohomology E := sorry

end Convergence

-- Proof sketch: boundedness implies eventual stabilization, so a page `E_r` lying in a weak
-- LinearRepresentations_Serre_1977 subcategory forces the corresponding `E_∞`-graded pieces to lie there as well. The
-- finite cohomology filtration from part (2) then shows `H^n(K^•)` itself belongs to the weak
-- LinearRepresentations_Serre_1977 subcategory by closure under extensions.
/-- Lemma 12.24.11 (4): let `\mathcal C` be a weak LinearRepresentations_Serre_1977 subcategory of the ambient abelian
category. If for some page `r` all terms `E_r^{p,q}` of the spectral sequence associated to the
filtered complex lie in `\mathcal C`, then every cohomology object `H^n(K^•)` lies in
`\mathcal C`. -/
theorem cohomologyObject_mem_of_page_mem_of_hasFiniteFiltrations
    (P : ObjectProperty 𝒜)
    [IsWeakSerreClass P]
    (hfin : K.HasFiniteFiltrations)
    (r : ℤ) (hr : 0 ≤ r)
    (hpage : ∀ p q : ℤ, P ((E.page r hr).X (p, q))) :
    ∀ n : ℤ, P (K.underlying.homology n) := sorry

end AssociatedSpectralSequence

end Abelian

end FilteredComplex
end CategoryTheory

/-! ### Lemma_12_24_12 (from Chap12) -/
open scoped BigOperators
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [LocallySmall 𝒜] [WellPowered 𝒜]
  [HasWidePullbacks 𝒜] [HasCoproducts 𝒜] [InitialMonoClass 𝒜]

/- Domain-style triage for Lemma `12.24.12`.
- source-facing layer: the finiteness and `K₀` consequences for the cohomology of a filtered
  complex whose associated spectral sequence has a finite-support page;
- core/canonical owners already available upstream in this chapter:
  `FilteredComplex`,
  `IsAssociatedToFilteredComplex`,
  `FilteredComplex.HasFiniteFiltrations`,
  `FilteredComplex.cohomologyObject_mem_of_page_mem_of_hasFiniteFiltrations`;
- bridge/view layer: the finite-support and alternating-sum conclusions stated in this file.

This file now reuses the Chapter 12 owners directly instead of rebuilding a parallel local
filtered-complex API. -/

namespace FilteredComplex

/- Canonical owner input reused below: pagewise membership in a weak LinearRepresentations_Serre_1977 subcategory already
comes from Lemma `12.24.11`. -/
#check FilteredComplex.cohomologyObject_mem_of_page_mem_of_hasFiniteFiltrations

-- Proof sketch: compare the alternating Euler characteristic of the even and odd parts of the
-- `r`-th page with that of the `r + 1`-st page, iterate until the differential vanishes, and then
-- use the finite filtration on each `H^n(K^•)` from Lemma `12.24.11` to read off that only
-- finitely many cohomology objects can remain nonzero.
/-- Lemma 12.24.12 (1): if the filtration on each `K^n` is finite and some page `E_r` of the
associated spectral sequence has only finitely many nonzero terms, then only finitely many
cohomology objects `H^n(K^•)` are nonzero. -/
theorem cohomologyObject_finite_nonzero_of_page_finite_nonzero
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E] (hfin : K.HasFiniteFiltrations)
    {r : ℤ} (hr : 0 ≤ r)
    (hpageFinite : { pq : ℤ × ℤ | ¬ IsZero ((E.page r hr).X (pq.1, pq.2)) }.Finite) :
    { n : ℤ | ¬ IsZero (K.underlying.homology n) }.Finite := sorry

-- Proof sketch: the differentials on each page split the finite-support page into even and odd
-- parts whose Euler characteristic is unchanged from `E_r` to `E_{r+1}`; after iterating to a
-- page with zero differential, identify the stable page with the graded pieces of the finite
-- filtration on `H^n(K^•)` and use additivity in `K₀`.
/-- Lemma 12.24.12 (2): let `P` be a weak LinearRepresentations_Serre_1977 subcategory containing the objects `E_r^{p,q}` on
some page `r`. For any finite set supporting the nonzero terms on that page, there is a finite set
supporting the nonzero cohomology objects `H^n(K^•)` such that the alternating sums of their
classes agree in the Grothendieck group `K₀(P.FullSubcategory)`. In particular, this applies to
the smallest weak LinearRepresentations_Serre_1977 subcategory generated by the objects `E_r^{p,q}` from the text. -/
theorem k0_alternatingSum_eq_of_page_support
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E] (hfin : K.HasFiniteFiltrations)
    {r : ℤ} (hr : 0 ≤ r) (P : ObjectProperty 𝒜) [IsWeakSerreClass P]
    (hpageP : ∀ p q : ℤ, P ((E.page r hr).X (p, q)))
    (s : Finset (ℤ × ℤ))
    (hs : ∀ ⦃pq : ℤ × ℤ⦄, pq ∉ s → IsZero ((E.page r hr).X (pq.1, pq.2))) :
    ∃ t : Finset ℤ,
      (∀ ⦃n : ℤ⦄, n ∉ t → IsZero (K.underlying.homology n)) ∧
        ((Finset.sum t fun n ↦
            if Even n then
              K₀[(⟨K.underlying.homology n,
                  cohomologyObject_mem_of_page_mem_of_hasFiniteFiltrations
                    K E P hfin r hr hpageP n⟩ : P.FullSubcategory)]
            else
              -K₀[(⟨K.underlying.homology n,
                  cohomologyObject_mem_of_page_mem_of_hasFiniteFiltrations
                    K E P hfin r hr hpageP n⟩ : P.FullSubcategory)]) =
          (Finset.sum s fun pq ↦
            if Even (pq.1 + pq.2) then
              K₀[(⟨(E.page r hr).X (pq.1, pq.2), hpageP pq.1 pq.2⟩ : P.FullSubcategory)]
            else
              -K₀[(⟨(E.page r hr).X (pq.1, pq.2), hpageP pq.1 pq.2⟩ : P.FullSubcategory)])) := sorry

end FilteredComplex
end CategoryTheory

/-! ### Lemma_12_24_13 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory
namespace FilteredComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Lemma `12.24.13`.
- primary domain: convergence criteria for associated cohomological spectral sequences of filtered
  cochain complexes, expressed through the induced cohomology filtration;
- sampled owner/canonical declarations in this domain:
  `FilteredComplex.inducedCohomologyFiltration`,
  `FilteredComplex.cohomologyFiltrationIsFinite`,
  `FilteredComplex.abutsToCohomology`,
  `FilteredComplex.convergesToCohomology`,
  `CohomologicalSpectralSequence.IsBounded`;
- best owner abstraction: the filtered-complex owner `K : FilteredComplex 𝒜` together with the
  chapter-level convergence and finiteness predicates already attached to it, and the canonical
  boundedness predicate on a chosen associated spectral sequence;
- primitive data: the two eventual stage-cohomology hypotheses on `K`;
- derived API: boundedness of any associated spectral sequence, finiteness of the induced
  cohomology filtration, the owner abutment statement `K.abutsToCohomology`, and convergence of a
  chosen associated spectral sequence to the cohomology of `K`;
- source/core/bridge triage:
  `source-facing`: `EventualStageCohomologyVanishesAbove`,
    `EventualStageCohomologyStabilizesBelow`;
  `core/canonical`: `CohomologicalSpectralSequence.IsBounded`,
    `FilteredComplex.cohomologyFiltrationIsFinite`, `FilteredComplex.abutsToCohomology`,
    `FilteredComplex.convergesToCohomology`;
  `bridge/view`: the stagewise cohomology maps `K.cohomologyMap p n`.

The eventual stage-control hypotheses are genuine source-facing input, but the conclusions should
land on the existing chapter owners rather than on parallel local wrappers. -/

/-- The upper-vanishing hypothesis from Lemma `12.24.13`: in each cohomological degree, the
cohomology of the filtration stages `F^p K^•` is zero for all sufficiently large `p`. -/
def EventualStageCohomologyVanishesAbove (K : FilteredComplex 𝒜) : Prop :=
  ∀ n : ℤ, ∃ p₀ : ℤ, ∀ ⦃p : ℤ⦄ (_ : p₀ ≤ p), IsZero ((K.stage p).homology n)

/-- The lower-stability hypothesis from Lemma `12.24.13`: in each cohomological degree, the map
`H^n(F^p K^•) ⟶ H^n(K^•)` is an isomorphism for all sufficiently small `p`. -/
def EventualStageCohomologyStabilizesBelow (K : FilteredComplex 𝒜) : Prop :=
  ∀ n : ℤ, ∃ p₁ : ℤ, ∀ ⦃p : ℤ⦄ (_ : p ≤ p₁), IsIso (K.cohomologyMap p n)

-- Proof sketch: acyclicity of the stage complex `F^p K^•` identifies every cohomology object
-- `H^n(F^p K^•)` with zero, so the source-facing stage-acyclicity hypothesis implies the owner
-- predicate `EventualStageCohomologyVanishesAbove`.
/-- Bridge/view layer: eventual acyclicity of the stage complexes implies the source-facing upper
vanishing hypothesis `EventualStageCohomologyVanishesAbove`. -/
theorem eventualStageCohomologyVanishesAbove_of_stageAcyclic
    (K : FilteredComplex 𝒜)
    (hAcyclic : ∃ p₀ : ℤ, ∀ ⦃p : ℤ⦄ (_ : p₀ ≤ p), (F^{p} K).Acyclic) :
    EventualStageCohomologyVanishesAbove K := by
  sorry

-- Proof sketch: if `F^p K^• ⟶ K^•` is a quasi-isomorphism, then every induced cohomology map is
-- an isomorphism, so the source-facing eventual quasi-isomorphism hypothesis implies the owner
-- predicate `EventualStageCohomologyStabilizesBelow`.
/-- Bridge/view layer: eventual quasi-isomorphism of the stage inclusions implies the source-facing
lower-stability hypothesis `EventualStageCohomologyStabilizesBelow`. -/
theorem eventualStageCohomologyStabilizesBelow_of_stageInclusion_quasiIso
    (K : FilteredComplex 𝒜)
    (hQuasi : ∃ p₁ : ℤ, ∀ ⦃p : ℤ⦄ (_ : p ≤ p₁), QuasiIso (K.stageInclusion p)) :
    EventualStageCohomologyStabilizesBelow K := by
  sorry

-- Proof sketch: use the long exact sequence attached to
-- `0 ⟶ F^{p + 1} K^• ⟶ F^p K^• ⟶ gr^p(K^•) ⟶ 0` to show that `H^n(gr^p(K^•))` vanishes for all
-- sufficiently large `p` and all sufficiently small `p`; only finitely many indices remain on
-- each total degree.
/-- Lemma 12.24.13 (1): if the stage cohomology of a filtered complex vanishes for all sufficiently
large filtration indices and stabilizes to `H^n(K^•)` for all sufficiently small filtration
indices, then the associated spectral sequence is bounded. -/
theorem associatedSpectralSequence_isBounded_of_eventual_stage_cohomology
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E]
    (hvanish : EventualStageCohomologyVanishesAbove K)
    (hstabilize : EventualStageCohomologyStabilizesBelow K) :
    CohomologicalSpectralSequence.IsBounded E := sorry

-- Proof sketch: for large `p`, the stage cohomology `H^n(F^p K^•)` is zero, so the image
-- filtration step on `H^n(K^•)` is zero; for sufficiently small `p`, the map
-- `H^n(F^p K^•) ⟶ H^n(K^•)` is an isomorphism, so the corresponding filtration step is the whole
-- cohomology object.
/-- Lemma 12.24.13 (2): under the same hypotheses, the induced filtration on each cohomology
object `H^n(K^•)` is finite. -/
theorem cohomologyFiltrationIsFinite_of_eventual_stage_cohomology
    (K : FilteredComplex 𝒜)
    (hvanish : EventualStageCohomologyVanishesAbove K)
    (hstabilize : EventualStageCohomologyStabilizesBelow K) :
    K.cohomologyFiltrationIsFinite := sorry

section Convergence

variable [LocallySmall 𝒜] [WellPowered 𝒜] [HasWidePullbacks 𝒜] [HasCoproducts 𝒜]
  [InitialMonoClass 𝒜]

-- Proof sketch: the eventual stage-cohomology hypotheses force the weak-convergence equalities
-- and the separated/exhaustive cohomology-filtration equalities from Lemma `12.24.10`, so the
-- filtered complex already abuts to the cohomology of its underlying complex.
/-- The eventual vanishing and eventual stabilization hypotheses of Lemma `12.24.13` imply the
owner abutment statement `K.abutsToCohomology`. -/
theorem abutsToCohomology_of_eventual_stage_cohomology
    (K : FilteredComplex 𝒜)
    (hvanish : EventualStageCohomologyVanishesAbove K)
    (hstabilize : EventualStageCohomologyStabilizesBelow K) :
    K.abutsToCohomology := sorry

-- Proof sketch: combine `abutsToCohomology_of_eventual_stage_cohomology` with boundedness of the
-- chosen associated spectral sequence, which gives regularity, and finiteness of the induced
-- cohomology filtration, which yields the completeness required in Definition `12.24.9`.
/-- Lemma 12.24.13 (3): under the eventual vanishing and eventual stabilization hypotheses, the
associated spectral sequence converges to the cohomology of the underlying complex. -/
theorem associatedSpectralSequence_convergesToCohomology_of_eventual_stage_cohomology
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E]
    (hvanish : EventualStageCohomologyVanishesAbove K)
    (hstabilize : EventualStageCohomologyStabilizesBelow K) :
    K.convergesToCohomology E := sorry

end Convergence

end FilteredComplex
end CategoryTheory
