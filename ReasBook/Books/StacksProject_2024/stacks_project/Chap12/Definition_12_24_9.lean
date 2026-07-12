import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap12.Aux_12_20_2_1
import StacksProject_2024.Chap12.Definition_12_24_5
import StacksProject_2024.Chap12.Lemma_12_24_2
import StacksProject_2024.Chap12.Lemma_12_24_8

-- Declarations for this item will be appended below by the statement pipeline.

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
    quotientSystemMap F (𝟙 p) = 𝟙 (quotientObj F p) := by
  -- Compare the two endomorphisms after the cokernel projection from `A`.
  refine (cancel_epi (cokernel.π (F.obj (unop p)).arrow)).1 ?_
  -- The quotient map attached to the reflexive inclusion fixes the projection.
  calc
    cokernel.π (F.obj (unop p)).arrow ≫ quotientSystemMap F (𝟙 p)
        = cokernel.π (F.obj (unop p)).arrow := by
            simp [quotientSystemMap, subobjectQuotientMap]
    _ = cokernel.π (F.obj (unop p)).arrow ≫ 𝟙 (quotientObj F p) := by
          simp

-- Proof sketch: both sides are the canonical quotient map induced by the composite inclusion
-- `F^r A ≤ F^q A ≤ F^p A`; compare them using the universal property of cokernels.
private theorem quotientSystemMap_comp {A : 𝒜} (F : DecreasingFiltration A)
    {p q r : ℤᵒᵖ} (f : p ⟶ q) (g : q ⟶ r) :
    quotientSystemMap F (f ≫ g) = quotientSystemMap F f ≫ quotientSystemMap F g := by
  -- Compare both quotient maps after the projection `A ⟶ A / F^p A`.
  refine (cancel_epi (cokernel.π (F.obj (unop p)).arrow)).1 ?_
  -- Each side carries the projection to the quotient by `F^r A`.
  calc
    cokernel.π (F.obj (unop p)).arrow ≫ quotientSystemMap F (f ≫ g)
        = cokernel.π (F.obj (unop r)).arrow := by
            simp [quotientSystemMap, subobjectQuotientMap]
    _ = cokernel.π (F.obj (unop q)).arrow ≫ quotientSystemMap F g := by
          symm
          simp [quotientSystemMap, subobjectQuotientMap]
    _ = (cokernel.π (F.obj (unop p)).arrow ≫ quotientSystemMap F f) ≫ quotientSystemMap F g := by
          simp [quotientSystemMap, subobjectQuotientMap]
    _ = cokernel.π (F.obj (unop p)).arrow ≫ (quotientSystemMap F f ≫ quotientSystemMap F g) := by
          simp [Category.assoc]

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
