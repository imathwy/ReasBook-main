import Mathlib
import StacksProject_2024.stacks_project.Chap12.Definition_12_10_1
import StacksProject_2024.stacks_project.Chap12.Definition_12_24_9
import StacksProject_2024.stacks_project.Chap12.Lemma_12_24_2
import StacksProject_2024.stacks_project.Chap12.Lemma_12_24_8
import StacksProject_2024.stacks_project.Chap12.Lemma_12_24_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open scoped ZeroObject

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
  Serre membership and convergence consequences for the cohomology objects.
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

omit [Abelian 𝒜] in
/-- Helper for Lemma 12.24.11: if the `(p + 1)`-st filtration stage is already the whole object,
then the stage inclusion `F^{p + 1} X ⟶ F^p X` is an isomorphism. -/
theorem stageInclusion_isIso_of_succ_eq_top (X : FilteredObject 𝒜) (p : ℤ)
    (h : X.filtration.obj (p + 1) = ⊤) :
    IsIso (X.filtration.stageInclusion p) := by
  -- Antitonicity forces the previous stage to be top as well.
  have hp : X.filtration.obj p = ⊤ := by
    apply top_unique
    simpa [h] using (X.filtration.antitone_obj (show p ≤ p + 1 by omega))
  letI : IsIso (X.filtration.obj p).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 hp
  letI : IsIso (X.filtration.obj (p + 1)).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 h
  -- The stage inclusion is the factorization of the two top-stage arrows through the ambient
  -- object, hence a composition of isomorphisms.
  have hEq :
      X.filtration.stageInclusion p =
        (X.filtration.obj (p + 1)).arrow ≫ inv (X.filtration.obj p).arrow := by
    apply (cancel_mono (X.filtration.obj p).arrow).1
    calc
      X.filtration.stageInclusion p ≫ (X.filtration.obj p).arrow =
          (X.filtration.obj (p + 1)).arrow := by
            exact Subobject.ofLE_arrow _
      _ =
          ((X.filtration.obj (p + 1)).arrow ≫ inv (X.filtration.obj p).arrow) ≫
            (X.filtration.obj p).arrow := by
              simp
  rw [hEq]
  infer_instance

/-- Helper for Lemma 12.24.11: a filtration stage equal to the zero subobject has zero underlying
object. -/
theorem stage_isZero_of_eq_bot (X : FilteredObject 𝒜) (p : ℤ)
    (hp : X.filtration.obj p = ⊥) :
    IsZero ((((X.filtration.obj p : Subobject X.obj) : 𝒜))) := by
  -- Replace the stage by the canonical zero subobject and transport the standard zero-object
  -- witness across that identification.
  let e : ((((X.filtration.obj p : Subobject X.obj) : 𝒜))) ≅ 0 :=
    Subobject.isoOfEqMk (X.filtration.obj p) (0 : (0 : 𝒜) ⟶ X.obj) (by
      simpa [Subobject.bot_eq_zero] using hp)
  exact Limits.IsZero.of_iso (Limits.isZero_zero 𝒜) e

/-- Helper for Lemma 12.24.11: if the `p`-th filtration stage is zero, then the stage inclusion
`F^{p + 1} X ⟶ F^p X` is an isomorphism. -/
theorem stageInclusion_isIso_of_eq_bot (X : FilteredObject 𝒜) (p : ℤ)
    (h : X.filtration.obj p = ⊥) :
    IsIso (X.filtration.stageInclusion p) := by
  -- Once the filtration reaches zero, the next stage is zero as well.
  have hp1 : X.filtration.obj (p + 1) = ⊥ := by
    apply bot_unique
    simpa [h] using (X.filtration.antitone_obj (show p ≤ p + 1 by omega))
  let hZ1 : IsZero ((((X.filtration.obj (p + 1) : Subobject X.obj) : 𝒜))) :=
    stage_isZero_of_eq_bot X (p + 1) hp1
  let hZ0 : IsZero ((((X.filtration.obj p : Subobject X.obj) : 𝒜))) :=
    stage_isZero_of_eq_bot X p h
  exact hZ1.isIso hZ0 _

/-- Helper for Lemma 12.24.11: the `p`-th graded piece of a filtered object vanishes once the
`(p + 1)`-st stage is already the whole object. -/
theorem gradedPiece_isZero_of_succ_eq_top (X : FilteredObject 𝒜) (p : ℤ)
    (h : X.filtration.obj (p + 1) = ⊤) :
    IsZero (X.filtration.gradedPiece p) := by
  -- The graded piece is the cokernel of an isomorphism in this extremal top-stage case.
  letI : IsIso (X.filtration.stageInclusion p) := stageInclusion_isIso_of_succ_eq_top X p h
  simpa [DecreasingFiltration.gradedPiece] using
    (Limits.isZero_cokernel_of_epi (X.filtration.stageInclusion p))

/-- Helper for Lemma 12.24.11: the `p`-th graded piece of a filtered object vanishes once the
`p`-th stage is already zero. -/
theorem gradedPiece_isZero_of_eq_bot (X : FilteredObject 𝒜) (p : ℤ)
    (h : X.filtration.obj p = ⊥) :
    IsZero (X.filtration.gradedPiece p) := by
  -- The graded piece is again the cokernel of an isomorphism, now because both stages are zero.
  letI : IsIso (X.filtration.stageInclusion p) := stageInclusion_isIso_of_eq_bot X p h
  simpa [DecreasingFiltration.gradedPiece] using
    (Limits.isZero_cokernel_of_epi (X.filtration.stageInclusion p))

/-- Helper for Lemma 12.24.11: if the relevant graded piece of `K^n` is zero, then the
corresponding page-zero entry `E_0^{p,n-p}` is zero. -/
theorem pageZero_entry_isZero_of_term_gradedPiece_isZero (n p : ℤ)
    (hzero : IsZero ((K.X n).filtration.gradedPiece p)) :
    IsZero ((E.page 0).X (p, n - p)) := by
  -- The page-zero comparison identifies this entry with the graded piece of `K^n`.
  let e' : (E.page 0).X (p, n - p) ≅ (K.gradedPieceColumn p).X (n - p) :=
    (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) (n - p)).mapIso (pageZeroIso K E p)
  let e : (E.page 0).X (p, n - p) ≅ ((K.X n).filtration.gradedPiece p) :=
    by simpa [gradedPieceColumn] using e'
  exact Limits.IsZero.of_iso hzero e

-- Proof sketch: on the initial page of total degree `n`, the entry `E₀^{p,n-p}` is the graded
-- piece `gr^p K^n`; finite filtrations on each `K^n` therefore give only finitely many nonzero
-- terms on every antidiagonal.
/-- Lemma 12.24.11 (1): if every term `K^n` of a filtered complex has a finite filtration, then
the associated spectral sequence is bounded. -/
theorem associatedSpectralSequence_isBounded_of_hasFiniteFiltrations
    (hfin : K.HasFiniteFiltrations) :
    CohomologicalSpectralSequence.IsBounded E := by
  -- It is enough to prove the two one-sided eventual vanishing bounds on the initial page.
  rw [CohomologicalSpectralSequence.isBounded_iff_isBoundedBelow_and_isBoundedAbove]
  refine ⟨?_, ?_⟩
  · intro n
    rcases hfin n with ⟨a, b, ha, hb⟩
    refine ⟨b, ?_⟩
    intro p hp
    -- For `p ≥ b`, the `p`-th stage is already zero, so the corresponding graded piece vanishes.
    have hpb : (K.X n).filtration.obj p = ⊥ := by
      apply bot_unique
      simpa [hb] using ((K.X n).filtration.antitone_obj hp)
    exact pageZero_entry_isZero_of_term_gradedPiece_isZero K E n p <|
      gradedPiece_isZero_of_eq_bot (K.X n) p hpb
  · intro n
    rcases hfin n with ⟨a, b, ha, hb⟩
    refine ⟨a - 1, ?_⟩
    intro p hp
    -- For `p ≤ a - 1`, the next stage `F^(p+1)` is already top, so this graded piece vanishes.
    have hpa : p + 1 ≤ a := by
      omega
    have hp1 : (K.X n).filtration.obj (p + 1) = ⊤ := by
      apply top_unique
      simpa [ha] using ((K.X n).filtration.antitone_obj hpa)
    exact pageZero_entry_isZero_of_term_gradedPiece_isZero K E n p <|
      gradedPiece_isZero_of_succ_eq_top (K.X n) p hp1

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
-- Serre subcategory forces the corresponding `E_∞`-graded pieces to lie there as well. The
-- finite cohomology filtration from part (2) then shows `H^n(K^•)` itself belongs to the weak
-- Serre subcategory by closure under extensions.
/-- Lemma 12.24.11 (4): let `\mathcal C` be a weak Serre subcategory of the ambient abelian
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
