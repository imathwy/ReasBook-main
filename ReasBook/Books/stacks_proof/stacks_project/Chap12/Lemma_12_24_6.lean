import Mathlib
import StacksProject_2024.Chap12.Aux_12_20_2_1
import StacksProject_2024.Chap12.Definition_12_20_2
import StacksProject_2024.Chap12.Lemma_12_24_2
import StacksProject_2024.Chap12.Definition_12_24_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped SpectralSequence

noncomputable section

universe v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

namespace CohomologicalSpectralSequence

variable [LocallySmall 𝒜] [WellPowered 𝒜] [HasWidePullbacks 𝒜] [HasCoproducts 𝒜]
  [InitialMonoClass 𝒜]

/-- Lemma 12.24.6 (1): in every bidegree, the limit term is the quotient
`E_∞^{p,q} = Z_∞^{p,q} / B_∞^{p,q}`. -/
@[stacks 012Q]
theorem infinityPage_def
    (E : CohomologicalSpectralSequence 𝒜 0) (pq : ℤ × ℤ) :
    (E.toPageOneSpectralSequence).infinityPage pq =
      cokernel
        (Subobject.ofLE
          ((E.toPageOneSpectralSequence).boundaryInfinity pq)
          ((E.toPageOneSpectralSequence).cycleInfinity pq)
          ((E.toPageOneSpectralSequence).boundaryInfinity_le_cycleInfinity pq)) := by
  simpa using
    SpectralSequence.infinityPage_def E.toPageOneSpectralSequence pq

end CohomologicalSpectralSequence

namespace FilteredComplex

variable [LocallySmall 𝒜] [WellPowered 𝒜] [HasWidePullbacks 𝒜] [HasCoproducts 𝒜]
  [InitialMonoClass 𝒜]

/-- Helper for Lemma 12.24.6: the stage subobject `F^p K^n ⊆ K^n`. -/
private abbrev filtration_stage (K : FilteredComplex 𝒜) (n p : ℤ) :
    Subobject ((K.X n).obj) :=
  (K.X n).filtration.obj p

/-- Helper for Lemma 12.24.6: the cocycle subobject `Ker(d^n) ⊆ K^n`. -/
private abbrev cycles_subobject (K : FilteredComplex 𝒜) (n : ℤ) :
    Subobject ((K.X n).obj) :=
  kernelSubobject ((K.d n (n + 1)).hom)

/-- Helper for Lemma 12.24.6: the coboundary subobject `Im(d^{n-1}) ⊆ K^n`. -/
private abbrev boundaries_subobject (K : FilteredComplex 𝒜) (n : ℤ) :
    Subobject ((K.X n).obj) :=
  imageSubobject ((K.d (n - 1) n).hom)

/-- Helper for Lemma 12.24.6: the eventual boundary representative
`⋃_r (F^p K^n ∩ im(F^{p-r+1} K^{n-1} ⟶ K^n)) + F^{p+1} K^n`. -/
private abbrev eventual_boundary_representative (K : FilteredComplex 𝒜) (n p : ℤ) :
    Subobject ((K.X n).obj) :=
  ⨆ r : ℕ,
    (filtration_stage K n p ⊓
        imageSubobject
          ((filtration_stage K (n - 1) (p - r + 1)).arrow ≫ (K.d (n - 1) n).hom)) ⊔
      filtration_stage K n (p + 1)

/-- Helper for Lemma 12.24.6: the eventual cycle representative
`⋂_r (F^p K^n ∩ (d^n)⁻¹(F^{p+r} K^{n+1})) + F^{p+1} K^n`. -/
private abbrev eventual_cycle_representative (K : FilteredComplex 𝒜) (n p : ℤ) :
    Subobject ((K.X n).obj) :=
  ⨅ r : ℕ,
    (filtration_stage K n p ⊓
        (Subobject.pullback ((K.d n (n + 1)).hom)).obj
          (filtration_stage K (n + 1) (p + r))) ⊔
      filtration_stage K n (p + 1)

/-- Helper for Lemma 12.24.6: the intrinsic cycle representative
`(\ker d^n ∩ F^p K^n) + F^{p+1} K^n`. -/
private abbrev cohomology_cycle_representative (K : FilteredComplex 𝒜) (n p : ℤ) :
    Subobject ((K.X n).obj) :=
  (cycles_subobject K n ⊓ filtration_stage K n p) ⊔ filtration_stage K n (p + 1)

/-- Helper for Lemma 12.24.6: the intrinsic boundary representative
`(\operatorname{im} d^{n-1} ∩ F^p K^n) + F^{p+1} K^n`. -/
private abbrev cohomology_boundary_representative (K : FilteredComplex 𝒜) (n p : ℤ) :
    Subobject ((K.X n).obj) :=
  (boundaries_subobject K n ⊓ filtration_stage K n p) ⊔ filtration_stage K n (p + 1)

/-- Helper for Lemma 12.24.6: the coboundary subobject is contained in the cocycle subobject
because consecutive differentials compose to zero. -/
private theorem boundaries_subobject_le_cycles_subobject (K : FilteredComplex 𝒜) (n : ℤ) :
    boundaries_subobject K n ≤ cycles_subobject K n := by
  -- The standard image-to-kernel comparison applies to `d^{n-1} ≫ d^n = 0`.
  simpa [boundaries_subobject, cycles_subobject] using
    (image_le_kernel
      ((K.d (n - 1) n).hom)
      ((K.d n (n + 1)).hom)
      (congrArg FilteredObject.Hom.hom (K.d_comp_d (n - 1) n (n + 1))))

/-- Helper for Lemma 12.24.6: equation `(12.24.6.2)` places the eventual boundary
representative below the intrinsic cohomology-boundary representative. -/
private theorem eventual_boundary_representative_le_cohomology_boundary_representative
    (K : FilteredComplex 𝒜) (n p : ℤ) :
    eventual_boundary_representative K n p ≤ cohomology_boundary_representative K n p := by
  -- Bound each fixed-`r` summand by the common intrinsic boundary representative.
  refine iSup_le fun r ↦ sup_le ?_ le_sup_right
  -- The image of the composite through `F^{p-r+1} K^{n-1}` factors through `im(d^{n-1})`.
  refine le_sup_of_le_left ?_
  refine le_inf ?_ inf_le_left
  exact inf_le_right.trans (imageSubobject_comp_le _ _)

/-- Helper for Lemma 12.24.6: the intrinsic boundary representative is contained in the intrinsic
cycle representative. -/
private theorem cohomology_boundary_representative_le_cohomology_cycle_representative
    (K : FilteredComplex 𝒜) (n p : ℤ) :
    cohomology_boundary_representative K n p ≤ cohomology_cycle_representative K n p := by
  -- Compare the boundary and cycle summands and keep the common `F^{p+1} K^n` term.
  refine sup_le ?_ le_sup_right
  exact le_sup_of_le_left <| inf_le_inf (boundaries_subobject_le_cycles_subobject K n) le_rfl

/-- Helper for Lemma 12.24.6: equation `(12.24.6.1)` places the intrinsic cohomology-cycle
representative below the eventual cycle representative. -/
private theorem cohomology_cycle_representative_le_eventual_cycle_representative
    (K : FilteredComplex 𝒜) (n p : ℤ) :
    cohomology_cycle_representative K n p ≤ eventual_cycle_representative K n p := by
  -- It is enough to bound the cocycle representative by each fixed pullback stage.
  refine le_iInf fun r ↦ sup_le ?_ le_sup_right
  have hkernel :
      ((Subobject.pullback ((K.d n (n + 1)).hom)).obj
          (filtration_stage K (n + 1) (p + r))).Factors
        (cycles_subobject K n).arrow := by
    rw [pullback_factors_iff]
    simpa [cycles_subobject] using
      (Subobject.factors_zero :
        (filtration_stage K (n + 1) (p + r)).Factors (0 : (cycles_subobject K n : 𝒜) ⟶ _))
  have hle :
      cycles_subobject K n ⊓ filtration_stage K n p ≤
        filtration_stage K n p ⊓
          (Subobject.pullback ((K.d n (n + 1)).hom)).obj
            (filtration_stage K (n + 1) (p + r)) := by
    refine le_inf inf_le_right ?_
    refine Subobject.le_of_factors ?_
    simpa using
      (Subobject.factors_of_factors_right
        (Subobject.ofLE (cycles_subobject K n ⊓ filtration_stage K n p) (cycles_subobject K n)
          inf_le_left)
        hkernel)
  simpa [cohomology_cycle_representative, eventual_cycle_representative] using hle.trans le_sup_left

/-- Helper for Lemma 12.24.6: the four textbook representatives in degree `n` and filtration
index `p` form the source-faithful chain used in the subquotient comparison. -/
private theorem cohomology_boundary_cycle_chain (K : FilteredComplex 𝒜) (n p : ℤ) :
    eventual_boundary_representative K n p ≤ cohomology_boundary_representative K n p ∧
      cohomology_boundary_representative K n p ≤ cohomology_cycle_representative K n p ∧
        cohomology_cycle_representative K n p ≤ eventual_cycle_representative K n p := by
  -- Collect the two source inequalities and the middle exactness comparison into one chain.
  refine ⟨
    eventual_boundary_representative_le_cohomology_boundary_representative K n p,
    cohomology_boundary_representative_le_cohomology_cycle_representative K n p,
    cohomology_cycle_representative_le_eventual_cycle_representative K n p⟩

/-- Helper for Lemma 12.24.6: the eventual boundary representative is contained in the eventual
cycle representative by composing the source-faithful chain
`B_∞^{p,n-p} ≤ B(H)^{p,n-p} ≤ Z(H)^{p,n-p} ≤ Z_∞^{p,n-p}`. -/
private theorem eventual_boundary_representative_le_eventual_cycle_representative
    (K : FilteredComplex 𝒜) (n p : ℤ) :
    eventual_boundary_representative K n p ≤ eventual_cycle_representative K n p := by
  -- Collapse the three-step representative chain to the outer inclusion `B_∞ ≤ Z_∞`.
  exact
    (eventual_boundary_representative_le_cohomology_boundary_representative K n p).trans
      ((cohomology_boundary_representative_le_cohomology_cycle_representative K n p).trans
        (cohomology_cycle_representative_le_eventual_cycle_representative K n p))

/-- Helper for Lemma 12.24.6: the eventual source-facing quotient obtained from the chain
`B_∞^{p,n-p} ≤ B(H)^{p,n-p} ≤ Z(H)^{p,n-p} ≤ Z_∞^{p,n-p}`. -/
private abbrev eventual_representative_subquotient
    (K : FilteredComplex 𝒜) (n p : ℤ) : 𝒜 :=
  subobjectSubquotient
    (eventual_boundary_representative_le_eventual_cycle_representative K n p)

/-- Helper for Lemma 12.24.6: the intrinsic cohomology quotient
`((im d ∩ F^p)+F^{p+1}) \ ((ker d ∩ F^p)+F^{p+1})` is already a subquotient of the eventual
source-facing quotient coming from the chain
`B_∞^{p,n-p} ≤ B(H)^{p,n-p} ≤ Z(H)^{p,n-p} ≤ Z_∞^{p,n-p}`. -/
private theorem cohomology_intrinsic_subquotient_isSubquotient_eventual_subquotient
    (K : FilteredComplex 𝒜) (n p : ℤ) :
    IsSubquotient
      (subobjectSubquotient
        (cohomology_boundary_representative_le_cohomology_cycle_representative K n p))
      (eventual_representative_subquotient K n p) := by
  obtain ⟨hBoundary, hMiddle, hCycle⟩ := cohomology_boundary_cycle_chain K n p
  -- Apply the general chain theorem to the four source-faithful representatives.
  exact subobjectSubquotient_isSubquotient_of_le_chain hBoundary hMiddle hCycle

/-- Helper for Lemma 12.24.6: once the induced graded piece is identified with the intrinsic
cohomology quotient, the textbook chain already realizes it as a subquotient of the eventual
source-facing quotient. -/
private theorem cohomology_graded_piece_isSubquotient_eventual_subquotient
    (K : FilteredComplex 𝒜) (n p : ℤ)
    (hLeft :
      Nonempty (((K.inducedCohomologyFiltration n).gradedPiece p) ≅
        subobjectSubquotient
          (cohomology_boundary_representative_le_cohomology_cycle_representative K n p))) :
    IsSubquotient ((K.inducedCohomologyFiltration n).gradedPiece p)
      (eventual_representative_subquotient K n p) := by
  obtain ⟨eLeft⟩ := hLeft
  -- First transport the graded piece to the intrinsic quotient, then apply the source chain.
  exact CategoryTheory.IsSubquotient.of_iso eLeft <|
    cohomology_intrinsic_subquotient_isSubquotient_eventual_subquotient K n p

/-- Helper for Lemma 12.24.6: after the left endpoint is identified with the intrinsic
cohomology quotient and the intrinsic quotient is compared directly with `E_∞`, the main
subquotient statement follows by left transport only. -/
private theorem cohomology_graded_piece_isSubquotient_limitTerm_of_endpoint_comparisons
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E]
    (n p : ℤ)
    (hLeft :
      Nonempty (((K.inducedCohomologyFiltration n).gradedPiece p) ≅
        subobjectSubquotient
          (cohomology_boundary_representative_le_cohomology_cycle_representative K n p)))
    (hRight :
      IsSubquotient
        (subobjectSubquotient
          (cohomology_boundary_representative_le_cohomology_cycle_representative K n p))
        ((E.toPageOneSpectralSequence).infinityPage (p, n - p))) :
    IsSubquotient ((K.inducedCohomologyFiltration n).gradedPiece p)
      ((E.toPageOneSpectralSequence).infinityPage (p, n - p)) := by
  obtain ⟨eLeft⟩ := hLeft
  -- The source-faithful finish transports only the left endpoint of the comparison.
  exact CategoryTheory.IsSubquotient.of_iso eLeft hRight

/-- Helper for Lemma 12.24.6: the `p`-th graded piece of the induced cohomology filtration is the
intrinsic quotient between the textbook boundary and cycle representatives in degree `n`. -/
private theorem inducedCohomologyGradedPiece_iso_intrinsic_subquotient
    (K : FilteredComplex 𝒜) (n p : ℤ) :
    Nonempty (((K.inducedCohomologyFiltration n).gradedPiece p) ≅
      subobjectSubquotient
        (cohomology_boundary_representative_le_cohomology_cycle_representative K n p)) := by
  -- Route correction: the left endpoint should be proved by identifying the owner filtration on
  -- `H^n(K^•)` with the textbook quotient owner `ker(d^n) / im(d^{n-1})`, then rewriting the
  -- graded piece as the quotient of consecutive stages via `Subobject.underlyingIso` and
  -- `cokernel.mapIso`.
  -- TODO: reuse the ambient cohomology / quotient-owner comparison from the `12.24.10` route,
  -- identify the stages of `K.inducedCohomologyFiltration n` with the images of the
  -- representatives `(\ker d^n ∩ F^q K^n) + im(d^{n-1})` inside that owner, and then compare the
  -- quotient of the `p + 1` and `p` stages with
  -- `subobjectSubquotient (cohomology_boundary_representative_le_cohomology_cycle_representative
  --   K n p)`.
  sorry

/-- Helper for Lemma 12.24.6: the eventual source-facing quotient
`Z_∞^{p,n-p} / B_∞^{p,n-p}` agrees with the canonical infinity-page object
`E_∞^{p,n-p}` of the associated spectral sequence. -/
private theorem eventual_representative_subquotient_iso_infinityPage
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E]
    (n p : ℤ) :
    Nonempty (eventual_representative_subquotient K n p ≅
      ((E.toPageOneSpectralSequence).infinityPage (p, n - p))) := by
  -- Route correction: the right endpoint must stay source-faithful. Compare the recursive page
  -- `cycle` and `boundary` subobjects on `E.toPageOneSpectralSequence` with the textbook
  -- representatives inside the page-one owner, pass to `cycleInfinity` and `boundaryInfinity`,
  -- and only then rewrite `E_∞` via `CohomologicalSpectralSequence.infinityPage_def`.
  -- TODO: first prove the finite-stage transport between the page-one recursive representatives
  -- and the textbook representatives under `FilteredComplex.pageOneIso K E p (n - p)`, then pass
  -- to the `iInf`/`iSup` limits and rewrite the quotient by `infinityPage_def`.
  sorry

/-- Helper for Lemma 12.24.6: the intrinsic textbook quotient in degree `n` and filtration
index `p` is a subquotient of the canonical infinity-page owner `E_∞^{p,n-p}`. -/
private theorem cohomology_intrinsic_subquotient_isSubquotient_limitTerm
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E]
    (n p : ℤ) :
    IsSubquotient
      (subobjectSubquotient
        (cohomology_boundary_representative_le_cohomology_cycle_representative K n p))
      ((E.toPageOneSpectralSequence).infinityPage (p, n - p)) := by
  have hChain :
      IsSubquotient
        (subobjectSubquotient
          (cohomology_boundary_representative_le_cohomology_cycle_representative K n p))
        (eventual_representative_subquotient K n p) :=
    cohomology_intrinsic_subquotient_isSubquotient_eventual_subquotient K n p
  let _ := hChain
  -- The middle subquotient comparison is already closed; only the right-endpoint transport from
  -- the eventual source quotient to the canonical infinity-page owner remains.
  -- TODO: transport `hChain` across
  -- `eventual_representative_subquotient_iso_infinityPage K E n p` once the source-faithful
  -- page-one / infinity-page comparison is proved.
  sorry

/-
Domain-style sampling for Lemma `12.24.6` in the filtered-complex layer.
- primary domain: the `E_∞`-comparison between the induced cohomology filtration and the infinity
  page of an associated cohomological spectral sequence;
- sampled owner declarations:
  `FilteredComplex.inducedCohomologyFiltration`,
  `SpectralSequence.infinityPage`,
  `IsAssociatedToFilteredComplex`,
  `CategoryTheory.IsSubquotient`;
- best owner abstraction:
  the graded piece of `K.inducedCohomologyFiltration n` and the canonical infinity-page object
  `(E.toPageOneSpectralSequence).infinityPage (p, n - p)`;
- primitive data: a filtered complex `K`, an associated spectral sequence `E`, and the indices
  `n`, `p`;
- derived API: the source-facing subquotient comparison below;
- source/core/bridge triage:
  `source-facing`: `cohomologyGradedPiece_isSubquotient_limitTerm`;
  `core/canonical`: `inducedCohomologyFiltration`, `infinityPage`,
    `IsAssociatedToFilteredComplex`;
  `bridge/view`: the subquotient comparison induced by the always-true inclusions
    `(12.24.6.2)` and `(12.24.6.1)`.

The weak-convergence equalities belong to the stronger isomorphism criterion of
`FilteredComplex.weaklyConvergesToCohomology_iff`; they are not primitive input for the
unconditional subquotient statement here. -/

/-- Lemma 12.24.6 (2): for an associated cohomological spectral sequence, the always-true
inclusions `(12.24.6.2)` and `(12.24.6.1)` make the graded piece `gr^p H^n(K^•)` of the induced
cohomology filtration a subquotient of the antidiagonal limit term `E_∞^{p,n-p}`. -/
@[stacks 012Q]
theorem cohomologyGradedPiece_isSubquotient_limitTerm
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E]
    (n p : ℤ) :
    IsSubquotient ((K.inducedCohomologyFiltration n).gradedPiece p)
      ((E.toPageOneSpectralSequence).infinityPage (p, n - p)) := by
  -- The source-faithful proof is now factored into the two endpoint identifications plus the
  -- already-closed middle chain comparison.
  exact
    cohomology_graded_piece_isSubquotient_limitTerm_of_endpoint_comparisons K E n p
      (inducedCohomologyGradedPiece_iso_intrinsic_subquotient K n p)
      (cohomology_intrinsic_subquotient_isSubquotient_limitTerm K E n p)

end FilteredComplex

end CategoryTheory
