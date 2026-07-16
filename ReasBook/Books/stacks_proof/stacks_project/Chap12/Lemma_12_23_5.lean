import Mathlib
import stacks_proof.stacks_project.Chap12.Aux_12_20_2_1
import stacks_proof.stacks_project.Chap12.Definition_12_20_2
import stacks_proof.stacks_project.Chap12.Definition_12_23_4
import stacks_proof.stacks_project.Chap12.Lemma_12_19_9
import stacks_proof.stacks_project.Chap12.Lemma_12_23_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped SpectralSequence

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace HomologicalComplex.Filtered

variable (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))

/-- Bridge/view layer: forgetting the `E₀` page of the associated spectral sequence attached to a
filtered differential object yields the canonical page-`E₁` owner to which Definition `12.20.2`
applies. -/
abbrev toPageOneSpectralSequence
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0) :
    SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 1 where
  page r hr := E.page r <| by omega
  iso r r' q hrr' hr := E.iso r r' q hrr' <| by omega

section WeakConvergence

variable [LocallySmall C] [WellPowered C] [HasWidePullbacks C] [HasCoproducts C]
  [InitialMonoClass C]

private abbrev filtrationStage (p : ℤ) : Subobject ((K.X PUnit.unit).obj) :=
  (K.X PUnit.unit).filtration.obj p

private abbrev cyclesSubobject : Subobject ((K.X PUnit.unit).obj) :=
  kernelSubobject ((K.d PUnit.unit PUnit.unit).hom)

private abbrev boundariesSubobject : Subobject ((K.X PUnit.unit).obj) :=
  imageSubobject ((K.d PUnit.unit PUnit.unit).hom)

/- Domain-style triage for Lemma `12.23.5`.
- source-facing layer: the eventual cycle/boundary representatives from equations `(12.23.5.1)`
  and `(12.23.5.2)`;
- core/canonical owner: `inducedHomologyFiltration K` and the spectral-sequence owner
  `SpectralSequence.infinityPage`;
- bridge/view layer: the comparison theorem below, which uses the source-facing eventual
  inclusions to compare the intrinsic graded piece of `H(K)` with the canonical owner
  `E_∞^p`. -/

/-- The eventual boundary representative
`⋃_r (F^p K ∩ im(F^{p-r+1} K ⟶ K)) + F^{p+1} K`
appearing in equation `(12.23.5.2)`. -/
def eventualBoundaryStep (p : ℤ) :
    Subobject ((K.X PUnit.unit).obj) :=
  ⨆ r : ℕ,
    (filtrationStage K p ⊓
        imageSubobject
          ((filtrationStage K (p - r + 1)).arrow ≫ (K.d PUnit.unit PUnit.unit).hom)) ⊔
      filtrationStage K (p + 1)

/-- The eventual cycle representative
`⋂_r (F^p K ∩ d⁻¹(F^{p+r} K)) + F^{p+1} K`
appearing in equation `(12.23.5.1)`. -/
def eventualCycleStep (p : ℤ) :
    Subobject ((K.X PUnit.unit).obj) :=
  ⨅ r : ℕ,
    (filtrationStage K p ⊓
        (Subobject.pullback ((K.d PUnit.unit PUnit.unit).hom)).obj
          (filtrationStage K (p + r))) ⊔
      filtrationStage K (p + 1)

/-- The cycle representative
`(\ker d ∩ F^p K) + F^{p+1} K`
for the `p`-th graded piece of the induced homology filtration. -/
def homologyCycleStep (p : ℤ) :
    Subobject ((K.X PUnit.unit).obj) :=
  (cyclesSubobject K ⊓ filtrationStage K p) ⊔ filtrationStage K (p + 1)

/-- The boundary representative
`(\operatorname{im} d ∩ F^p K) + F^{p+1} K`
for the `p`-th graded piece of the induced homology filtration. -/
def homologyBoundaryStep (p : ℤ) :
    Subobject ((K.X PUnit.unit).obj) :=
  (boundariesSubobject K ⊓ filtrationStage K p) ⊔ filtrationStage K (p + 1)

/-- The representative
`(\ker d ∩ F^p K) + \operatorname{im}(d)` for the `p`-th stage of the filtration induced on
homology. -/
private abbrev homologyFiltrationRepresentative (p : ℤ) :
    Subobject ((K.X PUnit.unit).obj) :=
  (cyclesSubobject K ⊓ filtrationStage K p) ⊔ boundariesSubobject K

-- Proof sketch: the source-facing inclusions from `(12.23.5.2)` and `(12.23.5.1)` place the
-- intrinsic representatives `homologyBoundaryStep K p ≤ homologyCycleStep K p` between the
-- actual limiting boundary and cycle pieces. Therefore `gr^p H(K)` is the intermediate quotient
-- of a chain of subobjects inside the eventual quotient `E_∞^p`.
/-- The eventual boundary representative is contained in the intrinsic boundary representative. -/
theorem eventualBoundaryStep_le_homologyBoundaryStep (p : ℤ) :
    eventualBoundaryStep K p ≤ homologyBoundaryStep K p := by
  -- It is enough to bound each fixed-`r` summand by the common intrinsic boundary term.
  refine iSup_le fun r ↦ sup_le ?_ le_sup_right
  -- The image of the composite through `F^{p-r+1}` factors through the image of `d`.
  refine le_sup_of_le_left ?_
  refine le_inf ?_ inf_le_left
  · exact inf_le_right.trans (imageSubobject_comp_le _ _)

/-- Helper for Lemma 12.23.5: the image of the differential lies in its kernel because
`d ≫ d = 0`. -/
theorem boundariesSubobject_le_cyclesSubobject :
    boundariesSubobject K ≤ cyclesSubobject K := by
  -- The standard image-to-kernel comparison applies to the square-zero differential.
  have hsq :
      (K.d PUnit.unit PUnit.unit).hom ≫ (K.d PUnit.unit PUnit.unit).hom = 0 := by
    exact congrArg FilteredObject.Hom.hom
      (K.d_comp_d PUnit.unit PUnit.unit PUnit.unit)
  simpa [boundariesSubobject, cyclesSubobject] using
    (image_le_kernel
      ((K.d PUnit.unit PUnit.unit).hom)
      ((K.d PUnit.unit PUnit.unit).hom)
      hsq)

/-- Helper for Lemma 12.23.5: the source representative
`(\ker d ∩ F^p K) + \operatorname{im}(d)` contains the boundary subobject. -/
private theorem boundariesSubobject_le_homologyFiltrationRepresentative (p : ℤ) :
    boundariesSubobject K ≤ homologyFiltrationRepresentative K p := by
  -- The boundary term is the right summand of the representative.
  exact le_sup_right

/-- Helper for Lemma 12.23.5: the source representative
`(\ker d ∩ F^p K) + \operatorname{im}(d)` stays inside the cycles. -/
private theorem homologyFiltrationRepresentative_le_cyclesSubobject (p : ℤ) :
    homologyFiltrationRepresentative K p ≤ cyclesSubobject K := by
  -- Both summands land in the cycles: the left one by projection, the right one by `d^2 = 0`.
  refine sup_le ?_ (boundariesSubobject_le_cyclesSubobject K)
  exact inf_le_left

/-- Helper for Lemma 12.23.5: the representative stages are antitone in the filtration index. -/
private theorem homologyFiltrationRepresentative_antitone {p q : ℤ} (hpq : p ≤ q) :
    homologyFiltrationRepresentative K q ≤ homologyFiltrationRepresentative K p := by
  -- Only the filtration summand changes with `p`; the boundary summand is fixed.
  refine sup_le ?_ le_sup_right
  exact le_sup_of_le_left <|
    inf_le_inf le_rfl ((K.X PUnit.unit).filtration.antitone_obj hpq)

/-- Helper for Lemma 12.23.5: consecutive representative stages form the quotient chain that
models the induced filtration on homology. -/
private theorem homologyFiltrationRepresentative_succ_le (p : ℤ) :
    homologyFiltrationRepresentative K (p + 1) ≤ homologyFiltrationRepresentative K p :=
  homologyFiltrationRepresentative_antitone K (show p ≤ p + 1 by omega)

/-- The intrinsic boundary representative is contained in the intrinsic cycle representative. -/
theorem homologyBoundaryStep_le_homologyCycleStep (p : ℤ) :
    homologyBoundaryStep K p ≤ homologyCycleStep K p := by
  -- Compare the boundary and cycle summands, then keep the common `F^{p+1}` term.
  refine sup_le ?_ le_sup_right
  exact le_sup_of_le_left (inf_le_inf (boundariesSubobject_le_cyclesSubobject K) le_rfl)

/-- The intrinsic cycle representative is contained in the eventual cycle representative. -/
theorem homologyCycleStep_le_eventualCycleStep (p : ℤ) :
    homologyCycleStep K p ≤ eventualCycleStep K p := by
  let Fp := filtrationStage K p
  let pullbackStage :=
    fun r : ℕ ↦
      (Subobject.pullback ((K.d PUnit.unit PUnit.unit).hom)).obj
        (filtrationStage K (p + r))
  -- Prove containment in each factor of the eventual intersection separately.
  refine le_iInf fun r ↦ sup_le ?_ le_sup_right
  have hkernel :
      (pullbackStage r).Factors (cyclesSubobject K).arrow := by
    rw [pullback_factors_iff]
    simpa [pullbackStage, cyclesSubobject] using
      (Subobject.factors_zero :
        (filtrationStage K (p + r)).Factors (0 : (cyclesSubobject K : C) ⟶ _))
  have hle : cyclesSubobject K ⊓ Fp ≤ Fp ⊓ pullbackStage r := by
    refine le_inf inf_le_right ?_
    refine Subobject.le_of_factors ?_
    simpa [Fp, pullbackStage] using
      (Subobject.factors_of_factors_right
        (Subobject.ofLE (cyclesSubobject K ⊓ Fp) (cyclesSubobject K) inf_le_left)
        hkernel)
  -- The cycle term lands in the left summand of the `r`-th eventual stage.
  simpa [Fp, pullbackStage, homologyCycleStep, eventualCycleStep] using hle.trans le_sup_left

/-- Helper for Lemma 12.23.5: the eventual boundary representative is contained in the eventual
cycle representative by passing through the intrinsic boundary and cycle representatives. -/
private theorem eventualBoundaryStep_le_eventualCycleStep (p : ℤ) :
    eventualBoundaryStep K p ≤ eventualCycleStep K p := by
  -- Compose the always-true boundary-to-cycle comparisons already established on the source side.
  exact
    (eventualBoundaryStep_le_homologyBoundaryStep K p).trans
      ((homologyBoundaryStep_le_homologyCycleStep K p).trans
        (homologyCycleStep_le_eventualCycleStep K p))

/-- Helper for Lemma 12.23.5: the textbook intrinsic quotient
`((im d ∩ F^p)+F^{p+1}) \ ((ker d ∩ F^p)+F^{p+1})` is already a subquotient of the eventual
source-facing quotient coming from the chain of representatives
`B_∞^p ≤ B(H)^p ≤ Z(H)^p ≤ Z_∞^p`. -/
theorem homology_subquotient_isSubquotient_eventual_subquotient (p : ℤ) :
    IsSubquotient
      (subobjectSubquotient (homologyBoundaryStep_le_homologyCycleStep K p))
      (subobjectSubquotient
        ((eventualBoundaryStep_le_homologyBoundaryStep K p).trans
          ((homologyBoundaryStep_le_homologyCycleStep K p).trans
            (homologyCycleStep_le_eventualCycleStep K p)))) := by
  -- Apply the general chain theorem to the four source-faithful representatives.
  exact subobjectSubquotient_isSubquotient_of_le_chain
    (eventualBoundaryStep_le_homologyBoundaryStep K p)
    (homologyBoundaryStep_le_homologyCycleStep K p)
    (homologyCycleStep_le_eventualCycleStep K p)

/-- Helper for Lemma 12.23.5: the ambient homology object `H(K)` is first made explicit as the
abelian coimage of `ker d ⟶ K / im(d)`. This isolates the owner used by the source proof before
comparing filtration stages inside it. -/
private noncomputable def ambient_homology_iso_coimage :
    (underlying K).homology PUnit.unit ≅
      Abelian.coimage
        (kernel.ι ((K.d PUnit.unit PUnit.unit).hom) ≫
          cokernel.π ((K.d PUnit.unit PUnit.unit).hom)) := by
  let S := (underlying K).sc' PUnit.unit PUnit.unit PUnit.unit
  -- First pass from the one-object complex homology to the centered short complex, then use the
  -- abelian coimage model of short-complex homology.
  exact
    (underlying K).homologyIsoSc' PUnit.unit PUnit.unit PUnit.unit rfl rfl ≪≫
      (ShortComplex.LeftHomologyData.ofAbelian S).homologyIso

/-- Helper for Lemma 12.23.5: the coimage owner of ambient homology is canonically the textbook
quotient `\ker(d) / \operatorname{im}(d)`. -/
private noncomputable theorem ambient_coimage_iso_intrinsic_subquotient :
    Abelian.coimage
      (kernel.ι ((K.d PUnit.unit PUnit.unit).hom) ≫
        cokernel.π ((K.d PUnit.unit PUnit.unit).hom)) ≅
      subobjectSubquotient (boundariesSubobject_le_cyclesSubobject K) := by
  let ψ :
      kernel ((K.d PUnit.unit PUnit.unit).hom) ⟶
        cokernel (boundariesSubobject K).arrow :=
    kernel.ι ((K.d PUnit.unit PUnit.unit).hom) ≫
      cokernel.π (boundariesSubobject K).arrow
  have hImage :
      imageSubobject ψ =
        subobjectSubquotientSubobject (boundariesSubobject_le_cyclesSubobject K) := by
    -- Compare the image of `ker(d) ⟶ K / im(d)` with the canonical `ker/im` representative.
    simpa [ψ, cyclesSubobject, boundariesSubobject] using
      (FilteredObject.image_subobject_toQuotient_eq_subobjectSubquotient
        (A := K.X PUnit.unit)
        (X := boundariesSubobject K)
        (Y := cyclesSubobject K)
        (boundariesSubobject_le_cyclesSubobject K))
  -- Move from the coimage owner to the image owner, then rewrite that image as `ker(d)/im(d)`.
  exact
    Abelian.coimageIsoImage ψ ≪≫
      (Abelian.imageIsoImage ψ).symm ≪≫
      (imageSubobjectIso ψ).symm ≪≫
      (Subobject.isoOfEq _ _ hImage)

/-- Helper for Lemma 12.23.5: the ambient homology owner is canonically the textbook quotient
`\ker(d) / \operatorname{im}(d)`. -/
private noncomputable theorem ambient_homology_iso_intrinsic_subquotient :
    (underlying K).homology PUnit.unit ≅
      subobjectSubquotient (boundariesSubobject_le_cyclesSubobject K) := by
  -- First expose `H(K)` as the coimage owner from the short-complex model, then rewrite that
  -- owner to the canonical `ker/im` quotient.
  exact
    ambient_homology_iso_coimage K ≪≫
      ambient_coimage_iso_intrinsic_subquotient K

/-- Helper for Lemma 12.23.5: each stage homology object `H(F^q K)` has the same short-complex
coimage presentation as the ambient homology object, now taken inside the one-object stage
complex. This is the left-endpoint owner exposed by the source proof before comparing images in
the ambient quotient. -/
private noncomputable def stage_homology_iso_coimage (q : ℤ) :
    (stage K q).homology PUnit.unit ≅
      Abelian.coimage
        (kernel.ι (((stage K q).d PUnit.unit PUnit.unit).hom) ≫
          cokernel.π (((stage K q).d PUnit.unit PUnit.unit).hom)) := by
  let S := (stage K q).sc' PUnit.unit PUnit.unit PUnit.unit
  -- The stage complex is again one-object, so the same short-complex/coimage comparison applies
  -- verbatim after replacing `K` by `stage K q`.
  exact
    (stage K q).homologyIsoSc' PUnit.unit PUnit.unit PUnit.unit rfl rfl ≪≫
      (ShortComplex.LeftHomologyData.ofAbelian S).homologyIso

/-- Helper for Lemma 12.23.5: the representative
`(\ker d ∩ F^p K) + \operatorname{im}(d)` always contains the boundaries and is contained in the
cycles. -/
private theorem homologyFiltrationRepresentative_bounds (p : ℤ) :
    boundariesSubobject K ≤ homologyFiltrationRepresentative K p ∧
      homologyFiltrationRepresentative K p ≤ cyclesSubobject K := by
  -- The boundary term is one summand of the representative, and the whole representative stays in
  -- the cycles because `im(d) ≤ ker(d)`.
  exact
    ⟨boundariesSubobject_le_homologyFiltrationRepresentative K p,
      homologyFiltrationRepresentative_le_cyclesSubobject K p⟩

/-- Helper for Lemma 12.23.5: on the quotient owner `\ker(d) / \operatorname{im}(d)`, the
quotient filtration coming from `\ker(d)` agrees with the filtration induced from the ambient
quotient `K / \operatorname{im}(d)`. -/
private theorem cycles_subquotient_filtration_eq_induced :
    (((K.X PUnit.unit).filtration.induced (cyclesSubobject K)).quotient
        (((K.X PUnit.unit).subobjectToSubquotient
          (boundariesSubobject_le_cyclesSubobject K)).hom)) =
      ((K.X PUnit.unit).subobjectSubquotientFilteredObject
        (boundariesSubobject_le_cyclesSubobject K)).filtration := by
  -- This is exactly Lemma `12.19.9` specialized to
  -- `im(d) ⊆ ker(d) ⊆ K`.
  simpa [cyclesSubobject, boundariesSubobject] using
    (FilteredObject.subquotient_quotient_filtration_eq_induced_filtration
      (A := K.X PUnit.unit)
      (X := boundariesSubobject K)
      (Y := cyclesSubobject K)
      (boundariesSubobject_le_cyclesSubobject K))

/-- Helper for Lemma 12.23.5: after embedding `\ker(d) / \operatorname{im}(d)` into the ambient
quotient `K / \operatorname{im}(d)`, its `p`-th stage becomes the image of the `p`-th filtered
cycle stage. -/
private theorem cycles_subquotient_stage_map_eq_image_stage_toQuotient (p : ℤ) :
    (Subobject.map
        (subobjectSubquotientSubobject
          (boundariesSubobject_le_cyclesSubobject K)).arrow).obj
        (((K.X PUnit.unit).subobjectSubquotientFilteredObject
          (boundariesSubobject_le_cyclesSubobject K)).filtration p) =
      imageSubobject
        ((((K.X PUnit.unit).filtration.induced (cyclesSubobject K)) p).arrow ≫
          (cyclesSubobject K).arrow ≫
            cokernel.π (boundariesSubobject K).arrow) := by
  -- This is the stagewise form of the same quotient-filtration comparison.
  simpa [cyclesSubobject, boundariesSubobject] using
    (FilteredObject.subobjectSubquotient_stage_map_eq_image_stage_toQuotient
      (A := K.X PUnit.unit)
      (X := boundariesSubobject K)
      (Y := cyclesSubobject K)
      (boundariesSubobject_le_cyclesSubobject K)
      p)

/-- Helper for Lemma 12.23.5: once the transported `q`-th stage of the induced homology
filtration is identified with the `q`-th stage of the canonical quotient filtration on
`\ker(d) / \operatorname{im}(d)`, the entire transported filtration agrees with that canonical
filtration. -/
private theorem transported_inducedHomologyFiltration_eq_subobjectSubquotientFiltration_of_stagewise
    (hstage :
      ∀ q : ℤ,
        imageSubobject (homologyMap K q ≫ (ambient_homology_iso_intrinsic_subquotient K).hom) =
          ((K.X PUnit.unit).subobjectSubquotientFilteredObject
            (boundariesSubobject_le_cyclesSubobject K)).filtration q) :
    (Subobject.mapIsoToOrderIso (ambient_homology_iso_intrinsic_subquotient K)).comp
        (inducedHomologyFiltration K) =
      ((K.X PUnit.unit).subobjectSubquotientFilteredObject
        (boundariesSubobject_le_cyclesSubobject K)).filtration := by
  ext q
  -- The owner stage of `inducedHomologyFiltration K` is definitionally the image of
  -- `homologyMap K q`, so the given stagewise comparison is exactly the desired equality.
  simpa [HomologicalComplex.Filtered.inducedHomologyFiltration_obj] using hstage q

/-- Helper for Lemma 12.23.5: the canonical limit term `E_∞^p` is the quotient of the eventual
cycle and boundary pieces inside the page-one owner. -/
private theorem limitTerm_infinityPage_def
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0)
    [IsAssociatedToFilteredDifferentialObject K E]
    (p : ℤ) :
    (toPageOneSpectralSequence K E).infinityPage p =
      cokernel
        (Subobject.ofLE
          ((toPageOneSpectralSequence K E).boundaryInfinity p)
          ((toPageOneSpectralSequence K E).cycleInfinity p)
          ((toPageOneSpectralSequence K E).boundaryInfinity_le_cycleInfinity p)) := by
  -- Unfold the page-one view of the associated spectral sequence and apply the public
  -- `SpectralSequence.infinityPage_def`.
  simpa using SpectralSequence.infinityPage_def (toPageOneSpectralSequence K E) p

/-- Helper for Lemma 12.23.5: the graded piece of the induced homology filtration is the
canonical quotient of the consecutive homology-image stages, hence it should agree with the
intrinsic quotient built from `homologyBoundaryStep` and `homologyCycleStep`. -/
theorem induced_homology_graded_piece_iso_intrinsic_subquotient (p : ℤ) :
    Nonempty (((inducedHomologyFiltration K).gradedPiece p) ≅
      subobjectSubquotient (homologyBoundaryStep_le_homologyCycleStep K p)) := by
  -- Route correction: compare the two consecutive image stages of `homologyMap` to the textbook
  -- representatives, then use the same `Subobject.underlyingIso` and `cokernel.mapIso` pattern
  -- as the module proof of `12.24.5.2`.
  -- The ambient owner is now explicit as `ambient_homology_iso_coimage K`, so the remaining work
  -- is to compare the image stages of `homologyMap K q` with the source representatives inside
  -- the concrete quotient owner `ambient_homology_iso_intrinsic_subquotient K` before taking the
  -- cokernel of the stage inclusion.
  -- The source representative chain inside `K` is now explicit:
  -- `boundaries ≤ homologyFiltrationRepresentative (p + 1) ≤ homologyFiltrationRepresentative p ≤ cycles`.
  -- TODO: first identify each owner stage `(inducedHomologyFiltration K).obj q` with the
  -- quotient `homologyFiltrationRepresentative K q / boundariesSubobject K`, then rewrite the
  -- graded piece as the quotient of consecutive representatives using
  -- `homologyFiltrationRepresentative_succ_le`; the quotient-owner API needed for this first step
  -- is now available as `stage_homology_iso_coimage`,
  -- `homologyFiltrationRepresentative_bounds`,
  -- `cycles_subquotient_filtration_eq_induced`, and
  -- `cycles_subquotient_stage_map_eq_image_stage_toQuotient`. The remaining gap is the explicit
  -- stage-image transport across `ambient_homology_iso_intrinsic_subquotient K`, followed by the
  -- second-isomorphism comparison with
  -- `subobjectSubquotient (homologyBoundaryStep_le_homologyCycleStep K p)`.
  sorry

/-- Helper for Lemma 12.23.5: after transporting the eventual source-facing quotient through the
page-one owner `(E.page 1).X p`, the intrinsic homology quotient becomes a subquotient of the
canonical infinity-page owner `E_∞^p`. -/
theorem intrinsic_subquotient_isSubquotient_limitTerm
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0)
    [IsAssociatedToFilteredDifferentialObject K E]
    (p : ℤ) :
    IsSubquotient (subobjectSubquotient (homologyBoundaryStep_le_homologyCycleStep K p))
      ((toPageOneSpectralSequence E).infinityPage p) := by
  have hchain :
      IsSubquotient
        (subobjectSubquotient (homologyBoundaryStep_le_homologyCycleStep K p))
        (subobjectSubquotient
          ((eventualBoundaryStep_le_homologyBoundaryStep K p).trans
            ((homologyBoundaryStep_le_homologyCycleStep K p).trans
              (homologyCycleStep_le_eventualCycleStep K p)))) :=
    homology_subquotient_isSubquotient_eventual_subquotient K p
  -- Route correction: the chain comparison is now closed; the only missing step is to transport
  -- its right endpoint from the eventual source quotient to the canonical owner `E_∞^p`.
  -- TODO: compare the recursive `cycle` and `boundary` subobjects on page one with the textbook
  -- representatives under `pageOneIso K E p`, pass to `cycleInfinity` and `boundaryInfinity`,
  -- and then rewrite `E_∞^p` via `limitTerm_infinityPage_def K E p`.
  sorry

/-- Helper for Lemma 12.23.5: once the left endpoint is identified with the intrinsic homology
quotient and that intrinsic quotient is compared with the canonical limit term `E_∞^p`, the main
subquotient statement follows by transporting only the left endpoint. -/
private theorem induced_homology_graded_piece_isSubquotient_limitTerm_of_endpoint_comparisons
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0)
    [IsAssociatedToFilteredDifferentialObject K E]
    (p : ℤ)
    (hLeft :
      Nonempty (((inducedHomologyFiltration K).gradedPiece p) ≅
        subobjectSubquotient (homologyBoundaryStep_le_homologyCycleStep K p)))
    (hRight :
      IsSubquotient (subobjectSubquotient (homologyBoundaryStep_le_homologyCycleStep K p))
        ((toPageOneSpectralSequence E).infinityPage p)) :
    IsSubquotient ((inducedHomologyFiltration K).gradedPiece p)
      ((toPageOneSpectralSequence E).infinityPage p) := by
  obtain ⟨eLeft⟩ := hLeft
  -- The source-faithful finish transports the graded piece `gr^p H(K)` to the intrinsic
  -- quotient, then applies the intrinsic comparison with `E_∞^p`.
  exact CategoryTheory.IsSubquotient.of_iso eLeft hRight

/-- Lemma 12.23.5: once the eventual cycle and boundary pieces `Z_∞^p` and `B_∞^p` exist, the
always-true inclusions `(12.23.5.2)` and `(12.23.5.1)` show that the graded piece `gr^p H(K)` of
the induced homology filtration is a subquotient of the canonical limit term `E_∞^p` of the
associated spectral sequence. -/
@[stacks 012F]
theorem inducedHomologyGradedPiece_isSubquotient_limitTerm
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0)
    [IsAssociatedToFilteredDifferentialObject K E]
    (p : ℤ) :
    IsSubquotient ((inducedHomologyFiltration K).gradedPiece p)
      ((toPageOneSpectralSequence E).infinityPage p) := by
  -- Combine the left-endpoint identification with the intrinsic-right-endpoint comparison.
  exact
    induced_homology_graded_piece_isSubquotient_limitTerm_of_endpoint_comparisons
      K E p
      (induced_homology_graded_piece_iso_intrinsic_subquotient K p)
      (intrinsic_subquotient_isSubquotient_limitTerm K E p)

end WeakConvergence

end HomologicalComplex.Filtered

end CategoryTheory
