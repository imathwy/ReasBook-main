import Mathlib
import stacks_project.Chap12.Aux_12_20_2_1
import stacks_project.Chap12.Definition_12_20_2
import stacks_project.Chap12.Lemma_12_23_2

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

-- Proof sketch: the source-facing inclusions from `(12.23.5.2)` and `(12.23.5.1)` place the
-- intrinsic representatives `homologyBoundaryStep K p ≤ homologyCycleStep K p` between the
-- actual limiting boundary and cycle pieces. Therefore `gr^p H(K)` is the intermediate quotient
-- of a chain of subobjects inside the eventual quotient `E_∞^p`.
/-- The eventual boundary representative is contained in the intrinsic boundary representative. -/
theorem eventualBoundaryStep_le_homologyBoundaryStep (p : ℤ) :
    eventualBoundaryStep K p ≤ homologyBoundaryStep K p := by
  sorry

/-- The intrinsic boundary representative is contained in the intrinsic cycle representative. -/
theorem homologyBoundaryStep_le_homologyCycleStep (p : ℤ) :
    homologyBoundaryStep K p ≤ homologyCycleStep K p := by
  sorry

/-- The intrinsic cycle representative is contained in the eventual cycle representative. -/
theorem homologyCycleStep_le_eventualCycleStep (p : ℤ) :
    homologyCycleStep K p ≤ eventualCycleStep K p := by
  sorry

/-- Lemma 12.23.5: once the eventual cycle and boundary pieces `Z_∞^p` and `B_∞^p` exist, the
always-true inclusions `(12.23.5.2)` and `(12.23.5.1)` show that the graded piece `gr^p H(K)` of
the induced homology filtration is a subquotient of the canonical limit term `E_∞^p` of the
associated spectral sequence. -/
theorem inducedHomologyGradedPiece_isSubquotient_limitTerm
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0)
    [IsAssociatedToFilteredDifferentialObject K E]
    (p : ℤ) :
    IsSubquotient ((inducedHomologyFiltration K).gradedPiece p)
      ((toPageOneSpectralSequence E).infinityPage p) := by
  sorry

end WeakConvergence

end HomologicalComplex.Filtered

end CategoryTheory
