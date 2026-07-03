import StacksProject_2024.Chap12.Definition_12_23_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace DecreasingFiltration

variable [HasZeroMorphisms C] [HasKernels C]
variable [LocallySmall C] [WellPowered C] [HasWidePullbacks C] [HasImages C] [HasCoproducts C]
  [InitialMonoClass C]
variable {X Y : C}

-- Proof sketch: it is enough to show that the left-hand side is contained in each factor of the
-- infimum. The summand `F^{p + 1} X` already lies in every factor. For the kernel summand, the
-- arrow of `kernelSubobject f` composes to zero with `f`, so it factors through the pullback of
-- every target filtration stage along `f`.
/-- Core/canonical owner: for a morphism `f : X ⟶ Y` between objects equipped with decreasing
filtrations `F` and `G`, the subobject `Ker(f) ∩ F^p X + F^{p + 1} X` is contained in the
intersection, over all natural numbers `r`, of the subobjects
`(F^p X ∩ f⁻¹(G^{p + r} Y)) + F^{p + 1} X`. -/
theorem kernel_inf_stage_sup_next_le_iInf_pullback_target_stage_sup_next
    (f : X ⟶ Y) (F : DecreasingFiltration X) (G : DecreasingFiltration Y) (p : ℤ) :
    ((kernelSubobject f ⊓ F.obj p) ⊔ F.obj (p + 1)) ≤
      ⨅ r : ℕ, ((F.obj p ⊓ (Subobject.pullback f).obj (G.obj (p + r))) ⊔ F.obj (p + 1)) := by
  let Fp := F.obj p
  let pullbackStage (r : ℕ) := (Subobject.pullback f).obj (G.obj (p + r))
  refine le_iInf fun r ↦ sup_le ?_ le_sup_right
  have hkernel :
      (pullbackStage r).Factors (kernelSubobject f).arrow := by
    rw [pullback_factors_iff]
    simpa using
      (Subobject.factors_zero :
        (G.obj (p + r)).Factors (0 : (kernelSubobject f : C) ⟶ _))
  have hle : kernelSubobject f ⊓ Fp ≤ Fp ⊓ pullbackStage r := by
    refine le_inf inf_le_right ?_
    refine Subobject.le_of_factors ?_
    simpa [Fp, pullbackStage] using
      (Subobject.factors_of_factors_right
        (Subobject.ofLE (kernelSubobject f ⊓ Fp) (kernelSubobject f) inf_le_left)
        hkernel)
  simpa [Fp, pullbackStage] using hle.trans le_sup_left

end DecreasingFiltration

namespace HomologicalComplex.Filtered

variable [Abelian C]
variable [LocallySmall C] [WellPowered C] [HasWidePullbacks C] [HasCoproducts C]
  [InitialMonoClass C]
variable (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))
variable (p : ℤ)

/- Domain-style sampling for 12.23.5.1:
- primary domain: filtration-stage estimates for a one-object filtered differential object;
- sampled owner declarations in this domain:
  `DecreasingFiltration.kernel_inf_stage_sup_next_le_iInf_pullback_target_stage_sup_next`,
  `HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1})`,
  `FilteredObject.Hom.preserves`,
  `Subobject.pullback`;
- best owner abstraction: the two-filtration subobject inequality on a morphism, specialized here
  to the one-object filtered differential object `K`;
- primitive data: the differential morphism and the source/target filtrations;
- derived API: the source-facing filtered-differential-object specialization of the owner theorem;
- source/core/bridge triage:
  `source-facing`: equation `(12.23.5.1)` for one filtered differential object;
  `core/canonical`: the owner theorem
    `DecreasingFiltration.kernel_inf_stage_sup_next_le_iInf_pullback_target_stage_sup_next`;
  `bridge/view`: the one-object filtered-differential-object specialization obtained by taking the
    source and target filtrations both equal to `(K.X PUnit.unit).filtration`.

This item adds no new public owner beyond that theorem, so it is refined to a direct
specialization check rather than a parallel local theorem. -/
/- 12.23.5.1 is the one-object filtered-differential-object specialization of the owner theorem
`DecreasingFiltration.kernel_inf_stage_sup_next_le_iInf_pullback_target_stage_sup_next`. -/
#check
  (DecreasingFiltration.kernel_inf_stage_sup_next_le_iInf_pullback_target_stage_sup_next
      (K.d PUnit.unit PUnit.unit).hom
      (K.X PUnit.unit).filtration
      (K.X PUnit.unit).filtration
      p :
    ((kernelSubobject (K.d PUnit.unit PUnit.unit).hom ⊓ (K.X PUnit.unit).filtration.obj p) ⊔
        (K.X PUnit.unit).filtration.obj (p + 1)) ≤
      ⨅ r : ℕ,
        (((K.X PUnit.unit).filtration.obj p ⊓
              (Subobject.pullback (K.d PUnit.unit PUnit.unit).hom).obj
                ((K.X PUnit.unit).filtration.obj (p + r))) ⊔
            (K.X PUnit.unit).filtration.obj (p + 1)))

end HomologicalComplex.Filtered

end CategoryTheory
