import Mathlib
import Mathlib.Algebra.Homology.CochainComplexOpposite
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import StacksProject_2024.stacks_project.Chap12.Definition_12_24_5
import StacksProject_2024.stacks_project.Chap12.Definition_12_24_9
import StacksProject_2024.stacks_project.Chap13.Definition_13_11_3
import StacksProject_2024.stacks_project.Chap13.Lemma_13_27_9
import StacksProject_2024.stacks_project.Chap13.Lemma_13_11_6
import StacksProject_2024.stacks_project.Chap15.Definition_15_59_13

open scoped BigOperators
open scoped DerivedTensorProduct
open scoped ZeroObject
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open CochainComplex
open DerivedCategory.TStructure

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

namespace CochainComplex

section Filtrations

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): the degreewise subobject defining the
local upper-truncation filtration. -/
private def truncationFiltrationSubobject (K : CochainComplex 𝒜 ℤ) (p n : ℤ) :
    Subobject (K.X n) :=
  if n < -p then
    ⊤
  else if n = -p then
    kernelSubobject (K.d n (n + 1))
  else
    ⊥

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): the local truncation filtration is
decreasing in the filtration index. -/
private theorem truncationFiltration_decreasing (K : CochainComplex 𝒜 ℤ) {p q n : ℤ}
    (hpq : p ≤ q) :
    truncationFiltrationSubobject K q n ≤ truncationFiltrationSubobject K p n := by
  -- As `p` increases, the cutoff `-p` decreases, so the later stage can only shrink.
  by_cases hqn : n < -q
  · have hpn : n < -p := lt_of_lt_of_le hqn (by simpa using neg_le_neg hpq)
    simp [truncationFiltrationSubobject, hqn, hpn]
  · by_cases heqn : n = -q
    · by_cases hpq_eq : p = q
      · subst hpq_eq
        simp [truncationFiltrationSubobject, hqn, heqn]
      · have hpn : n < -p := by
          omega
        have hpq_lt : p < q := lt_of_le_of_ne hpq hpq_eq
        simp [truncationFiltrationSubobject, heqn, hpn, hpq_lt]
    · simp [truncationFiltrationSubobject, hqn, heqn]

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): the local truncation filtration is
preserved by the differential. -/
private theorem truncationFiltration_d_preserves (K : CochainComplex 𝒜 ℤ) (p i j : ℤ) :
    truncationFiltrationSubobject K p i ≤
      (Subobject.pullback (K.d i j)).obj (truncationFiltrationSubobject K p j) := by
  -- Route correction: this is a degreewise cutoff argument, so we keep it local and avoid the
  -- heavier Chapter 13 owner route that caused the import-chain failure.
  by_cases hi_lt : i < -p
  · by_cases hij : j = i + 1
    · subst hij
      by_cases hj_lt : i + 1 < -p
      · rw [truncationFiltrationSubobject, if_pos hi_lt, truncationFiltrationSubobject,
          if_pos hj_lt, Subobject.pullback_top]
      · have hj_eq : i + 1 = -p := by omega
        rw [truncationFiltrationSubobject, if_pos hi_lt, truncationFiltrationSubobject,
          if_neg hj_lt, if_pos hj_eq]
        apply Subobject.le_of_factors
        rw [pullback_factors_iff]
        exact kernelSubobject_factors _ _ (by
          simpa using K.d_comp_d i (i + 1) (i + 2))
    · have hd : K.d i j = 0 := by
        have hshape : ¬ (ComplexShape.up ℤ).Rel i j := by
          simpa [ComplexShape.up, eq_comm] using hij
        apply K.shape
        exact hshape
      rw [truncationFiltrationSubobject, if_pos hi_lt]
      apply Subobject.le_of_factors
      rw [pullback_factors_iff]
      simpa [hd] using
        (Subobject.factors_zero :
          (truncationFiltrationSubobject K p j).Factors
            (0 : ((⊤ : Subobject (K.X i)) : 𝒜) ⟶ K.X j))
  · by_cases hi_eq : i = -p
    · subst i
      by_cases hij : j = -p + 1
      · subst j
        rw [truncationFiltrationSubobject, if_neg (lt_irrefl _), if_pos rfl,
          truncationFiltrationSubobject]
        have hj_not_lt : ¬ -p + 1 < -p := by omega
        have hj_ne : ¬ -p + 1 = -p := by omega
        rw [if_neg hj_not_lt, if_neg hj_ne]
        apply Subobject.le_of_factors
        rw [pullback_factors_iff]
        exact (Subobject.bot_factors_iff_zero _).2 (by
          simpa using (kernelSubobject_arrow_comp (f := K.d (-p) (-p + 1))))
      · have hd : K.d (-p) j = 0 := by
          have hshape : ¬ (ComplexShape.up ℤ).Rel (-p) j := by
            simpa [ComplexShape.up, eq_comm] using hij
          apply K.shape
          exact hshape
        rw [truncationFiltrationSubobject, if_neg (lt_irrefl _), if_pos rfl]
        apply Subobject.le_of_factors
        rw [pullback_factors_iff]
        simpa [hd] using
          (Subobject.factors_zero :
            (truncationFiltrationSubobject K p j).Factors
              (0 : ((kernelSubobject (K.d (-p) (-p + 1)) : Subobject (K.X (-p))) : 𝒜) ⟶
                K.X j))
    · rw [truncationFiltrationSubobject, if_neg hi_lt, if_neg hi_eq]
      exact bot_le

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): the local source filtration with stages
`F^p(K^•) = τ_{\le -p}(K^•)`. -/
def truncationFiltration (K : CochainComplex 𝒜 ℤ) : FilteredComplex 𝒜 where
  X n :=
    { obj := K.X n
      filtration :=
        { toFun := fun p ↦ truncationFiltrationSubobject K p n
          monotone' := fun _ _ hpq ↦ truncationFiltration_decreasing K hpq } }
  d i j :=
    { hom := K.d i j
      preserves := fun p ↦
        (pullback_factors_iff (K.d i j) (truncationFiltrationSubobject K p j)
          (truncationFiltrationSubobject K p i).arrow).1 <|
          (Subobject.factors_iff _ _).2
            ⟨Subobject.ofLE _ _ (truncationFiltration_d_preserves K p i j),
              Subobject.ofLE_arrow (truncationFiltration_d_preserves K p i j)⟩ }
  shape := fun i j hij ↦ FilteredObject.forget.map_injective (K.shape i j hij)
  d_comp_d' := fun i j k hij hjk ↦
    FilteredObject.forget.map_injective (K.d_comp_d' i j k hij hjk)

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): below the cutoff, the local
truncation-filtration stage agrees with the original term. -/
private theorem truncation_filtration_stage_term_iso_of_lt
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hn : n < -p) :
    ∃ e : ((K.truncationFiltration).stage p).X n ≅ K.X n,
      e.hom = ((K.truncationFiltration).stageInclusion p).f n := by
  -- Strictly below the cutoff, the local stage is the top subobject.
  change ∃ e : ((truncationFiltrationSubobject K p n : 𝒜) ≅ K.X n),
      e.hom = (truncationFiltrationSubobject K p n).arrow
  rw [truncationFiltrationSubobject, if_pos hn]
  rw [Subobject.top_eq_id]
  refine ⟨Subobject.underlyingIso (𝟙 (K.X n)), ?_⟩
  simpa using (Subobject.underlyingIso_hom_comp_eq_mk (𝟙 (K.X n)))

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): at the cutoff degree, the local
truncation-filtration stage is the cycles object. -/
private theorem truncation_filtration_stage_term_iso_cycles
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) :
    ∃ e : ((K.truncationFiltration).stage p).X (-p) ≅ K.cycles (-p),
      e.hom ≫ K.iCycles (-p) = ((K.truncationFiltration).stageInclusion p).f (-p) := by
  -- At the cutoff, the stage object is the kernel subobject of the outgoing differential.
  change ∃ e : ((truncationFiltrationSubobject K p (-p) : 𝒜) ≅ K.cycles (-p)),
      e.hom ≫ K.iCycles (-p) = (truncationFiltrationSubobject K p (-p)).arrow
  rw [truncationFiltrationSubobject, if_neg (lt_irrefl _), if_pos rfl]
  let S : ShortComplex 𝒜 := K.sc' (-p - 1) (-p) (-p + 1)
  let hprev : (ComplexShape.up ℤ).prev (-p) = -p - 1 := by
    apply ComplexShape.prev_eq'
    simpa [ComplexShape.up, ComplexShape.up'] using (show (-p - 1 : ℤ) + 1 = -p by omega)
  let hnext : (ComplexShape.up ℤ).next (-p) = -p + 1 := by
    apply ComplexShape.next_eq'
    simpa [ComplexShape.up, ComplexShape.up'] using (show (-p : ℤ) + 1 = -p + 1 by omega)
  refine ⟨kernelSubobjectIso (K.d (-p) (-p + 1)) ≪≫ S.cyclesIsoKernel.symm ≪≫
      (K.cyclesIsoSc' (-p - 1) (-p) (-p + 1) hprev hnext).symm, ?_⟩
  -- Rewrite the kernel inclusion through the standard cycles-kernel comparison.
  simp [S, Category.assoc, ShortComplex.cyclesIsoKernel,
    K.cyclesIsoSc'_inv_iCycles (-p - 1) (-p) (-p + 1) hprev hnext]
  have hk :
      kernel.ι (K.d (-p) (-p + 1)) ≫ S.g = 0 := by
    dsimp [S]
    exact kernel.condition (K.d (-p) (-p + 1))
  have hlift :
      S.liftCycles (kernel.ι (K.d (-p) (-p + 1))) hk ≫ S.iCycles =
        kernel.ι (K.d (-p) (-p + 1)) := by
    simpa [S] using
      (ShortComplex.liftCycles_i
        (S := S) (k := kernel.ι (K.d (-p) (-p + 1))) (hk := hk))
  calc
    (kernelSubobjectIso (K.d (-p) (-p + 1))).hom ≫
        (S.liftCycles (kernel.ι (K.d (-p) (-p + 1))) hk) ≫
          S.iCycles
      =
        (kernelSubobjectIso (K.d (-p) (-p + 1))).hom ≫ kernel.ι (K.d (-p) (-p + 1)) := by
          simpa only [Category.assoc] using
            congrArg
              (fun f ↦ (kernelSubobjectIso (K.d (-p) (-p + 1))).hom ≫ f)
              hlift
    _ = (kernelSubobject (K.d (-p) (-p + 1))).arrow := by
          simpa using (kernelSubobject_arrow (f := K.d (-p) (-p + 1)))

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): above the cutoff, the local
truncation-filtration stage vanishes. -/
private theorem truncation_filtration_stage_term_isZero_of_gt
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hn : -p < n) :
    IsZero (((K.truncationFiltration).stage p).X n) := by
  -- Strictly above the cutoff, the stage subobject is bottom.
  change IsZero ((truncationFiltrationSubobject K p n : 𝒜))
  rw [truncationFiltrationSubobject, if_neg (not_lt_of_ge (le_of_lt hn))]
  rw [if_neg (by omega : ¬ n = -p)]
  exact (isZero_zero _).of_iso Subobject.botCoeIsoZero

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): an index on or below the cutoff is
represented by the standard `embeddingUpIntLE`. -/
private theorem embeddingUpIntLE_toNat_sub_eq
    (p n : ℤ) (hn : n ≤ -p) :
    (embeddingUpIntLE (-p)).f (Int.toNat (-p - n)) = n := by
  -- The difference `-p - n` is nonnegative at and below the cutoff.
  dsimp [ComplexShape.embeddingUpIntLE]
  rw [Int.toNat_of_nonneg]
  · omega
  · omega

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): below the cutoff, the canonical
truncation term is the original term. -/
private noncomputable def truncLE_term_iso_of_lt
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hn : n < -p) :
    (K.truncLE (-p)).X n ≅ K.X n :=
  let i : ℕ := Int.toNat (-p - n)
  let hi' : (embeddingUpIntLE (-p)).f i = n := embeddingUpIntLE_toNat_sub_eq p n (le_of_lt hn)
  let hboundary : ¬ (embeddingUpIntLE (-p)).BoundaryLE i := by
    rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff]
    intro hi0
    have : -p = n := by
      simpa [i, hi0, ComplexShape.embeddingUpIntLE] using hi'
    omega
  K.truncLEXIso (e := embeddingUpIntLE (-p)) hi' hboundary

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): at the cutoff, the canonical
truncation term is the cycles object. -/
private noncomputable def truncLE_term_iso_cycles
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) :
    (K.truncLE (-p)).X (-p) ≅ K.cycles (-p) :=
  let hi' : (embeddingUpIntLE (-p)).f 0 = -p := by
    simp [ComplexShape.embeddingUpIntLE]
  let hboundary : (embeddingUpIntLE (-p)).BoundaryLE 0 := by
    simpa using (ComplexShape.boundaryLE_embeddingUpIntLE_iff (-p) 0).2 rfl
  K.truncLEXIsoCycles (e := embeddingUpIntLE (-p)) hi' hboundary

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): above the cutoff, the canonical
truncation term vanishes. -/
private theorem truncLE_term_isZero_of_gt
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hn : -p < n) :
    IsZero ((K.truncLE (-p)).X n) := by
  -- The upper truncation is strictly supported in degrees `≤ -p`.
  exact (K.truncLE (-p)).isZero_of_isStrictlyLE (-p) n hn

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): degreewise, the local stage agrees
with the canonical upper truncation. -/
private noncomputable abbrev truncation_filtration_stage_component_iso
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) :
    ((K.truncationFiltration).stage p).X n ≅ (K.truncLE (-p)).X n := by
  -- Use the same three cutoff regions everywhere so later rewrites have one fixed comparison.
  by_cases hn_lt : n < -p
  · exact Classical.choose (truncation_filtration_stage_term_iso_of_lt K p n hn_lt) ≪≫
      (truncLE_term_iso_of_lt K p n hn_lt).symm
  · by_cases hn_eq : n = -p
    · subst hn_eq
      exact Classical.choose (truncation_filtration_stage_term_iso_cycles K p) ≪≫
        (truncLE_term_iso_cycles K p).symm
    · have hn_gt : -p < n := by omega
      exact (truncation_filtration_stage_term_isZero_of_gt K p n hn_gt).isoZero ≪≫
        (truncLE_term_isZero_of_gt K p n hn_gt).isoZero.symm

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): below the cutoff, the truncation
inclusion component is the retained-term identification. -/
private theorem ιTruncLE_component_eq_of_lt
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hn : n < -p) :
    (K.ιTruncLE (-p)).f n = (truncLE_term_iso_of_lt K p n hn).hom := by
  let e := embeddingUpIntLE (-p)
  let i : ℕ := Int.toNat (-p - n)
  have hi' : e.f i = n := embeddingUpIntLE_toNat_sub_eq p n (le_of_lt hn)
  have hi : ¬ e.BoundaryLE i := by
    rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff]
    intro hi0
    have : -p = n := by
      simpa [e, i, hi0, ComplexShape.embeddingUpIntLE] using hi'
    omega
  -- Read the component from the dual truncation formula and then unop it.
  apply Quiver.Hom.op_inj
  change ((K.op.πTruncGE e.op).f n) =
    (K.op.truncGEXIso e.op hi' (by simpa using hi)).inv
  dsimp [CochainComplex.πTruncGE, HomologicalComplex.πTruncGE]
  rw [e.op.liftExtend_f (K.op.restrictionToTruncGE' e.op)
      (K.op.restrictionToTruncGE'_hasLift e.op) hi']
  rw [K.op.restrictionToTruncGE'_f_eq_iso_hom_iso_inv e.op hi' (by simpa using hi)]
  simp [HomologicalComplex.truncGEXIso, Category.assoc]
  rfl

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): at the cutoff, the truncation
inclusion component is the cycles inclusion. -/
private theorem ιTruncLE_component_eq_cycles
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) :
    (K.ιTruncLE (-p)).f (-p) = (truncLE_term_iso_cycles K p).hom ≫ K.iCycles (-p) := by
  let e := embeddingUpIntLE (-p)
  let hi' : e.f 0 = -p := by
    simpa [e] using (embeddingUpIntLE_toNat_sub_eq p (-p) le_rfl)
  have hi : e.BoundaryLE 0 := by
    simpa [e] using (ComplexShape.boundaryLE_embeddingUpIntLE_iff (-p) 0).2 rfl
  -- Route correction: the cutoff component is the dual boundary formula for `πTruncGE`.
  apply Quiver.Hom.op_inj
  change ((K.op.πTruncGE e.op).f (-p)) =
    ((truncLE_term_iso_cycles K p).hom ≫ K.iCycles (-p)).op
  dsimp [CochainComplex.πTruncGE, HomologicalComplex.πTruncGE]
  rw [e.op.liftExtend_f (K.op.restrictionToTruncGE' e.op)
      (K.op.restrictionToTruncGE'_hasLift e.op) hi']
  rw [K.op.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv e.op hi' (by simpa using hi)]
  simp [Category.assoc]
  change (K.op.pOpcycles (-p) ≫
      ((K.op.truncGE'XIsoOpcycles e.op hi' (by simpa using hi)).inv ≫
        (((K.op.truncGE' e.op).extendXIso e.op hi').inv))) =
    (K.sc (-p)).iCycles.op ≫ (truncLE_term_iso_cycles K p).hom.op
  rw [← (K.sc (-p)).op_pOpcycles_opcyclesOpIso_hom]
  have hcut :
      (K.opcyclesOpIso (-p)).hom ≫ (truncLE_term_iso_cycles K p).hom.op =
        (K.op.truncGE'XIsoOpcycles e.op hi' (by simpa using hi)).inv ≫
          (((K.op.truncGE' e.op).extendXIso e.op hi').inv) := by
    simp [truncLE_term_iso_cycles, CochainComplex.truncLE, HomologicalComplex.truncLEXIsoCycles,
      HomologicalComplex.truncGEXIsoOpcycles, HomologicalComplex.opcyclesOpIso,
      Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
    rfl
  simpa [HomologicalComplex.opcyclesOpIso, Category.assoc] using
    congrArg (fun f ↦ K.op.pOpcycles (-p) ≫ f) hcut.symm

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): degreewise, the chosen comparison
factors the local stage inclusion through the canonical truncation inclusion. -/
private theorem truncation_filtration_stage_component_hom_comp_ιTruncLE
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) :
    (truncation_filtration_stage_component_iso K p n).hom ≫ (K.ιTruncLE (-p)).f n =
      ((K.truncationFiltration).stageInclusion p).f n := by
  -- Compare the three cutoff regions separately.
  by_cases hn_lt : n < -p
  · rw [truncation_filtration_stage_component_iso, dif_pos hn_lt]
    simpa [Iso.trans_hom, Category.assoc,
      ιTruncLE_component_eq_of_lt K p n hn_lt] using
      Classical.choose_spec (truncation_filtration_stage_term_iso_of_lt K p n hn_lt)
  · by_cases hn_eq : n = -p
    · subst hn_eq
      rw [truncation_filtration_stage_component_iso, dif_neg (lt_irrefl _), dif_pos rfl]
      simpa [Iso.trans_hom, Category.assoc, ιTruncLE_component_eq_cycles K p] using
        Classical.choose_spec (truncation_filtration_stage_term_iso_cycles K p)
    · have hn_gt : -p < n := by omega
      exact (truncation_filtration_stage_term_isZero_of_gt K p n hn_gt).eq_of_src _ _

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): the local stage differential is the
restriction of the ambient differential along the stage inclusion. -/
private theorem truncation_filtration_stage_d_comp_stageInclusion
    (K : CochainComplex 𝒜 ℤ) (p i j : ℤ) :
    ((K.truncationFiltration).stage p).d i j ≫
      ((K.truncationFiltration).stageInclusion p).f j =
        ((K.truncationFiltration).stageInclusion p).f i ≫ K.d i j := by
  -- Re-express the stage differential as the `p`-stage map of the filtered differential.
  change FilteredObject.Hom.stageMap ((K.truncationFiltration).d i j) p ≫
      (FilteredObject.stageFunctorToForget p).app ((K.truncationFiltration).X j) =
    (FilteredObject.stageFunctorToForget p).app ((K.truncationFiltration).X i) ≫
      ((K.truncationFiltration).d i j).hom
  exact FilteredObject.Hom.stageMap_comm ((K.truncationFiltration).d i j) p

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): the chosen degreewise comparisons
commute with differentials. -/
private theorem truncation_filtration_stage_component_hom_comm_d_truncLE
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) :
    (truncation_filtration_stage_component_iso K p i).hom ≫ (K.truncLE (-p)).d i j =
      ((K.truncationFiltration).stage p).d i j ≫
        (truncation_filtration_stage_component_iso K p j).hom := by
  -- Route correction: cancel the mono `K.ιTruncLE (-p)` on the target side.
  let ι : K.truncLE (-p) ⟶ K := K.ιTruncLE (-p)
  letI : Mono (ι.f j) := by
    dsimp [ι, CochainComplex.ιTruncLE]
    infer_instance
  apply (cancel_mono (ι.f j)).1
  let eI := truncation_filtration_stage_component_iso K p i
  let eJ := truncation_filtration_stage_component_iso K p j
  have hι :
      eI.hom ≫ ((K.truncLE (-p)).d i j ≫ ι.f j) =
        eI.hom ≫ (ι.f i ≫ K.d i j) := by
    exact congrArg (fun f ↦ eI.hom ≫ f) (ι.comm i j).symm
  have hfactor_i :
      eI.hom ≫ ι.f i =
        ((K.truncationFiltration).stageInclusion p).f i :=
    truncation_filtration_stage_component_hom_comp_ιTruncLE K p i
  have hstage :
      ((K.truncationFiltration).stageInclusion p).f i ≫ K.d i j =
        ((K.truncationFiltration).stage p).d i j ≫
          ((K.truncationFiltration).stageInclusion p).f j :=
    (truncation_filtration_stage_d_comp_stageInclusion K p i j).symm
  have hfactor_j :
      ((K.truncationFiltration).stageInclusion p).f j =
        eJ.hom ≫ ι.f j :=
    (truncation_filtration_stage_component_hom_comp_ιTruncLE K p j).symm
  have hpost :
      ((truncation_filtration_stage_component_iso K p i).hom ≫
          (K.truncLE (-p)).d i j) ≫ ι.f j =
        (((K.truncationFiltration).stage p).d i j ≫
            (truncation_filtration_stage_component_iso K p j).hom) ≫
          ι.f j := by
    have h1 :
        ((truncation_filtration_stage_component_iso K p i).hom ≫
            (K.truncLE (-p)).d i j) ≫ ι.f j =
          eI.hom ≫ ((K.truncLE (-p)).d i j ≫ ι.f j) := by
      simp [eI, Category.assoc]
    have h2 : eI.hom ≫ ((K.truncLE (-p)).d i j ≫ ι.f j) =
        eI.hom ≫ (ι.f i ≫ K.d i j) := hι
    have h3 : eI.hom ≫ (ι.f i ≫ K.d i j) =
        (eI.hom ≫ ι.f i) ≫ K.d i j := by
      simp [Category.assoc]
    have h4 : (eI.hom ≫ ι.f i) ≫ K.d i j =
        ((K.truncationFiltration).stageInclusion p).f i ≫ K.d i j :=
      congrArg (fun f ↦ f ≫ K.d i j) hfactor_i
    have h5 : ((K.truncationFiltration).stageInclusion p).f i ≫ K.d i j =
        ((K.truncationFiltration).stage p).d i j ≫
          ((K.truncationFiltration).stageInclusion p).f j := hstage
    have h6 : ((K.truncationFiltration).stage p).d i j ≫
          ((K.truncationFiltration).stageInclusion p).f j =
        ((K.truncationFiltration).stage p).d i j ≫ (eJ.hom ≫ ι.f j) :=
      congrArg (fun f ↦ ((K.truncationFiltration).stage p).d i j ≫ f) hfactor_j
    have h7 : ((K.truncationFiltration).stage p).d i j ≫ (eJ.hom ≫ ι.f j) =
        (((K.truncationFiltration).stage p).d i j ≫ eJ.hom) ≫ ι.f j := by
      simp [eJ, Category.assoc]
    exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))
  simpa [ι] using hpost

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): the local stage inclusion factors
through `τ_{\le -p}` by an isomorphism. -/
theorem truncationFiltration_stageInclusion_factors_ιTruncLE
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) :
    ∃ φ : (K.truncationFiltration).stage p ⟶ K.truncLE (-p),
      φ ≫ K.ιTruncLE (-p) = (K.truncationFiltration).stageInclusion p ∧ IsIso φ := by
  -- Package the fixed degreewise comparisons into a chain isomorphism.
  let E : (K.truncationFiltration).stage p ≅ K.truncLE (-p) :=
    HomologicalComplex.Hom.isoOfComponents
      (truncation_filtration_stage_component_iso K p)
      (fun i j hij ↦ truncation_filtration_stage_component_hom_comm_d_truncLE K p hij)
  refine ⟨E.hom, ?_, ?_⟩
  · -- The degreewise factorization upgrades to the chain-map identity.
    ext n
    exact truncation_filtration_stage_component_hom_comp_ιTruncLE K p n
  · letI : IsIso E.hom := ⟨E.inv, E.hom_inv_id, E.inv_hom_id⟩
    infer_instance

end Filtrations

end CochainComplex

section

variable {R : Type u} [CommRing R]
variable [LocallySmall.{0} (ModuleCat R)] [WellPowered.{0} (ModuleCat R)]
  [CategoryTheory.Limits.HasWidePullbacks (ModuleCat R)]
  [CategoryTheory.Limits.HasCoproducts (ModuleCat R)]
  [CategoryTheory.Limits.InitialMonoClass (ModuleCat R)]

/- 
Domain-style sampling for Lemma `15.64.4`.
- primary domain: cohomological spectral sequences in the bounded derived category `D^b(R)`
  computing the cohomology of a derived tensor product;
- sampled owner/canonical declarations in this domain:
  `CohomologicalSpectralSequence`,
  `FilteredComplex.convergesToCohomology`,
  `exists_kunneth_filteredTensorSpectralSequence`,
  `derivedTensorProduct`;
- best owner abstraction: a cohomological spectral sequence
  `E : CohomologicalSpectralSequence (ModuleCat R) 0` together with the Chapter `12`
  convergence owner on an associated filtered complex, while the displayed `E₂`-page and
  abutment objects remain source-facing bridge abbreviations;
- primitive vs. derived:
  primitive data are the spectral sequence `E` and the associated filtered complex `F` in the
  convergence clause; the `E₂`-page and abutment comparisons are derived API expressed
  propositionally by existential/nonempty comparison isomorphisms, while boundedness and
  convergence are expressed through the canonical Chapter `12` owner `F.convergesToCohomology E`;
- source/core/bridge triage:
  `source-facing`: `IsKunnethDerivedTensorSpectralSequence`;
  `core/canonical`: `CohomologicalSpectralSequence`,
    `FilteredComplex.convergesToCohomology`, and the Chapter `15` owner theorem
    `exists_kunneth_filteredTensorSpectralSequence`;
  `bridge/view`: `boundedDerivedTensorCohomology`, `kunnethDerivedTensorPageTwo`, and the
    convergence predicate below.

The numbered item is source-facing, but its convergence clause should be phrased through the
canonical filtered-complex owner API rather than through a parallel local filtered-cochain wrapper.
-/

local notation "Mod" => ModuleCat R
local notation "DbMod" => Dᵇ(Mod)
local notation "H" => DerivedCategory.homologyFunctor Mod

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): the source filtration is the canonical
upper-truncation filtration `F^p = τ_{\le -p}` on the chosen preimage complex of a bounded
derived object. -/
private abbrev truncationFilteredPreimage (K : DbMod) : FilteredCochainComplex Mod :=
  (DerivedCategory.Q.objPreimage K.obj).truncationFiltration

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): a cochain-complex isomorphism preserves
acyclicity, so stage acyclicity can be checked on the simpler truncation model. -/
private theorem acyclic_of_iso
    {L M : CochainComplex Mod ℤ} (e : L ≅ M) (hM : M.Acyclic) :
    L.Acyclic := by
  -- Transport exactness across the induced homology isomorphisms.
  rw [HomologicalComplex.acyclic_iff] at hM ⊢
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((HomologicalComplex.homologyMapIso e i).isZero_iff).2 (by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact hM i)

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): the `p`-th stage inclusion of the
truncation filtration factors through `τ_{\le -p}` on the chosen preimage complex. -/
private theorem truncationFilteredPreimage_stage_factors_ιTruncLE
    (K : DbMod) (p : ℤ) :
    ∃ φ : (truncationFilteredPreimage K).stage p ⟶
        (DerivedCategory.Q.objPreimage K.obj).truncLE (-p),
      φ ≫ (DerivedCategory.Q.objPreimage K.obj).ιTruncLE (-p) =
        (truncationFilteredPreimage K).stageInclusion p ∧ IsIso φ := by
  -- This is exactly the canonical stage comparison for the truncation filtration.
  simpa [truncationFilteredPreimage] using
    (CochainComplex.truncationFiltration_stageInclusion_factors_ιTruncLE
      (DerivedCategory.Q.objPreimage K.obj) p)

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): choose the canonical comparison
`F^p(Q.objPreimage K) ≅ τ_{\le -p}(Q.objPreimage K)`. -/
private noncomputable def truncationFilteredPreimage_stageIsoTruncLE
    (K : DbMod) (p : ℤ) :
    (truncationFilteredPreimage K).stage p ≅
      (DerivedCategory.Q.objPreimage K.obj).truncLE (-p) :=
  let φ := Classical.choose (truncationFilteredPreimage_stage_factors_ιTruncLE K p)
  letI : IsIso φ := (Classical.choose_spec
    (truncationFilteredPreimage_stage_factors_ιTruncLE K p)).2
  asIso φ

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): the chosen stage comparison identifies
the filtration inclusion with the canonical truncation inclusion on the nose. -/
private theorem truncationFilteredPreimage_stageIsoTruncLE_hom_comp_ιTruncLE
    (K : DbMod) (p : ℤ) :
    (truncationFilteredPreimage_stageIsoTruncLE K p).hom ≫
        (DerivedCategory.Q.objPreimage K.obj).ιTruncLE (-p) =
      (truncationFilteredPreimage K).stageInclusion p := by
  -- Unpack the chosen factorization from the previous theorem.
  exact (Classical.choose_spec (truncationFilteredPreimage_stage_factors_ιTruncLE K p)).1

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): the adjacent upper truncation
`τ_{\le j - 1}` is automatically strictly bounded above in degree `j`. -/
private theorem preimageTruncLEStep_isStrictlyLE
    (K : DbMod) (j : ℤ) :
    ((DerivedCategory.Q.objPreimage K.obj).truncLE (j - 1)).IsStrictlyLE j := by
  -- Increase the strict upper bound by one step.
  exact
    ((DerivedCategory.Q.objPreimage K.obj).truncLE (j - 1)).isStrictlyLE_of_le
      (j - 1) j (by omega)

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): the canonical one-step map
`τ_{\le j - 1}(Q.objPreimage K) ⟶ τ_{\le j}(Q.objPreimage K)`. -/
private noncomputable def preimageTruncLEStep
    (K : DbMod) (j : ℤ) :
    (DerivedCategory.Q.objPreimage K.obj).truncLE (j - 1) ⟶
      (DerivedCategory.Q.objPreimage K.obj).truncLE j :=
  letI := preimageTruncLEStep_isStrictlyLE K j
  inv (((DerivedCategory.Q.objPreimage K.obj).truncLE (j - 1)).ιTruncLE j) ≫
    CochainComplex.truncLEMap ((DerivedCategory.Q.objPreimage K.obj).ιTruncLE (j - 1)) j

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): the one-step truncation map composes
with `ιTruncLE j` to the earlier inclusion `ιTruncLE (j - 1)`. -/
private theorem preimageTruncLEStep_comp_ιTruncLE
    (K : DbMod) (j : ℤ) :
    preimageTruncLEStep K j ≫ (DerivedCategory.Q.objPreimage K.obj).ιTruncLE j =
      (DerivedCategory.Q.objPreimage K.obj).ιTruncLE (j - 1) := by
  -- TODO: rewrite `truncLEMap ... j ≫ ιTruncLE j` by naturality, then cancel the inverse of
  -- `((Q.objPreimage K).truncLE (j - 1)).ιTruncLE j`.
  sorry

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): for sufficiently large `p`, the stage
`F^p = τ_{\le -p}` is acyclic because the bounded-below representative has no surviving homology
in those degrees. -/
private theorem truncationFilteredPreimage_eventually_acyclic
    (K : DbMod) :
    ∃ p0 : ℤ, ∀ ⦃p : ℤ⦄, p0 ≤ p → (F^{p} (truncationFilteredPreimage K)).Acyclic := by
  -- TODO: build the bounded-below witness from `derivedCategory_t_plus_iff`, prove that
  -- `τ_{\le -p}` has zero homology in every degree once `p` is large, and transport acyclicity
  -- back along `truncationFilteredPreimage_stageIsoTruncLE`.
  sorry

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): for sufficiently small `p`, the stage
inclusion `F^p ⟶ K` is a quasi-isomorphism because the bounded-above representative is already
captured by `τ_{\le -p}`. -/
private theorem truncationFilteredPreimage_eventually_quasiIso_stageInclusion
    (K : DbMod) :
    ∃ p1 : ℤ, ∀ ⦃p : ℤ⦄, p ≤ p1 → QuasiIso ((truncationFilteredPreimage K).stageInclusion p) := by
  -- TODO: show that for `p` far to the left the representative complex is already `IsLE (-p)`,
  -- use the canonical quasi-isomorphism of `ιTruncLE (-p)`, and then rewrite the stage inclusion
  -- through `truncationFilteredPreimage_stageIsoTruncLE_hom_comp_ιTruncLE`.
  sorry

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): package the two eventual stage-control
facts needed to apply Proposition `15.64.3` to the truncation filtrations of bounded objects. -/
private theorem truncationFilteredPreimage_stageControl
    (K : DbMod) :
    (∃ p0 : ℤ, ∀ ⦃p : ℤ⦄, p0 ≤ p → (F^{p} (truncationFilteredPreimage K)).Acyclic) ∧
      (∃ p1 : ℤ, ∀ ⦃p : ℤ⦄, p ≤ p1 → QuasiIso ((truncationFilteredPreimage K).stageInclusion p)) := by
  -- Keep the source package split exactly into the acyclic-tail and quasi-isomorphic-head pieces.
  exact ⟨truncationFilteredPreimage_eventually_acyclic K,
    truncationFilteredPreimage_eventually_quasiIso_stageInclusion K⟩

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): the affine coordinate change
`(p, q) ↦ (-q, p + 2q)` turns the page-`r - 1` cohomological shape into the page-`r` shape. -/
private theorem neg_swap_rel_iff
    (r p q p' q' : ℤ) :
    (ComplexShape.up' (⟨r - 1, 1 - (r - 1)⟩ : ℤ × ℤ)).Rel
        (-q, p + 2 * q) (-q', p' + 2 * q') ↔
      (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).Rel (p, q) (p', q') := by
  -- The linear reindexing is chosen so that bidegree `(r - 1, -r + 2)` becomes `(r, -r + 1)`.
  simp [ComplexShape.up']
  omega

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): for each positive page `r`, the
renumbered page has entries `S_{r-1}^{-q, p + 2q}` with the transported cohomological
differentials. -/
private def renumberedPositivePage
    (S : CohomologicalSpectralSequence Mod 0) (r : ℤ) (hr : 1 ≤ r) :
    HomologicalComplex Mod (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) where
  X pq := (S.page (r - 1) (by omega)).X (-pq.2, pq.1 + 2 * pq.2)
  d pq pq' := (S.page (r - 1) (by omega)).d (-pq.2, pq.1 + 2 * pq.2) (-pq'.2, pq'.1 + 2 * pq'.2)
  shape pq pq' hpq := by
    -- Rewrite the transformed bidegrees back to the original page before applying `S.shape`.
    apply (S.page (r - 1) (by omega)).shape
    intro hrel
    exact hpq ((neg_swap_rel_iff r pq.1 pq.2 pq'.1 pq'.2).1 hrel)
  d_comp_d' pq pq' pq'' hpq hpq' := by
    -- Square-zero is inherited verbatim from the source page after the coordinate change.
    exact
      (S.page (r - 1) (by omega)).d_comp_d
        (-pq.2, pq.1 + 2 * pq.2)
        (-pq'.2, pq'.1 + 2 * pq'.2)
        (-pq''.2, pq''.1 + 2 * pq''.2)

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): fixing the second index of the `E₁`
page produces an ordinary cochain complex in the first index. -/
private def associatedPageOneComplex
    (E : CohomologicalSpectralSequence Mod 0) (q : ℤ) : CochainComplex Mod ℤ where
  X p := (E.page 1).X (p, q)
  d p p' := (E.page 1).d (p, q) (p', q)
  shape p p' hpp' := by
    -- Fixing `q` reduces the ambient bidegree shape to the ordinary cochain shape in `p`.
    have hpq :
        ¬ (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ)).Rel (p, q) (p', q) := by
      simpa [ComplexShape.up'] using hpp'
    exact (E.page 1).shape (p, q) (p', q) hpq
  d_comp_d' p p' p'' hpp' hp'p'' := by
    -- The square-zero relation is inherited directly from the ambient `E₁` page.
    exact (E.page 1).d_comp_d (p, q) (p', q) (p'', q)

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): the short-complex view of the fixed-`q`
`E₁` slice agrees with the ambient short complex at bidegree `(p,q)`. -/
private noncomputable def associatedPageOneComplexScIso
    (E : CohomologicalSpectralSequence Mod 0) (p q : ℤ) :
    (associatedPageOneComplex E q).sc' (p - 1) p (p + 1) ≅
      (E.page 1).sc' (p - 1, q) (p, q) (p + 1, q) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [associatedPageOneComplex])
    (by simp [associatedPageOneComplex])

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): the `p`-th homology of the fixed-`q`
slice is the ambient page-one homology object at bidegree `(p,q)`. -/
private noncomputable def associatedPageOneComplex_homologyIso
    (E : CohomologicalSpectralSequence Mod 0) (p q : ℤ) :
    (associatedPageOneComplex E q).homology p ≅ (E.page 1).homology (p, q) :=
  let hprevSlice : (ComplexShape.up ℤ).prev p = p - 1 :=
    ComplexShape.prev_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])
  let hnextSlice : (ComplexShape.up ℤ).next p = p + 1 :=
    ComplexShape.next_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])
  let hprevPage :
      (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ)).prev (p, q) = (p - 1, q) :=
    ComplexShape.prev_eq' (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ))
      (by simp [ComplexShape.up'])
  let hnextPage :
      (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ)).next (p, q) = (p + 1, q) :=
    ComplexShape.next_eq' (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ))
      (by simp [ComplexShape.up'])
  -- The fixed-`q` slice keeps exactly the same differential data as the ambient page-one object.
  (associatedPageOneComplex E q).homologyIsoSc' (p - 1) p (p + 1) hprevSlice hnextSlice ≪≫
    ShortComplex.homologyMapIso (associatedPageOneComplexScIso E p q) ≪≫
    ((E.page 1).homologyIsoSc' (p - 1, q) (p, q) (p + 1, q) hprevPage hnextPage).symm

/-- Helper for Lemma 15.64.4 (Künneth Spectral Sequence): a comparison between a fixed-`q`
`E₁` slice and an ordinary cochain complex yields the corresponding `E₂`-page identification by
taking `p`-th homology. -/
private theorem associated_pageTwo_iso_of_pageOne_complex_iso
    (E : CohomologicalSpectralSequence Mod 0) (p q : ℤ)
    (C : CochainComplex Mod ℤ)
    (e : associatedPageOneComplex E q ≅ C) :
    Nonempty ((E.page 2).X (p, q) ≅ C.homology p) := by
  refine ⟨?_⟩
  -- First rewrite the ambient `E₂` term as page-one homology, then transport through the fixed
  -- slice and the chosen comparison with `C`.
  exact
    (E.iso 1 2 (p, q)).symm ≪≫
      (associatedPageOneComplex_homologyIso E p q).symm ≪≫
        HomologicalComplex.homologyMapIso e p

/-- The abutment object `H^n(K \otimes_R^{\mathbf L} L)` for bounded derived `R`-complexes
`K, L ∈ D^b(R)`. -/
abbrev boundedDerivedTensorCohomology
    (K L : DbMod) (n : ℤ) : ModuleCat R :=
  (H n).obj (K.obj ⊗[R]^L L.obj)

/-- The `E_2^{p,q}` term
`\bigoplus_{i + j = q} \operatorname{Tor}^R_{-p}(H^i(K), H^j(L))`
of the Künneth spectral sequence, with the convention that it is zero for `p > 0`. -/
abbrev kunnethDerivedTensorPageTwo
    (K L : DbMod) (p q : ℤ) : ModuleCat R :=
  if _ : p ≤ 0 then
    ∐ fun i : ℤ ↦
      (((Tor Mod (Int.toNat (-p))).obj
          ((H i).obj K.obj)).obj
        ((H (q - i)).obj L.obj))
  else
    (0 : Mod)

/-- A cohomological spectral sequence converges to `H^*(K ⊗[R]^L L)` if it is associated to a
filtered complex whose cohomology identifies with that of the derived tensor product and which
satisfies the Chapter `12` convergence owner. -/
def ConvergesToDerivedTensorCohomology
    (E : CohomologicalSpectralSequence Mod 0) (K L : DbMod) : Prop :=
  ∃ (F : FilteredComplex Mod) (_ : IsAssociatedToFilteredComplex F E),
    F.convergesToCohomology E ∧
      ∀ n : ℤ,
        Nonempty (F.underlying.homology n ≅ boundedDerivedTensorCohomology K L n)

/-- The Künneth spectral sequence for bounded derived `R`-complexes `K` and `L`: a bounded
cohomological spectral sequence with the expected `E_2`-page and abutment. -/
def IsKunnethDerivedTensorSpectralSequence
    (E : CohomologicalSpectralSequence Mod 0) (K L : DbMod) : Prop :=
  CohomologicalSpectralSequence.IsBounded E ∧
    (∀ p q : ℤ,
      Nonempty ((E.page 2).X (p, q) ≅ kunnethDerivedTensorPageTwo K L p q)) ∧
    ConvergesToDerivedTensorCohomology E K L

-- Proof sketch: represent `K` and `L` by bounded complexes, filter them by stupid truncations,
-- and apply Proposition `15.64.3` to the resulting filtered tensor complex. The associated
-- spectral sequence is bounded by the boundedness of `K` and `L`, its `E₁`-page identifies with
-- the graded pieces `H^{-i}(K)[i]` and `H^{-j}(L)[j]`, and reindexing the page `r - 1` terms by
-- `E_r^{p,q} = (E')_{r - 1}^{-q, p + 2q}` gives the stated `E₂`-page and abutment.
/-- Lemma 15.64.4 (Künneth Spectral Sequence): for bounded derived `R`-complexes `K` and `L`,
there exists a bounded cohomological spectral sequence whose `E_2`-page is
`\bigoplus_{i + j = q} \operatorname{Tor}^R_{-p}(H^i(K), H^j(L))` and which converges to
`H^{p + q}(K \otimes_R^{\mathbf L} L)`. The differentials are those of a cohomological spectral
sequence, so they have bidegree `(r, -r + 1)`. -/
theorem exists_kunnethDerivedTensorSpectralSequence
    (K L : DbMod) :
    ∃ E : CohomologicalSpectralSequence Mod 0,
      IsKunnethDerivedTensorSpectralSequence E K L := by
  -- Route correction: the theorem-local helper module now isolates the truncation-filtration API
  -- promised by the source proof: `F^p = τ_{\le -p}`, the stage/truncation comparison, the
  -- one-step truncation map, and the eventual stage-control package.
  let _ := truncationFilteredPreimage_stageControl (R := R) K
  let _ := truncationFilteredPreimage_stageControl (R := R) L
  -- TODO: once the upstream `.olean` for Proposition `15.64.3` is available in this workspace,
  -- specialize it to `truncationFilteredPreimage K` and `truncationFilteredPreimage L`, rewrite
  -- the raw `E₁`-page through `gr^{-j} ≅ shiftedCohomology`, convert the single-degree tensor
  -- homology to Tor, and then apply the affine renumbering
  -- `E_r^{p,q} = (E')_{r - 1}^{-q, p + 2q}`.
  sorry

end

end CategoryTheory
