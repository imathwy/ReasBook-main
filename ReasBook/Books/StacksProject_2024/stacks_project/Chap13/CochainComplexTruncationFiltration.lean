import Mathlib.Algebra.Homology.Embedding.StupidTrunc
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.Tactic
import StacksProject_2024.Chap12.Lemma_12_24_11

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open CochainComplex

noncomputable section

universe u v

namespace CategoryTheory

namespace CochainComplex

section Filtrations

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- The degreewise subobject defining the truncation filtration
`F^p(K^n) = τ_{\le -p}(K^n)`. -/
private def truncationFiltrationSubobject (K : CochainComplex 𝒜 ℤ) (p n : ℤ) :
    Subobject (K.X n) :=
  if n < -p then
    ⊤
  else if n = -p then
    kernelSubobject (K.d n (n + 1))
  else
    ⊥

/-- The truncation filtration is decreasing in the filtration index. -/
private theorem truncationFiltration_decreasing (K : CochainComplex 𝒜 ℤ) {p q n : ℤ}
    (hpq : p ≤ q) :
    truncationFiltrationSubobject K q n ≤ truncationFiltrationSubobject K p n := by
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

/-- The differential preserves the truncation filtration. -/
private theorem truncationFiltration_d_preserves (K : CochainComplex 𝒜 ℤ) (p i j : ℤ) :
    truncationFiltrationSubobject K p i ≤
      (Subobject.pullback (K.d i j)).obj (truncationFiltrationSubobject K p j) := by
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

/-- The truncation filtration `F^p(K^•) = τ_{\le -p}(K^•)` on a cochain complex. -/
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

/-- Below the cutoff, the truncation-filtration stage agrees with the original term. -/
private theorem truncation_filtration_stage_term_iso_of_lt
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hn : n < -p) :
    ∃ e : ((K.truncationFiltration).stage p).X n ≅ K.X n,
      e.hom = ((K.truncationFiltration).stageInclusion p).f n := by
  change ∃ e : ((truncationFiltrationSubobject K p n : 𝒜) ≅ K.X n),
      e.hom = (truncationFiltrationSubobject K p n).arrow
  rw [truncationFiltrationSubobject, if_pos hn]
  rw [Subobject.top_eq_id]
  refine ⟨Subobject.underlyingIso (𝟙 (K.X n)), ?_⟩
  simpa using (Subobject.underlyingIso_hom_comp_eq_mk (𝟙 (K.X n)))

/-- At the cutoff degree, the truncation-filtration stage is the cycles object. -/
private theorem truncation_filtration_stage_term_iso_cycles
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) :
    ∃ e : ((K.truncationFiltration).stage p).X (-p) ≅ K.cycles (-p),
      e.hom ≫ K.iCycles (-p) = ((K.truncationFiltration).stageInclusion p).f (-p) := by
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
  simp only [Iso.trans_hom, Iso.symm_hom, ShortComplex.cyclesIsoKernel_inv, Category.assoc,
    HomologicalComplex.cyclesIsoSc'_inv_iCycles]
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

/-- Above the cutoff, the truncation-filtration stage vanishes. -/
private theorem truncation_filtration_stage_term_isZero_of_gt
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hn : -p < n) :
    IsZero (((K.truncationFiltration).stage p).X n) := by
  change IsZero ((truncationFiltrationSubobject K p n : 𝒜))
  rw [truncationFiltrationSubobject, if_neg (not_lt_of_ge (le_of_lt hn))]
  rw [if_neg (by omega : ¬ n = -p)]
  exact (isZero_zero _).of_iso Subobject.botCoeIsoZero

/-- An index on or below the cutoff is represented by `embeddingUpIntLE`. -/
private theorem embeddingUpIntLE_toNat_sub_eq
    (p n : ℤ) (hn : n ≤ -p) :
    (embeddingUpIntLE (-p)).f (Int.toNat (-p - n)) = n := by
  dsimp [ComplexShape.embeddingUpIntLE]
  rw [Int.toNat_of_nonneg]
  · omega
  · omega

/-- Below the cutoff, the canonical truncation term is the original term. -/
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

/-- At the cutoff, the canonical truncation term is the cycles object. -/
private noncomputable def truncLE_term_iso_cycles
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) :
    (K.truncLE (-p)).X (-p) ≅ K.cycles (-p) :=
  let hi' : (embeddingUpIntLE (-p)).f 0 = -p := by
    simp [ComplexShape.embeddingUpIntLE]
  let hboundary : (embeddingUpIntLE (-p)).BoundaryLE 0 := by
    simpa using (ComplexShape.boundaryLE_embeddingUpIntLE_iff (-p) 0).2 rfl
  K.truncLEXIsoCycles (e := embeddingUpIntLE (-p)) hi' hboundary

/-- Above the cutoff, the canonical truncation term vanishes. -/
private theorem truncLE_term_isZero_of_gt
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hn : -p < n) :
    IsZero ((K.truncLE (-p)).X n) := by
  exact (K.truncLE (-p)).isZero_of_isStrictlyLE (-p) n hn

/-- Degreewise, the truncation-filtration stage agrees with the canonical upper truncation. -/
private noncomputable abbrev truncation_filtration_stage_component_iso
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) :
    ((K.truncationFiltration).stage p).X n ≅ (K.truncLE (-p)).X n := by
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

/-- Below the cutoff, the truncation inclusion component is the retained-term identification. -/
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
  apply Quiver.Hom.op_inj
  change ((K.op.πTruncGE e.op).f n) =
    (K.op.truncGEXIso e.op hi' (by simpa using hi)).inv
  dsimp [CochainComplex.πTruncGE, HomologicalComplex.πTruncGE]
  rw [e.op.liftExtend_f (K.op.restrictionToTruncGE' e.op)
      (K.op.restrictionToTruncGE'_hasLift e.op) hi']
  rw [K.op.restrictionToTruncGE'_f_eq_iso_hom_iso_inv e.op hi' (by simpa using hi)]
  simp [HomologicalComplex.truncGEXIso, Category.assoc]
  rfl

/-- At the cutoff, the truncation inclusion component is the cycles inclusion. -/
private theorem ιTruncLE_component_eq_cycles
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) :
    (K.ιTruncLE (-p)).f (-p) = (truncLE_term_iso_cycles K p).hom ≫ K.iCycles (-p) := by
  let e := embeddingUpIntLE (-p)
  let hi' : e.f 0 = -p := by
    simpa [e] using (embeddingUpIntLE_toNat_sub_eq p (-p) le_rfl)
  have hi : e.BoundaryLE 0 := by
    simpa [e] using (ComplexShape.boundaryLE_embeddingUpIntLE_iff (-p) 0).2 rfl
  apply Quiver.Hom.op_inj
  change ((K.op.πTruncGE e.op).f (-p)) =
    ((truncLE_term_iso_cycles K p).hom ≫ K.iCycles (-p)).op
  dsimp [CochainComplex.πTruncGE, HomologicalComplex.πTruncGE]
  rw [e.op.liftExtend_f (K.op.restrictionToTruncGE' e.op)
      (K.op.restrictionToTruncGE'_hasLift e.op) hi']
  rw [K.op.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv e.op hi' (by simpa using hi)]
  simp only [HomologicalComplex.op_X, HomologicalComplex.restriction_X, Embedding.op_f,
    Category.assoc, Iso.inv_hom_id_assoc]
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
      Iso.hom_inv_id_assoc]
    rfl
  simpa [HomologicalComplex.opcyclesOpIso, Category.assoc] using
    congrArg (fun f ↦ K.op.pOpcycles (-p) ≫ f) hcut.symm

/-- Degreewise, the chosen comparison factors the stage inclusion through `ιTruncLE`. -/
private theorem truncation_filtration_stage_component_hom_comp_ιTruncLE
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) :
    (truncation_filtration_stage_component_iso K p n).hom ≫ (K.ιTruncLE (-p)).f n =
      ((K.truncationFiltration).stageInclusion p).f n := by
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

/-- The stage differential is the restriction of the ambient differential. -/
private theorem truncation_filtration_stage_d_comp_stageInclusion
    (K : CochainComplex 𝒜 ℤ) (p i j : ℤ) :
    ((K.truncationFiltration).stage p).d i j ≫
      ((K.truncationFiltration).stageInclusion p).f j =
        ((K.truncationFiltration).stageInclusion p).f i ≫ K.d i j := by
  change FilteredObject.Hom.stageMap ((K.truncationFiltration).d i j) p ≫
      (FilteredObject.stageFunctorToForget p).app ((K.truncationFiltration).X j) =
    (FilteredObject.stageFunctorToForget p).app ((K.truncationFiltration).X i) ≫
      ((K.truncationFiltration).d i j).hom
  exact FilteredObject.Hom.stageMap_comm ((K.truncationFiltration).d i j) p

/-- The degreewise comparisons commute with differentials. -/
private theorem truncation_filtration_stage_component_hom_comm_d_truncLE
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) {i j : ℤ} (_hij : (ComplexShape.up ℤ).Rel i j) :
    (truncation_filtration_stage_component_iso K p i).hom ≫ (K.truncLE (-p)).d i j =
      ((K.truncationFiltration).stage p).d i j ≫
        (truncation_filtration_stage_component_iso K p j).hom := by
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

/-- The canonical inclusion of the `p`-th truncation-filtration stage into `K^•` factors through
`τ_{\le -p}(K^•) = K.truncLE (-p)` by an isomorphism. -/
theorem truncationFiltration_stageInclusion_factors_ιTruncLE
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) :
    ∃ φ : (K.truncationFiltration).stage p ⟶ K.truncLE (-p),
      φ ≫ K.ιTruncLE (-p) = (K.truncationFiltration).stageInclusion p ∧ IsIso φ := by
  let E : (K.truncationFiltration).stage p ≅ K.truncLE (-p) :=
    HomologicalComplex.Hom.isoOfComponents
      (truncation_filtration_stage_component_iso K p)
      (fun i j hij ↦ truncation_filtration_stage_component_hom_comm_d_truncLE K p hij)
  refine ⟨E.hom, ?_, ?_⟩
  · ext n
    exact truncation_filtration_stage_component_hom_comp_ιTruncLE K p n
  · letI : IsIso E.hom := ⟨E.inv, E.hom_inv_id, E.inv_hom_id⟩
    infer_instance

end Filtrations

end CochainComplex

end CategoryTheory
