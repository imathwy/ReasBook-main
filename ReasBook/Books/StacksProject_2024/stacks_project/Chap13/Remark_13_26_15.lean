import Mathlib
import StacksProject_2024.Chap13.CochainComplexStupidFiltration
import StacksProject_2024.Chap13.Lemma_13_21_3
import StacksProject_2024.Chap13.Lemma_13_26_14

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open CochainComplex
open DerivedCategory.TStructure

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace CochainComplex

section Filtrations

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜]

/-
Domain-style sampling for Remark `13.26.15`.
- primary domain: filtered right-derived spectral sequences attached to filtered cochain
  complexes, together with the bounded-below bridge back to the two Cartan-Eilenberg spectral
  sequences of Lemma `13.21.3`;
- sampled owner declarations:
  `CochainComplex`,
  `FilteredComplex`,
  `IsAssociatedToFilteredComplex`,
  `FilteredComplex.pageOneIso`,
  `FilteredComplex.cohomologyFiltrationIsFinite`,
  `FilteredComplex.convergesToCohomology`,
  `exists_filteredRightDerivedSpectralSequence`,
  `exists_cartanEilenberg_rightDerived_spectralSequences`;
- best owner abstraction: the Chapter `13` filtered right-derived spectral-sequence owner
  `exists_filteredRightDerivedSpectralSequence`, built on the Chapter `12` filtered-complex owner
  `FilteredComplex` together with the canonical association predicate
  `IsAssociatedToFilteredComplex`, and the earlier Cartan-Eilenberg owner
  `exists_cartanEilenberg_rightDerived_spectralSequences`; the source-facing stupid and
  truncation filtrations themselves belong on the canonical cochain-complex owner
  `CochainComplex 𝒜 ℤ`, while bounded-belowness is only part of the later bridge to the derived
  spectral sequence.

Source/core/bridge triage:
- `source-facing`: `CochainComplex.stupidFiltration` and
  `CochainComplex.truncationFiltration`;
- `core/canonical`: `FilteredComplex`, `IsAssociatedToFilteredComplex`,
  `exists_filteredRightDerivedSpectralSequence`, and
  `exists_cartanEilenberg_rightDerived_spectralSequences`;
- `bridge/view`: the two remark-level alternative-construction theorems, together with the
  explicit `E₁`/`E₂` page identifications, the `d₁` compatibility square, and the comparison
  theorems matching these constructions to the two spectral sequences of Lemma `13.21.3`.

The stupid and truncation filtrations are therefore defined directly on the canonical cochain-
complex owner, rather than on the bounded-below full subcategory. The remark-level spectral-
sequence theorems are then the bounded-below bridge/view specializations: they use `K.obj` only
to feed these source-facing filtrations into the Chapter `13` existence theorem, and return the
canonical filtered complex in `ℬ` carrying the associated spectral sequence. -/

/-- The degreewise subobject defining the truncation filtration `F^p(K^n) = τ_{\le -p}(K^n)`. -/
private def truncationFiltrationSubobject (K : CochainComplex 𝒜 ℤ) (p n : ℤ) :
    Subobject (K.X n) :=
  if n < -p then
    ⊤
  else if n = -p then
    kernelSubobject (K.d n (n + 1))
  else
    ⊥

-- Proof sketch: as `p` increases, the bound `-p` decreases, so the truncation stages form a
-- decreasing filtration; the kernel stage at `n = -p` is exactly the transition object.
/-- The truncation filtration is decreasing in the filtration index. -/
private theorem truncationFiltration_decreasing (K : CochainComplex 𝒜 ℤ) {p q n : ℤ}
    (hpq : p ≤ q) :
    truncationFiltrationSubobject K q n ≤ truncationFiltrationSubobject K p n := by
  -- The cutoff `-q` is at most `-p`, so the `q`-stage can only be smaller than the `p`-stage.
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

-- Proof sketch: below the cutoff the target filtration stage is `⊤`, at the cutoff it is the
-- kernel of the outgoing differential, and above the cutoff both sides are zero; these are the
-- usual truncation-preservation cases.
/-- The differential preserves the truncation filtration. -/
private theorem truncationFiltration_d_preserves (K : CochainComplex 𝒜 ℤ) (p i j : ℤ) :
    truncationFiltrationSubobject K p i ≤
      (Subobject.pullback (K.d i j)).obj (truncationFiltrationSubobject K p j) := by
  -- Route correction: this preservation argument is degreewise and does not use the later,
  -- currently problematic comparison with `truncGE`.
  by_cases hi_lt : i < -p
  · by_cases hij : j = i + 1
    · subst hij
      by_cases hj_lt : i + 1 < -p
      · -- Strictly below the cutoff, both stages are the whole object.
        rw [truncationFiltrationSubobject, if_pos hi_lt, truncationFiltrationSubobject,
          if_pos hj_lt, Subobject.pullback_top]
      · -- At the cutoff, the next stage is the kernel of the outgoing differential.
        have hj_eq : i + 1 = -p := by omega
        rw [truncationFiltrationSubobject, if_pos hi_lt, truncationFiltrationSubobject,
          if_neg hj_lt, if_pos hj_eq]
        apply Subobject.le_of_factors
        rw [pullback_factors_iff]
        exact kernelSubobject_factors _ _ (by
          simpa using K.d_comp_d i (i + 1) (i + 2))
    · -- Away from the successor degree, the differential is zero and hence factors through
      -- every target stage.
      have hd : K.d i j = 0 := by
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
        -- At the cutoff, the source stage is already the kernel of the outgoing differential.
        rw [truncationFiltrationSubobject, if_neg (lt_irrefl _), if_pos rfl,
          truncationFiltrationSubobject]
        have hj_not_lt : ¬ -p + 1 < -p := by omega
        have hj_ne : ¬ -p + 1 = -p := by omega
        rw [if_neg hj_not_lt, if_neg hj_ne]
        apply Subobject.le_of_factors
        rw [pullback_factors_iff]
        exact (Subobject.bot_factors_iff_zero _).2 (by
          simpa using (kernelSubobject_arrow_comp (f := K.d (-p) (-p + 1))))
      · -- Off the successor degree, the differential out of the kernel stage is zero.
        have hd : K.d (-p) j = 0 := by
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
              (0 : ((kernelSubobject (K.d (-p) (-p + 1)) : Subobject (K.X (-p))) : 𝒜) ⟶ K.X j))
    · -- Above the cutoff the filtration stage is zero.
      rw [truncationFiltrationSubobject, if_neg hi_lt, if_neg hi_eq]
      exact bot_le

/-- The filtered complex with stages `F^p(K^•) = τ_{\le -p}(K^•)`. -/
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

-- Proof sketch: for fixed `n`, the truncation filtration is `⊤` for sufficiently small `p`,
-- equals the single kernel stage at `p = -n`, and is `⊥` for sufficiently large `p`.
/-- The truncation filtration has finite filtrations in every degree. -/
theorem truncationFiltration_hasFiniteFiltrations (K : CochainComplex 𝒜 ℤ) :
    (truncationFiltration K).HasFiniteFiltrations := by
  intro n
  -- In degree `n`, stages far enough to the left are `⊤`, and stages far enough to the right
  -- are already `⊥`.
  refine ⟨-n - 1, -n + 1, ?_, ?_⟩
  · change truncationFiltrationSubobject K (-n - 1) n = ⊤
    simp [truncationFiltrationSubobject]
  · change truncationFiltrationSubobject K (-n + 1) n = ⊥
    simp [truncationFiltrationSubobject]

/-- Helper for Remark 13.26.15: below the cutoff, the truncation-filtration stage term is the
ambient term of the original complex. -/
private theorem truncation_filtration_stage_term_iso_of_lt
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hn : n < -p) :
    ∃ e : ((K.truncationFiltration).stage p).X n ≅ K.X n,
      e.hom = ((K.truncationFiltration).stageInclusion p).f n := by
  -- Strictly below the cutoff, the filtration stage is the top subobject.
  change ∃ e : ((truncationFiltrationSubobject K p n : 𝒜) ≅ K.X n),
      e.hom = (truncationFiltrationSubobject K p n).arrow
  rw [truncationFiltrationSubobject, if_pos hn]
  rw [Subobject.top_eq_id]
  refine ⟨Subobject.underlyingIso (𝟙 (K.X n)), ?_⟩
  simpa using (Subobject.underlyingIso_hom_comp_eq_mk (𝟙 (K.X n)))

/-- Helper for Remark 13.26.15: at the cutoff degree, the truncation-filtration stage term is the
cycles object of `K`. -/
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
  -- The kernel inclusion agrees with the cycles inclusion after the standard cycles-kernel
  -- identification.
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

/-- Helper for Remark 13.26.15: above the cutoff, the truncation-filtration stage term vanishes. -/
private theorem truncation_filtration_stage_term_isZero_of_gt
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hn : -p < n) :
    IsZero (((K.truncationFiltration).stage p).X n) := by
  -- Strictly above the cutoff, the stage subobject is `⊥`.
  change IsZero ((truncationFiltrationSubobject K p n : 𝒜))
  rw [truncationFiltrationSubobject, if_neg (not_lt_of_ge (le_of_lt hn))]
  rw [if_neg (by omega : ¬ n = -p)]
  exact (isZero_zero _).of_iso Subobject.botCoeIsoZero

/-- Helper for Remark 13.26.15: a degree `n ≤ -p` lies in the image of the embedding
`m ↦ -p - m`. -/
private theorem embeddingUpIntLE_toNat_sub_eq
    (p n : ℤ) (hn : n ≤ -p) :
    (embeddingUpIntLE (-p)).f (Int.toNat (-p - n)) = n := by
  -- The difference `-p - n` is nonnegative on and below the cutoff.
  dsimp [ComplexShape.embeddingUpIntLE]
  rw [Int.toNat_of_nonneg]
  · omega
  · omega

/-- Helper for Remark 13.26.15: below the cutoff, the canonical truncation term is the ambient
term of the original complex. -/
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

/-- Helper for Remark 13.26.15: at the cutoff, the canonical truncation term is the cycles object
of `K`. -/
private noncomputable def truncLE_term_iso_cycles
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) :
    (K.truncLE (-p)).X (-p) ≅ K.cycles (-p) :=
  let hi' : (embeddingUpIntLE (-p)).f 0 = -p := by
    simp [ComplexShape.embeddingUpIntLE]
  let hboundary : (embeddingUpIntLE (-p)).BoundaryLE 0 := by
    simpa using (ComplexShape.boundaryLE_embeddingUpIntLE_iff (-p) 0).2 rfl
  K.truncLEXIsoCycles (e := embeddingUpIntLE (-p)) hi' hboundary

/-- Helper for Remark 13.26.15: above the cutoff, the canonical truncation term vanishes. -/
private theorem truncLE_term_isZero_of_gt
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hn : -p < n) :
    IsZero ((K.truncLE (-p)).X n) := by
  -- The truncation `K.truncLE (-p)` is strictly supported in degrees `≤ -p`.
  exact (K.truncLE (-p)).isZero_of_isStrictlyLE (-p) n hn

/-- Helper for Remark 13.26.15: degreewise, the `p`th truncation-filtration stage agrees with the
canonical truncation `τ_{\le -p}(K^\bullet)`. -/
private theorem truncation_filtration_stage_component_iso_truncLE
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) :
    Nonempty (((K.truncationFiltration).stage p).X n ≅ (K.truncLE (-p)).X n) := by
  -- Route correction: first match the two constructions degreewise in the three source-faithful
  -- regions `n < -p`, `n = -p`, and `-p < n`.
  by_cases hn_lt : n < -p
  · exact ⟨Classical.choose (truncation_filtration_stage_term_iso_of_lt K p n hn_lt) ≪≫
        (truncLE_term_iso_of_lt K p n hn_lt).symm⟩
  · by_cases hn_eq : n = -p
    · subst hn_eq
      exact ⟨Classical.choose (truncation_filtration_stage_term_iso_cycles K p) ≪≫
          (truncLE_term_iso_cycles K p).symm⟩
    · have hn_gt : -p < n := by omega
      -- Above the cutoff, both complexes are zero in degree `n`.
      exact ⟨(truncation_filtration_stage_term_isZero_of_gt K p n hn_gt).isoZero ≪≫
        (truncLE_term_isZero_of_gt K p n hn_gt).isoZero.symm⟩

/-- Helper for Remark 13.26.15: choose one fixed degreewise comparison between the `p`th
truncation-filtration stage and `τ_{\le -p}(K^\bullet)`. -/
private noncomputable abbrev truncation_filtration_stage_component_iso
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) :
    ((K.truncationFiltration).stage p).X n ≅ (K.truncLE (-p)).X n := by
  -- Use the same three-region comparison everywhere so later rewrite lemmas talk about one fixed
  -- family of component isomorphisms.
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

/-- Helper for Remark 13.26.15: below the cutoff, the component of the canonical truncation
inclusion is the standard retained-term identification. -/
private theorem ιTruncLE_component_eq_of_lt
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hn : n < -p) :
    (K.ιTruncLE (-p)).f n = (truncLE_term_iso_of_lt K p n hn).hom := by
  let e := embeddingUpIntLE (-p)
  let i : ℕ := Int.toNat (-p - n)
  have hi' : e.f i = n := embeddingUpIntLE_toNat_sub_eq p n (le_of_lt hn)
  have hi : ¬ e.BoundaryLE i := by
    -- Below the cutoff, the chosen index is not the boundary index of the truncation.
    rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff]
    intro hi0
    have : -p = n := by
      simpa [e, i, hi0, ComplexShape.embeddingUpIntLE] using hi'
    omega
  -- Route correction: read the component from the dual `πTruncGE` formula and then unop it.
  apply Quiver.Hom.op_inj
  change ((K.op.πTruncGE e.op).f n) =
    (K.op.truncGEXIso e.op hi' (by simpa using hi)).inv
  dsimp [CochainComplex.πTruncGE, HomologicalComplex.πTruncGE]
  rw [e.op.liftExtend_f (K.op.restrictionToTruncGE' e.op)
      (K.op.restrictionToTruncGE'_hasLift e.op) hi']
  rw [K.op.restrictionToTruncGE'_f_eq_iso_hom_iso_inv e.op hi' (by simpa using hi)]
  simp [HomologicalComplex.truncGEXIso, Category.assoc]
  rfl

/-- Helper for Remark 13.26.15: at the cutoff, the canonical truncation inclusion is the cycles
inclusion under the standard cutoff-term identification. -/
private theorem ιTruncLE_component_eq_cycles
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) :
    (K.ιTruncLE (-p)).f (-p) = (truncLE_term_iso_cycles K p).hom ≫ K.iCycles (-p) := by
  let e := embeddingUpIntLE (-p)
  let hi' : e.f 0 = -p := by
    simpa [e] using (embeddingUpIntLE_toNat_sub_eq p (-p) le_rfl)
  have hi : e.BoundaryLE 0 := by
    simpa [e] using (ComplexShape.boundaryLE_embeddingUpIntLE_iff (-p) 0).2 rfl
  -- Route correction: the cutoff component is the dual boundary formula for `πTruncGE`,
  -- transported across the canonical `opcycles`/`cycles` identification.
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

/-- Helper for Remark 13.26.15: degreewise, the chosen comparison factors the stage inclusion
through the canonical truncation inclusion. -/
private theorem truncation_filtration_stage_component_hom_comp_ιTruncLE
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) :
    (truncation_filtration_stage_component_iso K p n).hom ≫ (K.ιTruncLE (-p)).f n =
      ((K.truncationFiltration).stageInclusion p).f n := by
  -- Compare the three source-faithful cutoff regions separately.
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

/-- Helper for Remark 13.26.15: the stage differential is the componentwise restriction of the
ambient differential along the truncation-filtration stage inclusion. -/
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

/-- Helper for Remark 13.26.15: the chosen degreewise comparisons commute with differentials in
the direct `isoOfComponents` form. -/
private theorem truncation_filtration_stage_component_hom_comm_d_truncLE
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) :
    (truncation_filtration_stage_component_iso K p i).hom ≫ (K.truncLE (-p)).d i j =
      ((K.truncationFiltration).stage p).d i j ≫
        (truncation_filtration_stage_component_iso K p j).hom := by
  -- Route correction: cancel the mono `K.ιTruncLE (-p)` on the target side instead of unfolding
  -- the transported cutoff differential directly.
  let ι : K.truncLE (-p) ⟶ K := K.ιTruncLE (-p)
  letI : Mono (ι.f j) := by
    dsimp [ι, CochainComplex.ιTruncLE]
    infer_instance
  apply (cancel_mono (ι.f j)).1
  -- Compare both composites after postcomposing with the mono truncation inclusion.
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

-- Proof sketch: the `p`-th stage inclusion of the truncation filtration lands in
-- `τ_{\le -p}(K^•)`, and degreewise this factor map is the identity below degree `-p`, the
-- kernel identification in degree `-p`, and zero above. Hence the factor through `K.truncLE (-p)`
-- is an isomorphism.
/-- The canonical inclusion of the `p`-th truncation-filtration stage into `K^\bullet` factors
through `τ_{\le -p}(K^\bullet) = K.truncLE (-p)` by an isomorphism. -/
theorem truncationFiltration_stageInclusion_factors_ιTruncLE
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) :
    ∃ φ : (K.truncationFiltration).stage p ⟶ K.truncLE (-p),
      φ ≫ K.ιTruncLE (-p) = (K.truncationFiltration).stageInclusion p ∧ IsIso φ :=
by
  -- Package the fixed degreewise comparisons into a chain isomorphism and take its forward map.
  let E : (K.truncationFiltration).stage p ≅ K.truncLE (-p) :=
    HomologicalComplex.Hom.isoOfComponents
      (truncation_filtration_stage_component_iso K p)
      (fun i j hij ↦ truncation_filtration_stage_component_hom_comm_d_truncLE K p hij)
  refine ⟨E.hom, ?_, ?_⟩
  · -- The componentwise factorization through `K.ιTruncLE (-p)` upgrades to a chain-map identity.
    ext n
    exact truncation_filtration_stage_component_hom_comp_ιTruncLE K p n
  · -- The comparison is the hom of an isomorphism by construction.
    letI : IsIso E.hom := ⟨E.inv, E.hom_inv_id, E.inv_hom_id⟩
    infer_instance

end Filtrations

end CochainComplex

namespace CochainComplex.Plus

section SpectralSequences

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜]
  [LocallySmall ℬ] [WellPowered ℬ] [HasWidePullbacks ℬ] [HasCoproducts ℬ]
  [InitialMonoClass ℬ]
  [HasInjectiveResolutions 𝒜] [HasDerivedCategory.{w} ℬ]
  [(mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)).IsLocalization
    (boundedBelowHomotopyQuasiIso 𝒜)]

local notation "Qplus" => mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)
local notation "Qhplus" => HomotopyCategory.Plus.quotient 𝒜
local notation "plusι" => ObjectProperty.ι (t.plus : ObjectProperty (D(ℬ)))
local notation "H" => DerivedCategory.homologyFunctor ℬ

private theorem zero_le_of_one_le {r : ℤ} (hr : 1 ≤ r) : 0 ≤ r :=
  le_trans (by decide : (0 : ℤ) ≤ 1) hr

-- Proof sketch: apply Lemma `13.26.14` to the source-facing filtration
-- `K.obj.stupidFiltration`. The resulting filtered complex lives in `ℬ`; its graded pieces are
-- the images of the single
-- complexes `K^p[-p]`, so the `E₁`-page identifies with `R^qT(K^p)`, and the first differential
-- corresponds to the differential of `K^•`. The finite abutment filtrations and convergence
-- package are inherited from the owner theorem and kept on the same returned filtered complex,
-- together with the canonical comparison from the abutment to `H^*(RT(K^•))`.
/-- Remark 13.26.15 (1): the stupid filtration `F^p(K^\bullet) = \sigma_{\ge p}(K^\bullet)`
gives an alternative construction of the first Cartan-Eilenberg spectral sequence of
Lemma `13.21.3`: it is a bridge/view specialization of
`exists_filteredRightDerivedSpectralSequence`, with `E_1`-page `R^qT(K^p)` and `d_1`
induced by `d_K^p`. The returned owner `M` also carries the canonical finite
abutment-filtration and convergence package, together with the explicit abutment comparison
`H^n(M^\bullet) ≅ H^n(RT(K^\bullet))`. -/
theorem rightDerived_spectralSequence_from_stupidFiltration
    (T : 𝒜 ⥤ ℬ) [T.Additive] [PreservesFiniteLimits T]
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow T)
      (boundedBelowHomotopyQuasiIso 𝒜)]
    (K : Plus 𝒜) :
    let F := K.obj.stupidFiltration
    ∃ (M : FilteredComplex ℬ)
      (E : CohomologicalSpectralSequence ℬ 0)
      (_ : IsAssociatedToFilteredComplex M E)
      (_ : ∀ p : ℤ, Nonempty (F.stage p ≅ K.obj.stupidTrunc (embeddingUpIntGE p)))
      (pageOneIso : ∀ (p : ℤ) (q : ℕ),
        (E.page 1).X (p, Int.ofNat q) ≅ (T.rightDerived q).obj (K.obj.X p))
      (pageOneCommSq : ∀ (p : ℤ) (q : ℕ),
        CommSq
          ((E.page 1).d (p, Int.ofNat q) (p + 1, Int.ofNat q))
          (pageOneIso p q).hom
          (pageOneIso (p + 1) q).hom
          ((T.rightDerived q).map (K.obj.d p (p + 1))))
      (abutmentIso : ∀ n : ℤ,
        M.underlying.homology n ≅
          ((plusι ⋙ H n).obj
            ((Functor.totalRightDerived
                (mapBoundedBelowHomotopyCategoryToDerivedBelow T)
                Qplus
                (boundedBelowHomotopyQuasiIso 𝒜)).obj
              ((Qhplus ⋙ Qplus).obj K)))),
      CohomologicalSpectralSequence.IsBounded E ∧
        M.cohomologyFiltrationIsFinite ∧
        M.convergesToCohomology E := by
  admit

-- Proof sketch: apply Lemma `13.26.14` to the source-facing filtration
-- `K.obj.truncationFiltration`. The resulting filtered complex again lives in `ℬ`; the graded
-- pieces are quasi-isomorphic to
-- `H^{-p}(K^•)[p]`, so the associated truncation-filtration spectral sequence has
-- `E₁^{p,q} = R^{p + q}T(H^{-p}(K^•)[p]) = R^{2p + q}T(H^{-p}(K^•))`. Reindexing by `i = 2p + q`
-- and `j = -p` identifies the `E₂`-page with the Cartan-Eilenberg terms
-- `R^iT(H^j(K^•))`. As above, the owner theorem supplies the canonical boundedness,
-- convergence, and abutment comparison package on the same filtered complex.
/-- Remark 13.26.15 (2): the truncation filtration `F^p(K^\bullet) = \tau_{\le -p}(K^\bullet)`
gives an alternative construction of the second Cartan-Eilenberg spectral sequence of
Lemma `13.21.3`: it is a bridge/view specialization of
`exists_filteredRightDerivedSpectralSequence`, and its `E_2`-page is the Cartan-Eilenberg page
`R^iT(H^j(K^\bullet))`. The returned owner `M` also carries the canonical finite
abutment-filtration and convergence package, together with the explicit abutment comparison
`H^n(M^\bullet) ≅ H^n(RT(K^\bullet))`. -/
theorem rightDerived_spectralSequence_from_truncationFiltration
    (T : 𝒜 ⥤ ℬ) [T.Additive] [PreservesFiniteLimits T]
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow T)
      (boundedBelowHomotopyQuasiIso 𝒜)]
    (K : Plus 𝒜) :
    let F := K.obj.truncationFiltration
    ∃ (M : FilteredComplex ℬ)
      (E : CohomologicalSpectralSequence ℬ 0)
      (_ : IsAssociatedToFilteredComplex M E)
      (_ : ∀ p : ℤ, ∃ φ : F.stage p ⟶ K.obj.truncLE (-p),
        φ ≫ K.obj.ιTruncLE (-p) = F.stageInclusion p ∧ IsIso φ)
      (pageTwoIso : ∀ (i : ℕ) (j : ℤ),
        (E.page 2).X (Int.ofNat i, j) ≅
          (T.rightDerived i).obj (K.obj.homology j))
      (abutmentIso : ∀ n : ℤ,
        M.underlying.homology n ≅
          ((plusι ⋙ H n).obj
            ((Functor.totalRightDerived
                (mapBoundedBelowHomotopyCategoryToDerivedBelow T)
                Qplus
                (boundedBelowHomotopyQuasiIso 𝒜)).obj
              ((Qhplus ⋙ Qplus).obj K)))),
      CohomologicalSpectralSequence.IsBounded E ∧
        M.cohomologyFiltrationIsFinite ∧
        M.convergesToCohomology E := by
  admit

-- Proof sketch: apply Lemma `13.21.3` to the chosen Cartan-Eilenberg resolution `CE` to obtain
-- the first spectral sequence on the canonical filtered total `FI₁`. Apply the stupid-filtration
-- construction of this remark using the filtered injective resolution induced by `CE`; both
-- constructions therefore come from the same filtered complex, so the choice-independence theorem
-- `exists_filteredRightDerivedSpectralSequenceIso_of_sameSource` produces a comparison morphism
-- that is an isomorphism from page `1` onward. The page-`1` square is the identity under the
-- common `R^qT(K^p)`-identification, and the `d₁`-compatibility comes from the previous theorem.
/-- Remark 13.26.15: for any Cartan-Eilenberg resolution `CE` of `K^\bullet`, the stupid-
filtration construction can be matched exactly with the first spectral sequence of
Lemma `13.21.3`. Concretely, after realizing both constructions on the canonical first filtered
total of `T(I^{\bullet,\bullet})`, there is a comparison morphism which is an isomorphism from
page `1` onward and is the identity on the common `E_1^{p,q} = R^qT(K^p)` terms. -/
theorem rightDerived_spectralSequence_from_stupidFiltration_matches_firstCartanEilenberg
    (T : 𝒜 ⥤ ℬ) [T.Additive] [PreservesFiniteLimits T]
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow T)
      (boundedBelowHomotopyQuasiIso 𝒜)]
    (K : Plus 𝒜) (CE : CartanEilenbergResolution K) :
    let F := K.obj.stupidFiltration
    let I :=
      ((T.mapHomologicalComplex (up ℤ)).mapHomologicalComplex (up ℤ)).obj CE.doubleComplex.obj
    let FI₁ := firstDoubleComplexFilteredComplex I
    ∃ (E E' : CohomologicalSpectralSequence ℬ 0)
      (_ : IsAssociatedToFilteredComplex FI₁ E)
      (_ : IsAssociatedToFilteredComplex FI₁ E')
      (_ : ∀ p : ℤ, Nonempty (F.stage p ≅ K.obj.stupidTrunc (embeddingUpIntGE p)))
      (pageOneIso : ∀ (p : ℤ) (q : ℕ),
        (E.page 1).X (p, Int.ofNat q) ≅ (T.rightDerived q).obj (K.obj.X p))
      (pageOneCommSq : ∀ (p : ℤ) (q : ℕ),
        CommSq
          ((E.page 1).d (p, Int.ofNat q) (p + 1, Int.ofNat q))
          (pageOneIso p q).hom
          (pageOneIso (p + 1) q).hom
          ((T.rightDerived q).map (K.obj.d p (p + 1))))
      (firstPageOneIso : ∀ (p : ℤ) (q : ℕ),
        (E'.page 1).X (p, Int.ofNat q) ≅ (T.rightDerived q).obj (K.obj.X p))
      (φ : E ⟶ E'),
      (∀ (p : ℤ) (q : ℕ),
        CommSq
          ((φ.hom 1).f (p, Int.ofNat q))
          (pageOneIso p q).hom
          (firstPageOneIso p q).hom
          (𝟙 _)) ∧
        ∀ (r : ℤ) (hr : 1 ≤ r) (p q : ℤ),
          IsIso ((φ.hom r (zero_le_of_one_le hr)).f (p, q)) := by
  admit

-- Proof sketch: apply Lemma `13.21.3` to `CE` to obtain the second Cartan-Eilenberg spectral
-- sequence on the canonical second filtered total `FI₂`. The truncation-filtration construction
-- from this remark is another realization of the spectral sequence attached to the same filtered
-- complex, so the same choice-independence argument yields a comparison morphism that is an
-- isomorphism from page `1` onward. Hence the `E₂`-page identification with
-- `R^iT(H^j(K^\bullet))` agrees with the one from Lemma `13.21.3`.
/-- Remark 13.26.15: for any Cartan-Eilenberg resolution `CE` of `K^\bullet`, the truncation-
filtration construction can be matched exactly with the second spectral sequence of
Lemma `13.21.3`. In particular, after identifying both constructions on the canonical second
filtered total of `T(I^{\bullet,\bullet})`, there is a comparison morphism which is an
isomorphism from page `1` onward, so the common `E_2^{i,j} = R^iT(H^j(K^\bullet))` page is the
second Cartan-Eilenberg page. -/
theorem rightDerived_spectralSequence_from_truncationFiltration_matches_secondCartanEilenberg
    (T : 𝒜 ⥤ ℬ) [T.Additive] [PreservesFiniteLimits T]
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow T)
      (boundedBelowHomotopyQuasiIso 𝒜)]
    (K : Plus 𝒜) (CE : CartanEilenbergResolution K) :
    let F := K.obj.truncationFiltration
    let I :=
      ((T.mapHomologicalComplex (up ℤ)).mapHomologicalComplex (up ℤ)).obj CE.doubleComplex.obj
    let FI₂ := secondDoubleComplexFilteredComplex I
    ∃ (E E' : CohomologicalSpectralSequence ℬ 0)
      (_ : IsAssociatedToFilteredComplex FI₂ E)
      (_ : IsAssociatedToFilteredComplex FI₂ E')
      (_ : ∀ p : ℤ, ∃ φ : F.stage p ⟶ K.obj.truncLE (-p),
        φ ≫ K.obj.ιTruncLE (-p) = F.stageInclusion p ∧ IsIso φ)
      (pageTwoIso : ∀ (i : ℕ) (j : ℤ),
        (E.page 2).X (Int.ofNat i, j) ≅
          (T.rightDerived i).obj (K.obj.homology j))
      (secondPageTwoIso : ∀ (i : ℕ) (j : ℤ),
        (E'.page 2).X (Int.ofNat i, j) ≅
          (T.rightDerived i).obj (K.obj.homology j))
      (φ : E ⟶ E'),
      (∀ (i : ℕ) (j : ℤ),
        CommSq
          ((φ.hom 2).f (Int.ofNat i, j))
          (pageTwoIso i j).hom
          (secondPageTwoIso i j).hom
          (𝟙 _)) ∧
        ∀ (r : ℤ) (hr : 1 ≤ r) (p q : ℤ),
          IsIso ((φ.hom r (zero_le_of_one_le hr)).f (p, q)) := by
  admit

end SpectralSequences

end CochainComplex.Plus

end CategoryTheory
