import LinearRepresentations_Serre_1977.Chap04.Lemma_4_49
import LinearRepresentations_Serre_1977.Chap04.Lemma_4_48
import LinearRepresentations_Serre_1977.Chap04.Theorem_4_5
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

-- Semantic recall: `MeasureTheory.convolution_mul` confirms the integral term is a canonical
-- convolution-type expression; the source-facing statement here keeps Serre's `y⁻¹ * x` formula
-- and the `Submodule.span` owner for finite linear combinations of regular-representation
-- translates.

universe u

section

variable {G : Type u} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
  [IsTopologicalGroup G] [MeasurableMul G] [CompactSpace G]

local notation "μG" => (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G) : Measure G)
local notation "L²G" => (G →₂[μG] ℂ)

/-- Helper for Lemma 4-50: choose the weighted-orbit representative of the convolution class
whenever `h ∈ L²(G)`, and choose `0` otherwise. -/
lemma compactGroupConvolutionFun_exists (f h : G → ℂ) :
    ∃ g : G → ℂ,
      (∀ hh : MemLp h (2 : ENNReal) μG,
          g =
            fun x : G ↦
              ((∫ y, f y • regularRepresentation μG y (MemLp.toLp h hh) ∂μG : L²G) : G → ℂ) x) ∨
        (¬ MemLp h (2 : ENNReal) μG ∧ g = 0) := by
  classical
  by_cases hh : MemLp h (2 : ENNReal) μG
  · refine ⟨fun x : G ↦
      ((∫ y, f y • regularRepresentation μG y (MemLp.toLp h hh) ∂μG : L²G) : G → ℂ) x, Or.inl ?_⟩
    intro hh'
    funext x
    have htoLp : MemLp.toLp h hh = MemLp.toLp h hh' :=
      MemLp.toLp_congr hh hh' (Filter.EventuallyEq.rfl)
    simp [htoLp]
  · exact ⟨0, Or.inr ⟨hh, rfl⟩⟩

/-- The `L²(G)` representative of the convolution class attached to `f` and `h`. When
`h ∈ L²(G)`, this is the function underlying the Bochner integral of the weighted regular orbit. -/
def compactGroupConvolutionFun (f h : G → ℂ) : G → ℂ :=
  Classical.choose (compactGroupConvolutionFun_exists (G := G) f h)

/-- The `ℂ`-submodule of `L²(G)` spanned by the left translates of `h` under the regular
representation. -/
def regularRepresentationTranslateSpan (h : L²G) : Submodule ℂ L²G :=
  Submodule.span ℂ (Set.range fun y : G ↦ regularRepresentation μG y h)

/-- The `L²(G)` class of the convolution function once a `MemLp` witness is fixed. -/
def compactGroupConvolutionToLp (f h : G → ℂ)
    (hF : MemLp (compactGroupConvolutionFun (G := G) f h) (2 : ENNReal) μG) : L²G :=
  MemLp.toLp (compactGroupConvolutionFun (G := G) f h) hF

/-- The span of left translates of the `L²(G)` class associated to `h`. -/
def regularRepresentationTranslateSpanOfMemLp (h : G → ℂ)
    (hh : MemLp h (2 : ENNReal) μG) : Submodule ℂ L²G :=
  regularRepresentationTranslateSpan (G := G) (MemLp.toLp h hh)

/-- Helper for Lemma 4-50: the `L²(G)`-valued regular-representation orbit weighted by an
integrable scalar function is Bochner integrable. -/
lemma integrable_weightedRegularRepresentationOrbit
    {f h : G → ℂ} (hf : Integrable f μG) (hh : MemLp h (2 : ENNReal) μG) :
    Integrable (fun y : G ↦ f y • regularRepresentation μG y (MemLp.toLp h hh)) μG := by
  have horbit_meas :
      AEStronglyMeasurable (fun y : G ↦ regularRepresentation μG y (MemLp.toLp h hh)) μG := by
    have hcont : Continuous fun y : G ↦ regularRepresentation μG y (MemLp.toLp h hh) := by
      simpa [regularRepresentation] using
        (continuous_id.smul continuous_const :
          Continuous fun y : G ↦ y • (MemLp.toLp h hh))
    have hcompact :
        HasCompactSupport (fun y : G ↦ regularRepresentation μG y (MemLp.toLp h hh)) := by
      exact HasCompactSupport.of_support_subset_isCompact isCompact_univ (by intro x hx; simp)
    have horbit_int :
        Integrable (fun y : G ↦ regularRepresentation μG y (MemLp.toLp h hh)) μG :=
      hcont.integrable_of_hasCompactSupport hcompact
    exact horbit_int.aestronglyMeasurable
  have horbit_bound :
      ∀ᵐ y : G ∂μG, ‖regularRepresentation μG y (MemLp.toLp h hh)‖ ≤ ‖MemLp.toLp h hh‖ := by
    exact Eventually.of_forall fun y ↦ by
      simpa [regularRepresentation, MulAction.compHom_smul_def] using
        (le_of_eq (DomMulAct.norm_smul_Lp (μ := μG) (p := (2 : ℝ≥0∞))
          (c := DomMulAct.mk y⁻¹) (f := MemLp.toLp h hh)))
  exact hf.smul_bdd ‖MemLp.toLp h hh‖ horbit_meas horbit_bound

/-- Helper for Lemma 4-50: once `h ∈ L²(G)`, `compactGroupConvolutionFun f h` is the function
underlying the weighted-orbit Bochner integral. -/
lemma compactGroupConvolutionFun_eq_of_memLp
    {f h : G → ℂ} (hh : MemLp h (2 : ENNReal) μG) :
    compactGroupConvolutionFun (G := G) f h =
      fun x : G ↦
        ((∫ y, f y • regularRepresentation μG y (MemLp.toLp h hh) ∂μG : L²G) : G → ℂ) x := by
  rcases Classical.choose_spec (compactGroupConvolutionFun_exists (G := G) f h) with hspec | hspec
  · exact hspec hh
  · exact (hspec.1 hh).elim

/-- Helper for Lemma 4-50: weighting any regular-representation orbit in `L²(G)` by an
integrable scalar function is Bochner integrable. -/
lemma integrable_weightedRegularRepresentationOrbit_lp
    {f : G → ℂ} (hf : Integrable f μG) (h₂ : L²G) :
    Integrable (fun y : G ↦ f y • regularRepresentation μG y h₂) μG := by
  have horbit_meas :
      AEStronglyMeasurable (fun y : G ↦ regularRepresentation μG y h₂) μG := by
    -- The orbit map is continuous on the compact group, hence a.e. strongly measurable.
    have hcont : Continuous fun y : G ↦ regularRepresentation μG y h₂ := by
      simpa [regularRepresentation] using
        (continuous_id.smul continuous_const : Continuous fun y : G ↦ y • h₂)
    have hsupport_subset :
        Function.support (fun y : G ↦ regularRepresentation μG y h₂) ⊆ (Set.univ : Set G) := by
      intro y hy
      simp
    have hcompact :
        HasCompactSupport (fun y : G ↦ regularRepresentation μG y h₂) := by
      exact HasCompactSupport.of_support_subset_isCompact isCompact_univ hsupport_subset
    have horbit_int :
        Integrable (fun y : G ↦ regularRepresentation μG y h₂) μG :=
      hcont.integrable_of_hasCompactSupport hcompact
    exact horbit_int.aestronglyMeasurable
  have horbit_bound :
      ∀ᵐ y : G ∂μG, ‖regularRepresentation μG y h₂‖ ≤ ‖h₂‖ := by
    exact Eventually.of_forall fun y ↦ by
      simpa [regularRepresentation, MulAction.compHom_smul_def] using
        (le_of_eq (DomMulAct.norm_smul_Lp (μ := μG) (p := (2 : ℝ≥0∞))
          (c := DomMulAct.mk y⁻¹) (f := h₂)))
  -- Combine the `L¹` weight with the uniform orbit norm bound.
  exact hf.smul_bdd ‖h₂‖ horbit_meas horbit_bound

/-- Helper for Lemma 4-50: the chosen `L²(G)` representative of the convolution class agrees
with the weighted regular-orbit integral. -/
lemma exists_compactGroupConvolutionToLp_eq_weightedOrbitIntegral
    {f h : G → ℂ} (hh : MemLp h (2 : ENNReal) μG) :
    ∃ hF : MemLp (compactGroupConvolutionFun (G := G) f h) (2 : ENNReal) μG,
      compactGroupConvolutionToLp (G := G) f h hF =
        ∫ y, f y • regularRepresentation μG y (MemLp.toLp h hh) ∂μG := by
  let T : L²G := ∫ y, f y • regularRepresentation μG y (MemLp.toLp h hh) ∂μG
  have hfun_eq :
      compactGroupConvolutionFun (G := G) f h = fun x : G ↦ (T : L²G) x := by
    simpa [T] using
      compactGroupConvolutionFun_eq_of_memLp (G := G) (f := f) (h := h) hh
  have hfun_ae :
      compactGroupConvolutionFun (G := G) f h =ᵐ[μG] fun x : G ↦ (T : L²G) x :=
    Filter.Eventually.of_forall fun x ↦ congrFun hfun_eq x
  have hT_mem : MemLp (fun x : G ↦ (T : L²G) x) (2 : ENNReal) μG := by
    simpa [T] using (Lp.memLp T)
  have hT_aestronglyMeasurable :
      AEStronglyMeasurable (fun x : G ↦ (T : L²G) x) μG := by
    simpa [T] using (Lp.aestronglyMeasurable T)
  have hfun_aestronglyMeasurable :
      AEStronglyMeasurable (compactGroupConvolutionFun (G := G) f h) μG := by
    simpa [hfun_eq] using hT_aestronglyMeasurable
  have hnorm_ae :
      ∀ᵐ x : G ∂μG,
        ‖(T : L²G) x‖ = ‖compactGroupConvolutionFun (G := G) f h x‖ := by
    exact hfun_ae.mono fun x hx ↦ by simp [hx]
  have hF :
      MemLp (compactGroupConvolutionFun (G := G) f h) (2 : ENNReal) μG :=
    hT_mem.congr_norm hfun_aestronglyMeasurable hnorm_ae
  have htoLp :
      compactGroupConvolutionToLp (G := G) f h hF = T := by
    simpa [compactGroupConvolutionToLp] using MemLp.toLp_congr hF (Lp.memLp T) hfun_ae
  have htoLp' :
      compactGroupConvolutionToLp (G := G) f h hF =
        ∫ y, f y • regularRepresentation μG y (MemLp.toLp h hh) ∂μG := by
    simpa [T] using htoLp
  exact ⟨hF, htoLp'⟩

/-- Helper for Lemma 4-50: on one partition cell, the weighted orbit error is bounded by
`∫ z in E i, ‖f z‖ * ε`. -/
lemma norm_integral_cell_weightedRegularRepresentation_sub_le
    {f : G → ℂ} (hf : Integrable f μG) {h₂ : L²G} {ε : ℝ}
    {n : ℕ} {y : Fin n → G} {E : Fin n → Set G}
    (hpart : IsRegularRepresentationApproxPartition h₂ ε y E) (i : Fin n) :
    ‖∫ z in E i,
        f z • (regularRepresentation μG (y i) h₂ - regularRepresentation μG z h₂) ∂μG‖ ≤
      ∫ z in E i, ‖f z‖ * ε ∂μG := by
  have hleft :
      Integrable (fun z : G ↦ f z • regularRepresentation μG (y i) h₂) μG := hf.smul_const _
  have hright :
      Integrable (fun z : G ↦ f z • regularRepresentation μG z h₂) μG :=
    integrable_weightedRegularRepresentationOrbit_lp (G := G) hf h₂
  have hdiff_int :
      IntegrableOn
        (fun z : G ↦
          f z • (regularRepresentation μG (y i) h₂ - regularRepresentation μG z h₂))
        (E i) μG := by
    -- Rewrite the difference as a single weighted orbit error before restricting to the cell.
    have hsub :
        Integrable
          (fun z : G ↦
            f z • regularRepresentation μG (y i) h₂ -
              f z • regularRepresentation μG z h₂) μG :=
      hleft.sub hright
    simpa [smul_sub] using hsub.integrableOn
  have hbound_int : IntegrableOn (fun z : G ↦ ‖f z‖ * ε) (E i) μG := by
    simpa [mul_comm] using (hf.norm.const_mul ε).integrableOn
  have hnorm_le :
      ‖∫ z in E i,
          f z • (regularRepresentation μG (y i) h₂ - regularRepresentation μG z h₂) ∂μG‖ ≤
        ∫ z in E i,
          ‖f z • (regularRepresentation μG (y i) h₂ - regularRepresentation μG z h₂)‖ ∂μG := by
    simpa [IntegrableOn] using
      (norm_integral_le_integral_norm
        (μ := μG.restrict (E i))
        (f := fun z : G ↦
          f z • (regularRepresentation μG (y i) h₂ - regularRepresentation μG z h₂)))
  refine hnorm_le.trans ?_
  refine setIntegral_mono_on hdiff_int.norm hbound_int (hpart.measurableSet i) ?_
  intro z hz
  calc
    ‖f z • (regularRepresentation μG (y i) h₂ - regularRepresentation μG z h₂)‖ =
        ‖f z‖ * ‖regularRepresentation μG (y i) h₂ - regularRepresentation μG z h₂‖ := by
          rw [norm_smul]
    _ ≤ ‖f z‖ * ε := by
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      simpa [norm_sub_rev] using le_of_lt (hpart.norm_sub_lt i hz)

/-- Helper for Lemma 4-50: the finite partition approximant stays within
`ε * ∫ z, ‖f z‖ ∂μG` of the weighted regular-orbit integral. -/
lemma weightedOrbit_partitionApprox_norm_le
    {f : G → ℂ} (hf : Integrable f μG) {h₂ : L²G} {ε : ℝ}
    {n : ℕ} {y : Fin n → G} {E : Fin n → Set G}
    (hpart : IsRegularRepresentationApproxPartition h₂ ε y E) :
    ‖(∑ i : Fin n, (∫ z in E i, f z ∂μG) • regularRepresentation μG (y i) h₂) -
        ∫ z, f z • regularRepresentation μG z h₂ ∂μG‖ ≤
      ε * ∫ z, ‖f z‖ ∂μG := by
  let orbit : G → L²G := fun z ↦ regularRepresentation μG z h₂
  let orbitWeighted : G → L²G := fun z ↦ f z • orbit z
  have horbitWeighted_int : Integrable orbitWeighted μG := by
    simpa [orbit, orbitWeighted] using
      integrable_weightedRegularRepresentationOrbit_lp (G := G) hf h₂
  have hT_split :
      (∫ z, orbitWeighted z ∂μG) = ∑ i : Fin n, ∫ z in E i, orbitWeighted z ∂μG := by
    -- Split the weighted-orbit integral along the measurable partition.
    have hsplt :=
      integral_iUnion_fintype (μ := μG) (f := orbitWeighted)
        (fun i ↦ hpart.measurableSet i)
        (fun i j hij ↦ hpart.pairwiseDisjoint hij)
        (fun i ↦ horbitWeighted_int.integrableOn)
    simpa [hpart.iUnion_eq_univ] using hsplt
  have hu_split :
      (∑ i : Fin n, (∫ z in E i, f z ∂μG) • orbit (y i)) =
        ∑ i : Fin n, ∫ z in E i, f z • orbit (y i) ∂μG := by
    -- Each cell contributes a constant orbit vector scaled by the scalar cell integral.
    symm
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    simpa [IntegrableOn] using
      (integral_smul_const
        (μ := μG.restrict (E i))
        (f := fun z : G ↦ f z)
        (c := orbit (y i)))
  have hdiff_split :
      (∑ i : Fin n, (∫ z in E i, f z ∂μG) • orbit (y i)) - ∫ z, orbitWeighted z ∂μG =
        ∑ i : Fin n, ∫ z in E i, f z • (orbit (y i) - orbit z) ∂μG := by
    rw [hT_split, hu_split]
    calc
      ∑ i : Fin n, ∫ z in E i, f z • orbit (y i) ∂μG -
          ∑ i : Fin n, ∫ z in E i, orbitWeighted z ∂μG
          = ∑ i : Fin n,
              ((∫ z in E i, f z • orbit (y i) ∂μG) -
                ∫ z in E i, orbitWeighted z ∂μG) := by
                simpa using (Finset.sum_sub_distrib :
                  (∑ i : Fin n,
                    ((∫ z in E i, f z • orbit (y i) ∂μG) -
                      ∫ z in E i, orbitWeighted z ∂μG)) =
                  _)
      _ = ∑ i : Fin n, ∫ z in E i, f z • (orbit (y i) - orbit z) ∂μG := by
            refine Finset.sum_congr rfl fun i hi ↦ ?_
            rw [← integral_sub]
            · apply integral_congr_ae
              exact Filter.Eventually.of_forall fun z ↦ by
                simp [orbitWeighted, smul_sub]
            · exact (hf.smul_const _).integrableOn
            · exact horbitWeighted_int.integrableOn
  have hnorm_partition :
      ‖∑ i : Fin n, ∫ z in E i, f z • (orbit (y i) - orbit z) ∂μG‖ ≤
        ∑ i : Fin n, ‖∫ z in E i, f z • (orbit (y i) - orbit z) ∂μG‖ := by
    exact norm_sum_le _ _
  have hbound_integrable :
      ∀ i : Fin n, IntegrableOn (fun z : G ↦ ‖f z‖ * ε) (E i) μG := by
    intro i
    simpa [mul_comm] using (hf.norm.const_mul ε).integrableOn
  calc
    ‖(∑ i : Fin n, (∫ z in E i, f z ∂μG) • regularRepresentation μG (y i) h₂) -
        ∫ z, f z • regularRepresentation μG z h₂ ∂μG‖
        =
          ‖∑ i : Fin n, ∫ z in E i, f z • (orbit (y i) - orbit z) ∂μG‖ := by
            rw [hdiff_split]
    _ ≤ ∑ i : Fin n, ‖∫ z in E i, f z • (orbit (y i) - orbit z) ∂μG‖ := hnorm_partition
    _ ≤ ∑ i : Fin n, ∫ z in E i, ‖f z‖ * ε ∂μG := by
          refine Finset.sum_le_sum fun i hi ↦ ?_
          simpa [orbit] using
            norm_integral_cell_weightedRegularRepresentation_sub_le
              (G := G) (f := f) hf hpart i
    _ = ∫ z, ‖f z‖ * ε ∂μG := by
          symm
          have hsplt :=
            integral_iUnion_fintype (μ := μG)
              (f := fun z : G ↦ ‖f z‖ * ε)
              (fun i ↦ hpart.measurableSet i)
              (fun i j hij ↦ hpart.pairwiseDisjoint hij)
              hbound_integrable
          simpa [hpart.iUnion_eq_univ] using hsplt
    _ = ε * ∫ z, ‖f z‖ ∂μG := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun z ↦ by ring

/-- Lemma 4-50: for a compact group `G`, an `L¹` function `f : G → ℂ`, and an `L²` function
`h : G → ℂ`, the convolution function `x ↦ ∫ y, f y * h (y⁻¹ * x) ∂μG` belongs to `L²(G)` and is
the limit in `L²(G)` of a sequence of finite linear combinations of left translates of
`MemLp.toLp h hh`. -/
theorem exists_tendsto_memLp_toLp_integral_mul_inv_mul
    {f h : G → ℂ} (hf : Integrable f μG) (hh : MemLp h (2 : ENNReal) μG) :
    ∃ hF : MemLp (compactGroupConvolutionFun (G := G) f h) (2 : ENNReal) μG,
      ∃ u : ℕ → L²G,
        Tendsto u atTop (𝓝 (compactGroupConvolutionToLp (G := G) f h hF)) ∧
        ∀ n, u n ∈ regularRepresentationTranslateSpanOfMemLp (G := G) h hh := by
  classical
  -- Route correction: isolate the dependent `hF` witness and the partition error estimate into
  -- helper lemmas so the main theorem only performs the final convergence assembly.
  let h₂ : L²G := MemLp.toLp h hh
  let T : L²G := ∫ y, f y • regularRepresentation μG y h₂ ∂μG
  rcases exists_compactGroupConvolutionToLp_eq_weightedOrbitIntegral
      (G := G) (f := f) (h := h) hh with ⟨hF, htoLp_raw⟩
  have htoLp : compactGroupConvolutionToLp (G := G) f h hF = T := by
    simpa [T, h₂] using htoLp_raw
  have hε_pos : ∀ n : ℕ, 0 < ((n : ℝ) + 1)⁻¹ := by
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    simpa using inv_pos.mpr hn
  choose N y E hpart using
    fun n : ℕ ↦
      exists_finite_borel_partition_regularRepresentation_norm_sub_lt
        (G := G) (ε := ((n : ℝ) + 1)⁻¹) h₂ (hε_pos n)
  let u : ℕ → L²G := fun n ↦
    ∑ i : Fin (N n), (∫ z in E n i, f z ∂μG) • regularRepresentation μG (y n i) h₂
  have hu_mem_aux : ∀ n, u n ∈ regularRepresentationTranslateSpan (G := G) h₂ := by
    intro n
    -- Each approximant is a finite linear combination of translates of `h₂`.
    have :
        (∑ i : Fin (N n),
            (∫ z in E n i, f z ∂μG) • regularRepresentation μG (y n i) h₂) ∈
          regularRepresentationTranslateSpan (G := G) h₂ := by
      refine Submodule.sum_mem _ fun i hi ↦ ?_
      refine (regularRepresentationTranslateSpan (G := G) h₂).smul_mem _ ?_
      exact Submodule.subset_span ⟨y n i, rfl⟩
    simpa [u] using this
  have hu_mem : ∀ n, u n ∈ regularRepresentationTranslateSpanOfMemLp (G := G) h hh := by
    intro n
    simpa [regularRepresentationTranslateSpanOfMemLp, h₂] using hu_mem_aux n
  have hdist_le : ∀ n, ‖u n - T‖ ≤ (((n : ℝ) + 1)⁻¹) * ∫ z, ‖f z‖ ∂μG := by
    intro n
    simpa [u, T, h₂] using
      weightedOrbit_partitionApprox_norm_le
        (G := G) (f := f) hf (hpart n)
  have hdist_tendsto : Tendsto (fun n ↦ dist (u n) T) atTop (𝓝 0) := by
    have hbound_tendsto :
        Tendsto (fun n : ℕ ↦ (((n : ℝ) + 1)⁻¹) * ∫ z, ‖f z‖ ∂μG) atTop (𝓝 0) := by
      have hε_tendsto : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
        have hnat_add : Tendsto (fun n : ℕ ↦ n + 1) atTop atTop :=
          Filter.tendsto_add_atTop_nat 1
        have hnat_cast :
            Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ))) atTop atTop :=
          tendsto_natCast_atTop_atTop.comp hnat_add
        simpa [Nat.cast_add] using tendsto_inv_atTop_zero.comp hnat_cast
      simpa [zero_mul] using hε_tendsto.mul_const (∫ z, ‖f z‖ ∂μG)
    refine squeeze_zero (fun n ↦ dist_nonneg) ?_ hbound_tendsto
    intro n
    simpa [dist_eq_norm] using hdist_le n
  refine ⟨hF, u, ?_, hu_mem⟩
  rw [htoLp]
  exact Metric.tendsto_atTop.2 <| by
    intro ε hε
    rcases Metric.tendsto_atTop.1 hdist_tendsto ε hε with ⟨Nε, hNε⟩
    exact ⟨Nε, fun n hn ↦ by simpa [dist_eq_norm] using hNε n hn⟩

end
