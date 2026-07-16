import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0015_Proposition_5_1»
import DifferentialForms_Cartan_1970.cartan.II.section06.«0018_Exercise_3»
import DifferentialForms_Cartan_1970.cartan.III.section11.frozen_0003_Theorem_III_5_extra_2
import DifferentialForms_Cartan_1970.cartan.III.section11.«0010_Definition_III_5_extra_7»
import DifferentialForms_Cartan_1970.cartan.III.section11.«frozen_0011_Proposition_5_1»
import DifferentialForms_Cartan_1970.cartan.III.section11.«0007_Remark_III_5_extra_6»
import DifferentialForms_Cartan_1970.cartan.III.section11.«0013_Proposition_5_2».ConstantShift
import DifferentialForms_Cartan_1970.cartan.III.section11.«0013_Proposition_5_2».NormalFormSupport
import DifferentialForms_Cartan_1970.cartan.III.section11.«0013_Proposition_5_2».WeightedLogResidues
import DifferentialForms_Cartan_1970.cartan.III.section11.«0013_Proposition_5_2».WeightedLogPeriodicity
import DifferentialForms_Cartan_1970.cartan.III.section11.«0013_Proposition_5_2».PeriodParallelogramBoundary
import DifferentialForms_Cartan_1970.cartan.III.section11.«0013_Proposition_5_2».PeriodParallelogramCoordinates
import DifferentialForms_Cartan_1970.cartan.III.section11.«0013_Proposition_5_2».BoundaryWeightedSums

open Filter
open scoped BigOperators Topology unitInterval
open MeromorphicOn

noncomputable section

variable {f : ℂ → ℂ} (L : PeriodPair) (P : Set ℂ)

/-- Helper for Proposition 5.2: the normalized weighted boundary integral on a boundary-generic
translated period parallelogram vanishes modulo the period lattice. -/
lemma weightedBoundaryIntegralDivTwoPiI_eq_zero_mod_periodLattice
    {g : ℂ → ℂ} {z₁ : ℂ}
    (hg : Meromorphic g)
    (hperiods : HasPeriodLattice L g)
    (hboundary : ∀ z ∈ frontier (L.periodParallelogram z₁),
      meromorphicOrderAt g z = (0 : WithTop ℤ)) :
    ((((∑ i : Unit,
          ∫ᶜ z in ((fun _ : Unit ↦
            (periodParallelogramBoundaryPath (L := L) z₁).toClosedPath) i).toPath,
            ((fun w ↦ w * logDeriv g w) dz) z) /
        (2 * Real.pi * Complex.I : ℂ)) : ℂ) :
      ℂ ⧸ L.lattice.toAddSubgroup) = 0 := by
  let z0 : ℂ := z₁
  let z1' : ℂ := z₁ + L.ω₁
  let z2 : ℂ := z₁ + L.ω₁ + L.ω₂
  let z3 : ℂ := z₁ + L.ω₂
  let gNF : ℂ → ℂ := toMeromorphicNFOn g Set.univ
  let nonzeroOwner : Set ℂ := {z | gNF z ≠ 0}
  have hω₁ : Function.Periodic (logDeriv g) L.ω₁ := by
    -- The first period of `g` is also a period of its logarithmic derivative.
    intro z
    simpa [add_assoc, add_left_comm, add_comm] using
      logDeriv_add_period_eq (L := L) (g := g) hperiods (ω := L.ω₁) (z := z)
        L.ω₁_mem_lattice
  have hω₂ : Function.Periodic (logDeriv g) L.ω₂ := by
    -- The second period of `g` is also a period of its logarithmic derivative.
    intro z
    simpa [add_assoc, add_left_comm, add_comm] using
      logDeriv_add_period_eq (L := L) (g := g) hperiods (ω := L.ω₂) (z := z)
        L.ω₂_mem_lattice
  have hω₁_ne : L.ω₁ ≠ 0 := by
    -- Each period-basis vector is nonzero.
    simpa using L.basis.ne_zero 0
  have hω₂_ne : L.ω₂ ≠ 0 := by
    -- The second period-basis vector is nonzero for the same reason.
    simpa using L.basis.ne_zero 1
  have hz0z1 : z0 ≠ z1' := by
    -- The bottom edge is nondegenerate because it moves by `ω₁`.
    intro hz
    have : z0 - z1' = 0 := sub_eq_zero.mpr hz
    exact hω₁_ne (by simpa [z0, z1'] using this)
  have hz1z2 : z1' ≠ z2 := by
    -- The right edge is nondegenerate because it moves by `ω₂`.
    intro hz
    have : z1' - z2 = 0 := sub_eq_zero.mpr hz
    exact hω₂_ne (by simpa [z1', z2, add_assoc] using this)
  have hz2z3 : z2 ≠ z3 := by
    -- The top edge is nondegenerate because it moves by `ω₁`.
    intro hz
    have : z2 - z3 = 0 := sub_eq_zero.mpr hz
    exact hω₁_ne (by simpa [z2, z3, add_assoc, add_left_comm, add_comm] using this)
  have hz0z3 : z0 ≠ z3 := by
    -- The left base edge is nondegenerate because it moves by `ω₂`.
    intro hz
    have : z0 - z3 = 0 := sub_eq_zero.mpr hz
    exact hω₂_ne (by simpa [z0, z3] using this)
  have hgNF : MeromorphicNFOn gNF Set.univ := by
    -- The global normal-form owner of `g` is meromorphic normal form on the whole plane.
    simpa [gNF] using meromorphicNFOn_toMeromorphicNFOn g Set.univ
  have hgNF_order :
      ∀ z ∈ frontier (L.periodParallelogram z₁), meromorphicOrderAt gNF z = 0 := by
    intro z hz
    -- On the frontier, the normal-form owner has the same order as `g`.
    dsimp [gNF]
    rw [meromorphicOrderAt_toMeromorphicNFOn hg.meromorphicOn (by simp)]
    simpa using hboundary z hz
  have hgNF_cont :
      ContinuousOn (logDeriv gNF) (frontier (L.periodParallelogram z₁)) := by
    intro z hz
    -- Order zero on the frontier makes the normal-form logarithmic derivative continuous there.
    exact
      (differentiableAt_logDeriv_of_meromorphicNFAt_order_zero
        (hgNF (by simp)) (hgNF_order z hz)).continuousAt.continuousWithinAt
  have hweightedNF_cont :
      ContinuousOn (fun z ↦ z * logDeriv gNF z) (frontier (L.periodParallelogram z₁)) := by
    intro z hz
    -- The same order-zero input gives continuity of the weighted logarithmic derivative.
    exact
      (differentiableAt_weighted_logDeriv_of_order_zero
        (hgNF (by simp)) (hgNF_order z hz)).continuousAt.continuousWithinAt
  have hweightedEq :
      (fun z ↦ z * logDeriv g z) =ᶠ[Filter.codiscreteWithin (Set.univ : Set ℂ)]
        (fun z ↦ z * logDeriv gNF z) := by
    -- On the whole plane, the weighted logarithmic derivative agrees codiscretely with the
    -- global normal-form owner.
    simpa [gNF] using
      weightedLogDeriv_toMeromorphicNFOn_eq_codiscrete (g := g) (U := Set.univ) hg.meromorphicOn
  have hlogEq :
      logDeriv g =ᶠ[Filter.codiscreteWithin (Set.univ : Set ℂ)] logDeriv gNF := by
    -- The same owner change also identifies the unweighted logarithmic derivative.
    simpa [gNF] using logDeriv_toMeromorphicNFOn_eq_codiscrete (U := Set.univ) hg.meromorphicOn
  have hweightedNF_form_cont :
      ContinuousOn (fun z ↦ ((fun w ↦ w * logDeriv gNF w) dz) z)
        (frontier (L.periodParallelogram z₁)) := by
    -- Repackage continuity of the scalar coefficient as continuity of the associated scalar
    -- one-form.
    simpa [Complex.scalarOneForm] using
      (ContinuousLinearMap.smulRightL ℂ ℂ ℂ).continuous₂.comp_continuousOn
        ((continuousOn_const :
            ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℂ] ℂ))
              (frontier (L.periodParallelogram z₁))).prodMk hweightedNF_cont)
  have hlogNF_form_cont :
      ContinuousOn (fun z ↦ ((logDeriv gNF dz) z)) (frontier (L.periodParallelogram z₁)) := by
    -- The same scalar-one-form package applies to the unweighted logarithmic derivative.
    simpa [Complex.scalarOneForm] using
      (ContinuousLinearMap.smulRightL ℂ ℂ ℂ).continuous₂.comp_continuousOn
        ((continuousOn_const :
            ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℂ] ℂ))
              (frontier (L.periodParallelogram z₁))).prodMk hgNF_cont)
  have hbottom_frontier :
      Set.range (Path.segment z0 z1') ⊆ frontier (L.periodParallelogram z₁) := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    have hpoint :
        Path.segment z0 z1' t = z₁ + (t : ℝ) • L.ω₁ + (0 : ℝ) • L.ω₂ := by
      simp [z0, z1', Path.segment_apply, AffineMap.lineMap_apply, add_assoc, add_left_comm,
        add_comm]
    rw [hpoint]
    exact
      mem_frontier_periodParallelogram_of_coord_eq_zero_or_one
        (L := L) (z₀ := z₁) t.2.1 t.2.2 (by norm_num) (by norm_num)
        (Or.inr <| Or.inr <| Or.inl rfl)
  have hright_frontier :
      Set.range (Path.segment z1' z2) ⊆ frontier (L.periodParallelogram z₁) := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    have hpoint :
        Path.segment z1' z2 t = z₁ + (1 : ℝ) • L.ω₁ + (t : ℝ) • L.ω₂ := by
      simp [z1', z2, Path.segment_apply, AffineMap.lineMap_apply, add_assoc, add_left_comm,
        add_comm]
    rw [hpoint]
    exact
      mem_frontier_periodParallelogram_of_coord_eq_zero_or_one
        (L := L) (z₀ := z₁) (by norm_num) (by norm_num) t.2.1 t.2.2
        (Or.inr <| Or.inl rfl)
  have htop_frontier :
      Set.range (Path.segment z2 z3) ⊆ frontier (L.periodParallelogram z₁) := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    have ht0 : 0 ≤ (1 - (t : ℝ)) := by linarith [t.2.2]
    have ht1 : (1 - (t : ℝ)) ≤ 1 := by linarith [t.2.1]
    have hpoint :
        Path.segment z2 z3 t = z₁ + (1 - (t : ℝ)) • L.ω₁ + (1 : ℝ) • L.ω₂ := by
      simp [z2, z3, Path.segment_apply, AffineMap.lineMap_apply, add_assoc, add_left_comm,
        add_comm, sub_eq_add_neg]
      ring
    rw [hpoint]
    exact
      mem_frontier_periodParallelogram_of_coord_eq_zero_or_one
        (L := L) (z₀ := z₁) ht0 ht1 (by norm_num) (by norm_num)
        (Or.inr <| Or.inr <| Or.inr rfl)
  have hleftBase_frontier :
      Set.range (Path.segment z0 z3) ⊆ frontier (L.periodParallelogram z₁) := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    have hpoint :
        Path.segment z0 z3 t = z₁ + (0 : ℝ) • L.ω₁ + (t : ℝ) • L.ω₂ := by
      simp [z0, z3, Path.segment_apply, AffineMap.lineMap_apply, add_assoc, add_left_comm,
        add_comm]
    rw [hpoint]
    exact
      mem_frontier_periodParallelogram_of_coord_eq_zero_or_one
        (L := L) (z₀ := z₁) (by norm_num) (by norm_num) t.2.1 t.2.2
        (Or.inl rfl)
  have hbottomNFInt :
      CurveIntegrable (fun z ↦ ((fun w ↦ w * logDeriv gNF w) dz) z) (Path.segment z0 z1') := by
    -- Continuity of the weighted normal-form integrand on the boundary gives bottom-edge
    -- curve-integrability.
    rw [curveIntegrable_segment]
    have hAlong :
        ContinuousOn
          (fun t : ℝ ↦ ((fun w ↦ w * logDeriv gNF w) dz) (AffineMap.lineMap z0 z1' t))
          (Set.Icc (0 : ℝ) 1) := by
      refine hweightedNF_form_cont.comp (by fun_prop) ?_
      intro t ht
      exact hbottom_frontier ⟨⟨t, ht⟩, by simp [Path.segment_apply]⟩
    have hParam :
        ContinuousOn
          (fun t : ℝ ↦ (((fun w ↦ w * logDeriv gNF w) dz) (AffineMap.lineMap z0 z1' t)) (z1' - z0))
          (Set.Icc (0 : ℝ) 1) := hAlong.clm_apply continuousOn_const
    have hParamU :
        ContinuousOn
          (fun t : ℝ ↦ (((fun w ↦ w * logDeriv gNF w) dz) (AffineMap.lineMap z0 z1' t)) (z1' - z0))
          (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc, zero_le_one] using hParam
    exact hParamU.intervalIntegrable
  have hrightNFInt :
      CurveIntegrable (fun z ↦ ((fun w ↦ w * logDeriv gNF w) dz) z) (Path.segment z1' z2) := by
    -- The same boundary continuity package handles the right edge.
    rw [curveIntegrable_segment]
    have hAlong :
        ContinuousOn
          (fun t : ℝ ↦ ((fun w ↦ w * logDeriv gNF w) dz) (AffineMap.lineMap z1' z2 t))
          (Set.Icc (0 : ℝ) 1) := by
      refine hweightedNF_form_cont.comp (by fun_prop) ?_
      intro t ht
      exact hright_frontier ⟨⟨t, ht⟩, by simp [Path.segment_apply]⟩
    have hParam :
        ContinuousOn
          (fun t : ℝ ↦ (((fun w ↦ w * logDeriv gNF w) dz) (AffineMap.lineMap z1' z2 t)) (z2 - z1'))
          (Set.Icc (0 : ℝ) 1) := hAlong.clm_apply continuousOn_const
    have hParamU :
        ContinuousOn
          (fun t : ℝ ↦ (((fun w ↦ w * logDeriv gNF w) dz) (AffineMap.lineMap z1' z2 t)) (z2 - z1'))
          (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc, zero_le_one] using hParam
    exact hParamU.intervalIntegrable
  have htopNFInt :
      CurveIntegrable (fun z ↦ ((fun w ↦ w * logDeriv gNF w) dz) z) (Path.segment z2 z3) := by
    -- The same boundary continuity package handles the top edge.
    rw [curveIntegrable_segment]
    have hAlong :
        ContinuousOn
          (fun t : ℝ ↦ ((fun w ↦ w * logDeriv gNF w) dz) (AffineMap.lineMap z2 z3 t))
          (Set.Icc (0 : ℝ) 1) := by
      refine hweightedNF_form_cont.comp (by fun_prop) ?_
      intro t ht
      exact htop_frontier ⟨⟨t, ht⟩, by simp [Path.segment_apply]⟩
    have hParam :
        ContinuousOn
          (fun t : ℝ ↦ (((fun w ↦ w * logDeriv gNF w) dz) (AffineMap.lineMap z2 z3 t)) (z3 - z2))
          (Set.Icc (0 : ℝ) 1) := hAlong.clm_apply continuousOn_const
    have hParamU :
        ContinuousOn
          (fun t : ℝ ↦ (((fun w ↦ w * logDeriv gNF w) dz) (AffineMap.lineMap z2 z3 t)) (z3 - z2))
          (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc, zero_le_one] using hParam
    exact hParamU.intervalIntegrable
  have hleftBaseNFInt :
      CurveIntegrable (fun z ↦ ((fun w ↦ w * logDeriv gNF w) dz) z) (Path.segment z0 z3) := by
    -- The same boundary continuity package handles the forward left base edge.
    rw [curveIntegrable_segment]
    have hAlong :
        ContinuousOn
          (fun t : ℝ ↦ ((fun w ↦ w * logDeriv gNF w) dz) (AffineMap.lineMap z0 z3 t))
          (Set.Icc (0 : ℝ) 1) := by
      refine hweightedNF_form_cont.comp (by fun_prop) ?_
      intro t ht
      exact hleftBase_frontier ⟨⟨t, ht⟩, by simp [Path.segment_apply]⟩
    have hParam :
        ContinuousOn
          (fun t : ℝ ↦ (((fun w ↦ w * logDeriv gNF w) dz) (AffineMap.lineMap z0 z3 t)) (z3 - z0))
          (Set.Icc (0 : ℝ) 1) := hAlong.clm_apply continuousOn_const
    have hParamU :
        ContinuousOn
          (fun t : ℝ ↦ (((fun w ↦ w * logDeriv gNF w) dz) (AffineMap.lineMap z0 z3 t)) (z3 - z0))
          (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc, zero_le_one] using hParam
    exact hParamU.intervalIntegrable
  have hbottomLogNFInt :
      CurveIntegrable (fun z ↦ ((logDeriv gNF dz) z)) (Path.segment z0 z1') := by
    -- Unweighted continuity on the frontier gives the bottom logarithmic integrability.
    rw [curveIntegrable_segment]
    have hAlong :
        ContinuousOn (fun t : ℝ ↦ ((logDeriv gNF dz) (AffineMap.lineMap z0 z1' t)))
          (Set.Icc (0 : ℝ) 1) := by
      refine hlogNF_form_cont.comp (by fun_prop) ?_
      intro t ht
      exact hbottom_frontier ⟨⟨t, ht⟩, by simp [Path.segment_apply]⟩
    have hParam :
        ContinuousOn
          (fun t : ℝ ↦ (((logDeriv gNF dz) (AffineMap.lineMap z0 z1' t)) (z1' - z0)))
          (Set.Icc (0 : ℝ) 1) := hAlong.clm_apply continuousOn_const
    have hParamU :
        ContinuousOn
          (fun t : ℝ ↦ (((logDeriv gNF dz) (AffineMap.lineMap z0 z1' t)) (z1' - z0)))
          (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc, zero_le_one] using hParam
    exact hParamU.intervalIntegrable
  have hleftBaseLogNFInt :
      CurveIntegrable (fun z ↦ ((logDeriv gNF dz) z)) (Path.segment z0 z3) := by
    -- The same continuity package handles the forward left logarithmic integral.
    rw [curveIntegrable_segment]
    have hAlong :
        ContinuousOn (fun t : ℝ ↦ ((logDeriv gNF dz) (AffineMap.lineMap z0 z3 t)))
          (Set.Icc (0 : ℝ) 1) := by
      refine hlogNF_form_cont.comp (by fun_prop) ?_
      intro t ht
      exact hleftBase_frontier ⟨⟨t, ht⟩, by simp [Path.segment_apply]⟩
    have hParam :
        ContinuousOn
          (fun t : ℝ ↦ (((logDeriv gNF dz) (AffineMap.lineMap z0 z3 t)) (z3 - z0)))
          (Set.Icc (0 : ℝ) 1) := hAlong.clm_apply continuousOn_const
    have hParamU :
        ContinuousOn
          (fun t : ℝ ↦ (((logDeriv gNF dz) (AffineMap.lineMap z0 z3 t)) (z3 - z0)))
          (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc, zero_le_one] using hParam
    exact hParamU.intervalIntegrable
  have hbottomInt :
      CurveIntegrable (fun z ↦ ((fun w ↦ w * logDeriv g w) dz) z) (Path.segment z0 z1') := by
    -- Transfer weighted integrability back from the normal-form owner along the bottom edge.
    refine
      curveIntegrable_segment_of_codiscreteWithin
        (a := z0) (b := z1') hz0z1 (by intro z hz; simp) hweightedEq hbottomNFInt
  have hrightInt :
      CurveIntegrable (fun z ↦ ((fun w ↦ w * logDeriv g w) dz) z) (Path.segment z1' z2) := by
    -- Transfer weighted integrability back from the normal-form owner along the right edge.
    refine
      curveIntegrable_segment_of_codiscreteWithin
        (a := z1') (b := z2) hz1z2 (by intro z hz; simp) hweightedEq hrightNFInt
  have htopInt :
      CurveIntegrable (fun z ↦ ((fun w ↦ w * logDeriv g w) dz) z) (Path.segment z2 z3) := by
    -- Transfer weighted integrability back from the normal-form owner along the top edge.
    refine
      curveIntegrable_segment_of_codiscreteWithin
        (a := z2) (b := z3) hz2z3 (by intro z hz; simp) hweightedEq htopNFInt
  have hleftBaseInt :
      CurveIntegrable (fun z ↦ ((fun w ↦ w * logDeriv g w) dz) z) (Path.segment z0 z3) := by
    -- Transfer weighted integrability back from the normal-form owner along the forward left
    -- base edge.
    refine
      curveIntegrable_segment_of_codiscreteWithin
        (a := z0) (b := z3) hz0z3 (by intro z hz; simp) hweightedEq hleftBaseNFInt
  have hleftInt :
      CurveIntegrable (fun z ↦ ((fun w ↦ w * logDeriv g w) dz) z) (Path.segment z3 z0) := by
    simpa using hleftBaseInt.symm
  have hbottomLogInt :
      CurveIntegrable (fun z ↦ ((logDeriv g dz) z)) (Path.segment z0 z1') := by
    -- Transfer logarithmic integrability back from the normal-form owner along the bottom edge.
    refine
      curveIntegrable_segment_of_codiscreteWithin
        (a := z0) (b := z1') hz0z1 (by intro z hz; simp) hlogEq hbottomLogNFInt
  have hleftBaseLogInt :
      CurveIntegrable (fun z ↦ ((logDeriv g dz) z)) (Path.segment z0 z3) := by
    -- Transfer logarithmic integrability back from the normal-form owner along the forward left
    -- base edge.
    refine
      curveIntegrable_segment_of_codiscreteWithin
        (a := z0) (b := z3) hz0z3 (by intro z hz; simp) hlogEq hleftBaseLogNFInt
  have hz0_frontier : z0 ∈ frontier (L.periodParallelogram z₁) := by
    exact hbottom_frontier ⟨0, by simp [z0, z1']⟩
  have hz1_frontier : z1' ∈ frontier (L.periodParallelogram z₁) := by
    exact hbottom_frontier ⟨1, by simp [z0, z1']⟩
  have hz3_frontier : z3 ∈ frontier (L.periodParallelogram z₁) := by
    exact hleftBase_frontier ⟨1, by simp [z0, z3]⟩
  have hnonzeroOwner_open : IsOpen nonzeroOwner := by
    -- Route correction: use the normal-form nonzero locus as the open owner on which the
    -- segment image path lives, instead of rebuilding a boundary collar.
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have horder : meromorphicOrderAt gNF z = 0 :=
      (hgNF (by simp)).meromorphicOrderAt_eq_zero_iff.2 hz
    have hanalytic : AnalyticAt ℂ gNF z :=
      analyticAt_of_meromorphicOrderAt_eq_zero (hgNF (by simp)) horder
    have hnonzero_nhds : {w : ℂ | w ≠ 0} ∈ 𝓝 (gNF z) := by
      exact isClosed_singleton.isOpen_compl.mem_nhds hz
    simpa [nonzeroOwner] using
      hanalytic.continuousAt.preimage_mem_nhds hnonzero_nhds
  have hnonzeroOwner_diff : DifferentiableOn ℂ gNF nonzeroOwner := by
    intro z hz
    -- On the normal-form nonzero locus, the owner is analytic and therefore differentiable.
    have horder : meromorphicOrderAt gNF z = 0 :=
      (hgNF (by simp)).meromorphicOrderAt_eq_zero_iff.2 hz
    exact
      (analyticAt_of_meromorphicOrderAt_eq_zero
        (hgNF (by simp)) horder).differentiableAt.differentiableWithinAt
  have hbottom_nonzero_range : Set.range (Path.segment z0 z1') ⊆ nonzeroOwner := by
    intro z hz
    -- Every point on the bottom edge has frontier order zero, so the normal-form owner is
    -- nonzero there.
    have hz_frontier : z ∈ frontier (L.periodParallelogram z₁) := hbottom_frontier hz
    simpa [gNF, nonzeroOwner] using
      toMeromorphicNFOn_nonzero_of_meromorphicOrderAt_eq_zero
        (g := g) (U := Set.univ) isOpen_univ hg.meromorphicOn
        (hz := by simp) (hboundary z hz_frontier)
  have hleft_nonzero_range : Set.range (Path.segment z0 z3) ⊆ nonzeroOwner := by
    intro z hz
    -- Every point on the left base edge has frontier order zero, so the normal-form owner is
    -- nonzero there.
    have hz_frontier : z ∈ frontier (L.periodParallelogram z₁) := hleftBase_frontier hz
    simpa [gNF, nonzeroOwner] using
      toMeromorphicNFOn_nonzero_of_meromorphicOrderAt_eq_zero
        (g := g) (U := Set.univ) isOpen_univ hg.meromorphicOn
        (hz := by simp) (hboundary z hz_frontier)
  have hbottom_endpoint :
      gNF z1' = gNF z0 := by
    -- The global normal-form owner takes equal values at endpoints differing by the period `ω₁`.
    simpa [gNF, z0, z1', add_assoc, add_left_comm, add_comm] using
      toMeromorphicNFOn_period_eq_of_meromorphicOrderAt_eq_zero
        (g := g) (U := Set.univ) isOpen_univ hg.meromorphicOn
        (z := z0) (ω := L.ω₁) (hz := by simp) (hzω := by simp [z0, z1'])
        (hperiodic := hperiods L.ω₁ L.ω₁_mem_lattice) (hboundary z0 hz0_frontier)
  have hleft_endpoint :
      gNF z3 = gNF z0 := by
    -- The global normal-form owner takes equal values at endpoints differing by the period `ω₂`.
    simpa [gNF, z0, z3, add_assoc, add_left_comm, add_comm] using
      toMeromorphicNFOn_period_eq_of_meromorphicOrderAt_eq_zero
        (g := g) (U := Set.univ) isOpen_univ hg.meromorphicOn
        (z := z0) (ω := L.ω₂) (hz := by simp) (hzω := by simp [z0, z3])
        (hperiodic := hperiods L.ω₂ L.ω₂_mem_lattice) (hboundary z0 hz0_frontier)
  have hbottom_nonzero_path : ∀ t : I, gNF (Path.segment z0 z1' t) ≠ 0 := by
    intro t
    exact hbottom_nonzero_range ⟨t, rfl⟩
  have hleft_nonzero_path : ∀ t : I, gNF (Path.segment z0 z3 t) ≠ 0 := by
    intro t
    exact hleft_nonzero_range ⟨t, rfl⟩
  have hbottomLogInt_eq_int :
      ∃ n : ℤ,
        (∫ᶜ z in Path.segment z0 z1', ((logDeriv g dz) z)) /
            (2 * Real.pi * Complex.I : ℂ) = (n : ℂ) := by
    have hbottomLogEq :
        ∫ᶜ z in Path.segment z0 z1', ((logDeriv g dz) z) =
          ∫ᶜ z in Path.segment z0 z1', ((logDeriv gNF dz) z) := by
      exact
        curveIntegral_segment_eq_of_codiscreteWithin
          (a := z0) (b := z1') hz0z1 hlogEq (by intro z hz; simp)
    rcases
        segmentLogDerivIntegral_divTwoPiI_eq_int_of_endpoint_eq
          (h := gNF) (a := z0) (b := z1') (U := nonzeroOwner)
          hnonzeroOwner_open hbottom_nonzero_range hnonzeroOwner_diff hbottom_endpoint
          hbottom_nonzero_path with
      ⟨n, hn⟩
    refine ⟨n, ?_⟩
    calc
      (∫ᶜ z in Path.segment z0 z1', ((logDeriv g dz) z)) /
          (2 * Real.pi * Complex.I : ℂ) =
        (∫ᶜ z in Path.segment z0 z1', ((logDeriv gNF dz) z)) /
            (2 * Real.pi * Complex.I : ℂ) := by rw [hbottomLogEq]
      _ = (n : ℂ) := hn
  have hleftLogInt_eq_int :
      ∃ n : ℤ,
        (∫ᶜ z in Path.segment z0 z3, ((logDeriv g dz) z)) /
            (2 * Real.pi * Complex.I : ℂ) = (n : ℂ) := by
    have hleftLogEq :
        ∫ᶜ z in Path.segment z0 z3, ((logDeriv g dz) z) =
          ∫ᶜ z in Path.segment z0 z3, ((logDeriv gNF dz) z) := by
      exact
        curveIntegral_segment_eq_of_codiscreteWithin
          (a := z0) (b := z3) hz0z3 hlogEq (by intro z hz; simp)
    rcases
        segmentLogDerivIntegral_divTwoPiI_eq_int_of_endpoint_eq
          (h := gNF) (a := z0) (b := z3) (U := nonzeroOwner)
          hnonzeroOwner_open hleft_nonzero_range hnonzeroOwner_diff hleft_endpoint
          hleft_nonzero_path with
      ⟨n, hn⟩
    refine ⟨n, ?_⟩
    calc
      (∫ᶜ z in Path.segment z0 z3, ((logDeriv g dz) z)) /
          (2 * Real.pi * Complex.I : ℂ) =
        (∫ᶜ z in Path.segment z0 z3, ((logDeriv gNF dz) z)) /
            (2 * Real.pi * Complex.I : ℂ) := by rw [hleftLogEq]
      _ = (n : ℂ) := hn
  have hbottomCorrection_zero :
      ((((L.ω₂ * (∫ᶜ z in Path.segment z0 z1', ((logDeriv g dz) z)) /
            (2 * Real.pi * Complex.I : ℂ) : ℂ) : ℂ) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) = 0 := by
    -- The bottom correction term is a lattice period times an integer.
    simpa [div_eq_mul_inv, mul_assoc] using
      periodSegmentCorrection_eq_zero_mod_periodLattice
        (L := L) (ω := L.ω₂)
        (J := ∫ᶜ z in Path.segment z0 z1', ((logDeriv g dz) z))
        L.ω₂_mem_lattice hbottomLogInt_eq_int
  have hleftCorrection_zero :
      ((((L.ω₁ * (∫ᶜ z in Path.segment z0 z3, ((logDeriv g dz) z)) /
            (2 * Real.pi * Complex.I : ℂ) : ℂ) : ℂ) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) = 0 := by
    -- The left correction term is a lattice period times an integer.
    simpa [div_eq_mul_inv, mul_assoc] using
      periodSegmentCorrection_eq_zero_mod_periodLattice
        (L := L) (ω := L.ω₁)
        (J := ∫ᶜ z in Path.segment z0 z3, ((logDeriv g dz) z))
        L.ω₁_mem_lattice hleftLogInt_eq_int
  have hleft_symm :
      ∫ᶜ z in Path.segment z3 z0, ((fun w ↦ w * logDeriv g w) dz) z =
        -∫ᶜ z in Path.segment z0 z3, ((fun w ↦ w * logDeriv g w) dz) z := by
    -- Reversing the left edge flips the sign of its weighted integral.
    simpa using
      curveIntegral_symm
        (ω := fun z ↦ ((fun w ↦ w * logDeriv g w) dz) z) (γ := Path.segment z0 z3)
  have hbottomLog_symm :
      ∫ᶜ z in Path.segment z1' z0, ((logDeriv g dz) z) =
        -∫ᶜ z in Path.segment z0 z1', ((logDeriv g dz) z) := by
    -- Reversing the bottom edge flips the sign of the unweighted logarithmic integral.
    simpa using curveIntegral_symm (ω := fun z ↦ ((logDeriv g dz) z)) (γ := Path.segment z0 z1')
  have hbottomWeighted_symm :
      ∫ᶜ z in Path.segment z1' z0, ((fun w ↦ w * logDeriv g w) dz) z =
        -∫ᶜ z in Path.segment z0 z1', ((fun w ↦ w * logDeriv g w) dz) z := by
    -- Reversing the bottom edge flips the sign of its weighted integral.
    simpa using
      curveIntegral_symm
        (ω := fun z ↦ ((fun w ↦ w * logDeriv g w) dz) z) (γ := Path.segment z0 z1')
  have hboundary_four_segments :
      ∫ᶜ z in (periodParallelogramBoundaryPath (L := L) z₁).toClosedPath.toPath,
          ((fun w ↦ w * logDeriv g w) dz) z =
        ∫ᶜ z in Path.segment z0 z1', ((fun w ↦ w * logDeriv g w) dz) z +
          ∫ᶜ z in Path.segment z1' z2, ((fun w ↦ w * logDeriv g w) dz) z +
            ∫ᶜ z in Path.segment z2 z3, ((fun w ↦ w * logDeriv g w) dz) z +
              ∫ᶜ z in Path.segment z3 z0, ((fun w ↦ w * logDeriv g w) dz) z := by
    -- Route correction: expand the loop first, before pairing translated opposite edges.
    calc
      ∫ᶜ z in (periodParallelogramBoundaryPath (L := L) z₁).toClosedPath.toPath,
          ((fun w ↦ w * logDeriv g w) dz) z =
        ∫ᶜ z in periodParallelogramBoundaryPath (L := L) z₁,
          ((fun w ↦ w * logDeriv g w) dz) z := by
            rw [loopToClosedPathToPathEqCast]
            simp [curveIntegral_cast]
      _ =
          ∫ᶜ z in Path.segment z0 z1', ((fun w ↦ w * logDeriv g w) dz) z +
            ∫ᶜ z in Path.segment z1' z2, ((fun w ↦ w * logDeriv g w) dz) z +
              ∫ᶜ z in Path.segment z2 z3, ((fun w ↦ w * logDeriv g w) dz) z +
                ∫ᶜ z in Path.segment z3 z0, ((fun w ↦ w * logDeriv g w) dz) z := by
            rw [periodParallelogramBoundaryPath,
              curveIntegral_trans hbottomInt
                (CurveIntegrable.trans hrightInt (CurveIntegrable.trans htopInt hleftInt))]
            rw [curveIntegral_trans hrightInt (CurveIntegrable.trans htopInt hleftInt)]
            rw [curveIntegral_trans htopInt hleftInt]
            ring
  have hright_eq :
      ∫ᶜ z in Path.segment z1' z2, ((fun w ↦ w * logDeriv g w) dz) z =
        ∫ᶜ z in Path.segment z0 z3, ((fun w ↦ w * logDeriv g w) dz) z +
          L.ω₁ * ∫ᶜ z in Path.segment z0 z3, ((logDeriv g dz) z) := by
    have htranslate :
      ∫ᶜ z in Path.segment z1' z2, ((fun w ↦ w * logDeriv g w) dz) z =
          ∫ᶜ z in Path.segment z0 z3,
            (((fun w ↦ (w + L.ω₁) * logDeriv g (w + L.ω₁)) dz) z) := by
      -- Translate the right edge back to the forward left base segment.
      rw [curveIntegral_segment, curveIntegral_segment]
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro t _
      have hline :
          AffineMap.lineMap z1' z2 t = AffineMap.lineMap z0 z3 t + L.ω₁ := by
        simp [z0, z1', z2, z3, AffineMap.lineMap_apply, add_assoc, add_left_comm, add_comm]
      have hdir : z2 - z1' = z3 - z0 := by
        simp [z0, z1', z2, z3, add_assoc, add_left_comm, add_comm]
      simp [Complex.scalarOneForm_apply, hline, hdir]
    have hlogSmulInt :
        CurveIntegrable (fun z ↦ ((fun w ↦ L.ω₁ * logDeriv g w) dz) z) (Path.segment z0 z3) := by
      -- The correction integrand is a constant multiple of the left-base logarithmic integrand.
      have hsmul_form :
          (fun z ↦ ((fun w ↦ L.ω₁ * logDeriv g w) dz) z) =
            L.ω₁ • (fun z ↦ ((logDeriv g dz) z)) := by
        funext z
        ext v
        simp [Complex.scalarOneForm_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
      rw [hsmul_form]
      exact CurveIntegrable.smul (c := L.ω₁) hleftBaseLogInt
    have hsum_form :
        (fun z ↦ (((fun w ↦ (w + L.ω₁) * logDeriv g (w + L.ω₁)) dz) z)) =
          (fun z ↦ ((fun w ↦ w * logDeriv g w + L.ω₁ * logDeriv g w) dz) z) := by
      funext z
      ext v
      simp [Complex.scalarOneForm_apply]
      rw [weighted_logDeriv_add_period_eq
        (L := L) (g := g) hperiods (ω := L.ω₁) (z := z) L.ω₁_mem_lattice]
    have hadd_form :
        (fun z ↦ ((fun w ↦ w * logDeriv g w + L.ω₁ * logDeriv g w) dz) z) =
          (fun z ↦ ((fun w ↦ w * logDeriv g w) dz) z) +
            (fun z ↦ ((fun w ↦ L.ω₁ * logDeriv g w) dz) z) := by
      funext z
      ext v
      simp [Complex.scalarOneForm_apply, add_mul]
    have hsmul_form :
        (fun z ↦ ((fun w ↦ L.ω₁ * logDeriv g w) dz) z) =
          L.ω₁ • (fun z ↦ ((logDeriv g dz) z)) := by
      funext z
      ext v
      simp [Complex.scalarOneForm_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
    calc
      ∫ᶜ z in Path.segment z1' z2, ((fun w ↦ w * logDeriv g w) dz) z =
          ∫ᶜ z in Path.segment z0 z3,
            (((fun w ↦ (w + L.ω₁) * logDeriv g (w + L.ω₁)) dz) z) := htranslate
      _ =
          ∫ᶜ z in Path.segment z0 z3,
            (((fun w ↦ w * logDeriv g w + L.ω₁ * logDeriv g w) dz) z) := by
              rw [hsum_form]
      _ =
          ∫ᶜ z in Path.segment z0 z3, ((fun w ↦ w * logDeriv g w) dz) z +
            ∫ᶜ z in Path.segment z0 z3, ((fun w ↦ L.ω₁ * logDeriv g w) dz) z := by
              rw [hadd_form, curveIntegral_add hleftBaseInt hlogSmulInt]
      _ =
          ∫ᶜ z in Path.segment z0 z3, ((fun w ↦ w * logDeriv g w) dz) z +
            L.ω₁ * ∫ᶜ z in Path.segment z0 z3, ((logDeriv g dz) z) := by
              rw [hsmul_form, curveIntegral_smul]
              rfl
  have htop_eq :
      ∫ᶜ z in Path.segment z2 z3, ((fun w ↦ w * logDeriv g w) dz) z =
        -∫ᶜ z in Path.segment z0 z1', ((fun w ↦ w * logDeriv g w) dz) z -
          L.ω₂ * ∫ᶜ z in Path.segment z0 z1', ((logDeriv g dz) z) := by
    have htranslate :
      ∫ᶜ z in Path.segment z2 z3, ((fun w ↦ w * logDeriv g w) dz) z =
          ∫ᶜ z in Path.segment z1' z0,
            (((fun w ↦ (w + L.ω₂) * logDeriv g (w + L.ω₂)) dz) z) := by
      -- Translate the top edge back to the reversed bottom edge.
      rw [curveIntegral_segment, curveIntegral_segment]
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro t _
      have hline :
          AffineMap.lineMap z2 z3 t = AffineMap.lineMap z1' z0 t + L.ω₂ := by
        simp [z0, z1', z2, z3, AffineMap.lineMap_apply, add_assoc, add_left_comm, add_comm]
      have hdir : z3 - z2 = z0 - z1' := by
        simp [z0, z1', z2, z3, add_assoc, add_left_comm, add_comm]
      simp [Complex.scalarOneForm_apply, hline, hdir]
    have hlogSmulInt :
        CurveIntegrable (fun z ↦ ((fun w ↦ L.ω₂ * logDeriv g w) dz) z) (Path.segment z1' z0) := by
      -- The correction integrand is a constant multiple of the reversed bottom logarithmic
      -- integrand.
      have hbottomLogInt_symm :
          CurveIntegrable (fun z ↦ ((logDeriv g dz) z)) (Path.segment z1' z0) := by
        simpa using hbottomLogInt.symm
      have hsmul_form :
          (fun z ↦ ((fun w ↦ L.ω₂ * logDeriv g w) dz) z) =
            L.ω₂ • (fun z ↦ ((logDeriv g dz) z)) := by
        funext z
        ext v
        simp [Complex.scalarOneForm_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
      rw [hsmul_form]
      exact CurveIntegrable.smul (c := L.ω₂) hbottomLogInt_symm
    have hbottomInt_symm :
        CurveIntegrable (fun z ↦ ((fun w ↦ w * logDeriv g w) dz) z) (Path.segment z1' z0) := by
      simpa using hbottomInt.symm
    have hsum_form :
        (fun z ↦ (((fun w ↦ (w + L.ω₂) * logDeriv g (w + L.ω₂)) dz) z)) =
          (fun z ↦ ((fun w ↦ w * logDeriv g w + L.ω₂ * logDeriv g w) dz) z) := by
      funext z
      ext v
      simp [Complex.scalarOneForm_apply]
      rw [weighted_logDeriv_add_period_eq
        (L := L) (g := g) hperiods (ω := L.ω₂) (z := z) L.ω₂_mem_lattice]
    have hadd_form :
        (fun z ↦ ((fun w ↦ w * logDeriv g w + L.ω₂ * logDeriv g w) dz) z) =
          (fun z ↦ ((fun w ↦ w * logDeriv g w) dz) z) +
            (fun z ↦ ((fun w ↦ L.ω₂ * logDeriv g w) dz) z) := by
      funext z
      ext v
      simp [Complex.scalarOneForm_apply, add_mul]
    have hsmul_form :
        (fun z ↦ ((fun w ↦ L.ω₂ * logDeriv g w) dz) z) =
          L.ω₂ • (fun z ↦ ((logDeriv g dz) z)) := by
      funext z
      ext v
      simp [Complex.scalarOneForm_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
    calc
      ∫ᶜ z in Path.segment z2 z3, ((fun w ↦ w * logDeriv g w) dz) z =
          ∫ᶜ z in Path.segment z1' z0,
            (((fun w ↦ (w + L.ω₂) * logDeriv g (w + L.ω₂)) dz) z) := htranslate
      _ =
          ∫ᶜ z in Path.segment z1' z0,
            (((fun w ↦ w * logDeriv g w + L.ω₂ * logDeriv g w) dz) z) := by
              rw [hsum_form]
      _ =
          ∫ᶜ z in Path.segment z1' z0, ((fun w ↦ w * logDeriv g w) dz) z +
            ∫ᶜ z in Path.segment z1' z0, ((fun w ↦ L.ω₂ * logDeriv g w) dz) z := by
              rw [hadd_form, curveIntegral_add hbottomInt_symm hlogSmulInt]
      _ =
          ∫ᶜ z in Path.segment z1' z0, ((fun w ↦ w * logDeriv g w) dz) z +
            L.ω₂ * ∫ᶜ z in Path.segment z1' z0, ((logDeriv g dz) z) := by
              rw [hsmul_form, curveIntegral_smul]
              rfl
      _ =
          -∫ᶜ z in Path.segment z0 z1', ((fun w ↦ w * logDeriv g w) dz) z -
            L.ω₂ * ∫ᶜ z in Path.segment z0 z1', ((logDeriv g dz) z) := by
              rw [hbottomWeighted_symm, hbottomLog_symm]
              ring
  have hboundary_corrections :
      ∫ᶜ z in (periodParallelogramBoundaryPath (L := L) z₁).toClosedPath.toPath,
          ((fun w ↦ w * logDeriv g w) dz) z =
        L.ω₁ * ∫ᶜ z in Path.segment z0 z3, ((logDeriv g dz) z) -
          L.ω₂ * ∫ᶜ z in Path.segment z0 z1', ((logDeriv g dz) z) := by
    -- Substitute the opposite-edge rewrites into the four-segment expansion and cancel the
    -- weighted left and bottom terms.
    calc
      ∫ᶜ z in (periodParallelogramBoundaryPath (L := L) z₁).toClosedPath.toPath,
          ((fun w ↦ w * logDeriv g w) dz) z =
        ∫ᶜ z in Path.segment z0 z1', ((fun w ↦ w * logDeriv g w) dz) z +
          ∫ᶜ z in Path.segment z1' z2, ((fun w ↦ w * logDeriv g w) dz) z +
            ∫ᶜ z in Path.segment z2 z3, ((fun w ↦ w * logDeriv g w) dz) z +
              ∫ᶜ z in Path.segment z3 z0, ((fun w ↦ w * logDeriv g w) dz) z :=
            hboundary_four_segments
      _ =
          ∫ᶜ z in Path.segment z0 z1', ((fun w ↦ w * logDeriv g w) dz) z +
            (∫ᶜ z in Path.segment z0 z3, ((fun w ↦ w * logDeriv g w) dz) z +
                L.ω₁ * ∫ᶜ z in Path.segment z0 z3, ((logDeriv g dz) z)) +
              (-∫ᶜ z in Path.segment z0 z1', ((fun w ↦ w * logDeriv g w) dz) z -
                  L.ω₂ * ∫ᶜ z in Path.segment z0 z1', ((logDeriv g dz) z)) +
                ∫ᶜ z in Path.segment z3 z0, ((fun w ↦ w * logDeriv g w) dz) z := by
              rw [hright_eq, htop_eq]
      _ =
          ∫ᶜ z in Path.segment z0 z1', ((fun w ↦ w * logDeriv g w) dz) z +
            (∫ᶜ z in Path.segment z0 z3, ((fun w ↦ w * logDeriv g w) dz) z +
                L.ω₁ * ∫ᶜ z in Path.segment z0 z3, ((logDeriv g dz) z)) +
              (-∫ᶜ z in Path.segment z0 z1', ((fun w ↦ w * logDeriv g w) dz) z -
                  L.ω₂ * ∫ᶜ z in Path.segment z0 z1', ((logDeriv g dz) z)) +
                (-∫ᶜ z in Path.segment z0 z3, ((fun w ↦ w * logDeriv g w) dz) z) := by
              rw [hleft_symm]
      _ =
          L.ω₁ * ∫ᶜ z in Path.segment z0 z3, ((logDeriv g dz) z) -
            L.ω₂ * ∫ᶜ z in Path.segment z0 z1', ((logDeriv g dz) z) := by
              ring
  have hboundary_sum_singleton :
      ∑ i : Unit,
          ∫ᶜ z in ((fun _ : Unit ↦
            (periodParallelogramBoundaryPath (L := L) z₁).toClosedPath) i).toPath,
            ((fun w ↦ w * logDeriv g w) dz) z =
        ∫ᶜ z in (periodParallelogramBoundaryPath (L := L) z₁).toClosedPath.toPath,
          ((fun w ↦ w * logDeriv g w) dz) z := by
    simp
  -- Divide by `2π i`, pass to the period quotient, and kill the two remaining correction terms.
  calc
    ((((∑ i : Unit,
            ∫ᶜ z in ((fun _ : Unit ↦
              (periodParallelogramBoundaryPath (L := L) z₁).toClosedPath) i).toPath,
              ((fun w ↦ w * logDeriv g w) dz) z) /
          (2 * Real.pi * Complex.I : ℂ)) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) =
      ((((L.ω₁ * ∫ᶜ z in Path.segment z0 z3, ((logDeriv g dz) z) -
            L.ω₂ * ∫ᶜ z in Path.segment z0 z1', ((logDeriv g dz) z)) /
          (2 * Real.pi * Complex.I : ℂ)) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := by
          rw [hboundary_sum_singleton, hboundary_corrections]
    _ =
        ((((L.ω₁ * ∫ᶜ z in Path.segment z0 z3, ((logDeriv g dz) z)) /
              (2 * Real.pi * Complex.I : ℂ) : ℂ) : ℂ) :
          ℂ ⧸ L.lattice.toAddSubgroup) -
          ((((L.ω₂ * ∫ᶜ z in Path.segment z0 z1', ((logDeriv g dz) z)) /
                (2 * Real.pi * Complex.I : ℂ) : ℂ) : ℂ) :
            ℂ ⧸ L.lattice.toAddSubgroup) := by
              simp [sub_eq_add_neg, div_eq_mul_inv, mul_add, add_mul, mul_assoc, mul_left_comm,
                mul_comm]
    _ = 0 := by
      rw [hleftCorrection_zero, hbottomCorrection_zero, sub_self]

/-- Helper for Proposition 5.2: on a boundary-generic translated period parallelogram, the source
four-edge contour computation yields the weighted divisor identity modulo the period lattice. -/
lemma weighted_divisor_sum_mod_period_lattice_eq_zero_of_boundary_generic_translate
    {g : ℂ → ℂ} {z₀ z₁ : ℂ}
    (hg : Meromorphic g)
    (hperiods : HasPeriodLattice L g)
    (hP : P ⊆ L.periodParallelogram z₀)
    (hπ : Set.BijOn ((↑) : ℂ → ℂ ⧸ L.lattice.toAddSubgroup) P Set.univ)
    (roots poles : Finset ℂ)
    (hroots : IsZeroRepresentativeSet g P roots)
    (hpoles : IsPoleRepresentativeSet g P poles)
    (hboundary : ∀ z ∈ frontier (L.periodParallelogram z₁),
      meromorphicOrderAt g z = (0 : WithTop ℤ)) :
    (((roots.sum fun z ↦ divisor g P z • z) : ℂ) :
      ℂ ⧸ L.lattice.toAddSubgroup) =
      (((poles.sum fun z ↦ (-divisor g P z) • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := by
  let Q : Set ℂ := L.periodParallelogram z₁
  let Γ : Unit → ClosedPath ℂ := fun _ ↦ (periodParallelogramBoundaryPath (L := L) z₁).toClosedPath
  have hΓ : IsOrientedBoundaryOf Q Γ := by
    -- The explicit translated four-edge loop already provides the oriented boundary owner.
    simpa [Q, Γ] using periodParallelogramBoundary_isOrientedBoundaryOf (L := L) z₁
  have hboundary_divisor_zero :
      ∀ z ∈ frontier Q, MeromorphicOn.divisor g Q z = 0 := by
    intro z hz
    -- Boundary order zero rewrites directly to divisor zero on the compact owner `Q`.
    simpa [Q] using
      divisor_eq_zero_on_frontier_of_boundary_order_zero
        (L := L) (g := g) z₁ hg hboundary hz
  have hQ_compact : IsCompact Q := by
    -- Compactness of the translated period cell is already available from the affine model.
    simpa [Q] using isCompact_periodParallelogram (L := L) z₁
  have hsupport_finite :
      (MeromorphicOn.divisor g Q).support.Finite :=
    divisor_support_finite_of_isCompact (K := Q) (g := g) hQ_compact
  let s : Finset ℂ := hsupport_finite.toFinset
  have hs : ∀ z, z ∈ s ↔ z ∈ (MeromorphicOn.divisor g Q).support := by
    intro z
    -- The compact-owner support finset is fixed once and for all for the residue computation.
    simpa [s] using (Set.Finite.mem_toFinset hsupport_finite)
  have hweighted_support :
      ((((∑ i : Unit,
            ∫ᶜ z in (Γ i).toPath, ((fun w ↦ w * logDeriv g w) dz) z) /
              (2 * Real.pi * Complex.I : ℂ)) : ℂ) :
          ℂ ⧸ L.lattice.toAddSubgroup) =
        (((roots.sum fun z ↦ divisor g P z • z) : ℂ) :
            ℂ ⧸ L.lattice.toAddSubgroup) -
          (((poles.sum fun z ↦ (-divisor g P z) • z) : ℂ) :
            ℂ ⧸ L.lattice.toAddSubgroup) := by
    have hweighted :
        (∑ i : Unit, ∫ᶜ z in (Γ i).toPath, ((fun w ↦ w * logDeriv g w) dz) z) /
            (2 * Real.pi * Complex.I : ℂ) =
          Finset.sum s (fun z ↦ (MeromorphicOn.divisor g Q z : ℂ) * z) := by
      -- The weighted residue theorem rewrites the normalized boundary integral as the compact-owner
      -- divisor-weighted support sum.
      simpa [Q, Γ, s] using
        (weightedBoundaryIntegralDivTwoPiI_eq_supportWeightedDivisorSum
          (L := L) (g := g) (z₁ := z₁) hg hboundary)
    have hsupport_transport :
        (((s.sum fun z ↦ ((MeromorphicOn.divisor g Q z : ℂ) * z)) : ℂ) :
            ℂ ⧸ L.lattice.toAddSubgroup) =
          (((roots.sum fun z ↦ divisor g P z • z) : ℂ) :
              ℂ ⧸ L.lattice.toAddSubgroup) -
            (((poles.sum fun z ↦ (-divisor g P z) • z) : ℂ) :
              ℂ ⧸ L.lattice.toAddSubgroup) := by
      -- The compact-owner support sum is already identified with the chosen root and pole
      -- representatives on `P`.
      simpa [Q, s] using
        (supportWeightedDivisorSum_eq_rootPoleSums_mod_periodLattice
          (L := L) (P := P) (g := g) (z₁ := z₁) hg hperiods hπ
          roots poles hroots hpoles s hs hboundary)
    -- Route correction: the residue package and the support transport now close in the quotient.
    calc
      ((((∑ i : Unit,
              ∫ᶜ z in (Γ i).toPath, ((fun w ↦ w * logDeriv g w) dz) z) /
                (2 * Real.pi * Complex.I : ℂ)) : ℂ) :
            ℂ ⧸ L.lattice.toAddSubgroup) =
          (((s.sum fun z ↦ ((MeromorphicOn.divisor g Q z : ℂ) * z)) : ℂ) :
            ℂ ⧸ L.lattice.toAddSubgroup) := by
              exact congrArg (fun w : ℂ ↦ ((w : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) hweighted
      _ =
          (((roots.sum fun z ↦ divisor g P z • z) : ℂ) :
              ℂ ⧸ L.lattice.toAddSubgroup) -
            (((poles.sum fun z ↦ (-divisor g P z) • z) : ℂ) :
              ℂ ⧸ L.lattice.toAddSubgroup) := hsupport_transport
  have hboundary_zero :
      ((((∑ i : Unit,
              ∫ᶜ z in (Γ i).toPath, ((fun w ↦ w * logDeriv g w) dz) z) /
            (2 * Real.pi * Complex.I : ℂ)) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) = 0 := by
    -- The weighted four-edge contour reduces to two lattice correction terms, both trivial mod `L`.
    simpa [Γ] using
      weightedBoundaryIntegralDivTwoPiI_eq_zero_mod_periodLattice
        (L := L) (g := g) (z₁ := z₁) hg hperiods hboundary
  -- Combine the vanishing boundary class with the already packaged residue/support transport.
  have hdiff_zero :
      (((roots.sum fun z ↦ divisor g P z • z) : ℂ) :
          ℂ ⧸ L.lattice.toAddSubgroup) -
        (((poles.sum fun z ↦ (-divisor g P z) • z) : ℂ) :
          ℂ ⧸ L.lattice.toAddSubgroup) = 0 := by
    calc
      (((roots.sum fun z ↦ divisor g P z • z) : ℂ) :
          ℂ ⧸ L.lattice.toAddSubgroup) -
        (((poles.sum fun z ↦ (-divisor g P z) • z) : ℂ) :
          ℂ ⧸ L.lattice.toAddSubgroup) =
          ((((∑ i : Unit,
                  ∫ᶜ z in (Γ i).toPath, ((fun w ↦ w * logDeriv g w) dz) z) /
                (2 * Real.pi * Complex.I : ℂ)) : ℂ) :
            ℂ ⧸ L.lattice.toAddSubgroup) := by
              symm
              exact hweighted_support
      _ = 0 := hboundary_zero
  exact sub_eq_zero.mp hdiff_zero

/-- Helper for Proposition 5.2: the core Abel relation for a periodic meromorphic function `g`
identified on one full set of representatives `P` for the quotient by the period lattice. -/
lemma sum_divisor_weighted_mod_period_lattice_eq_zero
    {g : ℂ → ℂ} {z₀ : ℂ}
    (hg : Meromorphic g)
    (hperiods : HasPeriodLattice L g)
    (hP : P ⊆ L.periodParallelogram z₀)
    (hπ : Set.BijOn ((↑) : ℂ → ℂ ⧸ L.lattice.toAddSubgroup) P Set.univ)
    (roots poles : Finset ℂ)
    (hroots : IsZeroRepresentativeSet g P roots)
    (hpoles : IsPoleRepresentativeSet g P poles) :
    (((roots.sum fun z ↦ divisor g P z • z) : ℂ) :
      ℂ ⧸ L.lattice.toAddSubgroup) =
      (((poles.sum fun z ↦ (-divisor g P z) • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := by
  by_cases htop : ∃ z, meromorphicOrderAt g z = ⊤
  · -- In the globally degenerate branch, connectedness forces every divisor value to vanish.
    exact periodic_meromorphic_order_top_trivializes_weighted_divisor_sum
      (L := L) (P := P) hg roots poles hroots hpoles htop
  · have hfinite : ∀ z, meromorphicOrderAt g z ≠ ⊤ := by
      intro z hz
      exact htop ⟨z, hz⟩
    obtain ⟨z₁, hboundary⟩ :=
      exists_boundary_regular_translate_for_finite_order_support
        (L := L) (P := P) hg hperiods hfinite hP hπ roots poles hroots hpoles
    -- Route correction: after removing the `⊤` branch, the remaining source-faithful proof is the
    -- translated boundary-generic contour computation.
    exact weighted_divisor_sum_mod_period_lattice_eq_zero_of_boundary_generic_translate
      (L := L) (P := P) (z₀ := z₀) (z₁ := z₁) hg hperiods hP hπ roots poles hroots hpoles
        hboundary

