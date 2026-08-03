module

public import Topology_Munkres_2000.Book.Theorem_63_6.JordanCrosscut
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Topology.Algebra.Affine
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Homeomorph.Lemmas

public section

open Set

/-- Helper for Remark 65.1: the frontier of a component of the complement of
a closed set lies in that closed set. -/
lemma frontier_connectedComponentIn_compl_subset_closed
    {E : Type*} [TopologicalSpace E] [LocallyConnectedSpace E]
    (C : Set E) (hCclosed : IsClosed C) (x : E) :
    frontier (connectedComponentIn Cᶜ x) ⊆ C := by
  let U : Set E := connectedComponentIn Cᶜ x
  have hUopen : IsOpen U := hCclosed.isOpen_compl.connectedComponentIn
  have hUunionCClosed : IsClosed (U ∪ C) := by
    rw [← isOpen_compl_iff]
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    have hyC : y ∈ Cᶜ := by
      intro hyC
      exact hy (Or.inr hyC)
    let V : Set E := connectedComponentIn Cᶜ y
    have hVopen : IsOpen V := hCclosed.isOpen_compl.connectedComponentIn
    have hyV : y ∈ V := mem_connectedComponentIn hyC
    apply Filter.mem_of_superset (hVopen.mem_nhds hyV)
    intro z hzV
    simp only [Set.mem_compl_iff, Set.mem_union]
    intro hz
    rcases hz with hzU | hzC
    · have hUV : U = V :=
        (connectedComponentIn_eq hzU).trans (connectedComponentIn_eq hzV).symm
      apply hy
      exact Or.inl (hUV.symm ▸ hyV)
    · exact (connectedComponentIn_subset Cᶜ y hzV) hzC
  have hclosureSubset : closure U ⊆ U ∪ C :=
    closure_minimal (fun _ hz ↦ Or.inl hz) hUunionCClosed
  intro y hyFrontier
  rcases hclosureSubset (frontier_subset_closure hyFrontier) with hyU | hyC
  · have : y ∈ U ∩ frontier U := ⟨hyU, hyFrontier⟩
    rw [hUopen.inter_frontier_eq] at this
    exact this.elim
  · exact hyC

/-- Helper for Remark 65.1: the component containing zero in a bounded open
subset of the real line is a nondegenerate bounded open interval. -/
lemma connectedComponentIn_zero_eq_Ioo
    (A : Set ℝ) (hAopen : IsOpen A) (hAbounded : Bornology.IsBounded A)
    (h0 : 0 ∈ A) :
    ∃ a b : ℝ, a < 0 ∧ 0 < b ∧
      connectedComponentIn A 0 = Ioo a b ∧
      closure (connectedComponentIn A 0) = Icc a b := by
  let I : Set ℝ := connectedComponentIn A 0
  have hIconnected : IsConnected I := (isConnected_connectedComponentIn_iff).mpr h0
  have hIopen : IsOpen I := hAopen.connectedComponentIn
  have h0I : 0 ∈ I := mem_connectedComponentIn h0
  have hIbounded : Bornology.IsBounded I :=
    hAbounded.subset (connectedComponentIn_subset A 0)
  have hIbddBelow : BddBelow I := hIbounded.bddBelow
  have hIbddAbove : BddAbove I := hIbounded.bddAbove
  have hleft (z : ℝ) (hz : z ∈ I) : sInf I < z := by
    -- Openness supplies a component point strictly to the left of `z`.
    obtain ⟨l, u, hzlu, hlu⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp (hIopen.mem_nhds hz)
    obtain ⟨y, hly, hyz⟩ := exists_between hzlu.1
    exact lt_of_le_of_lt (csInf_le hIbddBelow (hlu ⟨hly, lt_trans hyz hzlu.2⟩)) hyz
  have hright (z : ℝ) (hz : z ∈ I) : z < sSup I := by
    -- The same neighborhood argument supplies a component point to the right.
    obtain ⟨l, u, hzlu, hlu⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp (hIopen.mem_nhds hz)
    obtain ⟨y, hzy, hyu⟩ := exists_between hzlu.2
    exact lt_of_lt_of_le hzy (le_csSup hIbddAbove (hlu ⟨lt_trans hzlu.1 hzy, hyu⟩))
  have hIeq : I = Ioo (sInf I) (sSup I) := by
    -- Connectedness fills every point strictly between the extremal bounds.
    apply Set.Subset.antisymm
    · exact fun z hz ↦ ⟨hleft z hz, hright z hz⟩
    · exact hIconnected.Ioo_csInf_csSup_subset hIbddBelow hIbddAbove
  have hIclosure : closure I = Icc (sInf I) (sSup I) := by
    -- Closing the nondegenerate interval adds exactly its two endpoints.
    calc
      closure I = closure (Ioo (sInf I) (sSup I)) := congrArg closure hIeq
      _ = Icc (sInf I) (sSup I) :=
        closure_Ioo (ne_of_lt (lt_trans (hleft 0 h0I) (hright 0 h0I)))
  exact ⟨sInf I, sSup I, hleft 0 h0I, hright 0 h0I, hIeq, hIclosure⟩

/-- Helper for Remark 65.1: a nonconstant affine line through an interior
point pulls a bounded open domain back to a bounded open real set containing zero. -/
lemma affineLinePreimage_open_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (hUopen : IsOpen U) (hUbounded : Bornology.IsBounded U)
    (x : E) (hx : x ∈ U) (v : E) (hv : v ≠ 0) :
    let line : ℝ → E := AffineMap.lineMap x (x + v)
    IsOpen (line ⁻¹' U) ∧ Bornology.IsBounded (line ⁻¹' U) ∧
      0 ∈ line ⁻¹' U ∧ Function.Injective line := by
  let line : ℝ → E := AffineMap.lineMap x (x + v)
  have hendpoint : x ≠ x + v := by
    -- Equality of the two line endpoints would force the direction to vanish.
    intro h
    apply hv
    simpa only [add_sub_cancel_left, sub_self] using congrArg (fun y ↦ y - x) h.symm
  refine ⟨hUopen.preimage AffineMap.lineMap_continuous, ?_, ?_, ?_⟩
  · exact (antilipschitzWith_lineMap hendpoint).isBounded_preimage hUbounded
  · simpa only [line, Set.mem_preimage, AffineMap.lineMap_apply_zero] using hx
  · exact (antilipschitzWith_lineMap hendpoint).injective

/-- Helper for Remark 65.1: a nonconstant affine line through an interior
point cuts out a nondegenerate maximal interval in a bounded open domain. -/
lemma affineLineComponent_eq_Ioo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (hUopen : IsOpen U) (hUbounded : Bornology.IsBounded U)
    (x : E) (hx : x ∈ U) (v : E) (hv : v ≠ 0) :
    let line : ℝ → E := AffineMap.lineMap x (x + v)
    ∃ a b : ℝ, a < 0 ∧ 0 < b ∧ Function.Injective line ∧
      connectedComponentIn (line ⁻¹' U) 0 = Ioo a b ∧
      closure (connectedComponentIn (line ⁻¹' U) 0) = Icc a b := by
  let line : ℝ → E := AffineMap.lineMap x (x + v)
  obtain ⟨hpreOpen, hpreBounded, hzero, hlineInjective⟩ :=
    affineLinePreimage_open_bounded U hUopen hUbounded x hx v hv
  -- Normalize the connected component of zero in the pulled-back domain.
  obtain ⟨a, b, ha, hb, hcomponent, hclosure⟩ :=
    connectedComponentIn_zero_eq_Ioo (line ⁻¹' U) hpreOpen hpreBounded hzero
  exact ⟨a, b, ha, hb, hlineInjective, hcomponent, hclosure⟩

/-- Helper for Remark 65.1: every point of a bounded open set lies on a
Jordan crosscut obtained by taking the maximal interval on a nonconstant affine line. -/
lemma existsAffineLineJordanCrosscut
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (hUopen : IsOpen U) (hUbounded : Bornology.IsBounded U)
    (x : E) (hx : x ∈ U) (v : E) (hv : v ≠ 0) :
    ∃ p q : E, ∃ γ : JordanCrosscut U p q, x ∈ γ.carrier := by
  let line : ℝ → E := AffineMap.lineMap x (x + v)
  obtain ⟨a, b, ha, hb, hlineInjective, hcomponent, hclosure⟩ :=
    affineLineComponent_eq_Ioo U hUopen hUbounded x hx v hv
  have hab : a < b := ha.trans hb
  have hlineContinuous : Continuous line := AffineMap.lineMap_continuous
  let intervalLine : Icc a b → E := fun t ↦ line t
  have hintervalLineContinuous : Continuous intervalLine :=
    hlineContinuous.comp continuous_subtype_val
  have hintervalLineInjective : Function.Injective intervalLine :=
    hlineInjective.comp Subtype.val_injective
  let intervalEmbedding : Topology.IsEmbedding intervalLine :=
    (hintervalLineContinuous.isClosedEmbedding hintervalLineInjective).isEmbedding
  let parameterization : unitInterval ≃ₜ Set.range intervalLine :=
    (iccHomeoI a b hab).symm.trans intervalEmbedding.toHomeomorph
  have hcomponentImageSubset :
      line '' connectedComponentIn (line ⁻¹' U) 0 ⊆ U := by
    -- The selected real component lies in the preimage of the domain.
    exact (image_mono (connectedComponentIn_subset (line ⁻¹' U) 0)).trans
      (image_preimage_subset line U)
  have hcarrierClosure : Set.range intervalLine ⊆ closure U := by
    rintro y ⟨t, rfl⟩
    have htClosure : (t : ℝ) ∈ closure (connectedComponentIn (line ⁻¹' U) 0) := by
      rw [hclosure]
      exact t.property
    -- Continuity carries the closed parameter interval into the domain closure.
    exact closure_mono hcomponentImageSubset
      (image_closure_subset_closure_image hlineContinuous ⟨t, htClosure, rfl⟩)
  have haNotMem : line a ∉ U := by
    intro haU
    have hsegmentSubset : Icc a 0 ⊆ line ⁻¹' U := by
      intro t ht
      rcases ht.1.eq_or_lt with rfl | hat
      · exact haU
      · apply connectedComponentIn_subset (line ⁻¹' U) 0
        rw [hcomponent]
        exact ⟨hat, lt_of_le_of_lt ht.2 hb⟩
    have haComponent : a ∈ connectedComponentIn (line ⁻¹' U) 0 :=
      isPreconnected_Icc.subset_connectedComponentIn
        (right_mem_Icc.mpr ha.le) hsegmentSubset (left_mem_Icc.mpr ha.le)
    rw [hcomponent] at haComponent
    exact (lt_irrefl a) haComponent.1
  have hbNotMem : line b ∉ U := by
    intro hbU
    have hsegmentSubset : Icc 0 b ⊆ line ⁻¹' U := by
      intro t ht
      rcases ht.2.lt_or_eq with htb | rfl
      · apply connectedComponentIn_subset (line ⁻¹' U) 0
        rw [hcomponent]
        exact ⟨lt_of_lt_of_le ha ht.1, htb⟩
      · exact hbU
    have hbComponent : b ∈ connectedComponentIn (line ⁻¹' U) 0 :=
      isPreconnected_Icc.subset_connectedComponentIn
        (left_mem_Icc.mpr hb.le) hsegmentSubset (right_mem_Icc.mpr hb.le)
    rw [hcomponent] at hbComponent
    exact (lt_irrefl b) hbComponent.2
  have haFrontier : line a ∈ frontier U := by
    -- The left endpoint is in the closure but not in the open domain.
    rw [hUopen.frontier_eq]
    exact ⟨hcarrierClosure ⟨⟨a, le_rfl, hab.le⟩, rfl⟩, haNotMem⟩
  have hbFrontier : line b ∈ frontier U := by
    -- The right endpoint satisfies the symmetric boundary characterization.
    rw [hUopen.frontier_eq]
    exact ⟨hcarrierClosure ⟨⟨b, hab.le, le_rfl⟩, rfl⟩, hbNotMem⟩
  have hcarrierInterFrontier :
      Set.range intervalLine ∩ frontier U = {line a, line b} := by
    apply Set.Subset.antisymm
    · rintro y ⟨⟨t, rfl⟩, htFrontier⟩
      by_cases hta : (t : ℝ) = a
      · simpa only [intervalLine, hta] using Set.mem_insert (line a) {line b}
      · by_cases htb : (t : ℝ) = b
        · simpa only [intervalLine, htb] using
            Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton (line b)))
        · have hat : a < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm hta)
          have htb' : (t : ℝ) < b := lt_of_le_of_ne t.property.2 htb
          have htU : line t ∈ U := by
            apply connectedComponentIn_subset (line ⁻¹' U) 0
            rw [hcomponent]
            exact ⟨hat, htb'⟩
          have : line t ∈ U ∩ frontier U := ⟨htU, htFrontier⟩
          rw [hUopen.inter_frontier_eq] at this
          exact this.elim
    · rintro y (rfl | rfl)
      · exact ⟨⟨⟨a, le_rfl, hab.le⟩, rfl⟩, haFrontier⟩
      · exact ⟨⟨⟨b, hab.le, le_rfl⟩, rfl⟩, hbFrontier⟩
  have hparameterizationSource :
      (parameterization (0 : unitInterval) : E) = line a := by
    -- The interval homeomorphism sends zero to the left endpoint.
    simp only [parameterization, Homeomorph.trans_apply,
      Topology.IsEmbedding.toHomeomorph_apply_coe, intervalLine,
      iccHomeoI_symm_apply_coe, Set.Icc.coe_zero, mul_zero,
      zero_add]
  have hparameterizationTarget :
      (parameterization (1 : unitInterval) : E) = line b := by
    -- The interval homeomorphism sends one to the right endpoint.
    simp only [parameterization, Homeomorph.trans_apply,
      Topology.IsEmbedding.toHomeomorph_apply_coe, intervalLine,
      iccHomeoI_symm_apply_coe, Set.Icc.coe_one, mul_one]
    congr 1
    linarith
  let γ : JordanCrosscut U (line a) (line b) :=
    { carrier := Set.range intervalLine
      parameterization := parameterization
      source_eq := hparameterizationSource
      target_eq := hparameterizationTarget
      carrier_subset_closure := hcarrierClosure
      carrier_inter_frontier := hcarrierInterFrontier }
  refine ⟨line a, line b, γ, ?_⟩
  -- The parameter zero realizes the original interior point on the crosscut.
  refine ⟨⟨0, ha.le, hb.le⟩, ?_⟩
  simp only [intervalLine, line, AffineMap.lineMap_apply_zero]

namespace Topology.IsSimpleClosedCurve

/-- Helper for Remark 65.1: a bounded complementary component of a planar
simple closed curve has a Jordan crosscut through each of its points. -/
theorem existsJordanCrosscutThrough
    (C : Set (EuclideanSpace ℝ (Fin 2))) [Topology.IsSimpleClosedCurve C]
    (p : (Cᶜ : Set (EuclideanSpace ℝ (Fin 2))))
    (hbounded : Bornology.IsBounded (connectedComponentIn Cᶜ p)) :
    ∃ a b : C,
      ∃ γ : JordanCrosscut (connectedComponentIn Cᶜ p) (a : EuclideanSpace ℝ (Fin 2)) b,
        (p : EuclideanSpace ℝ (Fin 2)) ∈ γ.carrier := by
  classical
  -- Compactness of the circle model makes the planar curve closed.
  obtain ⟨e⟩ := Topology.IsSimpleClosedCurve.homeomorphic_circle (X := C)
  letI : CompactSpace C := e.symm.compactSpace
  have hCclosed : IsClosed C :=
    (isCompact_iff_compactSpace.mpr inferInstance).isClosed
  let U : Set (EuclideanSpace ℝ (Fin 2)) := connectedComponentIn Cᶜ p
  have hUopen : IsOpen U := hCclosed.isOpen_compl.connectedComponentIn
  have hpU : (p : EuclideanSpace ℝ (Fin 2)) ∈ U :=
    mem_connectedComponentIn p.property
  let v : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
  have hv : v ≠ 0 := by
    intro hv
    have hcoordinate := congrArg (fun w : EuclideanSpace ℝ (Fin 2) ↦ w 0) hv
    norm_num [v] at hcoordinate
  obtain ⟨a, b, γ, hpγ⟩ :=
    existsAffineLineJordanCrosscut U hUopen hbounded p hpU v hv
  have hfrontierSubset : frontier U ⊆ C :=
    frontier_connectedComponentIn_compl_subset_closed C hCclosed p
  have haC : a ∈ C := hfrontierSubset γ.endpoints_mem_frontier.1
  have hbC : b ∈ C := hfrontierSubset γ.endpoints_mem_frontier.2
  -- Package the two frontier endpoints as points of the original curve.
  exact ⟨⟨a, haC⟩, ⟨b, hbC⟩, γ, hpγ⟩

end Topology.IsSimpleClosedCurve
