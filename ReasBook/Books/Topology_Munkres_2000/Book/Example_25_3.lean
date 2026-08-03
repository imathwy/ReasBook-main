module

public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Order.IntermediateValue
public import Topology_Munkres_2000.Book.Example_23_2
public import Topology_Munkres_2000.Book.Example_23_4
public import Topology_Munkres_2000.Book.Example_24_7.Connectedness

public section

open Filter Set Topology

namespace Set.OrdConnected

/-- Part (1) of Example 25.3: Every nonempty interval or ray in `ℝ` is connected. -/
theorem isConnected {s : Set ℝ} (hs : s.OrdConnected) (hne : s.Nonempty) :
    IsConnected s := by
  -- Combine nonemptiness with order-convex preconnectedness.
  exact ⟨hne, hs.isPreconnected⟩

/-- Part (2) of Example 25.3: Every interval or ray in `ℝ` is locally connected in its
subspace topology. -/
instance instLocallyConnectedSpace {s : Set ℝ} [s.OrdConnected] :
    LocallyConnectedSpace s := by
  -- Closed order intervals give connected neighborhoods in the subtype order.
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro p U hU
  obtain ⟨a, b, hp, hab_nhds, habU⟩ := exists_Icc_mem_subset_of_mem_nhds hU
  letI : Inhabited s := ⟨p⟩
  exact ⟨Icc a b, hab_nhds, isPreconnected_Icc, habU⟩

end Set.OrdConnected

/-- Helper for Example 25.3: a space covered by two open locally connected subspaces is locally
connected. -/
lemma locallyConnectedSpace_of_open_pair {X : Type*} [TopologicalSpace X]
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [LocallyConnectedSpace U] [LocallyConnectedSpace V] : LocallyConnectedSpace X := by
  -- Work in whichever open member of the cover contains the chosen point.
  rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
  intro x W hW
  have hxcover : x ∈ U ∪ V := by
    rw [hcover]
    exact Set.mem_univ x
  rcases hxcover with hxU | hxV
  · obtain ⟨A, hAW, hAopen, hxA, hAconnected⟩ :=
      locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp inferInstance
        ⟨x, hxU⟩ (Subtype.val ⁻¹' W)
        (continuousAt_subtype_val.preimage_mem_nhds hW)
    refine ⟨Subtype.val '' A, ?_, ?_, ?_,
      hAconnected.image Subtype.val continuous_subtype_val.continuousOn⟩
    · exact Set.image_subset_iff.mpr hAW
    · exact hU.isOpenEmbedding_subtypeVal.isOpenMap A hAopen
    · exact ⟨⟨x, hxU⟩, hxA, rfl⟩
  · obtain ⟨A, hAW, hAopen, hxA, hAconnected⟩ :=
      locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp inferInstance
        ⟨x, hxV⟩ (Subtype.val ⁻¹' W)
        (continuousAt_subtype_val.preimage_mem_nhds hW)
    refine ⟨Subtype.val '' A, ?_, ?_, ?_,
      hAconnected.image Subtype.val continuous_subtype_val.continuousOn⟩
    · exact Set.image_subset_iff.mpr hAW
    · exact hV.isOpenEmbedding_subtypeVal.isOpenMap A hAopen
    · exact ⟨⟨x, hxV⟩, hxA, rfl⟩

namespace PuncturedInterval

/-- Part (3) of Example 25.3: The subspace `[-1, 0) ∪ (0, 1]` of `ℝ` is not connected. -/
theorem not_connected : ¬ ConnectedSpace Space := by
    -- A connected-space instance would forbid the canonical separation into two halves.
    intro hconnected
    letI : ConnectedSpace Space := hconnected
    apply (preconnectedSpace_iff_no_separation Space).mp inferInstance
    exact ⟨leftInSpace, rightInSpace, halves_isSeparation⟩

/-- Part (4) of Example 25.3: The subspace `[-1, 0) ∪ (0, 1]` of `ℝ` is locally connected. -/
instance instLocallyConnectedSpace : LocallyConnectedSpace Space := by
  -- Each open half is an order interval, and the two halves cover the punctured interval.
  letI : LocallyConnectedSpace left := inferInstance
  letI : LocallyConnectedSpace right := inferInstance
  have hleft : left ⊆ Set.range ((↑) : Space → ℝ) := by
    intro x hx
    exact ⟨⟨x, Or.inl hx⟩, rfl⟩
  have hright : right ⊆ Set.range ((↑) : Space → ℝ) := by
    intro x hx
    exact ⟨⟨x, Or.inr hx⟩, rfl⟩
  letI : LocallyConnectedSpace leftInSpace :=
    Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hleft |>.locallyConnectedSpace
  letI : LocallyConnectedSpace rightInSpace :=
    Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hright |>.locallyConnectedSpace
  exact locallyConnectedSpace_of_open_pair halves_isSeparation.isOpen_left
    halves_isSeparation.isOpen_right halves_isSeparation.union_eq_univ

end PuncturedInterval

namespace TopologistsSineCurve

/- Example 25.3 (5): The topologist's sine curve is connected. -/
#check (inferInstance : ConnectedSpace Space)

/-- Helper for Example 25.3: the oscillating graph is dense in its closure. -/
lemma dense_curvePart : Dense curvePart := by
  -- Subtype closure reduces to the defining ambient closure of `curve`.
  have himage : Subtype.val '' curvePart = curve := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact (mem_curvePart_iff q).mp hq
    · intro hp
      have hpCarrier : p ∈ carrier := subset_closure hp
      let q : Space := ⟨p, hpCarrier⟩
      exact ⟨q, (mem_curvePart_iff q).mpr hp, rfl⟩
  rw [dense_iff_closure_eq]
  ext p
  rw [closure_subtype]
  rw [himage]
  simp only [Set.mem_univ, iff_true]
  exact p.property

/-- Helper for Example 25.3: a carrier point with nonzero first coordinate lies on the graph. -/
lemma mem_curve_of_fst_ne_zero {p : ℝ × ℝ} (hp : p ∈ carrier) (hp_ne : p.1 ≠ 0) :
    p ∈ curve := by
  -- Sequential closure preserves the graph equation away from the singular first coordinate.
  rw [mem_closure_iff_seq_limit] at hp
  obtain ⟨v, hv_curve, hv_lim⟩ := hp
  have hx_lim : Filter.Tendsto (fun n ↦ (v n).1) Filter.atTop (𝓝 p.1) :=
    continuousAt_fst.tendsto.comp hv_lim
  have hy_lim : Filter.Tendsto (fun n ↦ (v n).2) Filter.atTop (𝓝 p.2) :=
    continuousAt_snd.tendsto.comp hv_lim
  have hpos : 0 ≤ p.1 := by
    apply ge_of_tendsto hx_lim
    filter_upwards with n
    rcases hv_curve n with ⟨x, hx, hv⟩
    rw [← hv]
    exact hx.1.le
  have hle : p.1 ≤ 1 := by
    apply le_of_tendsto hx_lim
    filter_upwards with n
    rcases hv_curve n with ⟨x, hx, hv⟩
    rw [← hv]
    exact hx.2
  have hsin_lim :
      Filter.Tendsto (fun n ↦ Real.sin (1 / (v n).1)) Filter.atTop
        (𝓝 (Real.sin (1 / p.1))) := by
    have hcont : ContinuousAt (fun x : ℝ ↦ Real.sin (1 / x)) p.1 := by
      fun_prop
    exact hcont.tendsto.comp hx_lim
  have hy_eq : p.2 = Real.sin (1 / p.1) := by
    apply tendsto_nhds_unique hy_lim
    convert hsin_lim using 1
    funext n
    rcases hv_curve n with ⟨x, hx, hv⟩
    rw [← hv]
  exact ⟨p.1, ⟨lt_of_le_of_ne hpos (Ne.symm hp_ne), hle⟩,
    Prod.ext rfl hy_eq.symm⟩

/-- Helper for Example 25.3: `sin (1 / u)` equals `-1` arbitrarily close to zero. -/
lemma exists_pos_lt_sin_inv_eq_neg_one {ε : ℝ} (hε : 0 < ε) :
    ∃ u, 0 < u ∧ u < ε ∧ Real.sin (1 / u) = -1 := by
  -- Reciprocals of large phases `3π/2 + 2nπ` approach zero from the right.
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (1 / (2 * Real.pi * ε))
  let a : ℝ := 3 * Real.pi / 2 + n * (2 * Real.pi)
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have ha_large : 1 / ε < a := by
    have hpi : 0 < 2 * Real.pi := by
      positivity
    have hn' : 1 / ε < (n : ℝ) * (2 * Real.pi) := by
      calc
        1 / ε = (1 / (2 * Real.pi * ε)) * (2 * Real.pi) := by field_simp
        _ < (n : ℝ) * (2 * Real.pi) := mul_lt_mul_of_pos_right hn hpi
    dsimp [a]
    linarith [Real.pi_pos]
  refine ⟨1 / a, one_div_pos.mpr ha_pos, ?_, ?_⟩
  · apply (div_lt_iff₀ ha_pos).2
    have hscaled := (div_lt_iff₀ hε).1 ha_large
    nlinarith
  · simp only [one_div, inv_inv]
    dsimp [a]
    rw [Real.sin_add_nat_mul_two_pi]
    rw [show (3 : ℝ) * Real.pi / 2 = Real.pi / 2 + Real.pi by ring]
    rw [Real.sin_add_pi, Real.sin_pi_div_two]

/-- Helper for Example 25.3: the origin belongs to the topologist's sine curve carrier. -/
lemma origin_mem_carrier : (0, 0) ∈ carrier := by
  -- Graph points at reciprocal positive integer multiples of `π` converge to the origin.
  rw [mem_closure_iff_seq_limit]
  let v : ℕ → ℝ × ℝ := fun n ↦
    (1 / (((n + 1 : ℕ) : ℝ) * Real.pi), 0)
  refine ⟨v, ?_, ?_⟩
  · intro n
    refine ⟨1 / (((n + 1 : ℕ) : ℝ) * Real.pi), ?_, ?_⟩
    · constructor
      · positivity
      · have hden : 1 ≤ (((n + 1 : ℕ) : ℝ) * Real.pi) := by
          have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by
            exact_mod_cast Nat.succ_pos n
          have hpi : (2 : ℝ) ≤ Real.pi := by
            linarith [Real.one_le_pi_div_two]
          nlinarith
        apply (div_le_iff₀
          (show (0 : ℝ) < (((n + 1 : ℕ) : ℝ) * Real.pi) by positivity)).2
        simpa using hden
    · apply Prod.ext
      · rfl
      · dsimp [v]
        simp only [one_div, inv_inv]
        simpa only using Real.sin_nat_mul_pi (n + 1)
  · have hx :
        Filter.Tendsto (fun n : ℕ ↦ 1 / (((n + 1 : ℕ) : ℝ) * Real.pi))
          Filter.atTop (𝓝 0) := by
      have hbase : Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1))
          Filter.atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      convert hbase.const_mul (1 / Real.pi) using 1
      · funext n
        simp only [Nat.cast_add, Nat.cast_one]
        field_simp
      · simp
    have hy : Filter.Tendsto (fun _ : ℕ ↦ (0 : ℝ)) Filter.atTop (𝓝 0) :=
      tendsto_const_nhds
    rw [nhds_prod_eq]
    exact hx.prodMk hy

/-- Part (6) of Example 25.3: The topologist's sine curve is not locally connected. -/
theorem not_locallyConnected : ¬ LocallyConnectedSpace Space := by
  -- A connected neighborhood high on the vertical segment must meet both extremes of the graph.
  intro hlocal
  letI : LocallyConnectedSpace Space := hlocal
  let origin : Space := ⟨(0, 0), origin_mem_carrier⟩
  let upper : Set Space := {p | (-1 / 2 : ℝ) < p.1.2}
  have horiginUpper : origin ∈ upper := by
    norm_num [origin, upper]
  have hupperOpen : IsOpen upper := by
    exact isOpen_lt continuous_const
      (continuous_snd.comp continuous_subtype_val)
  obtain ⟨V, hVnhds, hVpre, hVupper⟩ :=
    locallyConnectedSpace_iff_connected_subsets.mp inferInstance origin
      upper (hupperOpen.mem_nhds horiginUpper)
  have horiginV : origin ∈ V := mem_of_mem_nhds hVnhds
  obtain ⟨q, hqCurve, hqV⟩ := dense_curvePart.inter_nhds_nonempty hVnhds
  have hqCurveAmbient : q.1 ∈ curve := (mem_curvePart_iff q).mp hqCurve
  rcases hqCurveAmbient with ⟨x, hx, hqeq⟩
  have hqfst : q.1.1 = x := congrArg Prod.fst hqeq.symm
  have hqpos : 0 < q.1.1 := by
    rw [hqfst]
    exact hx.1
  obtain ⟨u, hu_pos, hu_lt, hu_sin⟩ :=
    exists_pos_lt_sin_inv_eq_neg_one hqpos
  have hu_between : u ∈ Icc ((origin : Space).1.1) q.1.1 := by
    change u ∈ Icc 0 q.1.1
    exact ⟨hu_pos.le, hu_lt.le⟩
  have hfstContinuous : ContinuousOn (fun p : Space ↦ p.1.1) V :=
    (continuous_fst.comp continuous_subtype_val).continuousOn
  obtain ⟨r, hrV, hrfst⟩ :=
    hVpre.intermediate_value horiginV hqV hfstContinuous hu_between
  have hrfst_pos : r.1.1 ≠ 0 := by
    intro hrzero
    change r.1.1 = u at hrfst
    rw [hrzero] at hrfst
    linarith
  have hrCurve : r.1 ∈ curve := mem_curve_of_fst_ne_zero r.property hrfst_pos
  rcases hrCurve with ⟨y, hy, hryeq⟩
  have hryfst : y = u := by
    calc
      y = r.1.1 := congrArg Prod.fst hryeq
      _ = u := hrfst
  have hrsnd : r.1.2 = -1 := by
    calc
      r.1.2 = Real.sin (1 / y) := (congrArg Prod.snd hryeq).symm
      _ = Real.sin (1 / u) := by rw [hryfst]
      _ = -1 := hu_sin
  have hrUpper : r ∈ upper := hVupper hrV
  change (-1 / 2 : ℝ) < r.1.2 at hrUpper
  rw [hrsnd] at hrUpper
  norm_num at hrUpper

end TopologistsSineCurve

/- Example 25.3 (7): The rationals `ℚ` are not connected. -/
#check rat_not_connected

/-- Part (8) of Example 25.3: The rationals `ℚ` are not locally connected. -/
theorem rat_not_locallyConnected : ¬ LocallyConnectedSpace ℚ := by
  -- Local connectedness would make the singleton connected component of zero open.
  intro hlocal
  letI : LocallyConnectedSpace ℚ := hlocal
  apply not_isOpen_singleton (0 : ℚ)
  rw [← connectedComponent_eq_singleton (0 : ℚ)]
  exact isOpen_connectedComponent

/-- Example 25.3: intervals and rays, the punctured interval, the topologist's sine curve,
and `ℚ` have the stated connectedness and local connectedness properties. -/
theorem Example_25_3 :
    (∀ {s : Set ℝ}, s.OrdConnected → s.Nonempty → IsConnected s) ∧
      (∀ {s : Set ℝ}, s.OrdConnected → LocallyConnectedSpace s) ∧
      (¬ ConnectedSpace PuncturedInterval.Space) ∧
      LocallyConnectedSpace PuncturedInterval.Space ∧
      ConnectedSpace TopologistsSineCurve.Space ∧
      (¬ LocallyConnectedSpace TopologistsSineCurve.Space) ∧
      (¬ ConnectedSpace ℚ) ∧
      (¬ LocallyConnectedSpace ℚ) := by
  -- Assemble the eight source-facing claims into the planned declaration.
  constructor
  · intro s hs hne
    exact hs.isConnected hne
  constructor
  · intro s hs
    letI : s.OrdConnected := hs
    infer_instance
  constructor
  · exact PuncturedInterval.not_connected
  constructor
  · infer_instance
  constructor
  · infer_instance
  constructor
  · exact TopologistsSineCurve.not_locallyConnected
  constructor
  · exact rat_not_connected
  · exact rat_not_locallyConnected
