module

public import Topology_Munkres_2000.Book.Example_24_7.Connectedness
public import Topology_Munkres_2000.Book.Example_50_1
public import Topology_Munkres_2000.Book.Definition_50_3.CoveringDimension
public import Topology_Munkres_2000.Book.Exercise_50_2
public import Mathlib.Topology.MetricSpace.Thickening

public section

open scoped CoveringDimension
open Filter Topology

namespace TopologistsSineCurve

/-- Helper for Exercise 50.3: every positive graph parameter at most `1` gives a
point of the sine-curve carrier. -/
lemma graphPoint_mem_carrier {x : ℝ} (hx : x ∈ Set.Ioc 0 1) :
    ((x, Real.sin (1 / x)) : ℝ × ℝ) ∈ carrier := by
  -- The parametrized point belongs to the oscillating curve, hence to its closure.
  apply subset_closure
  rw [curve]
  exact ⟨x, hx, rfl⟩

/-- Helper for Exercise 50.3: the graph point with first coordinate `1` belongs to the
sine-curve carrier. -/
lemma rightGraphPoint_mem_carrier :
    ((1, Real.sin (1 / 1)) : ℝ × ℝ) ∈ carrier := by
  -- Specialize the general graph-membership lemma at the right endpoint.
  exact graphPoint_mem_carrier (by norm_num)

/-- Helper for Exercise 50.3: the graph point with first coordinate `1 / 2` belongs to
the sine-curve carrier. -/
lemma middleGraphPoint_mem_carrier :
    ((1 / 2, Real.sin (1 / (1 / 2))) : ℝ × ℝ) ∈ carrier := by
  -- Specialize the general graph-membership lemma at an interior parameter.
  exact graphPoint_mem_carrier (by norm_num)

/-- Helper for Exercise 50.3: two graph parameters give distinct points of the sine
curve. -/
lemma middleGraphPoint_ne_rightGraphPoint :
    (⟨(1 / 2, Real.sin (1 / (1 / 2))), middleGraphPoint_mem_carrier⟩ : Space) ≠
      ⟨(1, Real.sin (1 / 1)), rightGraphPoint_mem_carrier⟩ := by
  -- Equality of subtype points would force equality of their first coordinates.
  intro h
  have hfst := congrArg (fun p : Space ↦ p.1.1) h
  norm_num at hfst

/-- Helper for Exercise 50.3: every point of the limiting vertical interval belongs
to the sine-curve carrier. -/
lemma verticalPoint_mem_carrier {y : ℝ} (hy : y ∈ Set.Icc (-1) 1) :
    ((0, y) : ℝ × ℝ) ∈ carrier := by
  -- Approach `(0, y)` along graph points whose phases differ by full periods.
  rw [mem_closure_iff_seq_limit]
  let phase : ℕ → ℝ := fun n ↦ Real.arcsin y + (n + 1) * (2 * Real.pi)
  let v : ℕ → ℝ × ℝ := fun n ↦ (1 / phase n, y)
  have hphase_pos (n : ℕ) : 0 < phase n := by
    have harcsin : -(Real.pi / 2) ≤ Real.arcsin y := Real.neg_pi_div_two_le_arcsin _
    have hn : (1 : ℝ) ≤ n + 1 := by norm_num
    dsimp [phase]
    nlinarith [Real.pi_pos]
  refine ⟨v, ?_, ?_⟩
  · intro n
    rw [curve]
    refine ⟨1 / phase n, ?_, ?_⟩
    · constructor
      · exact one_div_pos.mpr (hphase_pos n)
      · apply (div_le_iff₀ (hphase_pos n)).2
        dsimp [phase]
        have harcsin : -(Real.pi / 2) ≤ Real.arcsin y := Real.neg_pi_div_two_le_arcsin _
        have hn : (1 : ℝ) ≤ n + 1 := by norm_num
        have hpi : (2 : ℝ) ≤ Real.pi := by
          linarith [Real.one_le_pi_div_two]
        nlinarith
    · apply Prod.ext
      · rfl
      · dsimp [v]
        simp only [one_div, inv_inv]
        dsimp [phase]
        convert Real.sin_add_nat_mul_two_pi (Real.arcsin y) (n + 1) using 1
        · norm_num
        exact (Real.sin_arcsin hy.1 hy.2).symm
  · have hphase : Filter.Tendsto phase Filter.atTop Filter.atTop := by
      dsimp [phase]
      apply tendsto_atTop_add_const_left
      have hnat : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) + 1)
          Filter.atTop Filter.atTop :=
        tendsto_atTop_add_const_right Filter.atTop 1 tendsto_natCast_atTop_atTop
      exact hnat.atTop_mul_const
        (show (0 : ℝ) < 2 * Real.pi by positivity)
    have hx : Filter.Tendsto (fun n ↦ 1 / phase n) Filter.atTop (𝓝 0) :=
      (tendsto_inv_atTop_zero.comp hphase).congr fun n ↦ by
        simp only [Function.comp_apply, one_div]
    exact hx.prodMk_nhds tendsto_const_nhds

/-- Helper for Exercise 50.3: first coordinates of sine-curve points are
nonnegative. -/
lemma fst_nonneg (p : Space) : 0 ≤ p.1.1 := by
  -- The closed right half-plane contains the graph, so it contains its closure.
  have hcurve : curve ⊆ {q : ℝ × ℝ | 0 ≤ q.1} := by
    rintro q ⟨x, hx, rfl⟩
    exact hx.1.le
  exact closure_minimal hcurve (isClosed_le continuous_const continuous_fst) p.property

/-- Helper for Exercise 50.3: first coordinates of sine-curve points are at most
`1`. -/
lemma fst_le_one (p : Space) : p.1.1 ≤ 1 := by
  -- The closed left half-plane at `1` contains the graph and therefore its closure.
  have hcurve : curve ⊆ {q : ℝ × ℝ | q.1 ≤ 1} := by
    rintro q ⟨x, hx, rfl⟩
    exact hx.2
  exact closure_minimal hcurve (isClosed_le continuous_fst continuous_const) p.property

/-- Helper for Exercise 50.3: every sine-curve point has first coordinate in the
closed unit interval. -/
lemma fst_mem_unitInterval (p : Space) : p.1.1 ∈ Set.Icc 0 1 := by
  -- Combine the two closed-half-plane bounds on the carrier.
  exact ⟨fst_nonneg p, fst_le_one p⟩

/-- Helper for Exercise 50.3: second coordinates of sine-curve points lie in
`Set.Icc (-1) 1`. -/
lemma snd_mem_unitInterval (p : Space) : p.1.2 ∈ Set.Icc (-1) 1 := by
  -- The closed horizontal strip contains the graph and therefore its closure.
  have hcurve : curve ⊆ {q : ℝ × ℝ | q.2 ∈ Set.Icc (-1) 1} := by
    rintro q ⟨x, hx, rfl⟩
    exact ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  have hstrip : IsClosed {q : ℝ × ℝ | q.2 ∈ Set.Icc (-1) 1} := by
    exact (isClosed_Icc.preimage continuous_snd)
  exact closure_minimal hcurve hstrip p.property

/-- Helper for Exercise 50.3: the second-coordinate projection into the closed
unit interval. -/
def verticalCoord : Space → Set.Icc (-1 : ℝ) 1 :=
  fun p ↦ ⟨p.1.2, snd_mem_unitInterval p⟩

/-- Helper for Exercise 50.3: the interval-valued second-coordinate projection is
continuous. -/
lemma continuous_verticalCoord : Continuous verticalCoord := by
  -- Continuity is checked after composing with the subtype inclusion.
  rw [Topology.IsInducing.subtypeVal.continuous_iff]
  exact continuous_snd.comp continuous_subtype_val

/-- Helper for Exercise 50.3: a carrier point with positive first coordinate is the
graph point parametrized by that coordinate. -/
lemma eq_graphPoint_of_fst_pos (p : Space) (hp : 0 < p.1.1) :
    p.1 = (p.1.1, Real.sin (1 / p.1.1)) := by
  -- Represent the carrier point as a limit of graph points and pass the graph
  -- equation to the limit using continuity away from zero.
  have hp_carrier : p.1 ∈ closure curve := p.property
  rw [mem_closure_iff_seq_limit] at hp_carrier
  obtain ⟨v, hv_curve, hv_lim⟩ := hp_carrier
  have hx_lim : Filter.Tendsto (fun n ↦ (v n).1) Filter.atTop (𝓝 p.1.1) :=
    continuousAt_fst.tendsto.comp hv_lim
  have hy_lim : Filter.Tendsto (fun n ↦ (v n).2) Filter.atTop (𝓝 p.1.2) :=
    continuousAt_snd.tendsto.comp hv_lim
  have hsin_lim :
      Filter.Tendsto (fun n ↦ Real.sin (1 / (v n).1)) Filter.atTop
        (𝓝 (Real.sin (1 / p.1.1))) := by
    have hp_ne : p.1.1 ≠ 0 := ne_of_gt hp
    have hcontinuous : ContinuousAt (fun x : ℝ ↦ Real.sin (1 / x)) p.1.1 :=
      Real.continuous_sin.continuousAt.comp
        (continuousAt_const.div₀ continuousAt_id hp_ne)
    exact hcontinuous.tendsto.comp hx_lim
  have hy_eq : p.1.2 = Real.sin (1 / p.1.1) := by
    -- Every approximating graph point already satisfies the graph equation.
    apply tendsto_nhds_unique hy_lim
    convert hsin_lim using 1
    funext n
    rcases hv_curve n with ⟨x, hx, hv⟩
    rw [← hv]
  exact Prod.ext rfl hy_eq

/-- Helper for Exercise 50.3: pulling a family back along a function does not
increase its order. -/
lemma preimageFamily_hasOrderLE {X Y : Type*} (f : X → Y)
    (𝒰 : Set (Set Y)) (n : ℕ) (h𝒰 : 𝒰.HasOrderLE n) :
    ((fun U : Set Y ↦ f ⁻¹' U) '' 𝒰).HasOrderLE n := by
  -- At each point, preimage membership identifies the pulled-back members with
  -- a subset of the original members containing its image.
  rw [Set.hasOrderLE_iff]
  intro x
  have hpulled :
      {V ∈ (fun U : Set Y ↦ f ⁻¹' U) '' 𝒰 | x ∈ V} =
        (fun U : Set Y ↦ f ⁻¹' U) '' {U ∈ 𝒰 | f x ∈ U} := by
    ext V
    constructor
    · rintro ⟨⟨U, hU𝒰, rfl⟩, hxU⟩
      exact ⟨U, ⟨hU𝒰, hxU⟩, rfl⟩
    · rintro ⟨U, ⟨hU𝒰, hxU⟩, rfl⟩
      exact ⟨⟨U, hU𝒰, rfl⟩, hxU⟩
  rw [hpulled]
  exact (Set.encard_image_le _ _).trans (Set.hasOrderLE_iff.mp h𝒰 (f x))

/-- Helper for Exercise 50.3: an indexed image family has bounded order when the
set of relevant indices has the same bound pointwise. -/
lemma imageFamily_hasOrderLE_of_fiber {ι X : Type*} (F : ι → Set X)
    (s : Set ι) (n : ℕ) (hfiber : ∀ x, Set.encard {i ∈ s | x ∈ F i} ≤ n) :
    (F '' s).HasOrderLE n := by
  -- Express the members through a point as an image of the corresponding index fiber.
  rw [Set.hasOrderLE_iff]
  intro x
  have hmembers : {U ∈ F '' s | x ∈ U} = F '' {i ∈ s | x ∈ F i} := by
    ext U
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, hxi⟩
      exact ⟨i, ⟨hi, hxi⟩, rfl⟩
    · rintro ⟨i, ⟨hi, hxi⟩, rfl⟩
      exact ⟨⟨i, hi, rfl⟩, hxi⟩
  rw [hmembers]
  exact (Set.encard_image_le _ _).trans (hfiber x)

/-- Helper for Exercise 50.3: a singleton consisting of an open set subordinate to
an open cover is itself an open refinement. -/
lemma singleton_isOpenRefinement {X : Type*} [TopologicalSpace X]
    {𝒜 : Set (Set X)} {C : Set X} (hC_open : IsOpen C)
    (hC_refines : ∃ A ∈ 𝒜, C ⊆ A) :
    IsOpenRefinement ({C} : Set (Set X)) 𝒜 := by
  -- The unique member has the required parent and is open by hypothesis.
  rw [isOpenRefinement_iff, isRefinement_iff]
  constructor
  · intro U hU
    rw [Set.mem_singleton_iff] at hU
    simpa [hU] using hC_refines
  · intro U hU
    rw [Set.mem_singleton_iff] at hU
    simpa [hU] using hC_open

/-- Helper for Exercise 50.3: a singleton family has order at most two. -/
lemma singleton_hasOrderLE_two {X : Type*} (C : Set X) :
    ({C} : Set (Set X)).HasOrderLE 2 := by
  -- At each point the family of containing members is empty or a singleton.
  rw [Set.hasOrderLE_iff]
  intro x
  by_cases hx : x ∈ C
  · have hmembers : {U ∈ ({C} : Set (Set X)) | x ∈ U} = {C} := by
      ext U
      constructor
      · intro hU
        exact hU.1
      · intro hU
        have hUC : U = C := Set.mem_singleton_iff.mp hU
        exact ⟨hU, hUC ▸ hx⟩
    rw [hmembers, Set.encard_singleton]
    norm_num
  · have hmembers : {U ∈ ({C} : Set (Set X)) | x ∈ U} = ∅ := by
      ext U
      constructor
      · intro hU
        have hUC : U = C := Set.mem_singleton_iff.mp hU.1
        exact (hx (hUC ▸ hU.2)).elim
      · intro hU
        exact hU.elim
    rw [hmembers, Set.encard_empty]
    norm_num

/-- Helper for Exercise 50.3: two order-two families that share one connector and
have disjoint nonconnector members still have order at most two after union. -/
lemma orderLE_union_of_sharedConnector {X : Type*} {𝒱 𝒲 : Set (Set X)}
    {C : Set X} (h𝒱 : 𝒱.HasOrderLE 2) (h𝒲 : 𝒲.HasOrderLE 2)
    (hC𝒱 : C ∈ 𝒱) (hC𝒲 : C ∈ 𝒲)
    (hcross : ∀ V ∈ 𝒱 \ {C}, ∀ W ∈ 𝒲 \ {C}, Disjoint V W) :
    (𝒱 ∪ 𝒲).HasOrderLE 2 := by
  -- At a point of the connector, each side contributes at most one further set,
  -- and cross-disjointness makes those possible further sets coincide in family membership.
  rw [Set.hasOrderLE_iff]
  intro x
  let members : Set (Set X) := {U ∈ 𝒱 ∪ 𝒲 | x ∈ U}
  by_cases hxC : x ∈ C
  · have hnonconnector : (members \ {C}).Subsingleton := by
      intro U hU V hV
      rcases hU.1.1 with hU𝒱 | hU𝒲
      · rcases hV.1.1 with hV𝒱 | hV𝒲
        · have hsub : ({A ∈ 𝒱 | x ∈ A} \ {C}).Subsingleton := by
            rw [← Set.encard_le_one_iff_subsingleton]
            have hcard := Set.hasOrderLE_iff.mp h𝒱 x
            have hCmem : C ∈ {A ∈ 𝒱 | x ∈ A} := ⟨hC𝒱, hxC⟩
            rw [← Set.encard_sdiff_add_encard_of_subset
              (Set.singleton_subset_iff.mpr hCmem), Set.encard_singleton,
              ← one_add_one_eq_two] at hcard
            norm_num at hcard
            apply (ENat.addLECancellable_of_ne_top ENat.one_ne_top)
            calc
              1 + ({A ∈ 𝒱 | x ∈ A} \ {C}).encard ≤ (2 : ℕ∞) := by
                simpa only [add_comm] using hcard
              _ = 1 + 1 := by norm_num
          exact hsub ⟨⟨hU𝒱, hU.1.2⟩, hU.2⟩ ⟨⟨hV𝒱, hV.1.2⟩, hV.2⟩
        · exact (Set.disjoint_left.mp
            (hcross U ⟨hU𝒱, hU.2⟩ V ⟨hV𝒲, hV.2⟩) hU.1.2 hV.1.2).elim
      · rcases hV.1.1 with hV𝒱 | hV𝒲
        · exact (Set.disjoint_left.mp
            (hcross V ⟨hV𝒱, hV.2⟩ U ⟨hU𝒲, hU.2⟩) hV.1.2 hU.1.2).elim
        · have hsub : ({A ∈ 𝒲 | x ∈ A} \ {C}).Subsingleton := by
            rw [← Set.encard_le_one_iff_subsingleton]
            have hcard := Set.hasOrderLE_iff.mp h𝒲 x
            have hCmem : C ∈ {A ∈ 𝒲 | x ∈ A} := ⟨hC𝒲, hxC⟩
            rw [← Set.encard_sdiff_add_encard_of_subset
              (Set.singleton_subset_iff.mpr hCmem), Set.encard_singleton,
              ← one_add_one_eq_two] at hcard
            norm_num at hcard
            apply (ENat.addLECancellable_of_ne_top ENat.one_ne_top)
            calc
              1 + ({A ∈ 𝒲 | x ∈ A} \ {C}).encard ≤ (2 : ℕ∞) := by
                simpa only [add_comm] using hcard
              _ = 1 + 1 := by norm_num
          exact hsub ⟨⟨hU𝒲, hU.1.2⟩, hU.2⟩ ⟨⟨hV𝒲, hV.1.2⟩, hV.2⟩
    have hCmem : C ∈ members := ⟨Or.inl hC𝒱, hxC⟩
    rw [← Set.encard_sdiff_add_encard_of_subset
      (Set.singleton_subset_iff.mpr hCmem), Set.encard_singleton,
      ← one_add_one_eq_two]
    calc
      (members \ {C}).encard + 1 ≤ 1 + 1 :=
        add_le_add_left (Set.encard_le_one_iff_subsingleton.mpr hnonconnector) 1
      _ = (2 : ℕ∞) := by norm_num
  · -- Away from the connector, cross-disjointness forces all members through `x`
    -- to come from just one of the two original families.
    by_cases hleft : ∃ V ∈ 𝒱, x ∈ V
    · obtain ⟨V, hV𝒱, hxV⟩ := hleft
      have hsub : members ⊆ {U ∈ 𝒱 | x ∈ U} := by
        intro U hU
        refine ⟨?_, hU.2⟩
        rcases hU.1 with hU𝒱 | hU𝒲
        · exact hU𝒱
        · by_contra hU𝒱'
          have hVC : V ≠ C := fun h ↦ hxC (h ▸ hxV)
          have hUC : U ≠ C := fun h ↦ hxC (h ▸ hU.2)
          exact Set.disjoint_left.mp
            (hcross V ⟨hV𝒱, by simpa⟩ U ⟨hU𝒲, by simpa⟩) hxV hU.2
      exact (Set.encard_le_encard hsub).trans (Set.hasOrderLE_iff.mp h𝒱 x)
    · have hsub : members ⊆ {U ∈ 𝒲 | x ∈ U} := by
        intro U hU
        refine ⟨?_, hU.2⟩
        rcases hU.1 with hU𝒱 | hU𝒲
        · exact (hleft ⟨U, hU𝒱, hU.2⟩).elim
        · exact hU𝒲
      exact (Set.encard_le_encard hsub).trans (Set.hasOrderLE_iff.mp h𝒲 x)

/-- Helper for Exercise 50.3: indexed data for an anchored interval-chain
refinement of a real ray. -/
structure AnchoredIntervalChain (𝒜 : Set (Set ℝ)) (a : ℝ) (C : Set ℝ) where
  /-- The successive right endpoints of the chain. -/
  endpoint : ℕ → ℝ
  /-- The open members represented by the chain indices. -/
  member : ℕ → Set ℝ
  endpoint_zero : endpoint 0 = a
  endpoint_strictMono : StrictMono endpoint
  endpoint_tendsto : Filter.Tendsto endpoint Filter.atTop Filter.atTop
  member_zero : member 0 = C
  member_open : ∀ n, IsOpen (member n)
  member_refines : ∀ n, ∃ A ∈ 𝒜, member n ⊆ A
  ray_covered : Set.Ici a ⊆ ⋃₀ Set.range member
  nonzero_support : ∀ n ≠ 0, member n ⊆ Set.Ioi a
  index_order_two : ∀ x, Set.encard {n | x ∈ member n} ≤ 2

namespace AnchoredIntervalChain

/-- Helper for Exercise 50.3: the set-family represented by an anchored interval
chain. -/
def family {𝒜 : Set (Set ℝ)} {a : ℝ} {C : Set ℝ}
    (chain : AnchoredIntervalChain 𝒜 a C) : Set (Set ℝ) :=
  Set.range chain.member

/-- Helper for Exercise 50.3: the connector is the zeroth member of the represented
family. -/
lemma connector_mem {𝒜 : Set (Set ℝ)} {a : ℝ} {C : Set ℝ}
    (chain : AnchoredIntervalChain 𝒜 a C) : C ∈ chain.family := by
  -- Use the zeroth chain index and its anchoring equation.
  exact ⟨0, chain.member_zero⟩

/-- Helper for Exercise 50.3: the represented family is an open refinement of the
parent cover. -/
lemma family_isOpenRefinement {𝒜 : Set (Set ℝ)} {a : ℝ} {C : Set ℝ}
    (chain : AnchoredIntervalChain 𝒜 a C) : IsOpenRefinement chain.family 𝒜 := by
  -- Read openness and parent subordination directly from the indexed data.
  rw [isOpenRefinement_iff, isRefinement_iff]
  constructor
  · rintro U ⟨n, rfl⟩
    exact chain.member_refines n
  · rintro U ⟨n, rfl⟩
    exact chain.member_open n

/-- Helper for Exercise 50.3: the represented family covers the anchored real ray. -/
lemma ray_subset_sUnion_family {𝒜 : Set (Set ℝ)} {a : ℝ} {C : Set ℝ}
    (chain : AnchoredIntervalChain 𝒜 a C) : Set.Ici a ⊆ ⋃₀ chain.family := by
  -- The family definition is exactly the range used by the stored coverage field.
  exact chain.ray_covered

/-- Helper for Exercise 50.3: every nonconnector chain member lies strictly to the
right of the anchor. -/
lemma nonconnector_subset_Ioi {𝒜 : Set (Set ℝ)} {a : ℝ} {C : Set ℝ}
    (chain : AnchoredIntervalChain 𝒜 a C) :
    ∀ U ∈ chain.family \ {C}, U ⊆ Set.Ioi a := by
  -- A nonconnector member cannot have index zero, so the support invariant applies.
  rintro U ⟨⟨n, rfl⟩, hnC⟩
  apply chain.nonzero_support n
  intro hn
  subst n
  exact hnC chain.member_zero

/-- Helper for Exercise 50.3: the represented family has multiplicity at most two. -/
lemma family_hasOrderLE_two {𝒜 : Set (Set ℝ)} {a : ℝ} {C : Set ℝ}
    (chain : AnchoredIntervalChain 𝒜 a C) : chain.family.HasOrderLE 2 := by
  -- Members containing a point are the image of the chain indices containing it.
  rw [Set.hasOrderLE_iff]
  intro x
  have hmembers :
      {U ∈ chain.family | x ∈ U} =
        chain.member '' {n | x ∈ chain.member n} := by
    ext U
    constructor
    · rintro ⟨⟨n, rfl⟩, hx⟩
      exact ⟨n, hx, rfl⟩
    · rintro ⟨n, hx, rfl⟩
      exact ⟨⟨n, rfl⟩, hx⟩
  rw [hmembers]
  exact (Set.encard_image_le _ _).trans (chain.index_order_two x)

/-- Helper for Exercise 50.3: the family-level specification follows from the
indexed interval-chain invariants. -/
lemma family_spec {𝒜 : Set (Set ℝ)} {a : ℝ} {C : Set ℝ}
    (chain : AnchoredIntervalChain 𝒜 a C) :
    C ∈ chain.family ∧ IsOpenRefinement chain.family 𝒜 ∧
      chain.family.HasOrderLE 2 ∧ Set.Ici a ⊆ ⋃₀ chain.family ∧
      ∀ U ∈ chain.family \ {C}, U ⊆ Set.Ioi a := by
  -- Assemble the independent family projections for later transport to the graph.
  exact ⟨chain.connector_mem, chain.family_isOpenRefinement,
    chain.family_hasOrderLE_two, chain.ray_subset_sUnion_family,
    chain.nonconnector_subset_Ioi⟩

end AnchoredIntervalChain

/-- Helper for Exercise 50.3: every open cover has an order-two open refinement
covering the limiting vertical interval. -/
lemma existsVerticalOpenRefinementOrderTwo
    (𝒜 : Set (Set Space)) (h𝒜_open : ∀ U ∈ 𝒜, IsOpen U)
    (h𝒜_cover : ⋃₀ 𝒜 = Set.univ) :
    ∃ 𝒯 : Set (Set Space), IsOpenRefinement 𝒯 𝒜 ∧ 𝒯.HasOrderLE 2 ∧
      {p | p.1.1 = 0} ⊆ ⋃₀ 𝒯 := by
  -- Pull the cover back to the vertical interval and refine it there.
  classical
  let verticalMap : Set.Icc (-1 : ℝ) 1 → Space := fun y ↦
    ⟨(0, y), verticalPoint_mem_carrier y.property⟩
  have hverticalMap_continuous : Continuous verticalMap := by
    rw [Topology.IsInducing.subtypeVal.continuous_iff]
    exact continuous_const.prodMk continuous_subtype_val
  let pulledCover : Set (Set (Set.Icc (-1 : ℝ) 1)) :=
    (fun U : Set Space ↦ verticalMap ⁻¹' U) '' 𝒜
  have hpulled_open : ∀ U ∈ pulledCover, IsOpen U := by
    rintro U ⟨A, hA, rfl⟩
    exact (h𝒜_open A hA).preimage hverticalMap_continuous
  have hpulled_cover : ⋃₀ pulledCover = Set.univ := by
    ext y
    constructor
    · intro _
      exact Set.mem_univ y
    · intro _
      have hy : verticalMap y ∈ ⋃₀ 𝒜 := by
        rw [h𝒜_cover]
        exact Set.mem_univ _
      obtain ⟨A, hA, hyA⟩ := hy
      exact ⟨verticalMap ⁻¹' A, ⟨A, hA, rfl⟩, hyA⟩
  obtain ⟨𝓡, h𝓡_refines, h𝓡_cover, h𝓡_order⟩ :=
    Set.real_hasCoveringDimensionLE_one (Set.Icc (-1 : ℝ) 1)
      pulledCover hpulled_open hpulled_cover
  -- Choose a parent cover member for each interval-refinement member, and lift
  -- it by the second-coordinate projection.
  have hparent_exists (i : 𝓡) :
      ∃ A ∈ 𝒜, (i.1 : Set (Set.Icc (-1 : ℝ) 1)) ⊆ verticalMap ⁻¹' A := by
    obtain ⟨B, hB, hiB⟩ := h𝓡_refines.subset_of_mem i.property
    obtain ⟨A, hA, rfl⟩ := hB
    exact ⟨A, hA, hiB⟩
  let parent : 𝓡 → Set Space := fun i ↦ Classical.choose (hparent_exists i)
  have hparent_mem (i : 𝓡) : parent i ∈ 𝒜 :=
    (Classical.choose_spec (hparent_exists i)).1
  have hinterval_subset_parent (i : 𝓡) :
      (i.1 : Set (Set.Icc (-1 : ℝ) 1)) ⊆ verticalMap ⁻¹' parent i :=
    (Classical.choose_spec (hparent_exists i)).2
  let lifted : 𝓡 → Set Space := fun i ↦ verticalCoord ⁻¹' i.1 ∩ parent i
  have hlifted_open (i : 𝓡) : IsOpen (lifted i) := by
    exact ((h𝓡_refines.isOpen_of_mem i.property).preimage continuous_verticalCoord).inter
      (h𝒜_open (parent i) (hparent_mem i))
  have hlifted_subset_parent (i : 𝓡) : lifted i ⊆ parent i := by
    intro p hp
    exact hp.2
  have hlifted_index_order (p : Space) :
      Set.encard {i : 𝓡 | p ∈ lifted i} ≤ 2 := by
    calc
      Set.encard {i : 𝓡 | p ∈ lifted i} ≤
          Set.encard {R ∈ 𝓡 | verticalCoord p ∈ R} := by
        apply Set.encard_le_encard_of_injOn
        · intro i hi
          exact ⟨i.property, hi.1⟩
        · intro i _ j _ hij
          exact Subtype.ext hij
      _ ≤ 2 := Set.hasOrderLE_iff.mp h𝓡_order (verticalCoord p)
  have hlifted_order : (Set.range lifted).HasOrderLE 2 := by
    simpa only [Set.image_univ] using
      imageFamily_hasOrderLE_of_fiber lifted Set.univ 2 fun p ↦ by
        simp only [Set.mem_univ, true_and]
        norm_num
        exact hlifted_index_order p
  refine ⟨Set.range lifted, ?_, hlifted_order, ?_⟩
  · -- Every lifted member is open and remains inside its chosen parent.
    rw [isOpenRefinement_iff, isRefinement_iff]
    constructor
    · rintro U ⟨i, rfl⟩
      exact ⟨parent i, hparent_mem i, hlifted_subset_parent i⟩
    · rintro U ⟨i, rfl⟩
      exact hlifted_open i
  · -- A vertical point is the image of its second coordinate, so interval
    -- coverage lifts back to coverage by the constructed family.
    intro p hp
    have hvertical_eq : verticalMap (verticalCoord p) = p := by
      apply Subtype.ext
      apply Prod.ext
      · simpa only [verticalMap, verticalCoord] using hp.symm
      · rfl
    have hcoord_cover : verticalCoord p ∈ ⋃₀ 𝓡 := by
      rw [h𝓡_cover]
      exact Set.mem_univ _
    obtain ⟨R, hR, hpR⟩ := hcoord_cover
    let i : 𝓡 := ⟨R, hR⟩
    have hp_parent : p ∈ parent i := by
      rw [← hvertical_eq]
      exact hinterval_subset_parent i hpR
    exact ⟨lifted i, ⟨i, rfl⟩, hpR, hp_parent⟩

/-- Helper for Exercise 50.3: an arbitrary open cover admits an anchored order-two
refinement of a neighborhood of the limiting vertical interval. -/
lemma exists_nearVertical_anchoredRefinement
    (𝒜 : Set (Set Space)) (h𝒜_open : ∀ U ∈ 𝒜, IsOpen U)
    (h𝒜_cover : ⋃₀ 𝒜 = Set.univ) :
    ∃ (a b : ℝ) (C : Set Space) (𝒱 : Set (Set Space)),
      0 < a ∧ a < b ∧ C ∈ 𝒱 ∧ IsOpenRefinement 𝒱 𝒜 ∧
        𝒱.HasOrderLE 2 ∧ {p | p.1.1 ≤ a} ⊆ ⋃₀ 𝒱 ∧
        (∀ V ∈ 𝒱 \ {C}, V ⊆ {p | p.1.1 < a}) ∧
        {p | a ≤ p.1.1 ∧ p.1.1 < b} ⊆ C ∧
        C ⊆ {p | p.1.1 < b} := by
  -- Route correction: the connector must retain the vertical point in its anchor
  -- member, so only the upper first-coordinate bound is imposed on it.
  classical
  obtain ⟨𝒯, h𝒯_refines, h𝒯_order, h𝒯_vertical⟩ :=
    existsVerticalOpenRefinementOrderTwo 𝒜 h𝒜_open h𝒜_cover
  -- Compactness of the vertical interval gives a uniform strip covered by `𝒯`.
  let verticalMap : Set.Icc (-1 : ℝ) 1 → Space := fun y ↦
    ⟨(0, y), verticalPoint_mem_carrier y.property⟩
  have hverticalMap_continuous : Continuous verticalMap := by
    rw [Topology.IsInducing.subtypeVal.continuous_iff]
    exact continuous_const.prodMk continuous_subtype_val
  have hvertical_range : Set.range verticalMap = {p : Space | p.1.1 = 0} := by
    ext p
    constructor
    · rintro ⟨y, rfl⟩
      rfl
    · intro hp
      refine ⟨verticalCoord p, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · simpa only [verticalMap, verticalCoord] using hp.symm
      · rfl
  have hvertical_compact : IsCompact {p : Space | p.1.1 = 0} := by
    rw [← hvertical_range]
    simpa only [Set.image_univ] using
      (isCompact_univ.image hverticalMap_continuous)
  have h𝒯_union_open : IsOpen (⋃₀ 𝒯) :=
    isOpen_sUnion fun U hU ↦ h𝒯_refines.isOpen_of_mem hU
  obtain ⟨δ, hδ, hδ_subset⟩ :=
    hvertical_compact.exists_thickening_subset_open h𝒯_union_open h𝒯_vertical
  -- Choose the member through the vertical origin and a reciprocal-π graph point
  -- inside it, still within the uniform strip.
  have hzero_interval : (0 : ℝ) ∈ Set.Icc (-1) 1 := by
    norm_num
  let origin : Space := ⟨(0, 0), verticalPoint_mem_carrier hzero_interval⟩
  have horigin_vertical : origin ∈ {p : Space | p.1.1 = 0} := by
    rfl
  obtain ⟨T₀, hT₀, horigin_T₀⟩ := h𝒯_vertical horigin_vertical
  have hT₀_open : IsOpen T₀ := h𝒯_refines.isOpen_of_mem hT₀
  have hparameter (n : ℕ) :
      1 / (((n + 1 : ℕ) : ℝ) * Real.pi) ∈ Set.Ioc (0 : ℝ) 1 := by
    have hden_pos : 0 < (((n + 1 : ℕ) : ℝ) * Real.pi) := by
      positivity
    constructor
    · exact one_div_pos.mpr hden_pos
    · have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by
        exact_mod_cast Nat.succ_pos n
      have hpi : (2 : ℝ) ≤ Real.pi := by
        linarith [Real.one_le_pi_div_two]
      apply (div_le_iff₀ hden_pos).2
      nlinarith
  have hsequence_carrier (n : ℕ) :
      (1 / (((n + 1 : ℕ) : ℝ) * Real.pi), 0) ∈ carrier := by
    have hgraph := graphPoint_mem_carrier (hparameter n)
    have hsin :
        Real.sin (1 / (1 / (((n + 1 : ℕ) : ℝ) * Real.pi))) = 0 := by
      simp only [one_div, inv_inv]
      simpa only using Real.sin_nat_mul_pi (n + 1)
    rwa [hsin] at hgraph
  let zeroGraphSequence : ℕ → Space := fun n ↦
    ⟨(1 / (((n + 1 : ℕ) : ℝ) * Real.pi), 0), hsequence_carrier n⟩
  have hfirst_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ 1 / (((n + 1 : ℕ) : ℝ) * Real.pi))
        Filter.atTop (𝓝 0) := by
    have hbase : Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1))
        Filter.atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    convert hbase.const_mul (1 / Real.pi) using 1
    · funext n
      simp only [Nat.cast_add, Nat.cast_one]
      field_simp
    · simp
  have hsequence_tendsto :
      Filter.Tendsto zeroGraphSequence Filter.atTop (𝓝 origin) := by
    rw [tendsto_subtype_rng]
    simpa only [zeroGraphSequence, origin] using
      hfirst_tendsto.prodMk_nhds tendsto_const_nhds
  have heventually_T₀ : ∀ᶠ n in Filter.atTop, zeroGraphSequence n ∈ T₀ :=
    hsequence_tendsto.eventually (hT₀_open.mem_nhds horigin_T₀)
  have heventually_delta :
      ∀ᶠ n in Filter.atTop, 1 / (((n + 1 : ℕ) : ℝ) * Real.pi) < δ :=
    (tendsto_order.1 hfirst_tendsto).2 δ hδ
  obtain ⟨n, hnT₀, hnδ⟩ := (heventually_T₀.and heventually_delta).exists
  let a : ℝ := 1 / (((n + 1 : ℕ) : ℝ) * Real.pi)
  have ha : 0 < a := (hparameter n).1
  have haδ : a < δ := hnδ
  -- Use an ambient representative of `T₀` to obtain a right-hand graph interval
  -- lying in the distinguished member.
  obtain ⟨O, hO_open, hO_preimage⟩ :=
    Topology.IsInducing.subtypeVal.isOpen_iff.mp hT₀_open
  have hzeroGraph_O : (zeroGraphSequence n).1 ∈ O := by
    have hz : zeroGraphSequence n ∈ Subtype.val ⁻¹' O := by
      rw [hO_preimage]
      exact hnT₀
    exact hz
  have hsin_a : Real.sin (1 / a) = 0 := by
    dsimp [a]
    simp only [one_div, inv_inv]
    simpa only using Real.sin_nat_mul_pi (n + 1)
  have hgraph_a_O : (a, Real.sin (1 / a)) ∈ O := by
    simpa only [zeroGraphSequence, a, hsin_a] using hzeroGraph_O
  have hgraph_continuousAt :
      ContinuousAt (fun x : ℝ ↦ (x, Real.sin (1 / x))) a := by
    have ha_ne : a ≠ 0 := ne_of_gt ha
    exact continuousAt_id.prodMk
      (Real.continuous_sin.continuousAt.comp
        (continuousAt_const.div₀ continuousAt_id ha_ne))
  have hgraph_preimage_nhds :
      (fun x : ℝ ↦ (x, Real.sin (1 / x))) ⁻¹' O ∈ 𝓝 a :=
    hgraph_continuousAt (hO_open.mem_nhds hgraph_a_O)
  obtain ⟨l, u, ⟨hla, hau⟩, hlu⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp hgraph_preimage_nhds
  let b : ℝ := (a + u) / 2
  have hab : a < b := by
    dsimp [b]
    linarith
  have hbu : b < u := by
    dsimp [b]
    linarith
  let C : Set Space := T₀ ∩ {p | p.1.1 < b}
  have hC_open : IsOpen C := by
    exact hT₀_open.inter
      (isOpen_lt (continuous_fst.comp continuous_subtype_val) continuous_const)
  have hband : {p : Space | a ≤ p.1.1 ∧ p.1.1 < b} ⊆ C := by
    intro p hp
    have hp_pos : 0 < p.1.1 := ha.trans_le hp.1
    have hp_graph := eq_graphPoint_of_fst_pos p hp_pos
    have hp_interval : p.1.1 ∈ Set.Ioo l u :=
      ⟨hla.trans_le hp.1, hp.2.trans hbu⟩
    have hp_O : p.1 ∈ O := by
      rw [hp_graph]
      exact hlu hp_interval
    have hp_T₀ : p ∈ T₀ := by
      rw [← hO_preimage]
      exact hp_O
    exact ⟨hp_T₀, hp.2⟩
  let i₀ : 𝒯 := ⟨T₀, hT₀⟩
  let nearMember : 𝒯 → Set Space := fun i ↦
    if i = i₀ then C else i.1 ∩ {p | p.1.1 < a}
  let 𝒱 : Set (Set Space) := Set.range nearMember
  have hnear_subset_original (i : 𝒯) : nearMember i ⊆ i.1 := by
    by_cases hi : i = i₀
    · simp only [nearMember, hi, if_pos]
      exact Set.inter_subset_left
    · simp only [nearMember, hi, if_false]
      exact Set.inter_subset_left
  have hnear_open (i : 𝒯) : IsOpen (nearMember i) := by
    by_cases hi : i = i₀
    · simpa only [nearMember, hi, if_pos] using hC_open
    · simp only [nearMember, hi, if_false]
      exact (h𝒯_refines.isOpen_of_mem i.property).inter
        (isOpen_lt (continuous_fst.comp continuous_subtype_val) continuous_const)
  have hnear_order : 𝒱.HasOrderLE 2 := by
    have hfiber (p : Space) : Set.encard {i : 𝒯 | p ∈ nearMember i} ≤ 2 := by
      calc
        Set.encard {i : 𝒯 | p ∈ nearMember i} ≤
            Set.encard {U ∈ 𝒯 | p ∈ U} := by
          apply Set.encard_le_encard_of_injOn
          · intro i hi
            exact ⟨i.property, hnear_subset_original i hi⟩
          · intro i _ j _ hij
            exact Subtype.ext hij
        _ ≤ 2 := Set.hasOrderLE_iff.mp h𝒯_order p
    simpa only [𝒱, Set.image_univ] using
      imageFamily_hasOrderLE_of_fiber nearMember Set.univ 2 fun p ↦ by
        simp only [Set.mem_univ, true_and]
        norm_num
        exact hfiber p
  have hC_mem : C ∈ 𝒱 := by
    refine ⟨i₀, ?_⟩
    simp only [nearMember, if_pos]
  have h𝒱_refines : IsOpenRefinement 𝒱 𝒜 := by
    rw [isOpenRefinement_iff, isRefinement_iff]
    constructor
    · rintro V ⟨i, rfl⟩
      obtain ⟨A, hA, hiA⟩ := h𝒯_refines.subset_of_mem i.property
      exact ⟨A, hA, (hnear_subset_original i).trans hiA⟩
    · rintro V ⟨i, rfl⟩
      exact hnear_open i
  have hstrip_cover : {p : Space | p.1.1 ≤ a} ⊆ ⋃₀ 𝒱 := by
    intro p hp
    by_cases hpa : p.1.1 = a
    · exact ⟨C, hC_mem, hband ⟨hpa.ge, hpa ▸ hab⟩⟩
    · have hp_lt_a : p.1.1 < a := lt_of_le_of_ne hp hpa
      have hvertical_point : ((⟨(0, p.1.2), verticalPoint_mem_carrier
          (snd_mem_unitInterval p)⟩ : Space)) ∈ {q : Space | q.1.1 = 0} := by
        rfl
      let q : Space :=
        ⟨(0, p.1.2), verticalPoint_mem_carrier (snd_mem_unitInterval p)⟩
      have hp_distance : dist p q < δ := by
        have hdist : dist p q = p.1.1 := by
          rw [Subtype.dist_eq, Prod.dist_eq]
          simp only [q, Real.dist_eq, sub_zero, abs_of_nonneg (fst_nonneg p),
            sub_self, abs_zero]
          exact max_eq_left (fst_nonneg p)
        rw [hdist]
        exact hp_lt_a.trans haδ
      have hp_thickening : p ∈ Metric.thickening δ {q : Space | q.1.1 = 0} :=
        Metric.mem_thickening_iff.mpr ⟨q, hvertical_point, hp_distance⟩
      obtain ⟨T, hT, hpT⟩ := hδ_subset hp_thickening
      let i : 𝒯 := ⟨T, hT⟩
      by_cases hi : i = i₀
      · have hpT₀ : p ∈ T₀ := by
          have hTT₀ : T = T₀ := by
            simpa only [i, i₀] using congrArg Subtype.val hi
          rwa [hTT₀] at hpT
        have hpC : p ∈ C := ⟨hpT₀, hp_lt_a.trans hab⟩
        exact ⟨C, hC_mem, hpC⟩
      · have hp_near : p ∈ nearMember i := by
          simp only [nearMember, hi, if_false]
          exact ⟨hpT, hp_lt_a⟩
        exact ⟨nearMember i, ⟨i, rfl⟩, hp_near⟩
  have hnear_support : ∀ V ∈ 𝒱 \ {C}, V ⊆ {p | p.1.1 < a} := by
    rintro V ⟨⟨i, rfl⟩, hiC⟩
    by_cases hi : i = i₀
    · subst i
      have hnear_eq : nearMember i₀ = C := by
        simp only [nearMember, if_pos]
      have hnear_mem : nearMember i₀ ∈ ({C} : Set (Set Space)) := by
        rw [hnear_eq]
        exact Set.mem_singleton C
      exact (hiC hnear_mem).elim
    · simp only [nearMember, hi, if_false]
      exact Set.inter_subset_right
  have hC_bounded : C ⊆ {p : Space | p.1.1 < b} := Set.inter_subset_right
  exact ⟨a, b, C, 𝒱, ha, hab, hC_mem, h𝒱_refines, hnear_order,
    hstrip_cover, hnear_support, hband, hC_bounded⟩

/-- Helper for Exercise 50.3: an anchored connector extends to an order-two
refinement of the positive graph tail. -/
lemma exists_graphTail_anchoredRefinement
    (𝒜 : Set (Set Space)) (h𝒜_open : ∀ U ∈ 𝒜, IsOpen U)
    (h𝒜_cover : ⋃₀ 𝒜 = Set.univ) (a b : ℝ) (C : Set Space)
    (ha : 0 < a) (hab : a < b) (hC_open : IsOpen C)
    (hC_refines : ∃ A ∈ 𝒜, C ⊆ A)
    (hband : {p | a ≤ p.1.1 ∧ p.1.1 < b} ⊆ C)
    (hC_bounded : C ⊆ {p | p.1.1 < b}) :
    ∃ 𝒲 : Set (Set Space), C ∈ 𝒲 ∧ IsOpenRefinement 𝒲 𝒜 ∧
      𝒲.HasOrderLE 2 ∧ {p | a ≤ p.1.1} ⊆ ⋃₀ 𝒲 ∧
      ∀ W ∈ 𝒲 \ {C}, W ⊆ {p | a < p.1.1} := by
  -- Route correction: separate the trivial tail beyond the carrier bound before
  -- invoking any compact interval refinement on the remaining interval `[b, 1]`.
  by_cases h1b : 1 < b
  · -- When `b` lies past the carrier, the connector already covers the whole tail.
    refine ⟨{C}, Set.mem_singleton C,
      singleton_isOpenRefinement hC_open hC_refines,
      singleton_hasOrderLE_two C, ?_, ?_⟩
    · intro p hp
      refine ⟨C, Set.mem_singleton C, hband ⟨hp, ?_⟩⟩
      exact (fst_le_one p).trans_lt h1b
    · intro W hW
      exact (hW.2 hW.1).elim
  · -- Pull the cover back to `[b, 1]` along the graph parametrization.
    classical
    have hb1 : b ≤ 1 := le_of_not_gt h1b
    have hb : 0 < b := ha.trans hab
    have hgraph_parameter (x : Set.Icc b (1 : ℝ)) :
        (x : ℝ) ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨hb.trans_le x.property.1, x.property.2⟩
    let graphMap : Set.Icc b (1 : ℝ) → Space := fun x ↦
      ⟨((x : ℝ), Real.sin (1 / (x : ℝ))),
        graphPoint_mem_carrier (hgraph_parameter x)⟩
    have hgraphMap_continuous : Continuous graphMap := by
      rw [Topology.IsInducing.subtypeVal.continuous_iff]
      have hnonzero (x : Set.Icc b (1 : ℝ)) : (x : ℝ) ≠ 0 :=
        ne_of_gt (hb.trans_le x.property.1)
      exact continuous_subtype_val.prodMk
        (Real.continuous_sin.comp
          (continuous_const.div continuous_subtype_val hnonzero))
    let pulledCover : Set (Set (Set.Icc b (1 : ℝ))) :=
      (fun A : Set Space ↦ graphMap ⁻¹' A) '' 𝒜
    have hpulled_open : ∀ U ∈ pulledCover, IsOpen U := by
      rintro U ⟨A, hA, rfl⟩
      exact (h𝒜_open A hA).preimage hgraphMap_continuous
    have hpulled_cover : ⋃₀ pulledCover = Set.univ := by
      ext x
      constructor
      · intro _
        exact Set.mem_univ x
      · intro _
        have hx : graphMap x ∈ ⋃₀ 𝒜 := by
          rw [h𝒜_cover]
          exact Set.mem_univ _
        obtain ⟨A, hA, hxA⟩ := hx
        exact ⟨graphMap ⁻¹' A, ⟨A, hA, rfl⟩, hxA⟩
    obtain ⟨𝓡, h𝓡_refines, h𝓡_cover, h𝓡_order⟩ :=
      Set.real_hasCoveringDimensionLE_one (Set.Icc b (1 : ℝ))
        pulledCover hpulled_open hpulled_cover
    -- Choose both a cover parent and an ambient-open representative for every
    -- member of the relative interval refinement.
    have hparent_exists (i : 𝓡) :
        ∃ A ∈ 𝒜, (i.1 : Set (Set.Icc b (1 : ℝ))) ⊆ graphMap ⁻¹' A := by
      obtain ⟨B, hB, hiB⟩ := h𝓡_refines.subset_of_mem i.property
      obtain ⟨A, hA, rfl⟩ := hB
      exact ⟨A, hA, hiB⟩
    have hambient_exists (i : 𝓡) :
        ∃ O : Set ℝ, IsOpen O ∧
          ((fun x : Set.Icc b (1 : ℝ) ↦ (x : ℝ)) ⁻¹' O) = i.1 :=
      Topology.IsInducing.subtypeVal.isOpen_iff.mp
        (h𝓡_refines.isOpen_of_mem i.property)
    let parent : 𝓡 → Set Space := fun i ↦ Classical.choose (hparent_exists i)
    let ambient : 𝓡 → Set ℝ := fun i ↦ Classical.choose (hambient_exists i)
    have hparent_mem (i : 𝓡) : parent i ∈ 𝒜 :=
      (Classical.choose_spec (hparent_exists i)).1
    have hinterval_subset_parent (i : 𝓡) :
        (i.1 : Set (Set.Icc b (1 : ℝ))) ⊆ graphMap ⁻¹' parent i :=
      (Classical.choose_spec (hparent_exists i)).2
    have hambient_open (i : 𝓡) : IsOpen (ambient i) :=
      (Classical.choose_spec (hambient_exists i)).1
    have hambient_preimage (i : 𝓡) :
        (fun x : Set.Icc b (1 : ℝ) ↦ (x : ℝ)) ⁻¹' ambient i = i.1 :=
      (Classical.choose_spec (hambient_exists i)).2
    let leftEndpoint : Set.Icc b (1 : ℝ) := ⟨b, le_rfl, hb1⟩
    have hleft_covered : leftEndpoint ∈ ⋃₀ 𝓡 := by
      rw [h𝓡_cover]
      exact Set.mem_univ _
    obtain ⟨R₀, hR₀, hleft_R₀⟩ := hleft_covered
    let i₀ : 𝓡 := ⟨R₀, hR₀⟩
    let lifted : 𝓡 → Set Space := fun i ↦
      (parent i ∩ (fun p : Space ↦ p.1.1) ⁻¹' ambient i) ∩
        {p | (if i = i₀ then a else b) < p.1.1}
    have hlifted_open (i : 𝓡) : IsOpen (lifted i) := by
      exact ((h𝒜_open (parent i) (hparent_mem i)).inter
        ((hambient_open i).preimage
          (continuous_fst.comp continuous_subtype_val))).inter
        (isOpen_lt continuous_const
          (continuous_fst.comp continuous_subtype_val))
    have hlifted_subset_parent (i : 𝓡) : lifted i ⊆ parent i := by
      intro p hp
      exact hp.1.1
    have hgraphMap_mem_lifted (i : 𝓡) (x : Set.Icc b (1 : ℝ))
        (hxi : x ∈ i.1) (hcut : (if i = i₀ then a else b) < (x : ℝ)) :
        graphMap x ∈ lifted i := by
      have hx_parent : graphMap x ∈ parent i := hinterval_subset_parent i hxi
      have hx_ambient : (x : ℝ) ∈ ambient i := by
        have hx_preimage : x ∈
            (fun y : Set.Icc b (1 : ℝ) ↦ (y : ℝ)) ⁻¹' ambient i := by
          rw [hambient_preimage]
          exact hxi
        exact hx_preimage
      exact ⟨⟨hx_parent, hx_ambient⟩, hcut⟩
    let 𝒲 : Set (Set Space) := {C} ∪ Set.range lifted
    have hC_mem : C ∈ 𝒲 := Or.inl (Set.mem_singleton C)
    have h𝒲_refines : IsOpenRefinement 𝒲 𝒜 := by
      rw [isOpenRefinement_iff, isRefinement_iff]
      constructor
      · intro W hW
        rcases hW with hWC | ⟨i, rfl⟩
        · have hWC_eq : W = C := Set.mem_singleton_iff.mp hWC
          simpa only [hWC_eq] using hC_refines
        · exact ⟨parent i, hparent_mem i, hlifted_subset_parent i⟩
      · intro W hW
        rcases hW with hWC | ⟨i, rfl⟩
        · have hWC_eq : W = C := Set.mem_singleton_iff.mp hWC
          simpa only [hWC_eq] using hC_open
        · exact hlifted_open i
    -- Below `b` only the selected endpoint lift can occur; at and above `b`,
    -- interval-refinement multiplicity controls all lifted members.
    have h𝒲_order : 𝒲.HasOrderLE 2 := by
      rw [Set.hasOrderLE_iff]
      intro p
      by_cases hpb : p.1.1 < b
      · have hmembers_subset :
            {W ∈ 𝒲 | p ∈ W} ⊆ {C, lifted i₀} := by
          intro W hW
          rcases hW.1 with hWC | ⟨i, rfl⟩
          · exact Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hWC))
          · by_cases hi : i = i₀
            · exact Set.mem_insert_iff.mpr
                (Or.inr (Set.mem_singleton_iff.mpr (congrArg lifted hi)))
            · have hbi : b < p.1.1 := by
                simpa only [lifted, hi, if_false, Set.mem_setOf_eq] using hW.2.2
              exact (lt_asymm hbi hpb).elim
        calc
          Set.encard {W ∈ 𝒲 | p ∈ W} ≤ Set.encard ({C, lifted i₀} : Set (Set Space)) :=
            Set.encard_le_encard hmembers_subset
          _ ≤ 2 := by
            have hinsert := Set.encard_insert_le ({lifted i₀} : Set (Set Space)) C
            norm_num at hinsert ⊢
            exact hinsert
      · have hbp : b ≤ p.1.1 := le_of_not_gt hpb
        have hpC : p ∉ C := by
          intro hp
          exact hpb (hC_bounded hp)
        let x : Set.Icc b (1 : ℝ) := ⟨p.1.1, hbp, fst_le_one p⟩
        have hindex_order : Set.encard {i : 𝓡 | p ∈ lifted i} ≤ 2 := by
          calc
            Set.encard {i : 𝓡 | p ∈ lifted i} ≤
                Set.encard {R ∈ 𝓡 | x ∈ R} := by
              apply Set.encard_le_encard_of_injOn
              · intro i hi
                refine ⟨i.property, ?_⟩
                have hx_ambient : (x : ℝ) ∈ ambient i := hi.1.2
                have hx_preimage : x ∈
                    (fun y : Set.Icc b (1 : ℝ) ↦ (y : ℝ)) ⁻¹' ambient i :=
                  hx_ambient
                rw [hambient_preimage] at hx_preimage
                exact hx_preimage
              · intro i _ j _ hij
                exact Subtype.ext hij
            _ ≤ 2 := Set.hasOrderLE_iff.mp h𝓡_order x
        have hmembers :
            {W ∈ 𝒲 | p ∈ W} = lifted '' {i : 𝓡 | p ∈ lifted i} := by
          ext W
          constructor
          · intro hW
            rcases hW.1 with hWC | ⟨i, rfl⟩
            · have hWC_eq : W = C := Set.mem_singleton_iff.mp hWC
              exact (hpC (hWC_eq ▸ hW.2)).elim
            · exact ⟨i, hW.2, rfl⟩
          · rintro ⟨i, hpi, rfl⟩
            exact ⟨Or.inr ⟨i, rfl⟩, hpi⟩
        rw [hmembers]
        exact (Set.encard_image_le _ _).trans hindex_order
    have htail_cover : {p : Space | a ≤ p.1.1} ⊆ ⋃₀ 𝒲 := by
      intro p hp
      by_cases hpb : p.1.1 < b
      · exact ⟨C, hC_mem, hband ⟨hp, hpb⟩⟩
      · have hbp : b ≤ p.1.1 := le_of_not_gt hpb
        let x : Set.Icc b (1 : ℝ) := ⟨p.1.1, hbp, fst_le_one p⟩
        have hgraph_eq : graphMap x = p := by
          apply Subtype.ext
          exact (eq_graphPoint_of_fst_pos p (ha.trans_le hp)).symm
        by_cases hxb : p.1.1 = b
        · have hx_left : x = leftEndpoint := by
            apply Subtype.ext
            exact hxb
          have hx_R₀ : x ∈ i₀.1 := by
            simpa only [i₀, hx_left, leftEndpoint] using hleft_R₀
          have hcut : (if i₀ = i₀ then a else b) < (x : ℝ) := by
            simp only [if_pos]
            simpa only [x, hxb] using hab
          have hp_lifted : p ∈ lifted i₀ := by
            rw [← hgraph_eq]
            exact hgraphMap_mem_lifted i₀ x hx_R₀ hcut
          exact ⟨lifted i₀, Or.inr ⟨i₀, rfl⟩, hp_lifted⟩
        · have hx_cover : x ∈ ⋃₀ 𝓡 := by
            rw [h𝓡_cover]
            exact Set.mem_univ _
          obtain ⟨R, hR, hxR⟩ := hx_cover
          let i : 𝓡 := ⟨R, hR⟩
          have hbx : b < p.1.1 :=
            lt_of_le_of_ne hbp fun h ↦ hxb h.symm
          have hcut : (if i = i₀ then a else b) < (x : ℝ) := by
            by_cases hi : i = i₀
            · simp only [hi, if_pos, x]
              exact hab.trans_le hbp
            · simp only [hi, if_false, x]
              exact hbx
          have hp_lifted : p ∈ lifted i := by
            rw [← hgraph_eq]
            exact hgraphMap_mem_lifted i x hxR hcut
          exact ⟨lifted i, Or.inr ⟨i, rfl⟩, hp_lifted⟩
    have hlifted_support :
        ∀ W ∈ 𝒲 \ {C}, W ⊆ {p | a < p.1.1} := by
      intro W hW p hp
      rcases hW.1 with hWC | ⟨i, rfl⟩
      · exact (hW.2 hWC).elim
      · have hcut := hp.2
        by_cases hi : i = i₀
        · simpa only [lifted, hi, if_pos] using hcut
        · have hbp : b < p.1.1 := by
            simpa only [lifted, hi, if_false, Set.mem_setOf_eq] using hcut
          exact hab.trans hbp
    exact ⟨𝒲, hC_mem, h𝒲_refines, h𝒲_order, htail_cover, hlifted_support⟩

/-- Helper for Exercise 50.3: the topologist's sine curve has covering dimension at
most one. -/
lemma hasCoveringDimensionLE_one : HasCoveringDimensionLE Space 1 := by
  -- Split the space at a positive cutoff, using the same connector in both local chains.
  rw [hasCoveringDimensionLE_iff]
  intro 𝒜 h𝒜_open h𝒜_cover
  obtain ⟨a, b, C, 𝒱, ha, hab, hC𝒱, h𝒱_refines, h𝒱_order,
      h𝒱_cover, h𝒱_support, hband, hC_support⟩ :=
    exists_nearVertical_anchoredRefinement 𝒜 h𝒜_open h𝒜_cover
  have hC_open : IsOpen C := h𝒱_refines.isOpen_of_mem hC𝒱
  obtain ⟨A, hA𝒜, hCA⟩ := h𝒱_refines.subset_of_mem hC𝒱
  obtain ⟨𝒲, hC𝒲, h𝒲_refines, h𝒲_order, h𝒲_cover, h𝒲_support⟩ :=
    exists_graphTail_anchoredRefinement 𝒜 h𝒜_open h𝒜_cover a b C ha hab hC_open
      ⟨A, hA𝒜, hCA⟩ hband hC_support
  have hcross : ∀ V ∈ 𝒱 \ {C}, ∀ W ∈ 𝒲 \ {C}, Disjoint V W := by
    intro V hV W hW
    rw [Set.disjoint_left]
    intro p hpV hpW
    have hp_left := h𝒱_support V hV hpV
    have hp_right := h𝒲_support W hW hpW
    simp only [Set.mem_setOf_eq] at hp_left hp_right
    exact (not_lt_of_ge hp_right.le hp_left)
  refine ⟨𝒱 ∪ 𝒲, ?_, ?_, orderLE_union_of_sharedConnector
    h𝒱_order h𝒲_order hC𝒱 hC𝒲 hcross⟩
  · -- Refinement and openness are inherited from the two local families.
    rw [isOpenRefinement_iff, isRefinement_iff]
    constructor
    · intro U hU
      rcases hU with hU𝒱 | hU𝒲
      · exact h𝒱_refines.subset_of_mem hU𝒱
      · exact h𝒲_refines.subset_of_mem hU𝒲
    · intro U hU
      rcases hU with hU𝒱 | hU𝒲
      · exact h𝒱_refines.isOpen_of_mem hU𝒱
      · exact h𝒲_refines.isOpen_of_mem hU𝒲
  · -- Every point lies on the near-vertical side or on the graph-tail side.
    ext p
    constructor
    · intro _
      exact Set.mem_univ p
    · intro _
      by_cases hp : p.1.1 ≤ a
      · obtain ⟨V, hV𝒱, hpV⟩ := h𝒱_cover hp
        exact ⟨V, Or.inl hV𝒱, hpV⟩
      · obtain ⟨W, hW𝒲, hpW⟩ := h𝒲_cover (le_of_not_ge hp)
        exact ⟨W, Or.inr hW𝒲, hpW⟩

/-- Exercise 50.3. The topologist's sine curve has dimension one. -/
theorem coveringDimension_eq_one : dim Space = 1 := by
  -- The cover construction supplies the upper bound.
  apply le_antisymm
  · exact (coveringDimension_le_iff Space 1).mpr hasCoveringDimensionLE_one
  · -- Two explicit graph points make the connected `T1` space nontrivial.
    letI : Nontrivial Space :=
      ⟨⟨⟨(1 / 2, Real.sin (1 / (1 / 2))), middleGraphPoint_mem_carrier⟩,
        ⟨(1, Real.sin (1 / 1)), rightGraphPoint_mem_carrier⟩,
        middleGraphPoint_ne_rightGraphPoint⟩⟩
    exact ConnectedSpace.one_le_coveringDimension

end TopologistsSineCurve
