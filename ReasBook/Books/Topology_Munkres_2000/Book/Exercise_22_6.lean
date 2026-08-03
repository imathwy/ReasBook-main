module

public import Topology_Munkres_2000.Book.Exercise_22_6.RealKLine
public import Topology_Munkres_2000.Book.Lemma_13_4
public import Mathlib.Topology.Algebra.Module.Cardinality
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Separation.Hausdorff

public section

namespace RealKCollapse

/-- Helper for Exercise 22.6: the usual topology on the underlying real line. -/
abbrev standardRealTopology : TopologicalSpace ℝ :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- Helper for Exercise 22.6: the positive reciprocal subset of `RealKLine`. -/
def positiveReciprocalsSet : Set RealKLine :=
  {x | x ∈ RealTopology.positiveReciprocals}

/-- Helper for Exercise 22.6: membership in the `RealKLine` copy of the positive
reciprocal set agrees with membership in `RealTopology.positiveReciprocals`. -/
lemma mem_positiveReciprocalsSet (x : RealKLine) :
    x ∈ positiveReciprocalsSet ↔ x ∈ RealTopology.positiveReciprocals := by
  -- This is the defining membership condition of the carrier copy.
  rfl

/-- Two points of `RealKLine` are related when they are equal or both belong to
`RealTopology.positiveReciprocals`. -/
def rel (x y : RealKLine) : Prop :=
  x = y ∨
    (x ∈ RealTopology.positiveReciprocals ∧ y ∈ RealTopology.positiveReciprocals)

/-- Collapsing `RealTopology.positiveReciprocals` defines an equivalence relation on
`RealKLine`. -/
theorem rel_equivalence : Equivalence rel := by
  refine ⟨fun _ ↦ Or.inl rfl, ?_, ?_⟩
  · intro x y hxy
    rcases hxy with hxy | ⟨hx, hy⟩
    · exact Or.inl hxy.symm
    · exact Or.inr ⟨hy, hx⟩
  · intro x y z hxy hyz
    rcases hxy with hxy | ⟨hx, hy⟩
    · exact hxy ▸ hyz
    rcases hyz with hyz | ⟨_, hz⟩
    · exact hyz ▸ Or.inr ⟨hx, hy⟩
    · exact Or.inr ⟨hx, hz⟩

/-- The setoid on `RealKLine` that identifies all positive reciprocals with one another. -/
def setoid : Setoid RealKLine where
  r := rel
  iseqv := rel_equivalence

end RealKCollapse

/-- The quotient of `RealKLine` obtained by collapsing
`RealTopology.positiveReciprocals` to one point. -/
abbrev RealKCollapse := Quotient RealKCollapse.setoid

namespace RealKCollapse

/-- The canonical map from `RealKLine` to `RealKCollapse`. -/
def map : RealKLine → RealKCollapse :=
  Quotient.mk setoid

/-- The common quotient point represented by the positive reciprocal `1`. -/
def point : RealKCollapse :=
  map (1 : ℝ)

/-- Helper for Exercise 22.6: two representatives have the same image precisely when
they are equal or both lie in `RealTopology.positiveReciprocals`. -/
lemma map_eq_map_iff (x y : RealKLine) :
    map x = map y ↔
      x = y ∨
        (x ∈ RealTopology.positiveReciprocals ∧
          y ∈ RealTopology.positiveReciprocals) := by
  -- Quotient equality unfolds exactly to the defining collapse relation.
  rw [map, Quotient.eq]
  rfl

/-- A point maps to the collapsed point exactly when it is a positive reciprocal. -/
theorem map_eq_point_iff (x : RealKLine) :
    map x = point ↔ x ∈ RealTopology.positiveReciprocals := by
  -- The representative `1` belongs to the collapsed set.
  have hone : (1 : RealKLine) ∈ RealTopology.positiveReciprocals := by
    exact (RealTopology.mem_positiveReciprocals (1 : ℝ)).mpr
      ⟨1, by norm_num, by norm_num⟩
  -- The quotient equality computation reduces the claim to the two relation cases.
  rw [point, map_eq_map_iff]
  constructor
  · rintro (hx | ⟨hx, _⟩)
    · subst x
      exact hone
    · exact hx
  · intro hx
    exact Or.inr ⟨hx, hone⟩

/-- Helper for Exercise 22.6: the complement of the positive reciprocal set is the
union of deleted intervals of radius one. -/
lemma compl_positiveReciprocals_eq_iUnion_deletedIntervals :
    RealTopology.positiveReciprocalsᶜ =
      ⋃ c : ℝ, Set.Ioo (c - 1) (c + 1) \ RealTopology.positiveReciprocals := by
  -- Every point outside `K` lies in the deleted interval of radius one centered at itself.
  ext x
  constructor
  · intro hx
    have hleft : x - 1 < x := by
      linarith
    have hright : x < x + 1 := by
      linarith
    rw [Set.mem_iUnion]
    refine ⟨x, ?_⟩
    exact ⟨⟨hleft, hright⟩, hx⟩
  · intro hx
    obtain ⟨c, _, hxK⟩ := Set.mem_iUnion.mp hx
    exact hxK

/-- Helper for Exercise 22.6: the positive reciprocal set is closed in the `K`-topology. -/
lemma positiveReciprocalsClosed : IsClosed positiveReciprocalsSet := by
  -- Rewrite the complement as a union of deleted intervals from the generating family.
  apply isOpen_compl_iff.mp
  change @IsOpen ℝ RealTopology.k RealTopology.positiveReciprocalsᶜ
  rw [compl_positiveReciprocals_eq_iUnion_deletedIntervals,
    RealTopology.k_eq_generateFrom]
  letI : TopologicalSpace ℝ :=
    TopologicalSpace.generateFrom RealTopology.kBasis
  apply isOpen_iUnion
  intro c
  apply TopologicalSpace.isOpen_generateFrom_of_mem
  have hinterval : c - 1 < c + 1 := by
    linarith
  exact (RealTopology.mem_kBasis_iff _).mpr
    ⟨c - 1, c + 1, hinterval, Or.inr rfl⟩

/-- Helper for Exercise 22.6: a `K`-open neighborhood has a standard-open refinement
whose deletion of `RealTopology.positiveReciprocals` stays inside the neighborhood, and
whose whole set stays inside when the center belongs to the reciprocal set. -/
lemma exists_standardOpen_refinement_of_kOpen {u : Set ℝ}
    (hu : @IsOpen ℝ RealTopology.k u) {x : ℝ} (hx : x ∈ u) :
    ∃ v : Set ℝ, IsOpen v ∧ x ∈ v ∧
      v \ RealTopology.positiveReciprocals ⊆ u ∧
      (x ∈ RealTopology.positiveReciprocals → v ⊆ u) := by
  -- Route correction: use the exported generated-topology equation and carry both
  -- neighborhood refinements through one induction instead of unfolding the topology.
  rw [RealTopology.k_eq_generateFrom] at hu
  induction hu generalizing x with
  | basic s hs =>
      obtain ⟨a, b, hab, hs | hs⟩ := (RealTopology.mem_kBasis_iff s).mp hs
      · subst s
        refine ⟨Set.Ioo a b, isOpen_Ioo, hx, ?_, ?_⟩
        · intro z hz
          exact hz.1
        · intro _ z hz
          exact hz
      · subst s
        refine ⟨Set.Ioo a b, isOpen_Ioo, hx.1, ?_, ?_⟩
        · intro z hz
          exact hz
        · intro hxK
          exact False.elim (hx.2 hxK)
  | univ =>
      refine ⟨Set.univ, isOpen_univ, Set.mem_univ x, ?_, ?_⟩
      · intro z _
        exact Set.mem_univ z
      · intro _ z _
        exact Set.mem_univ z
  | inter s t _ _ hs ht =>
      obtain ⟨v, hvOpen, hxv, hvDiff, hv⟩ := hs hx.1
      obtain ⟨w, hwOpen, hxw, hwDiff, hw⟩ := ht hx.2
      refine ⟨v ∩ w, hvOpen.inter hwOpen, ⟨hxv, hxw⟩, ?_, ?_⟩
      · intro z hz
        exact ⟨hvDiff ⟨hz.1.1, hz.2⟩, hwDiff ⟨hz.1.2, hz.2⟩⟩
      · intro hxK z hz
        exact ⟨hv hxK hz.1, hw hxK hz.2⟩
  | sUnion S _ hS =>
      obtain ⟨s, hsS, hxs⟩ := Set.mem_sUnion.mp hx
      obtain ⟨v, hvOpen, hxv, hvDiff, hv⟩ := hS s hsS hxs
      refine ⟨v, hvOpen, hxv, ?_, ?_⟩
      · intro z hz
        exact Set.mem_sUnion_of_mem (hvDiff hz) hsS
      · intro hxK z hz
        exact Set.mem_sUnion_of_mem (hv hxK hz) hsS

/-- Helper for Exercise 22.6: every `K`-open neighborhood contains a standard-open
neighborhood after deleting `RealTopology.positiveReciprocals`. -/
lemma exists_standardOpen_sdiff_subset_of_kOpen {u : Set ℝ}
    (hu : @IsOpen ℝ RealTopology.k u) {x : ℝ} (hx : x ∈ u) :
    ∃ v : Set ℝ, IsOpen v ∧ x ∈ v ∧
      v \ RealTopology.positiveReciprocals ⊆ u := by
  -- Discard the stronger conditional conclusion from the combined refinement.
  obtain ⟨v, hvOpen, hxv, hvDiff, _⟩ :=
    exists_standardOpen_refinement_of_kOpen hu hx
  exact ⟨v, hvOpen, hxv, hvDiff⟩

/-- Helper for Exercise 22.6: at a point of `RealTopology.positiveReciprocals`, every
`K`-open neighborhood contains a standard-open neighborhood. -/
lemma exists_standardOpen_subset_of_kOpen_of_mem_positiveReciprocals {u : Set ℝ}
    (hu : @IsOpen ℝ RealTopology.k u) {x : ℝ}
    (hxK : x ∈ RealTopology.positiveReciprocals) (hx : x ∈ u) :
    ∃ v : Set ℝ, IsOpen v ∧ x ∈ v ∧ v ⊆ u := by
  -- Apply the stronger field of the combined refinement at a point of `K`.
  obtain ⟨v, hvOpen, hxv, _, hv⟩ :=
    exists_standardOpen_refinement_of_kOpen hu hx
  exact ⟨v, hvOpen, hxv, hv hxK⟩

/-- Helper for Exercise 22.6: `RealTopology.positiveReciprocals` is countable. -/
lemma positiveReciprocalsCountable : RealTopology.positiveReciprocals.Countable := by
  -- The set is contained in the range of the reciprocal map on positive naturals.
  refine (Set.countable_range fun n : {n : ℕ // 0 < n} ↦ ((n : ℕ) : ℝ)⁻¹).mono ?_
  intro x hx
  obtain ⟨n, hn, rfl⟩ := (RealTopology.mem_positiveReciprocals x).mp hx
  exact ⟨⟨n, hn⟩, rfl⟩

/-- Helper for Exercise 22.6: zero and the positive reciprocal set cannot be separated
by disjoint `K`-open sets. -/
lemma not_separated_zero_positiveReciprocals :
    ¬ ∃ u v : Set ℝ,
      @IsOpen ℝ RealTopology.k u ∧ @IsOpen ℝ RealTopology.k v ∧
        0 ∈ u ∧ RealTopology.positiveReciprocals ⊆ v ∧ Disjoint u v := by
  -- Standard-open refinements on both sides overlap outside the countable set `K`.
  rintro ⟨u, v, hu, hv, h0u, hKv, huv⟩
  obtain ⟨u₀, hu₀_open, h0u₀, hu₀⟩ :=
    exists_standardOpen_sdiff_subset_of_kOpen hu h0u
  obtain ⟨a, b, hab, habu⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hu₀_open.mem_nhds h0u₀)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hab.2
  let r : ℝ := 1 / (n + 1 : ℝ)
  have hr_pos : 0 < r := one_div_pos.mpr (by positivity)
  have hrK : r ∈ RealTopology.positiveReciprocals := by
    exact (RealTopology.mem_positiveReciprocals r).mpr
      ⟨n + 1, Nat.succ_pos n, by simp [r, one_div]⟩
  have hru₀ : r ∈ u₀ := habu ⟨hab.1.trans hr_pos, hn⟩
  obtain ⟨v₀, hv₀_open, hrv₀, hv₀⟩ :=
    exists_standardOpen_subset_of_kOpen_of_mem_positiveReciprocals hv hrK (hKv hrK)
  have hinter_nonempty : (u₀ ∩ v₀).Nonempty := ⟨r, hru₀, hrv₀⟩
  obtain ⟨z, hzK, hzu₀, hzv₀⟩ :=
    (positiveReciprocalsCountable.dense_compl ℝ).exists_mem_open
      (hu₀_open.inter hv₀_open) hinter_nonempty
  exact Set.disjoint_left.mp huv (hu₀ ⟨hzu₀, hzK⟩) (hv₀ hzv₀)

/-- The canonical collapse map is a quotient map. -/
theorem map_isQuotientMap : Topology.IsQuotientMap map :=
  isQuotientMap_quotient_mk'

/-- The product of the canonical collapse map with itself. -/
def productMap : RealKLine × RealKLine → RealKCollapse × RealKCollapse :=
  Prod.map map map

/-- Helper for Exercise 22.6: the quotient obtained by collapsing
`RealTopology.positiveReciprocals` in `RealKLine` is a `T₁` space. -/
instance instT1Space : T1Space RealKCollapse := by
  -- The finer `K`-topology inherits Hausdorffness from the standard real topology.
  letI : T2Space RealKLine :=
    @t2Space_antitone RealKLine RealKLine.instTopologicalSpace standardRealTopology
      RealTopology.k_lt_standard.le (inferInstance : @T2Space ℝ standardRealTopology)
  refine ⟨fun y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := Quotient.exists_rep y
  -- Each quotient fiber is either the closed set `K` or a closed singleton.
  apply map_isQuotientMap.isCoinducing.isClosed_preimage.mp
  by_cases hx : x ∈ RealTopology.positiveReciprocals
  · have hfiber : map ⁻¹' ({map x} : Set RealKCollapse) =
        positiveReciprocalsSet := by
      ext z
      rw [Set.mem_preimage, Set.mem_singleton_iff, map_eq_map_iff]
      constructor
      · rintro (hz | ⟨hz, _⟩)
        · exact (mem_positiveReciprocalsSet z).mpr (hz ▸ hx)
        · exact (mem_positiveReciprocalsSet z).mpr hz
      · intro hz
        exact Or.inr ⟨(mem_positiveReciprocalsSet z).mp hz, hx⟩
    change IsClosed (map ⁻¹' ({map x} : Set RealKCollapse))
    rw [hfiber]
    exact positiveReciprocalsClosed
  · have hfiber : map ⁻¹' ({map x} : Set RealKCollapse) = {x} := by
      ext z
      rw [Set.mem_preimage, Set.mem_singleton_iff, map_eq_map_iff]
      constructor
      · rintro (hz | ⟨_, hzx⟩)
        · exact hz
        · exact False.elim (hx hzx)
      · exact Or.inl
    change IsClosed (map ⁻¹' ({map x} : Set RealKCollapse))
    rw [hfiber]
    exact isClosed_singleton

/-- Helper for Exercise 22.6: the quotient obtained by collapsing
`RealTopology.positiveReciprocals` in `RealKLine` is not Hausdorff. -/
theorem not_t2Space : ¬ T2Space RealKCollapse := by
  -- A hypothetical Hausdorff separation of `map 0` and the collapsed point pulls back to
  -- a forbidden separation of zero from all positive reciprocals.
  intro hT2
  letI : T2Space RealKCollapse := hT2
  have hzero : (0 : ℝ) ∉ RealTopology.positiveReciprocals := by
    intro hzeroK
    obtain ⟨n, hn, hzero⟩ := (RealTopology.mem_positiveReciprocals 0).mp hzeroK
    have hnonzero : ((n : ℝ)⁻¹) ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))
    exact hnonzero hzero.symm
  have hne : map (0 : RealKLine) ≠ point := by
    intro h
    exact hzero ((map_eq_point_iff 0).mp h)
  obtain ⟨u, v, hu, hv, h0u, hpv, huv⟩ := t2_separation hne
  apply not_separated_zero_positiveReciprocals
  refine ⟨map ⁻¹' u, map ⁻¹' v, ?_, ?_, h0u, ?_, ?_⟩
  · exact hu.preimage map_isQuotientMap.continuous
  · exact hv.preimage map_isQuotientMap.continuous
  · intro x hx
    exact Set.mem_preimage.mpr ((map_eq_point_iff x).mpr hx ▸ hpv)
  · exact huv.preimage map

/-- Exercise 22.6: The product of the quotient map with itself is not a quotient map. -/
theorem not_isQuotientMap_productMap : ¬ Topology.IsQuotientMap productMap := by
  -- Normalize the pulled-back diagonal to the diagonal together with `K × K`.
  have hpreimage : productMap ⁻¹' Set.diagonal RealKCollapse =
      Set.diagonal RealKLine ∪
        (positiveReciprocalsSet ×ˢ positiveReciprocalsSet) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_prod]
    unfold productMap Prod.map
    rw [Set.mem_diagonal_iff]
    rw [map_eq_map_iff]
    constructor
    · rintro (hz | ⟨hz₁, hz₂⟩)
      · exact Or.inl hz
      · exact Or.inr ⟨(mem_positiveReciprocalsSet z.1).mpr hz₁,
          (mem_positiveReciprocalsSet z.2).mpr hz₂⟩
    · rintro (hz | ⟨hz₁, hz₂⟩)
      · exact Or.inl hz
      · exact Or.inr ⟨(mem_positiveReciprocalsSet z.1).mp hz₁,
          (mem_positiveReciprocalsSet z.2).mp hz₂⟩
  -- This normalized preimage is closed because `RealKLine` is Hausdorff and `K` is closed.
  letI : T2Space RealKLine :=
    @t2Space_antitone RealKLine RealKLine.instTopologicalSpace standardRealTopology
      RealTopology.k_lt_standard.le (inferInstance : @T2Space ℝ standardRealTopology)
  have hclosed : IsClosed (productMap ⁻¹' Set.diagonal RealKCollapse) := by
    rw [hpreimage]
    exact isClosed_diagonal.union (positiveReciprocalsClosed.prod positiveReciprocalsClosed)
  -- A quotient map would reflect this closedness to the diagonal, forcing Hausdorffness.
  intro hquotient
  have hdiagonal : IsClosed (Set.diagonal RealKCollapse) :=
    hquotient.isCoinducing.isClosed_preimage.mp hclosed
  exact not_t2Space (t2_iff_isClosed_diagonal.mpr hdiagonal)

end RealKCollapse


end
