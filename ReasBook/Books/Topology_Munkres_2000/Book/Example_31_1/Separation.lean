module

public import Topology_Munkres_2000.Book.Definition_13_3.RealLine
public import Mathlib.Topology.Separation.Regular

public section

namespace RealTopology

/-- The real line with the `K`-topology is Hausdorff. -/
instance kT2Space : @T2Space ℝ k := by
  -- Every ordinary interval is a `K`-generator, so `k` is finer than the standard topology.
  have hkStandard : k ≤ (inferInstance : TopologicalSpace ℝ) := by
    intro u hu
    have hInterval (x : ℝ) (hx : x ∈ u) :
        ∃ a b : ℝ, x ∈ Set.Ioo a b ∧ Set.Ioo a b ⊆ u :=
      mem_nhds_iff_exists_Ioo_subset.mp (hu.mem_nhds hx)
    letI : TopologicalSpace ℝ := k
    refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
    obtain ⟨a, b, hxab, habu⟩ := hInterval x hx
    refine ⟨Set.Ioo a b, habu, ?_, hxab⟩
    rw [k_eq_generateFrom]
    apply TopologicalSpace.isOpen_generateFrom_of_mem
    exact (mem_kBasis_iff _).mpr ⟨a, b, hxab.1.trans hxab.2, Or.inl rfl⟩
  -- Hausdorffness transfers from the standard topology to the finer topology.
  exact t2Space_antitone hkStandard inferInstance

/-- The positive reciprocal set is closed in the `K`-topology. -/
theorem positiveReciprocalsClosed :
    @IsClosed ℝ k positiveReciprocals := by
  -- Deleted intervals centered at a point outside `positiveReciprocals` cover its complement.
  letI : TopologicalSpace ℝ := k
  rw [← isOpen_compl_iff]
  refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
  refine ⟨Set.Ioo (x - 1) (x + 1) \ positiveReciprocals, ?_, ?_, ?_⟩
  · intro y hy
    exact hy.2
  · rw [k_eq_generateFrom]
    apply TopologicalSpace.isOpen_generateFrom_of_mem
    have hEndpoints : x - 1 < x + 1 := by
      linarith
    exact (mem_kBasis_iff _).mpr ⟨x - 1, x + 1, hEndpoints, Or.inr rfl⟩
  · have hxInterval : x ∈ Set.Ioo (x - 1) (x + 1) := by
      constructor
      · linarith
      · linarith
    exact ⟨hxInterval, hx⟩

/-- Zero does not belong to the positive reciprocal set. -/
theorem zeroNotMemPositiveReciprocals :
    (0 : ℝ) ∉ positiveReciprocals := by
  -- A positive natural has a nonzero cast, hence also a nonzero reciprocal.
  intro hzero
  obtain ⟨n, hn, hzero⟩ := (mem_positiveReciprocals 0).mp hzero
  have hnCast : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  exact (inv_ne_zero hnCast) hzero.symm

/-- Helper for Example 31.1: every `K`-open neighborhood admits an interval refinement
whose deletion by `positiveReciprocals` lies in the neighborhood, and whose whole interval
does so when its center is a positive reciprocal. -/
private lemma existsIntervalRefinementOfKOpen {u : Set ℝ} {x : ℝ}
    (hu : @IsOpen ℝ k u) (hxu : x ∈ u) :
    ∃ a b : ℝ, x ∈ Set.Ioo a b ∧
      Set.Ioo a b \ positiveReciprocals ⊆ u ∧
      (x ∈ positiveReciprocals → Set.Ioo a b ⊆ u) := by
  -- The claimed interval interface is preserved by every constructor of a generated open set.
  rw [k_eq_generateFrom] at hu
  induction hu generalizing x with
  | basic s hs =>
      obtain ⟨a, b, hab, rfl | rfl⟩ := (mem_kBasis_iff s).mp hs
      · refine ⟨a, b, hxu, ?_, ?_⟩
        · intro z hz
          exact hz.1
        · intro _ z hz
          exact hz
      · refine ⟨a, b, hxu.1, ?_, ?_⟩
        · intro z hz
          exact hz
        · intro hxK
          exact False.elim (hxu.2 hxK)
  | univ =>
      have hxInterval : x ∈ Set.Ioo (x - 1) (x + 1) := by
        constructor
        · linarith
        · linarith
      refine ⟨x - 1, x + 1, hxInterval, ?_, ?_⟩
      · intro z _
        exact Set.mem_univ z
      · intro _ z _
        exact Set.mem_univ z
  | inter s t _ _ hs ht =>
      obtain ⟨a, b, hxab, habDiff, hab⟩ := hs hxu.1
      obtain ⟨c, d, hxcd, hcdDiff, hcd⟩ := ht hxu.2
      refine ⟨max a c, min b d,
        ⟨max_lt hxab.1 hxcd.1, lt_min hxab.2 hxcd.2⟩, ?_, ?_⟩
      · intro z hz
        exact ⟨habDiff ⟨⟨(le_max_left _ _).trans_lt hz.1.1,
          hz.1.2.trans_le (min_le_left _ _)⟩, hz.2⟩,
          hcdDiff ⟨⟨(le_max_right _ _).trans_lt hz.1.1,
            hz.1.2.trans_le (min_le_right _ _)⟩, hz.2⟩⟩
      · intro hxK z hz
        exact ⟨hab hxK ⟨(le_max_left _ _).trans_lt hz.1,
          hz.2.trans_le (min_le_left _ _)⟩,
          hcd hxK ⟨(le_max_right _ _).trans_lt hz.1,
            hz.2.trans_le (min_le_right _ _)⟩⟩
  | sUnion S _ hS =>
      obtain ⟨s, hsS, hxs⟩ := Set.mem_sUnion.mp hxu
      obtain ⟨a, b, hxab, habDiff, hab⟩ := hS s hsS hxs
      refine ⟨a, b, hxab, ?_, ?_⟩
      · intro z hz
        exact Set.mem_sUnion_of_mem (habDiff hz) hsS
      · intro hxK z hz
        exact Set.mem_sUnion_of_mem (hab hxK hz) hsS

/-- Helper for Example 31.1: zero and `positiveReciprocals` have no disjoint
`K`-open neighborhoods. -/
lemma zeroAndPositiveReciprocalsNotSeparated :
    ¬ ∃ u v : Set ℝ, @IsOpen ℝ k u ∧ @IsOpen ℝ k v ∧
      0 ∈ u ∧ positiveReciprocals ⊆ v ∧ Disjoint u v := by
  -- Refine both alleged neighborhoods by ordinary intervals as in the source proof.
  rintro ⟨u, v, hu, hv, h0u, hKv, huv⟩
  obtain ⟨a, b, h0ab, habu, _⟩ := existsIntervalRefinementOfKOpen hu h0u
  obtain ⟨n, hn, hnInvLt⟩ := Real.exists_nat_pos_inv_lt h0ab.2
  have hnCastPos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnInvPos : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hnCastPos
  have hnInvMem : (n : ℝ)⁻¹ ∈ Set.Ioo a b :=
    ⟨h0ab.1.trans hnInvPos, hnInvLt⟩
  have hnK : (n : ℝ)⁻¹ ∈ positiveReciprocals :=
    (mem_positiveReciprocals _).mpr ⟨n, hn, rfl⟩
  obtain ⟨c, d, hncd, _, hcdv⟩ :=
    existsIntervalRefinementOfKOpen hv (hKv hnK)
  -- Consecutive reciprocal values leave a nonempty interval below `1 / n`.
  have hnSuccCastPos : 0 < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have hConsecutive : ((n + 1 : ℕ) : ℝ)⁻¹ < (n : ℝ)⁻¹ := by
    rw [inv_lt_inv₀ hnSuccCastPos hnCastPos]
    exact_mod_cast Nat.lt_succ_self n
  let z := (max c ((n + 1 : ℕ) : ℝ)⁻¹ + (n : ℝ)⁻¹) / 2
  have hzBounds : max c ((n + 1 : ℕ) : ℝ)⁻¹ < z ∧ z < (n : ℝ)⁻¹ := by
    dsimp [z]
    constructor
    · linarith [max_lt hncd.1 hConsecutive]
    · linarith [max_lt hncd.1 hConsecutive]
  -- No positive reciprocal lies strictly between two consecutive reciprocal values.
  have hzNotK : z ∉ positiveReciprocals := by
    intro hzK
    obtain ⟨m, hm, hzm⟩ := (mem_positiveReciprocals z).mp hzK
    have hmCastPos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
    have hnm : n < m := by
      have hInv : (m : ℝ)⁻¹ < (n : ℝ)⁻¹ := by
        rw [← hzm]
        exact hzBounds.2
      have hCast : (n : ℝ) < (m : ℝ) :=
        (inv_lt_inv₀ hmCastPos hnCastPos).mp hInv
      exact_mod_cast hCast
    have hmnSucc : m < n + 1 := by
      have hInv : ((n + 1 : ℕ) : ℝ)⁻¹ < (m : ℝ)⁻¹ := by
        rw [← hzm]
        exact (le_max_right c _).trans_lt hzBounds.1
      have hCast : (m : ℝ) < ((n + 1 : ℕ) : ℝ) :=
        (inv_lt_inv₀ hnSuccCastPos hmCastPos).mp hInv
      exact_mod_cast hCast
    omega
  -- The midpoint belongs to both alleged neighborhoods, contradicting disjointness.
  have hzu : z ∈ u := by
    apply habu
    refine ⟨⟨?_, hzBounds.2.trans hnInvMem.2⟩, hzNotK⟩
    exact h0ab.1.trans (inv_pos.mpr hnSuccCastPos) |>.trans
      ((le_max_right c _).trans_lt hzBounds.1)
  have hzv : z ∈ v := by
    apply hcdv hnK
    exact ⟨(le_max_left c _).trans_lt hzBounds.1, hzBounds.2.trans hncd.2⟩
  exact Set.disjoint_left.mp huv hzu hzv

end RealTopology
