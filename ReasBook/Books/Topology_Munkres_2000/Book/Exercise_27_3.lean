module

public import Topology_Munkres_2000.Book.Exercise_22_6.RealKLine
public import Topology_Munkres_2000.Book.Lemma_13_4
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.Instances.Nat
public import Mathlib.NumberTheory.Real.Irrational

public section

namespace RealKLine

open Set

/-- Helper for Exercise 27.3: every standard-open subset of `ℝ` is open in
`RealKLine`. -/
lemma isOpen_of_standard {u : Set ℝ} (hu : IsOpen u) :
    @IsOpen ℝ RealTopology.k u := by
  -- The `K`-topology is finer than the standard topology.
  exact RealTopology.k_lt_standard.le u hu


/-- Helper for Exercise 27.3: each positive reciprocal has a standard-open
interval containing no other positive reciprocal. -/
lemma exists_isOpen_reciprocal_isolating (n : ℕ) (hn : 0 < n) :
    ∃ u : Set ℝ, IsOpen u ∧ (n : ℝ)⁻¹ ∈ u ∧
      u ∩ RealTopology.positiveReciprocals = {(n : ℝ)⁻¹} := by
  -- Consecutive reciprocal values provide separating endpoints.
  let a : ℝ := ((n + 1 : ℕ) : ℝ)⁻¹
  let b : ℝ := if n = 1 then 2 else ((n - 1 : ℕ) : ℝ)⁻¹
  refine ⟨Ioo a b, isOpen_Ioo, ?_, ?_⟩
  · constructor
    · dsimp [a]
      rw [inv_lt_inv₀ (by positivity) (by positivity)]
      exact_mod_cast Nat.lt_succ_self n
    · dsimp [b]
      split_ifs with h
      · subst n
        norm_num
      · have hn1 : 1 < n := (Nat.one_lt_iff_ne_zero_and_ne_one).2 ⟨Nat.ne_of_gt hn, h⟩
        have hnsub : 0 < ((n - 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.sub_pos_of_lt hn1
        rw [inv_lt_inv₀ (by positivity) hnsub]
        exact_mod_cast Nat.sub_lt (Nat.zero_lt_of_lt hn1) (by omega)
  · ext x
    constructor
    · rintro ⟨hx, hrecipMem⟩
      obtain ⟨m, hm, rfl⟩ := (RealTopology.mem_positiveReciprocals x).mp hrecipMem
      have hmn : m ≤ n := by
        by_contra hle
        have hnm : n < m := Nat.lt_of_not_ge hle
        have hrecip : (m : ℝ)⁻¹ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by
          rw [inv_le_inv₀ (by positivity) (by positivity)]
          exact_mod_cast Nat.succ_le_iff.2 hnm
        exact (not_lt_of_ge hrecip) hx.1
      have hnm : n ≤ m := by
        by_contra hle
        have hmn' : m < n := Nat.lt_of_not_ge hle
        have hn1 : n ≠ 1 := by omega
        have hrecip : ((n - 1 : ℕ) : ℝ)⁻¹ ≤ (m : ℝ)⁻¹ := by
          have hnsub : 0 < ((n - 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.sub_pos_of_lt (by omega : 1 < n)
          rw [inv_le_inv₀ hnsub (by positivity)]
          exact_mod_cast (Nat.le_sub_one_iff_lt hn).2 hmn'
        dsimp [b] at hx
        rw [if_neg hn1] at hx
        exact (not_lt_of_ge hrecip) hx.2
      simp [Nat.le_antisymm hmn hnm]
    · intro hx
      have hxn : x = (n : ℝ)⁻¹ := by simpa using hx
      subst x
      refine ⟨?_, (RealTopology.mem_positiveReciprocals _).mpr ⟨n, hn, rfl⟩⟩
      constructor
      · dsimp [a]
        rw [inv_lt_inv₀ (by positivity) (by positivity)]
        exact_mod_cast Nat.lt_succ_self n
      · dsimp [b]
        split_ifs with h
        · subst n
          norm_num
        · have hn1 : 1 < n := (Nat.one_lt_iff_ne_zero_and_ne_one).2 ⟨Nat.ne_of_gt hn, h⟩
          have hnsub : 0 < ((n - 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.sub_pos_of_lt hn1
          rw [inv_lt_inv₀ (by positivity) hnsub]
          exact_mod_cast Nat.sub_lt (Nat.zero_lt_of_lt hn1) (by omega)

/-- Helper for Exercise 27.3: the positive reciprocal set is discrete in
`RealKLine`. -/
lemma positiveReciprocals_isDiscrete :
    @IsDiscrete ℝ RealTopology.k RealTopology.positiveReciprocals := by
  -- Use the isolating standard intervals, which remain open in the finer topology.
  letI : TopologicalSpace ℝ := RealTopology.k
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  obtain ⟨n, hn, rfl⟩ := (RealTopology.mem_positiveReciprocals x).mp hx
  obtain ⟨u, hu, hmem, hinter⟩ := exists_isOpen_reciprocal_isolating n hn
  exact ⟨u, isOpen_of_standard hu, hinter⟩

/-- Helper for Exercise 27.3: the positive reciprocal set is infinite. -/
lemma positiveReciprocals_infinite : RealTopology.positiveReciprocals.Infinite := by
  -- It contains the injective image of the positive natural numbers under inversion.
  let reciprocal : ℕ → ℝ := fun n ↦ ((n + 1 : ℕ) : ℝ)⁻¹
  have hinjective : Function.Injective reciprocal := by
    intro m n hmn
    dsimp [reciprocal] at hmn
    exact Nat.add_right_cancel (Nat.cast_injective (inv_injective hmn))
  exact Set.infinite_of_injective_forall_mem hinjective fun n ↦
    (RealTopology.mem_positiveReciprocals _).mpr ⟨n + 1, by omega, rfl⟩

/-- Helper for Exercise 27.3: every member of the defining `K`-basis is
open in the `K`-topology. -/
lemma isOpen_k_of_mem_kBasis {u : Set ℝ} (hu : u ∈ RealTopology.kBasis) :
    @IsOpen ℝ RealTopology.k u := by
  -- Rewrite through the owner equation, then use generator openness.
  rw [RealTopology.k_eq_generateFrom]
  exact TopologicalSpace.isOpen_generateFrom_of_mem hu

/-- Helper for Exercise 27.3: the positive reciprocal set is closed in the
`K`-topology. -/
lemma positiveReciprocals_isClosed :
    @IsClosed ℝ RealTopology.k RealTopology.positiveReciprocals := by
  -- Work entirely in the `K`-topology while constructing removed intervals.
  letI : TopologicalSpace ℝ := RealTopology.k
  rw [← isOpen_compl_iff]
  refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
  let u := Ioo (x - 1) (x + 1) \ RealTopology.positiveReciprocals
  refine ⟨u, ?_, ?_, ?_⟩
  · intro y hy
    exact hy.2
  · apply isOpen_k_of_mem_kBasis
    rw [RealTopology.mem_kBasis_iff]
    exact ⟨x - 1, x + 1, by linarith, Or.inr rfl⟩
  · exact ⟨by constructor <;> linarith, hx⟩

/-- Helper for Exercise 27.3: every positive reciprocal lies in the unit
interval. -/
lemma positiveReciprocals_subset_unitInterval :
    RealTopology.positiveReciprocals ⊆ Set.Icc (0 : ℝ) 1 := by
  -- Positivity and the bound `1 ≤ n` give the two interval inequalities.
  intro x hx
  obtain ⟨n, hn, rfl⟩ := (RealTopology.mem_positiveReciprocals x).mp hx
  constructor
  · positivity
  · rw [inv_le_one₀ (by positivity)]
    exact_mod_cast hn

/-- Helper for Exercise 27.3, part (a): The interval `[0, 1]` is not compact as a
subspace of the real line with the `K`-topology. -/
theorem unitIntervalNotCompact :
    ¬ IsCompact (Set.Icc (0 : RealKLine) 1) := by
  -- A compact unit interval would make its closed discrete reciprocal subset finite.
  intro hcompact
  have hreciprocalCompact :
      @IsCompact ℝ RealTopology.k RealTopology.positiveReciprocals :=
    hcompact.of_isClosed_subset positiveReciprocals_isClosed
      positiveReciprocals_subset_unitInterval
  exact positiveReciprocals_infinite
    (@IsCompact.finite ℝ RealTopology.k RealTopology.positiveReciprocals
      hreciprocalCompact positiveReciprocals_isDiscrete)

/-- Helper for Exercise 27.3: positive reciprocals are closed relative to the positive ray. -/
lemma positiveReciprocals_isClosedIn_positiveRay :
    IsClosed ((fun x : Set.Ioi (0 : ℝ) => (x : ℝ)) ⁻¹'
      RealTopology.positiveReciprocals) := by
  -- Invert the closed set of nonzero natural casts inside the nonzero reals.
  let nonzeroNaturals : Set {x : ℝ // x ≠ 0} :=
    (fun x : {x : ℝ // x ≠ 0} => (x : ℝ)) ⁻¹'
      Set.range (fun n : ℕ => (n : ℝ))
  have hnonzeroNaturals : IsClosed nonzeroNaturals := by
    exact (Nat.isClosedEmbedding_coe_real.isClosed_range).preimage continuous_subtype_val
  have hinverted : IsClosed ((Homeomorph.inv₀ ℝ) '' nonzeroNaturals) := by
    exact (Homeomorph.inv₀ ℝ).isClosed_image.mpr hnonzeroNaturals
  let toNonzero : Set.Ioi (0 : ℝ) → {x : ℝ // x ≠ 0} :=
    fun x => ⟨x, x.property.ne'⟩
  have htoNonzero : Continuous toNonzero := by
    exact continuous_subtype_val.subtype_mk fun x => x.property.ne'
  have hpre : IsClosed (toNonzero ⁻¹' ((Homeomorph.inv₀ ℝ) '' nonzeroNaturals)) :=
    hinverted.preimage htoNonzero
  rw [show (fun x : Set.Ioi (0 : ℝ) => (x : ℝ)) ⁻¹'
      RealTopology.positiveReciprocals =
      toNonzero ⁻¹' ((Homeomorph.inv₀ ℝ) '' nonzeroNaturals) by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn, heq⟩ := (RealTopology.mem_positiveReciprocals x).mp hx
      refine ⟨⟨(n : ℝ), by positivity⟩, ⟨n, rfl⟩, Subtype.ext heq.symm⟩
    · rintro ⟨y, hy, hxy⟩
      obtain ⟨n, hn⟩ := hy
      have hnpos : 0 < n := by
        by_contra hn0
        have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn0
        subst n
        exact y.property (by simpa using hn.symm)
      apply (RealTopology.mem_positiveReciprocals _).mpr
      refine ⟨n, hnpos, ?_⟩
      have hxyVal := congrArg Subtype.val hxy
      calc
        (x : ℝ) = (y : ℝ)⁻¹ := hxyVal.symm
        _ = (n : ℝ)⁻¹ := congrArg Inv.inv hn.symm]
  exact hpre

/-- Helper for Exercise 27.3: the negative standard ray includes continuously into the `K`-line. -/
lemma continuous_negativeRay_toK :
    @Continuous (Set.Iio (0 : ℝ)) ℝ inferInstance RealTopology.k
      (fun x => (x : ℝ)) := by
  -- Check preimages of the two kinds of generating intervals.
  rw [RealTopology.k_eq_generateFrom, continuous_generateFrom_iff]
  intro s hs
  rw [RealTopology.mem_kBasis_iff] at hs
  obtain ⟨a, b, _, rfl | rfl⟩ := hs
  · exact isOpen_Ioo.preimage continuous_subtype_val
  · rw [show (fun x : Set.Iio (0 : ℝ) => (x : ℝ)) ⁻¹'
        (Ioo a b \ RealTopology.positiveReciprocals) =
        (fun x : Set.Iio (0 : ℝ) => (x : ℝ)) ⁻¹' Ioo a b by
      ext x
      simp only [mem_preimage, mem_sdiff, mem_Ioo, and_iff_left_iff_imp]
      intro _ hx
      obtain ⟨n, hn, heq⟩ := (RealTopology.mem_positiveReciprocals x).mp hx
      have hxpos : (0 : ℝ) < x := by rw [heq]; positivity
      exact (not_lt_of_ge hxpos.le) x.property]
    exact isOpen_Ioo.preimage continuous_subtype_val

/-- Helper for Exercise 27.3: the positive standard ray includes continuously into the `K`-line. -/
lemma continuous_positiveRay_toK :
    @Continuous (Set.Ioi (0 : ℝ)) ℝ inferInstance RealTopology.k
      (fun x => (x : ℝ)) := by
  -- Removed intervals stay open because the reciprocal set is relatively closed.
  rw [RealTopology.k_eq_generateFrom, continuous_generateFrom_iff]
  intro s hs
  rw [RealTopology.mem_kBasis_iff] at hs
  obtain ⟨a, b, _, rfl | rfl⟩ := hs
  · exact isOpen_Ioo.preimage continuous_subtype_val
  · rw [Set.preimage_sdiff]
    exact (isOpen_Ioo.preimage continuous_subtype_val).sdiff
      positiveReciprocals_isClosedIn_positiveRay

/-- Helper for Exercise 27.3: a generated `K`-open neighborhood of zero
contains a punctured basis interval. -/
lemma exists_puncturedInterval_subset_of_generateOpen {u : Set ℝ}
    (hu : TopologicalSpace.GenerateOpen RealTopology.kBasis u)
    (hzero : (0 : ℝ) ∈ u) :
    ∃ a b : ℝ, a < 0 ∧ 0 < b ∧
      Ioo a b \ RealTopology.positiveReciprocals ⊆ u := by
  -- The invariant is stable under finite intersections and arbitrary unions.
  induction hu with
  | basic s hs =>
      rw [RealTopology.mem_kBasis_iff] at hs
      obtain ⟨a, b, _, rfl | rfl⟩ := hs
      · exact ⟨a, b, hzero.1, hzero.2, sdiff_subset⟩
      · exact ⟨a, b, hzero.1.1, hzero.1.2, Subset.rfl⟩
  | univ =>
      exact ⟨-1, 1, by norm_num, by norm_num, subset_univ _⟩
  | inter s t hs ht ihs iht =>
      obtain ⟨a, b, ha, hb, hab⟩ := ihs hzero.1
      obtain ⟨c, d, hc, hd, hcd⟩ := iht hzero.2
      refine ⟨max a c, min b d, ?_, ?_, ?_⟩
      · simpa only [max_lt_iff] using And.intro ha hc
      · simpa only [lt_min_iff] using And.intro hb hd
      · intro x hx
        simp only [mem_sdiff, mem_Ioo, max_lt_iff, lt_min_iff] at hx
        exact ⟨hab ⟨⟨hx.1.1.1, hx.1.2.1⟩, hx.2⟩,
          hcd ⟨⟨hx.1.1.2, hx.1.2.2⟩, hx.2⟩⟩
  | sUnion S hS ih =>
      obtain ⟨s, hsS, hzeros⟩ := hzero
      obtain ⟨a, b, ha, hb, hab⟩ := ih s hsS hzeros
      exact ⟨a, b, ha, hb, fun x hx => ⟨s, hsS, hab hx⟩⟩

/-- Helper for Exercise 27.3: zero is in the `K`-closure of both open rays. -/
lemma zero_mem_closure_openRays :
    (0 : ℝ) ∈ @closure ℝ RealTopology.k (Iio 0) ∧
      (0 : ℝ) ∈ @closure ℝ RealTopology.k (Ioi 0) := by
  -- The negative ray uses a negative midpoint; the positive ray uses an irrational point.
  constructor
  · apply (@mem_closure_iff ℝ RealTopology.k 0 (Iio 0)).mpr
    intro u hu hzero
    rw [RealTopology.k_eq_generateFrom] at hu
    obtain ⟨a, b, ha, hb, hab⟩ :=
      exists_puncturedInterval_subset_of_generateOpen hu hzero
    let x := a / 2
    refine ⟨x, ?_, ?_⟩
    · apply hab
      exact ⟨⟨by dsimp [x]; linarith, by dsimp [x]; linarith⟩, by
        intro hx
        obtain ⟨n, hn, heq⟩ := (RealTopology.mem_positiveReciprocals x).mp hx
        have hxpos : (0 : ℝ) < x := by rw [heq]; positivity
        dsimp [x] at hxpos
        linarith⟩
    · dsimp [x]
      exact div_neg_of_neg_of_pos ha (by norm_num)
  · apply (@mem_closure_iff ℝ RealTopology.k 0 (Ioi 0)).mpr
    intro u hu hzero
    rw [RealTopology.k_eq_generateFrom] at hu
    obtain ⟨a, b, ha, hb, hab⟩ :=
      exists_puncturedInterval_subset_of_generateOpen hu hzero
    obtain ⟨x, hirr, hxpos, hxb⟩ := exists_irrational_btwn hb
    refine ⟨x, ?_, hxpos⟩
    apply hab
    refine ⟨⟨by linarith, hxb⟩, ?_⟩
    intro hx
    obtain ⟨n, hn, heq⟩ := (RealTopology.mem_positiveReciprocals x).mp hx
    exact hirr.ne_rat ((n : ℚ)⁻¹) (by simpa using heq)

/-- Helper for Exercise 27.3: the two closed rays are connected in the `K`-topology. -/
lemma closedRays_isConnected :
    @IsConnected ℝ RealTopology.k (Iic 0) ∧
      @IsConnected ℝ RealTopology.k (Ici 0) := by
  -- Transport standard connectedness along the two continuous ray inclusions.
  have hnegativeOpen : @IsConnected ℝ RealTopology.k (Iio 0) := by
    have hconnectedSubtype : @ConnectedSpace (Set.Iio (0 : ℝ)) inferInstance :=
      isConnected_iff_connectedSpace.mp isConnected_Iio
    have hrange : @IsConnected ℝ RealTopology.k
        (Set.range fun x : Set.Iio (0 : ℝ) => (x : ℝ)) :=
      @isConnected_range (Set.Iio (0 : ℝ)) ℝ inferInstance RealTopology.k
        hconnectedSubtype _ continuous_negativeRay_toK
    rw [Subtype.range_val] at hrange
    exact hrange
  have hpositiveOpen : @IsConnected ℝ RealTopology.k (Ioi 0) := by
    have hconnectedSubtype : @ConnectedSpace (Set.Ioi (0 : ℝ)) inferInstance :=
      isConnected_iff_connectedSpace.mp isConnected_Ioi
    have hrange : @IsConnected ℝ RealTopology.k
        (Set.range fun x : Set.Ioi (0 : ℝ) => (x : ℝ)) :=
      @isConnected_range (Set.Ioi (0 : ℝ)) ℝ inferInstance RealTopology.k
        hconnectedSubtype _ continuous_positiveRay_toK
    rw [Subtype.range_val] at hrange
    exact hrange
  constructor
  · refine @IsConnected.subset_closure ℝ RealTopology.k (Iio 0) (Iic 0)
      hnegativeOpen Iio_subset_Iic_self ?_
    intro x hx
    rcases lt_or_eq_of_le (show x ≤ 0 from hx) with hlt | rfl
    · exact @subset_closure ℝ RealTopology.k (Iio 0) x hlt
    · exact zero_mem_closure_openRays.1
  · refine @IsConnected.subset_closure ℝ RealTopology.k (Ioi 0) (Ici 0)
      hpositiveOpen Ioi_subset_Ici_self ?_
    intro x hx
    rcases eq_or_lt_of_le (show 0 ≤ x from hx) with rfl | hlt
    · exact zero_mem_closure_openRays.2
    · exact @subset_closure ℝ RealTopology.k (Ioi 0) x hlt

/-- Helper for Exercise 27.3, part (b): The real line with the `K`-topology is
connected. -/
instance instConnectedSpace : ConnectedSpace RealKLine := by
  -- The connected closed rays meet at zero and cover the whole line.
  rw [connectedSpace_iff_univ]
  rw [← Set.Iic_union_Ici (a := (0 : RealKLine))]
  have hintersection : (Set.Iic (0 : RealKLine) ∩ Set.Ici 0).Nonempty := by
    refine ⟨0, ?_⟩
    exact ⟨show (0 : RealKLine) ≤ 0 from le_rfl, show (0 : RealKLine) ≤ 0 from le_rfl⟩
  exact IsConnected.union hintersection
    closedRays_isConnected.1 closedRays_isConnected.2

/-- Helper for Exercise 27.3: forgetting the `K`-topology gives a continuous map to standard `ℝ`. -/
lemma continuousToReal :
    @Continuous RealKLine ℝ RealKLine.instTopologicalSpace inferInstance
      (fun x : RealKLine ↦ (x : ℝ)) := by
  -- Normalize the cross-alias identity before comparing the two topologies.
  rw [continuous_iff_le_induced]
  change RealTopology.k ≤ TopologicalSpace.induced id (inferInstance : TopologicalSpace ℝ)
  rw [induced_id]
  exact RealTopology.k_lt_standard.le

/-- Exercise 27.3: The real line with the `K`-topology is not
path connected. -/
theorem notPathConnected : ¬ PathConnectedSpace RealKLine := by
  -- A hypothetical path from zero to one has compact `K`-range.
  intro hpathConnected
  letI : PathConnectedSpace RealKLine := hpathConnected
  let path : Path (0 : RealKLine) 1 := (PathConnectedSpace.joined 0 1).somePath
  have hcompactRange : IsCompact (Set.range path) := isCompact_range path.continuous
  -- After forgetting the finer topology, connectedness forces the whole unit
  -- interval into the range.
  let realPath : Set.Icc (0 : ℝ) 1 → ℝ := fun t ↦ (path t : ℝ)
  have hcontinuousReal : Continuous realPath := continuousToReal.comp path.continuous
  have hconnected : IsConnected (Set.range realPath) := isConnected_range hcontinuousReal
  have hzero : (0 : ℝ) ∈ Set.range realPath := by
    refine ⟨0, ?_⟩
    exact congrArg (fun x : RealKLine ↦ (x : ℝ)) path.source
  have hone : (1 : ℝ) ∈ Set.range realPath := by
    refine ⟨1, ?_⟩
    exact congrArg (fun x : RealKLine ↦ (x : ℝ)) path.target
  have hunitSubsetReal : Set.Icc (0 : ℝ) 1 ⊆ Set.range realPath :=
    hconnected.Icc_subset hzero hone
  have hunitSubset : Set.Icc (0 : RealKLine) 1 ⊆ Set.range path := by
    intro x hx
    obtain ⟨t, ht⟩ := hunitSubsetReal hx
    exact ⟨t, ht⟩
  -- The unit interval is `K`-closed, hence compact inside the compact path range.
  have hunitClosed : @IsClosed ℝ RealTopology.k (Set.Icc 0 1) := by
    have hstandardOpen : @IsOpen ℝ inferInstance (Set.Icc (0 : ℝ) 1)ᶜ :=
      isClosed_Icc.isOpen_compl
    exact (@isOpen_compl_iff ℝ (Set.Icc (0 : ℝ) 1) RealTopology.k).mp
      (RealTopology.k_lt_standard.le _ hstandardOpen)
  exact unitIntervalNotCompact
    (hcompactRange.of_isClosed_subset hunitClosed hunitSubset)

end RealKLine
