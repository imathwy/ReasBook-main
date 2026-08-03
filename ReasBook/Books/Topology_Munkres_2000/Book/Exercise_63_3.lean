module

public import Topology_Munkres_2000.Book.Theorem_63_4
public import Topology_Munkres_2000.Book.Theorem_63_3
public import Topology_Munkres_2000.Book.Example_24_7.Connectedness
public import Topology_Munkres_2000.Book.Definition_61_4
public import Topology_Munkres_2000.Book.Definition_61_4.ClosedCurve
public import Topology_Munkres_2000.Book.Theorem_9_0_1.ArcNonseparation
public import Topology_Munkres_2000.Book.Exercise_63_3.LeftCore
public import Mathlib.Topology.Subpath

public section

open Set
open Filter Topology
open scoped Topology

/-- Helper for Exercise 63.3: the planar carrier of the topologist's sine curve is compact. -/
private lemma sineCurveCarrier_isCompact :
    IsCompact TopologistsSineCurve.carrier := by
  -- Enclose the graph in a compact rectangle and then pass to its closure.
  have hrectangle : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hcurve : TopologistsSineCurve.curve ⊆
      Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := by
    rintro p ⟨t, ht, rfl⟩
    exact ⟨⟨ht.1.le, ht.2⟩, Real.neg_one_le_sin _, Real.sin_le_one _⟩
  exact hrectangle.of_isClosed_subset isClosed_closure
    (closure_minimal hcurve hrectangle.isClosed)

/-- Helper for Exercise 63.3: every real line segment in the plane is compact. -/
private lemma planeSegment_isCompact (a b : ℝ × ℝ) :
    IsCompact (segment ℝ a b) := by
  -- Express the segment as the convex hull of its finite endpoint set.
  rw [← convexHull_pair]
  exact ((Set.finite_singleton b).insert a).isCompact_convexHull ℝ

/-- Helper for Exercise 63.3: the planar closed topologist's sine curve is compact. -/
private lemma closedSineCurveCarrier_isCompact :
    IsCompact TopologistsSineCurve.closedCarrier := by
  -- The added broken line is a finite union of compact segments.
  have hbroken : IsCompact TopologistsSineCurve.brokenLine := by
    have hbrokenEq : TopologistsSineCurve.brokenLine =
        segment ℝ (0, -1) (0, -2) ∪
          (segment ℝ (0, -2) (1, -2) ∪
            segment ℝ (1, -2) (1, Real.sin 1)) := by
      ext p
      rw [TopologistsSineCurve.mem_brokenLine_iff]
      simp only [Set.mem_union]
    rw [hbrokenEq]
    exact (planeSegment_isCompact (0, -1) (0, -2)).union
      ((planeSegment_isCompact (0, -2) (1, -2)).union
        (planeSegment_isCompact (1, -2) (1, Real.sin 1)))
  have hclosedEq : TopologistsSineCurve.closedCarrier =
      TopologistsSineCurve.carrier ∪ TopologistsSineCurve.brokenLine := by
    ext p
    rw [TopologistsSineCurve.mem_closedCarrier_iff]
    simp only [Set.mem_union]
  rw [hclosedEq]
  exact sineCurveCarrier_isCompact.union hbroken

/-- Helper for Exercise 63.3: an embedded copy of the topologist's sine curve
in the standard sphere is closed. -/
private lemma isClosed_of_homeomorphic_topologistsSineCurve
    (D : Set (StandardSphere 2))
    (hD : Nonempty (D ≃ₜ TopologistsSineCurve.Space)) : IsClosed D := by
  -- Transfer compactness from the planar carrier through the supplied homeomorphism.
  obtain ⟨e⟩ := hD
  letI : CompactSpace TopologistsSineCurve.Space :=
    isCompact_iff_compactSpace.mp sineCurveCarrier_isCompact
  letI : CompactSpace D := e.symm.compactSpace
  exact (isCompact_iff_compactSpace.mpr inferInstance).isClosed

/-- Helper for Exercise 63.3: an embedded copy of the closed topologist's sine
curve in the standard sphere is closed. -/
private lemma isClosed_of_homeomorphic_closedSineCurve
    (C : Set (StandardSphere 2))
    (hC : Nonempty (C ≃ₜ TopologistsSineCurve.ClosedSpace)) : IsClosed C := by
  -- Transfer compactness from the planar closed carrier through the supplied homeomorphism.
  obtain ⟨e⟩ := hC
  letI : CompactSpace TopologistsSineCurve.ClosedSpace :=
    isCompact_iff_compactSpace.mp closedSineCurveCarrier_isCompact
  letI : CompactSpace C := e.symm.compactSpace
  exact (isCompact_iff_compactSpace.mpr inferInstance).isClosed

/-- Helper for Exercise 63.3: the complement of a spherical arc joins any two
of its points by a path. -/
private lemma joinedIn_compl_of_isArc
    (A : Set (StandardSphere 2)) (hAarc : Topology.IsArc A)
    {x y : StandardSphere 2} (hx : x ∈ Aᶜ) (hy : y ∈ Aᶜ) :
    JoinedIn Aᶜ x y := by
  -- Arc compactness makes the complement open, and nonseparation makes it connected.
  letI : Topology.IsArc A := hAarc
  letI : LocallyPathConnectedSpace (StandardSphere 2) :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin 2)) (StandardSphere 2)
  classical
  obtain ⟨e⟩ := Topology.IsArc.homeomorphic_unitInterval (X := A)
  letI : CompactSpace A := e.symm.compactSpace
  have hAclosed : IsClosed A :=
    (isCompact_iff_compactSpace.mpr inferInstance).isClosed
  have hpreconnectedSpace : PreconnectedSpace (Aᶜ : Set (StandardSphere 2)) := by
    have hnonseparating := arc_not_separates A
    rw [Set.separates_iff] at hnonseparating
    exact not_not.mp hnonseparating
  have hconnected : IsConnected Aᶜ :=
    ⟨⟨x, hx⟩, isPreconnected_iff_preconnectedSpace.mpr hpreconnectedSpace⟩
  have hpathConnected : IsPathConnected Aᶜ :=
    (hAclosed.isOpen_compl.isConnected_iff_isPathConnected).mp hconnected
  exact hpathConnected.joinedIn x hx y hy

/-- Helper for Exercise 63.3: a decreasing family of closed cores with an arc
as its limit proves nonseparation once paths can be pushed across every tail. -/
private lemma not_separates_of_decreasing_closed_cores
    (D V : Set (StandardSphere 2)) (K : ℕ → Set (StandardSphere 2))
    (hKclosed : ∀ n, IsClosed (K n))
    (hKdirected : Directed (· ⊇ ·) K)
    (hKinter : ⋂ n, K n = V)
    (hVjoined : ∀ x ∈ Dᶜ, ∀ y ∈ Dᶜ, JoinedIn Vᶜ x y)
    (hpush : ∀ n x, x ∈ Dᶜ → ∀ y, y ∈ Dᶜ →
      JoinedIn (K n)ᶜ x y → JoinedIn Dᶜ x y) :
    ¬ D.Separates := by
  -- It suffices to put each pair of exterior points in one relative component.
  apply not_separates_of_pairwise_mem_connectedComponentIn D
  intro x hx y hy
  let hxyV : JoinedIn Vᶜ x y := hVjoined x hx y hy
  let γ : Path x y := hxyV.somePath
  have hcompact : IsCompact (Set.range γ) := isCompact_range γ.continuous
  have hlimitAvoided : Set.range γ ∩ ⋂ n, K n = ∅ := by
    rw [hKinter]
    apply eq_empty_iff_forall_notMem.mpr
    rintro z ⟨⟨t, rfl⟩, hzV⟩
    exact hxyV.somePath_mem t hzV
  obtain ⟨n, hn⟩ :=
    hcompact.elim_directed_family_closed K hKclosed hlimitAvoided hKdirected
  have hxyK : JoinedIn (K n)ᶜ x y := by
    refine ⟨γ, ?_⟩
    intro t ht
    have hmem : γ t ∈ Set.range γ ∩ K n := ⟨Set.mem_range_self t, ht⟩
    rw [hn] at hmem
    exact hmem
  let hxyD := hpush n x hx y hy hxyK
  have hrangeConnected : IsConnected (Set.range hxyD.somePath) :=
    isConnected_range hxyD.somePath.continuous
  apply hrangeConnected.isPreconnected.subset_connectedComponentIn
    hxyD.somePath.source_mem_range
  · rintro z ⟨t, rfl⟩
    exact hxyD.somePath_mem t
  · exact hxyD.somePath.target_mem_range

/-- Helper for Exercise 63.3: exterior points of a closed nonseparating
spherical set can be joined through its complement. -/
private lemma joinedIn_compl_of_closed_not_separates
    (B : Set (StandardSphere 2)) (hBclosed : IsClosed B)
    (hBnonseparating : ¬ B.Separates)
    {x y : StandardSphere 2} (hx : x ∈ Bᶜ) (hy : y ∈ Bᶜ) :
    JoinedIn Bᶜ x y := by
  -- In the locally path connected sphere, the open connected complement is path connected.
  letI : LocallyPathConnectedSpace (StandardSphere 2) :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin 2)) (StandardSphere 2)
  have hpreconnectedSpace : PreconnectedSpace (Bᶜ : Set (StandardSphere 2)) := by
    rw [Set.separates_iff] at hBnonseparating
    exact not_not.mp hBnonseparating
  have hconnected : IsConnected Bᶜ :=
    ⟨⟨x, hx⟩, isPreconnected_iff_preconnectedSpace.mpr hpreconnectedSpace⟩
  have hpathConnected : IsPathConnected Bᶜ :=
    (hBclosed.isOpen_compl.isConnected_iff_isPathConnected).mp hconnected
  exact hpathConnected.joinedIn x hx y hy

/-- Helper for Exercise 63.3: adjoining an arc at one endpoint preserves a
given path component of the complement. -/
private lemma joinedIn_compl_union_of_arc_endpoint
    (K A : Set (StandardSphere 2))
    (hKclosed : IsClosed K)
    (hAarc : Topology.IsArc A)
    (hinter : ∃ p : A,
      @Topology.IsArc.IsEndpoint A _ hAarc p ∧ K ∩ A = {p.1})
    {x y : StandardSphere 2} (hx : x ∈ (K ∪ A)ᶜ) (hy : y ∈ (K ∪ A)ᶜ)
    (hxy : JoinedIn Kᶜ x y) : JoinedIn (K ∪ A)ᶜ x y := by
  -- Route correction: compare the arc tail with the component carrying the
  -- supplied path; connectedness of the exterior is not needed.
  letI : LocallyPathConnectedSpace (StandardSphere 2) :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin 2)) (StandardSphere 2)
  classical
  letI : Topology.IsArc A := hAarc
  obtain ⟨p, hpEndpoint, hinter⟩ := hinter
  have hpInter : (p : StandardSphere 2) ∈ K ∩ A := by
    rw [hinter]
    exact Set.mem_singleton p.1
  have hremEq : A \ K = Subtype.val '' (({p} : Set A)ᶜ) := by
    ext z
    constructor
    · intro hz
      let zA : A := ⟨z, hz.1⟩
      have hzp : zA ≠ p := by
        intro hzp
        have hzEq : z = (p : StandardSphere 2) := congrArg Subtype.val hzp
        have hzK : z ∈ K := by
          rw [hzEq]
          exact hpInter.1
        exact hz.2 hzK
      exact ⟨zA, hzp, rfl⟩
    · rintro ⟨z, hzp, rfl⟩
      refine ⟨z.2, ?_⟩
      intro hzK
      have hzInter : (z : StandardSphere 2) ∈ K ∩ A := ⟨hzK, z.2⟩
      rw [hinter] at hzInter
      exact hzp (Subtype.ext hzInter)
  have hremConnected : IsConnected (A \ K) := by
    rw [hremEq]
    obtain ⟨e⟩ := Topology.IsArc.homeomorphic_unitInterval (X := A)
    have hpuncturedArc : IsConnected (({p} : Set A)ᶜ) := by
      rw [← e.isConnected_image, e.image_compl, Set.image_singleton,
        unitInterval.isConnected_compl_singleton_iff]
      rw [Topology.IsArc.isEndpoint_iff e] at hpEndpoint
      rcases hpEndpoint with hp | hp
      · left
        simp only [hp, e.apply_symm_apply]
      · right
        simp only [hp, e.apply_symm_apply]
    exact hpuncturedArc.image Subtype.val continuous_subtype_val.continuousOn
  obtain ⟨a, haRem⟩ := hremConnected.nonempty
  let U : Set (StandardSphere 2) := connectedComponentIn Kᶜ x
  let W : Set (StandardSphere 2) := connectedComponentIn Kᶜ a
  have hxK : x ∈ Kᶜ := fun hxK ↦ hx (Or.inl hxK)
  have hyK : y ∈ Kᶜ := fun hyK ↦ hy (Or.inl hyK)
  have hpathSubU : Set.range hxy.somePath ⊆ U := by
    exact (isConnected_range hxy.somePath.continuous).isPreconnected.subset_connectedComponentIn
      hxy.somePath.source_mem_range (by
        rintro z ⟨t, rfl⟩
        exact hxy.somePath_mem t)
  have hyU : y ∈ U := hpathSubU hxy.somePath.target_mem_range
  have hremSubW : A \ K ⊆ W :=
    hremConnected.isPreconnected.subset_connectedComponentIn haRem (fun _ hz ↦ hz.2)
  by_cases haU : a ∈ U
  · have hUW : U = W := connectedComponentIn_eq haU
    have hremSubU : A \ K ⊆ U := hUW ▸ hremSubW
    let E : Set (StandardSphere 2) := Uᶜ
    have hUopen : IsOpen U := hKclosed.isOpen_compl.connectedComponentIn
    have hEclosed : IsClosed E := hUopen.isClosed_compl
    have hUconnected : IsConnected U := isConnected_connectedComponentIn_iff.mpr hxK
    have hEnonseparating : ¬ E.Separates := by
      intro hEsep
      rw [Set.separates_iff] at hEsep
      apply hEsep
      have hEcompl : Eᶜ = U := by
        simp only [E, compl_compl]
      rw [hEcompl]
      exact isPreconnected_iff_preconnectedSpace.mp hUconnected.isPreconnected
    have hEinterA : E ∩ A = {(p : StandardSphere 2)} := by
      ext z
      constructor
      · intro hz
        have hzK : z ∈ K := by
          by_contra hzK
          exact hz.1 (hremSubU ⟨hz.2, hzK⟩)
        have hzInter : z ∈ K ∩ A := ⟨hzK, hz.2⟩
        rwa [hinter] at hzInter
      · intro hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        refine ⟨?_, p.2⟩
        intro hpU
        exact (connectedComponentIn_subset Kᶜ x hpU) hpInter.1
    have hAclosed : IsClosed A := by
      obtain ⟨e⟩ := Topology.IsArc.homeomorphic_unitInterval (X := A)
      letI : CompactSpace A := e.symm.compactSpace
      exact (isCompact_iff_compactSpace.mpr inferInstance).isClosed
    have hinterSimplyConnected : IsSimplyConnected ((E ∩ A)ᶜ) := by
      rw [hEinterA]
      let chart := StandardSphere.puncturedHomeomorphPlane (p : StandardSphere 2)
      exact chart.toHomotopyEquiv.simplyConnectedSpace_iff.mpr inferInstance
    have hUnionNonseparating : ¬ (E ∪ A).Separates :=
      union_not_separates_of_compl_inter_simplyConnected E A hEclosed hAclosed
        hinterSimplyConnected hEnonseparating (arc_not_separates A)
    have hxEA : x ∈ (E ∪ A)ᶜ := by
      intro hxEA
      exact hxEA.elim (fun hxE ↦ hxE (mem_connectedComponentIn hxK))
        (fun hxA ↦ hx (Or.inr hxA))
    have hyEA : y ∈ (E ∪ A)ᶜ := by
      intro hyEA
      exact hyEA.elim (fun hyE ↦ hyE hyU) (fun hyA ↦ hy (Or.inr hyA))
    have hjoinedEA := joinedIn_compl_of_closed_not_separates (E ∪ A)
      (hEclosed.union hAclosed) hUnionNonseparating hxEA hyEA
    have hKsubE : K ⊆ E := by
      intro z hzK hzU
      exact (connectedComponentIn_subset Kᶜ x hzU) hzK
    refine ⟨hjoinedEA.somePath, ?_⟩
    intro t htUnion
    rcases htUnion with htK | htA
    · exact hjoinedEA.somePath_mem t (Or.inl (hKsubE htK))
    · exact hjoinedEA.somePath_mem t (Or.inr htA)
  · have hUdisjointA : Disjoint U A := by
      rw [Set.disjoint_left]
      intro z hzU hzA
      have hzK : z ∉ K := connectedComponentIn_subset Kᶜ x hzU
      have hzW : z ∈ W := hremSubW ⟨hzA, hzK⟩
      have hUW : U = W :=
        (connectedComponentIn_eq hzU).trans (connectedComponentIn_eq hzW).symm
      exact haU (hUW ▸ mem_connectedComponentIn haRem.2)
    refine ⟨hxy.somePath, ?_⟩
    intro t htUnion
    rcases htUnion with htK | htA
    · exact hxy.somePath_mem t htK
    · exact Set.disjoint_left.mp hUdisjointA (hpathSubU (Set.mem_range_self t)) htA

/-- Helper for Exercise 63.3: adjoining an arc at one endpoint to a closed
nonseparating set preserves nonseparation. -/
private lemma union_not_separates_of_arc_endpoint
    (K A : Set (StandardSphere 2))
    (hKclosed : IsClosed K) (hKnonseparating : ¬ K.Separates)
    (hAarc : Topology.IsArc A)
    (hinter : ∃ p : A,
      @Topology.IsArc.IsEndpoint A _ hAarc p ∧ K ∩ A = {p.1}) :
    ¬ (K ∪ A).Separates := by
  -- Join exterior points around `K`, then push that path off the endpoint-attached arc.
  apply not_separates_of_pairwise_mem_connectedComponentIn (K ∪ A)
  intro x hx y hy
  have hxK : x ∈ Kᶜ := fun hxK ↦ hx (Or.inl hxK)
  have hyK : y ∈ Kᶜ := fun hyK ↦ hy (Or.inl hyK)
  have hxyK := joinedIn_compl_of_closed_not_separates K hKclosed
    hKnonseparating hxK hyK
  have hxy := joinedIn_compl_union_of_arc_endpoint K A hKclosed hAarc
    hinter hx hy hxyK
  have hrangeConnected : IsConnected (Set.range hxy.somePath) :=
    isConnected_range hxy.somePath.continuous
  apply hrangeConnected.isPreconnected.subset_connectedComponentIn
    hxy.somePath.source_mem_range
  · rintro z ⟨t, rfl⟩
    exact hxy.somePath_mem t
  · exact hxy.somePath.target_mem_range

/-- Helper for Exercise 63.3: the cutoff used for the `n`th sine-curve core. -/
private noncomputable def sineCurveCutoff (n : ℕ) : ℝ :=
  1 / (n + 2 : ℕ)

/-- Helper for Exercise 63.3: every sine-curve cutoff is positive. -/
private lemma sineCurveCutoff_pos (n : ℕ) : 0 < sineCurveCutoff n := by
  -- The denominator is a positive natural number.
  simp only [sineCurveCutoff, Nat.cast_add, Nat.cast_ofNat]
  positivity

/-- Helper for Exercise 63.3: every sine-curve cutoff is strictly below one. -/
private lemma sineCurveCutoff_lt_one (n : ℕ) : sineCurveCutoff n < 1 := by
  -- Compare the denominator `n + 2` with one before taking reciprocals.
  have hden : (1 : ℝ) < (n + 2 : ℕ) := by
    have hnat : 1 < n + 2 := by omega
    exact_mod_cast hnat
  calc
    sineCurveCutoff n = 1 / (n + 2 : ℕ) := rfl
    _ < 1 / (1 : ℝ) := one_div_lt_one_div_of_lt zero_lt_one hden
    _ = 1 := by norm_num

/-- Helper for Exercise 63.3: the cutoff sequence is antitone. -/
private lemma sineCurveCutoff_anti {m n : ℕ} (hmn : m ≤ n) :
    sineCurveCutoff n ≤ sineCurveCutoff m := by
  -- Increasing the positive denominator decreases its reciprocal.
  have hden : (m + 2 : ℕ) ≤ n + 2 := Nat.add_le_add_right hmn 2
  apply one_div_le_one_div_of_le
  · have hnat : 0 < m + 2 := by omega
    exact_mod_cast hnat
  · exact_mod_cast hden

/-- Helper for Exercise 63.3: the standard vertical parametrization belongs
to the sine-curve carrier. -/
private lemma sineVerticalParam_mem_carrier (t : unitInterval) :
    ((0 : ℝ), 2 * (t : ℝ) - 1) ∈ TopologistsSineCurve.carrier := by
  -- Its first coordinate is zero and its second coordinate lies in `[-1,1]`.
  rw [TopologistsSineCurve.carrier_eq_curve_union_vertical]
  right
  rw [TopologistsSineCurve.mem_vertical_iff]
  have hlower : (-1 : ℝ) ≤ 2 * (t : ℝ) - 1 := by
    linarith [t.property.1]
  have hupper : 2 * (t : ℝ) - 1 ≤ 1 := by
    linarith [t.property.2]
  exact ⟨rfl, ⟨hlower, hupper⟩⟩

/-- Helper for Exercise 63.3: the vertical interval as a parametrized subset
of the sine-curve space. -/
private def sineVerticalParam (t : unitInterval) : TopologistsSineCurve.Space :=
  ⟨((0 : ℝ), 2 * (t : ℝ) - 1), sineVerticalParam_mem_carrier t⟩

/-- Helper for Exercise 63.3: the vertical parametrization is continuous. -/
private lemma continuous_sineVerticalParam : Continuous sineVerticalParam := by
  -- Continuity follows coordinatewise and then through the subtype constructor.
  apply Continuous.subtype_mk
  fun_prop

/-- Helper for Exercise 63.3: the vertical parametrization is injective. -/
private lemma injective_sineVerticalParam : Function.Injective sineVerticalParam := by
  -- Equality of second coordinates recovers the interval parameter.
  intro s t hst
  have hsnd := congrArg (fun z : TopologistsSineCurve.Space ↦ z.1.2) hst
  apply Subtype.ext
  dsimp [sineVerticalParam] at hsnd ⊢
  linarith

/-- Helper for Exercise 63.3: the vertical parametrization has range exactly
the vertical part of the sine curve. -/
private lemma range_sineVerticalParam :
    Set.range sineVerticalParam = TopologistsSineCurve.verticalPart := by
  -- Solve explicitly for the interval parameter from the second coordinate.
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    rw [TopologistsSineCurve.mem_verticalPart_iff,
      TopologistsSineCurve.mem_vertical_iff]
    change (0 : ℝ) = 0 ∧ 2 * (t : ℝ) - 1 ∈ Icc (-1 : ℝ) 1
    have hlower : (-1 : ℝ) ≤ 2 * (t : ℝ) - 1 := by
      linarith [t.property.1]
    have hupper : 2 * (t : ℝ) - 1 ≤ 1 := by
      linarith [t.property.2]
    exact ⟨rfl, ⟨hlower, hupper⟩⟩
  · intro hz
    rw [TopologistsSineCurve.mem_verticalPart_iff,
      TopologistsSineCurve.mem_vertical_iff] at hz
    have htmem : (z.1.2 + 1) / 2 ∈ Icc (0 : ℝ) 1 := by
      constructor
      · linarith [hz.2.1]
      · linarith [hz.2.2]
    let t : unitInterval := ⟨(z.1.2 + 1) / 2, htmem⟩
    refine ⟨t, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact hz.1.symm
    · dsimp [sineVerticalParam, t]
      linarith

/-- Helper for Exercise 63.3: the first coordinate of the graph-tail
parametrization. -/
private noncomputable def sineTailX (n : ℕ) (t : unitInterval) : ℝ :=
  sineCurveCutoff n + (1 - sineCurveCutoff n) * (t : ℝ)

/-- Helper for Exercise 63.3: a graph-tail parameter has positive first coordinate. -/
private lemma sineTailX_pos (n : ℕ) (t : unitInterval) : 0 < sineTailX n t := by
  -- The affine parameter starts at the positive cutoff and moves rightward.
  have hfactor : 0 ≤ 1 - sineCurveCutoff n :=
    sub_nonneg.mpr (sineCurveCutoff_lt_one n).le
  dsimp [sineTailX]
  nlinarith [sineCurveCutoff_pos n, t.property.1]

/-- Helper for Exercise 63.3: a graph-tail parameter has first coordinate at most one. -/
private lemma sineTailX_le_one (n : ℕ) (t : unitInterval) : sineTailX n t ≤ 1 := by
  -- The affine parameter stays between its cutoff and its right endpoint.
  have hfactor : 0 ≤ 1 - sineCurveCutoff n :=
    sub_nonneg.mpr (sineCurveCutoff_lt_one n).le
  dsimp [sineTailX]
  nlinarith [t.property.2]

/-- Helper for Exercise 63.3: the graph-tail parametrization belongs to the carrier. -/
private lemma sineTailParam_mem_carrier (n : ℕ) (t : unitInterval) :
    (sineTailX n t, Real.sin (1 / sineTailX n t)) ∈
      TopologistsSineCurve.carrier := by
  -- The point lies on the defining graph over `(0,1]`.
  rw [TopologistsSineCurve.carrier_eq_curve_union_vertical]
  left
  exact ⟨sineTailX n t, ⟨sineTailX_pos n t, sineTailX_le_one n t⟩, rfl⟩

/-- Helper for Exercise 63.3: the graph tail from the `n`th cutoff to `x = 1`. -/
private noncomputable def sineTailParam (n : ℕ) (t : unitInterval) :
    TopologistsSineCurve.Space :=
  ⟨(sineTailX n t, Real.sin (1 / sineTailX n t)),
    sineTailParam_mem_carrier n t⟩

/-- Helper for Exercise 63.3: each graph-tail parametrization is continuous. -/
private lemma continuous_sineTailParam (n : ℕ) : Continuous (sineTailParam n) := by
  -- Positivity of the affine first coordinate makes the reciprocal continuous.
  apply Continuous.subtype_mk
  have hx : Continuous (sineTailX n) := by
    unfold sineTailX
    fun_prop
  exact hx.prodMk (Real.continuous_sin.comp
    (continuous_const.div hx (fun t ↦ (sineTailX_pos n t).ne')))

/-- Helper for Exercise 63.3: each graph-tail parametrization is injective. -/
private lemma injective_sineTailParam (n : ℕ) : Function.Injective (sineTailParam n) := by
  -- Its strictly positive affine first coordinate determines the parameter.
  intro s t hst
  have hfst := congrArg (fun z : TopologistsSineCurve.Space ↦ z.1.1) hst
  apply Subtype.ext
  dsimp [sineTailParam, sineTailX] at hfst ⊢
  have hfactor : 0 < 1 - sineCurveCutoff n := sub_pos.mpr (sineCurveCutoff_lt_one n)
  nlinarith

/-- Helper for Exercise 63.3: the graph-tail range is the portion of the
carrier whose first coordinate is at least the cutoff. -/
private lemma range_sineTailParam (n : ℕ) :
    Set.range (sineTailParam n) =
      {z : TopologistsSineCurve.Space | sineCurveCutoff n ≤ z.1.1} := by
  -- Forward membership is affine monotonicity; backward membership solves for the parameter.
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    change sineCurveCutoff n ≤ sineTailX n t
    dsimp [sineTailX]
    have hfactor : 0 ≤ 1 - sineCurveCutoff n :=
      sub_nonneg.mpr (sineCurveCutoff_lt_one n).le
    nlinarith [t.property.1]
  · intro hz
    have hzCurve : z.1 ∈ TopologistsSineCurve.curve := by
      have hzCarrier := z.property
      change z.1 ∈ TopologistsSineCurve.carrier at hzCarrier
      rw [TopologistsSineCurve.carrier_eq_curve_union_vertical] at hzCarrier
      rcases hzCarrier with hzCurve | hzVertical
      · exact hzCurve
      · rw [TopologistsSineCurve.mem_vertical_iff] at hzVertical
        change sineCurveCutoff n ≤ z.1.1 at hz
        linarith [hz, sineCurveCutoff_pos n]
    rcases hzCurve with ⟨u, hu, huz⟩
    have hfactor : 0 < 1 - sineCurveCutoff n := sub_pos.mpr (sineCurveCutoff_lt_one n)
    have hzu : z.1.1 = u := congrArg Prod.fst huz.symm
    have htmem : (z.1.1 - sineCurveCutoff n) / (1 - sineCurveCutoff n) ∈
        Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hz) hfactor.le
      · apply (div_le_one hfactor).mpr
        rw [hzu]
        linarith [hu.2]
    let t : unitInterval :=
      ⟨(z.1.1 - sineCurveCutoff n) / (1 - sineCurveCutoff n), htmem⟩
    refine ⟨t, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · dsimp [sineTailParam, sineTailX, t]
      field_simp
      ring
    · have hsnd : z.1.2 = Real.sin (1 / z.1.1) := by
        rw [hzu]
        exact congrArg Prod.snd huz.symm
      dsimp [sineTailParam]
      rw [hsnd]
      congr 2
      dsimp [sineTailX, t]
      field_simp
      ring

/-- Helper for Exercise 63.3: the decreasing source-side cores intersect in
the vertical part. -/
private lemma iInter_sineCurveCore_eq_verticalPart :
    (⋂ n : ℕ, {z : TopologistsSineCurve.Space | z.1.1 ≤ sineCurveCutoff n}) =
      TopologistsSineCurve.verticalPart := by
  -- A positive first coordinate eventually exceeds the reciprocal cutoffs.
  ext z
  constructor
  · intro hz
    have hznonneg : 0 ≤ z.1.1 := by
      have hzCarrier := z.property
      change z.1 ∈ TopologistsSineCurve.carrier at hzCarrier
      rw [TopologistsSineCurve.carrier_eq_curve_union_vertical] at hzCarrier
      rcases hzCarrier with hzCurve | hzVertical
      · rcases hzCurve with ⟨u, hu, huz⟩
        rw [← huz]
        exact hu.1.le
      · rw [TopologistsSineCurve.mem_vertical_iff] at hzVertical
        exact hzVertical.1.symm.le
    have hzfst : z.1.1 = 0 := by
      apply le_antisymm
      · by_contra hzpos
        have hzpos' : 0 < z.1.1 := lt_of_not_ge hzpos
        obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (1 / z.1.1)
        have hden : 1 / z.1.1 < (n + 2 : ℕ) := by
          have hnNat : n < n + 2 := by omega
          have hnReal : (n : ℝ) < (n + 2 : ℕ) := by
            exact_mod_cast hnNat
          exact lt_trans hn hnReal
        have hcut : sineCurveCutoff n < z.1.1 := by
          calc
            sineCurveCutoff n = 1 / (n + 2 : ℕ) := rfl
            _ < 1 / (1 / z.1.1) :=
              one_div_lt_one_div_of_lt (one_div_pos.mpr hzpos') hden
            _ = z.1.1 := by field_simp
        exact (not_lt_of_ge (Set.mem_iInter.mp hz n)) hcut
      · exact hznonneg
    rw [TopologistsSineCurve.mem_verticalPart_iff]
    have hzCarrier := z.property
    change z.1 ∈ TopologistsSineCurve.carrier at hzCarrier
    rw [TopologistsSineCurve.carrier_eq_curve_union_vertical] at hzCarrier
    rcases hzCarrier with hzCurve | hzVertical
    · rcases hzCurve with ⟨u, hu, huz⟩
      have hzu : z.1.1 = u := congrArg Prod.fst huz.symm
      linarith [hu.1]
    · exact hzVertical
  · intro hz
    apply Set.mem_iInter.mpr
    intro n
    rw [TopologistsSineCurve.mem_verticalPart_iff,
      TopologistsSineCurve.mem_vertical_iff] at hz
    dsimp
    rw [hz.1]
    exact (sineCurveCutoff_pos n).le

/-- Helper for Exercise 63.3: the range of a continuous injective interval
parametrization in a Hausdorff space is an arc. -/
private lemma isArc_range_of_continuous_injective
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (g : unitInterval → X) (hg : Continuous g) (hginj : Function.Injective g) :
    Topology.IsArc (Set.range g) := by
  -- Compactness of the interval turns the parametrization into an embedding.
  let embedding : Topology.IsEmbedding g := hg.isClosedEmbedding hginj |>.isEmbedding
  exact ⟨⟨embedding.toHomeomorph.symm⟩⟩

/-- Helper for Exercise 63.3: an embedded topologist's sine curve admits
decreasing closed truncation cores with arc tails and vertical-arc limit. -/
private lemma topologistsSineCurve_truncationData
    (D : Set (StandardSphere 2))
    (hD : Nonempty (D ≃ₜ TopologistsSineCurve.Space)) :
    ∃ (V : Set (StandardSphere 2))
      (K A : ℕ → Set (StandardSphere 2)),
      Topology.IsArc V ∧ V ⊆ D ∧
      (∀ n, IsClosed (K n)) ∧
      Directed (· ⊇ ·) K ∧
      ⋂ n, K n = V ∧
      ∀ n, ∃ hAarc : Topology.IsArc (A n), D = K n ∪ A n ∧
          ∃ p : A n, @Topology.IsArc.IsEndpoint (A n) _ hAarc p ∧
            K n ∩ A n = {p.1} := by
  -- Transport the source-side vertical interval, closed left cores, and graph tails.
  classical
  obtain ⟨e⟩ := hD
  let f : TopologistsSineCurve.Space → StandardSphere 2 :=
    fun z ↦ (e.symm z).1
  let V : Set (StandardSphere 2) := Set.range (f ∘ sineVerticalParam)
  let K : ℕ → Set (StandardSphere 2) := fun n ↦
    f '' {z : TopologistsSineCurve.Space | z.1.1 ≤ sineCurveCutoff n}
  let A : ℕ → Set (StandardSphere 2) := fun n ↦
    Set.range (f ∘ sineTailParam n)
  have hfContinuous : Continuous f :=
    continuous_subtype_val.comp e.symm.continuous
  have hfInjective : Function.Injective f :=
    Subtype.val_injective.comp e.symm.injective
  have hfRange : Set.range f = D := by
    apply Set.Subset.antisymm
    · rintro z ⟨u, rfl⟩
      exact (e.symm u).2
    · intro z hz
      refine ⟨e ⟨z, hz⟩, ?_⟩
      simp only [f, e.symm_apply_apply]
  letI : CompactSpace TopologistsSineCurve.Space :=
    isCompact_iff_compactSpace.mp sineCurveCarrier_isCompact
  have hVcontinuous : Continuous (f ∘ sineVerticalParam) :=
    hfContinuous.comp continuous_sineVerticalParam
  have hVinjective : Function.Injective (f ∘ sineVerticalParam) :=
    hfInjective.comp injective_sineVerticalParam
  have hVarc : Topology.IsArc V :=
    isArc_range_of_continuous_injective (f ∘ sineVerticalParam)
      hVcontinuous hVinjective
  refine ⟨V, K, A, hVarc, ?_, ?_, ?_, ?_, ?_⟩
  · -- Every transported vertical point lies in the embedded copy `D`.
    rintro z ⟨t, rfl⟩
    rw [← hfRange]
    exact Set.mem_range_self (sineVerticalParam t)
  · -- Compactness of each source core makes its transported image closed.
    intro n
    have hcoreClosed : IsClosed
        {z : TopologistsSineCurve.Space | z.1.1 ≤ sineCurveCutoff n} := by
      exact isClosed_Iic.preimage (continuous_fst.comp continuous_subtype_val)
    exact (hcoreClosed.isCompact.image hfContinuous).isClosed
  · -- A later cutoff core is contained in each earlier one.
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · rintro z ⟨u, hu, rfl⟩
      refine ⟨u, ?_, rfl⟩
      exact hu.trans (sineCurveCutoff_anti (Nat.le_max_left i j))
    · rintro z ⟨u, hu, rfl⟩
      refine ⟨u, ?_, rfl⟩
      exact hu.trans (sineCurveCutoff_anti (Nat.le_max_right i j))
  · -- Injectivity of the transport turns the source core intersection into `V`.
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨u, huZero, huf⟩ := Set.mem_iInter.mp hz 0
      have huAll : u ∈ ⋂ n : ℕ,
          {w : TopologistsSineCurve.Space | w.1.1 ≤ sineCurveCutoff n} := by
        apply Set.mem_iInter.mpr
        intro n
        obtain ⟨v, hv, hvf⟩ := Set.mem_iInter.mp hz n
        have huv : u = v := hfInjective (huf.trans hvf.symm)
        exact huv ▸ hv
      rw [iInter_sineCurveCore_eq_verticalPart] at huAll
      rw [← range_sineVerticalParam] at huAll
      obtain ⟨t, htu⟩ := huAll
      refine ⟨t, ?_⟩
      change f (sineVerticalParam t) = z
      rw [htu, huf]
    · rintro z ⟨t, rfl⟩
      apply Set.mem_iInter.mpr
      intro n
      refine ⟨sineVerticalParam t, ?_, rfl⟩
      change (0 : ℝ) ≤ sineCurveCutoff n
      exact (sineCurveCutoff_pos n).le
  · intro n
    let g : unitInterval → StandardSphere 2 := f ∘ sineTailParam n
    have hgContinuous : Continuous g :=
      hfContinuous.comp (continuous_sineTailParam n)
    have hgInjective : Function.Injective g :=
      hfInjective.comp (injective_sineTailParam n)
    let embedding : Topology.IsEmbedding g :=
      hgContinuous.isClosedEmbedding hgInjective |>.isEmbedding
    let arcHomeomorph : (Set.range g) ≃ₜ unitInterval :=
      embedding.toHomeomorph.symm
    have hAarc : Topology.IsArc (A n) := by
      change Topology.IsArc (Set.range g)
      exact ⟨⟨arcHomeomorph⟩⟩
    refine ⟨hAarc, ?_, ?_⟩
    · -- The core and its graph tail cover the entire transported carrier.
      apply Set.Subset.antisymm
      · intro z hzD
        rw [← hfRange] at hzD
        obtain ⟨u, rfl⟩ := hzD
        by_cases hu : u.1.1 ≤ sineCurveCutoff n
        · exact Or.inl ⟨u, hu, rfl⟩
        · right
          have huTail : u ∈
              {w : TopologistsSineCurve.Space | sineCurveCutoff n ≤ w.1.1} :=
            le_of_not_ge hu
          rw [← range_sineTailParam] at huTail
          obtain ⟨t, htu⟩ := huTail
          refine ⟨t, ?_⟩
          change f (sineTailParam n t) = f u
          rw [htu]
      · intro z hz
        rcases hz with hzK | hzA
        · obtain ⟨u, -, rfl⟩ := hzK
          rw [← hfRange]
          exact Set.mem_range_self u
        · obtain ⟨t, rfl⟩ := hzA
          rw [← hfRange]
          exact Set.mem_range_self (sineTailParam n t)
    · -- The common point is the initial point of the graph-tail arc.
      let p : A n := ⟨g 0, Set.mem_range_self 0⟩
      refine ⟨p, ?_, ?_⟩
      · rw [@Topology.IsArc.isEndpoint_iff (A n) _ hAarc arcHomeomorph p]
        left
        apply Subtype.ext
        rfl
      · ext z
        constructor
        · intro hz
          obtain ⟨u, hu, huf⟩ := hz.1
          obtain ⟨t, htf⟩ := hz.2
          have hut : u = sineTailParam n t :=
            hfInjective (huf.trans htf.symm)
          have htZero : t = 0 := by
            have hbound : sineTailX n t ≤ sineCurveCutoff n := by
              rw [hut] at hu
              exact hu
            apply Subtype.ext
            dsimp [sineTailX] at hbound ⊢
            have hfactor : 0 < 1 - sineCurveCutoff n :=
              sub_pos.mpr (sineCurveCutoff_lt_one n)
            nlinarith [t.property.1]
          rw [Set.mem_singleton_iff]
          change z = g 0
          rw [← htf, htZero]
        · intro hz
          rw [Set.mem_singleton_iff] at hz
          subst z
          constructor
          · refine ⟨sineTailParam n 0, ?_, rfl⟩
            change sineTailX n 0 ≤ sineCurveCutoff n
            dsimp [sineTailX]
            linarith
          · exact Set.mem_range_self 0

/-- Part (a) of Exercise 63.3: A subspace of the standard two-sphere homeomorphic to the
topologist's sine curve does not separate the sphere. -/
theorem topologistsSineCurve_not_separates
    (D : Set (StandardSphere 2))
    (hD : Nonempty (D ≃ₜ TopologistsSineCurve.Space)) :
    ¬ D.Separates := by
  -- Use the source truncations to reduce arbitrary exterior points to one closed core.
  obtain ⟨V, K, A, hVarc, hVD, hKclosed, hKdirected, hKinter, hgeometry⟩ :=
    topologistsSineCurve_truncationData D hD
  apply not_separates_of_decreasing_closed_cores D V K hKclosed hKdirected hKinter
  · intro x hx y hy
    exact joinedIn_compl_of_isArc V hVarc (fun hxV ↦ hx (hVD hxV))
      (fun hyV ↦ hy (hVD hyV))
  · intro n x hx y hy hxy
    obtain ⟨hAarc, hUnion, hinter⟩ := hgeometry n
    have hxUnion : x ∈ (K n ∪ A n)ᶜ := by
      simpa only [← hUnion] using hx
    have hyUnion : y ∈ (K n ∪ A n)ᶜ := by
      simpa only [← hUnion] using hy
    have hjoined := joinedIn_compl_union_of_arc_endpoint (K n) (A n)
      (hKclosed n) hAarc hinter hxUnion hyUnion hxy
    simpa only [← hUnion] using hjoined

/-- Helper for Exercise 63.3: a continuous injection carries an arc to an arc. -/
private lemma isArc_image_of_continuous_injective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (f : X → Y) (hf : Continuous f) (hfinj : Function.Injective f)
    (S : Set X) (hSarc : Topology.IsArc S) :
    Topology.IsArc (f '' S) := by
  -- Parametrize the source arc by the unit interval and compose with `f`.
  letI : Topology.IsArc S := hSarc
  obtain ⟨e⟩ := Topology.IsArc.homeomorphic_unitInterval (X := S)
  let g : unitInterval → Y := fun t ↦ f (e.symm t).1
  have hgContinuous : Continuous g :=
    hf.comp (continuous_subtype_val.comp e.symm.continuous)
  have hgInjective : Function.Injective g :=
    hfinj.comp (Subtype.val_injective.comp e.symm.injective)
  have hRange : Set.range g = f '' S := by
    apply Set.Subset.antisymm
    · rintro y ⟨t, rfl⟩
      exact ⟨(e.symm t).1, (e.symm t).2, rfl⟩
    · rintro y ⟨x, hx, rfl⟩
      refine ⟨e ⟨x, hx⟩, ?_⟩
      simp only [g, e.symm_apply_apply]
  rw [← hRange]
  exact isArc_range_of_continuous_injective g hgContinuous hgInjective

/-- Helper for Exercise 63.3: a continuous injection carries an arc endpoint
to an endpoint of the image arc. -/
private lemma isEndpoint_image_of_continuous_injective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (f : X → Y) (hf : Continuous f) (hfinj : Function.Injective f)
    (S : Set X) (hSarc : Topology.IsArc S)
    (hImageArc : Topology.IsArc (f '' S)) (p : S)
    (hp : @Topology.IsArc.IsEndpoint S _ hSarc p) :
    @Topology.IsArc.IsEndpoint (f '' S) _ hImageArc
      (⟨f p.1, ⟨p.1, p.2, rfl⟩⟩ : f '' S) := by
  -- The restricted embedding is a homeomorphism onto the image and preserves endpoint coordinates.
  letI : Topology.IsArc S := hSarc
  obtain ⟨e⟩ := Topology.IsArc.homeomorphic_unitInterval (X := S)
  letI : CompactSpace S := e.symm.compactSpace
  let g : S → Y := fun x ↦ f x.1
  have hgContinuous : Continuous g := hf.comp continuous_subtype_val
  have hgInjective : Function.Injective g := hfinj.comp Subtype.val_injective
  let embedding : Topology.IsEmbedding g :=
    hgContinuous.isClosedEmbedding hgInjective |>.isEmbedding
  have hRange : Set.range g = f '' S := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  let F : S ≃ₜ (f '' S) :=
    embedding.toHomeomorph.trans (Homeomorph.setCongr hRange)
  let q : f '' S := ⟨f p.1, ⟨p.1, p.2, rfl⟩⟩
  let eImage : (f '' S) ≃ₜ unitInterval := F.symm.trans e
  have hFp : F p = q := by
    apply Subtype.ext
    rfl
  have heq : eImage q = e p := by
    rw [← hFp]
    simp only [eImage, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  rw [@Topology.IsArc.isEndpoint_iff S _ hSarc e p] at hp
  rw [@Topology.IsArc.isEndpoint_iff (f '' S) _ hImageArc eImage q]
  rcases hp with hp | hp
  · left
    apply eImage.injective
    simp only [heq, hp, e.apply_symm_apply, eImage.apply_symm_apply]
  · right
    apply eImage.injective
    simp only [heq, hp, e.apply_symm_apply, eImage.apply_symm_apply]

/-- Helper for Exercise 63.3: an embedded positive left core of the sine curve
does not separate the sphere. -/
private lemma sineLeftCore_not_separates
    (f : TopologistsSineCurve.Space → StandardSphere 2)
    (hf : Continuous f) (hfinj : Function.Injective f)
    (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    ¬ (f '' TopologistsSineCurve.leftCore c).Separates := by
  -- Transport the arbitrary-cutoff truncation interface and repeat part (a).
  classical
  obtain ⟨V, K, A, hVarc, hVcore, hKclosed, hKdirected, hKinter, hgeometry⟩ :=
    TopologistsSineCurve.leftCoreTruncationData c hc hc1
  let D : Set (StandardSphere 2) := f '' TopologistsSineCurve.leftCore c
  let V' : Set (StandardSphere 2) := f '' V
  let K' : ℕ → Set (StandardSphere 2) := fun n ↦ f '' K n
  let A' : ℕ → Set (StandardSphere 2) := fun n ↦ f '' A n
  letI : CompactSpace TopologistsSineCurve.Space :=
    isCompact_iff_compactSpace.mp sineCurveCarrier_isCompact
  have hV'arc : Topology.IsArc V' :=
    isArc_image_of_continuous_injective f hf hfinj V hVarc
  have hV'D : V' ⊆ D := Set.image_mono hVcore
  have hK'closed : ∀ n, IsClosed (K' n) := by
    intro n
    exact ((hKclosed n).isCompact.image hf).isClosed
  have hK'directed : Directed (· ⊇ ·) K' := by
    intro i j
    obtain ⟨k, hki, hkj⟩ := hKdirected i j
    exact ⟨k, Set.image_mono hki, Set.image_mono hkj⟩
  have hK'inter : ⋂ n, K' n = V' := by
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨u, huZero, huf⟩ := Set.mem_iInter.mp hz 0
      have huAll : u ∈ ⋂ n, K n := by
        apply Set.mem_iInter.mpr
        intro n
        obtain ⟨v, hv, hvf⟩ := Set.mem_iInter.mp hz n
        exact hfinj (huf.trans hvf.symm) ▸ hv
      rw [hKinter] at huAll
      exact ⟨u, huAll, huf⟩
    · rintro z ⟨u, hu, rfl⟩
      have huAll : u ∈ ⋂ n, K n := by
        rwa [hKinter]
      apply Set.mem_iInter.mpr
      intro n
      exact ⟨u, Set.mem_iInter.mp huAll n, rfl⟩
  apply not_separates_of_decreasing_closed_cores D V' K'
    hK'closed hK'directed hK'inter
  · -- The transported vertical arc joins every pair of exterior points.
    intro x hx y hy
    exact joinedIn_compl_of_isArc V' hV'arc
      (fun hxV ↦ hx (hV'D hxV)) (fun hyV ↦ hy (hV'D hyV))
  · intro n x hx y hy hxy
    obtain ⟨hAarc, hUnion, p, hpEndpoint, hinter⟩ := hgeometry n
    have hA'arc : Topology.IsArc (A' n) :=
      isArc_image_of_continuous_injective f hf hfinj (A n) hAarc
    let q : A' n := ⟨f p.1, ⟨p.1, p.2, rfl⟩⟩
    have hqEndpoint : @Topology.IsArc.IsEndpoint (A' n) _ hA'arc q :=
      isEndpoint_image_of_continuous_injective f hf hfinj (A n)
        hAarc hA'arc p hpEndpoint
    have hinter' : K' n ∩ A' n = {(q : StandardSphere 2)} := by
      ext z
      constructor
      · rintro ⟨⟨u, hu, huf⟩, ⟨v, hv, hvf⟩⟩
        have huv : u = v := hfinj (huf.trans hvf.symm)
        have huInter : u ∈ K n ∩ A n := ⟨hu, huv ▸ hv⟩
        rw [hinter, Set.mem_singleton_iff] at huInter
        rw [Set.mem_singleton_iff]
        change z = f p.1
        rw [← huf, huInter]
      · intro hz
        rw [Set.mem_singleton_iff] at hz
        have hpInter : p.1 ∈ K n ∩ A n := by
          rw [hinter]
          exact Set.mem_singleton p.1
        subst z
        exact ⟨⟨p.1, hpInter.1, rfl⟩, ⟨p.1, hpInter.2, rfl⟩⟩
    have hDunion : D = K' n ∪ A' n := by
      change f '' TopologistsSineCurve.leftCore c = f '' K n ∪ f '' A n
      rw [← Set.image_union, ← hUnion]
    have hxUnion : x ∈ (K' n ∪ A' n)ᶜ := by
      simpa only [← hDunion] using hx
    have hyUnion : y ∈ (K' n ∪ A' n)ᶜ := by
      simpa only [← hDunion] using hy
    have hjoined := joinedIn_compl_union_of_arc_endpoint (K' n) (A' n)
      (hK'closed n) hA'arc ⟨q, hqEndpoint, hinter'⟩ hxUnion hyUnion hxy
    simpa only [← hDunion] using hjoined

/-- Helper for Exercise 63.3: concatenating two injective paths whose ranges
meet only at their common endpoint remains injective. -/
private lemma Path.trans_injective_of_range_inter_eq_singleton
    {X : Type*} [TopologicalSpace X] {a b c : X}
    (g₁ : Path a b) (g₂ : Path b c)
    (hg₁ : Function.Injective g₁) (hg₂ : Function.Injective g₂)
    (hinter : Set.range g₁ ∩ Set.range g₂ = {b}) :
    Function.Injective (g₁.trans g₂) := by
  -- Compare the two parameters according to the halves used by `Path.trans`.
  have hcross (s t : unitInterval) (hs : (s : ℝ) ≤ 1 / 2)
      (ht : ¬ (t : ℝ) ≤ 1 / 2) (hst : (g₁.trans g₂) s = (g₁.trans g₂) t) :
      s = t := by
    rw [Path.trans_apply, dif_pos hs, Path.trans_apply, dif_neg ht] at hst
    have hsMem : 2 * (s : ℝ) ∈ Icc (0 : ℝ) 1 := by
      constructor
      · linarith [s.property.1]
      · linarith
    have htMem : 2 * (t : ℝ) - 1 ∈ Icc (0 : ℝ) 1 := by
      constructor
      · linarith [not_le.mp ht]
      · linarith [t.property.2]
    let s₁ : unitInterval := ⟨2 * (s : ℝ), hsMem⟩
    let t₂ : unitInterval := ⟨2 * (t : ℝ) - 1, htMem⟩
    change g₁ s₁ = g₂ t₂ at hst
    have hsInter : g₁ s₁ ∈ Set.range g₁ ∩ Set.range g₂ :=
      ⟨Set.mem_range_self s₁, ⟨t₂, hst.symm⟩⟩
    rw [hinter, Set.mem_singleton_iff] at hsInter
    have hsOne : s₁ = 1 := hg₁ (hsInter.trans g₁.target.symm)
    have htZero : t₂ = 0 := hg₂ (hst.symm.trans hsInter |>.trans g₂.source.symm)
    apply Subtype.ext
    have hsVal := congrArg Subtype.val hsOne
    have htVal := congrArg Subtype.val htZero
    dsimp [s₁, t₂] at hsVal htVal ⊢
    linarith
  intro s t hst
  by_cases hs : (s : ℝ) ≤ 1 / 2
  · by_cases ht : (t : ℝ) ≤ 1 / 2
    · rw [Path.trans_apply, dif_pos hs, Path.trans_apply, dif_pos ht] at hst
      have hparam := congrArg Subtype.val (hg₁ hst)
      apply Subtype.ext
      dsimp at hparam ⊢
      linarith
    · exact hcross s t hs ht hst
  · by_cases ht : (t : ℝ) ≤ 1 / 2
    · exact (hcross t s ht hs hst.symm).symm
    · rw [Path.trans_apply, dif_neg hs, Path.trans_apply, dif_neg ht] at hst
      have hparam := congrArg Subtype.val (hg₂ hst)
      apply Subtype.ext
      dsimp at hparam ⊢
      linarith

/-- Helper for Exercise 63.3: the first two polygonal segments meet only at
their common endpoint `(0,-2)`. -/
private lemma firstSecondSegment_inter :
    segment ℝ ((0, -1) : ℝ × ℝ) (0, -2) ∩
      segment ℝ (0, -2) (1, -2) = {((0, -2) : ℝ × ℝ)} := by
  -- The first segment has first coordinate zero and the second has second coordinate `-2`.
  ext z
  constructor
  · intro hz
    have hfirst := Prod.segment_subset ((0, -1) : ℝ × ℝ) (0, -2) hz.1
    have hsecond := Prod.segment_subset ((0, -2) : ℝ × ℝ) (1, -2) hz.2
    rw [Set.mem_singleton_iff]
    apply Prod.ext
    · simpa only [segment_same, Set.mem_singleton_iff] using hfirst.1
    · simpa only [segment_same, Set.mem_singleton_iff] using hsecond.2
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩

/-- Helper for Exercise 63.3: the last two polygonal segments meet only at
their common endpoint `(1,-2)`. -/
private lemma secondThirdSegment_inter :
    segment ℝ ((0, -2) : ℝ × ℝ) (1, -2) ∩
      segment ℝ (1, -2) (1, Real.sin 1) = {((1, -2) : ℝ × ℝ)} := by
  -- The horizontal segment has second coordinate `-2`, while the vertical
  -- segment has first coordinate one.
  ext z
  constructor
  · intro hz
    have hsecond :=
      Prod.segment_subset ((0, -2) : ℝ × ℝ) (1, -2) hz.1
    have hthird := Prod.segment_subset ((1, -2) : ℝ × ℝ)
      (1, Real.sin 1) hz.2
    rw [Set.mem_singleton_iff]
    apply Prod.ext
    · simpa only [segment_same, Set.mem_singleton_iff] using hthird.1
    · simpa only [segment_same, Set.mem_singleton_iff] using hsecond.2
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩

/-- Helper for Exercise 63.3: the first polygonal segment meets the union of
the last two only at `(0,-2)`. -/
private lemma firstSegment_inter_lastTwo :
    segment ℝ ((0, -1) : ℝ × ℝ) (0, -2) ∩
      (segment ℝ (0, -2) (1, -2) ∪
        segment ℝ (1, -2) (1, Real.sin 1)) =
      {((0, -2) : ℝ × ℝ)} := by
  -- The third segment has first coordinate one, so it misses the first segment.
  ext z
  constructor
  · intro hz
    rcases hz.2 with hzSecond | hzThird
    · have hzPair : z ∈
          segment ℝ ((0, -1) : ℝ × ℝ) (0, -2) ∩
            segment ℝ (0, -2) (1, -2) := ⟨hz.1, hzSecond⟩
      rwa [firstSecondSegment_inter] at hzPair
    · have hfirst := Prod.segment_subset ((0, -1) : ℝ × ℝ) (0, -2) hz.1
      have hthird := Prod.segment_subset ((1, -2) : ℝ × ℝ)
        (1, Real.sin 1) hzThird
      have hxZero : z.1 = 0 := by
        simpa only [segment_same, Set.mem_singleton_iff] using hfirst.1
      have hxOne : z.1 = 1 := by
        simpa only [segment_same, Set.mem_singleton_iff] using hthird.1
      norm_num [hxZero] at hxOne
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact ⟨right_mem_segment ℝ _ _, Or.inl (left_mem_segment ℝ _ _)⟩

/-- Helper for Exercise 63.3: the three-segment path parametrizing the added
broken line. -/
private noncomputable def closedSineBrokenLinePath :
    Path ((0, -1) : ℝ × ℝ) (1, Real.sin 1) :=
  (Path.segment (0, -1) (0, -2)).trans
    ((Path.segment (0, -2) (1, -2)).trans
      (Path.segment (1, -2) (1, Real.sin 1)))

/-- Helper for Exercise 63.3: the three-segment path has exactly the broken
line as its range. -/
private lemma range_closedSineBrokenLinePath :
    Set.range closedSineBrokenLinePath = TopologistsSineCurve.brokenLine := by
  -- Expand the two concatenations and the three segment ranges.
  rw [closedSineBrokenLinePath, Path.trans_range, Path.trans_range,
    Path.range_segment, Path.range_segment, Path.range_segment]
  ext z
  rw [TopologistsSineCurve.mem_brokenLine_iff]
  simp only [Set.mem_union]

/-- Helper for Exercise 63.3: the broken-line parametrization is injective. -/
private lemma injective_closedSineBrokenLinePath :
    Function.Injective closedSineBrokenLinePath := by
  -- First combine the last two segments, then attach the first segment.
  have hsecondNe : ((0, -2) : ℝ × ℝ) ≠ (1, -2) := by norm_num
  have hthirdNe : ((1, -2) : ℝ × ℝ) ≠ (1, Real.sin 1) := by
    intro h
    have hsnd := congrArg Prod.snd h
    linarith [Real.neg_one_le_sin 1]
  have hfirstNe : ((0, -1) : ℝ × ℝ) ≠ (0, -2) := by norm_num
  have hlastInjective : Function.Injective
      ((Path.segment ((0, -2) : ℝ × ℝ) (1, -2)).trans
        (Path.segment (1, -2) (1, Real.sin 1))) := by
    apply Path.trans_injective_of_range_inter_eq_singleton
    · exact Path.segment_injective_of_ne hsecondNe
    · exact Path.segment_injective_of_ne hthirdNe
    · simpa only [Path.range_segment] using secondThirdSegment_inter
  apply Path.trans_injective_of_range_inter_eq_singleton
  · exact Path.segment_injective_of_ne hfirstNe
  · exact hlastInjective
  · simpa only [Path.range_segment, Path.trans_range] using firstSegment_inter_lastTwo

/-- Helper for Exercise 63.3: the planar broken line is an arc. -/
private lemma closedSineBrokenLine_isArc :
    Topology.IsArc TopologistsSineCurve.brokenLine := by
  -- Use the injective three-segment interval parametrization.
  rw [← range_closedSineBrokenLinePath]
  exact isArc_range_of_continuous_injective closedSineBrokenLinePath
    closedSineBrokenLinePath.continuous injective_closedSineBrokenLinePath

/-- Helper for Exercise 63.3: the sine carrier meets the added broken line
only at the two joining endpoints. -/
private lemma sineCarrier_inter_brokenLine :
    TopologistsSineCurve.carrier ∩ TopologistsSineCurve.brokenLine =
      {((0, -1) : ℝ × ℝ), (1, Real.sin 1)} := by
  -- Analyze a common point using the graph/vertical and three-segment decompositions.
  ext z
  constructor
  · rintro ⟨hzCarrier, hzBroken⟩
    rw [TopologistsSineCurve.carrier_eq_curve_union_vertical] at hzCarrier
    rw [TopologistsSineCurve.mem_brokenLine_iff] at hzBroken
    rcases hzCarrier with hzCurve | hzVertical
    · rcases hzCurve with ⟨x, hx, rfl⟩
      rcases hzBroken with hzFirst | hzSecond | hzThird
      · have hcoords := Prod.segment_subset ((0, -1) : ℝ × ℝ) (0, -2) hzFirst
        simp only [segment_same] at hcoords
        exact False.elim (hx.1.ne' hcoords.1)
      · have hcoords := Prod.segment_subset ((0, -2) : ℝ × ℝ) (1, -2) hzSecond
        have hy : Real.sin (1 / x) = -2 := by
          simpa only [segment_same, Set.mem_singleton_iff] using hcoords.2
        linarith [Real.neg_one_le_sin (1 / x)]
      · have hcoords := Prod.segment_subset ((1, -2) : ℝ × ℝ)
          (1, Real.sin 1) hzThird
        have hxOne : x = 1 := by
          simpa only [segment_same, Set.mem_singleton_iff] using hcoords.1
        subst x
        simp
    · rw [TopologistsSineCurve.mem_vertical_iff] at hzVertical
      rcases hzBroken with hzFirst | hzSecond | hzThird
      · have hcoords := Prod.segment_subset ((0, -1) : ℝ × ℝ) (0, -2) hzFirst
        have hySegment : z.2 ∈ segment ℝ (-1) (-2) := hcoords.2
        have hyUpper : z.2 ≤ -1 := by
          have horder : (-2 : ℝ) ≤ -1 := by norm_num
          rw [segment_eq_uIcc, uIcc_of_ge horder] at hySegment
          exact hySegment.2
        have hy : z.2 = -1 := le_antisymm hyUpper hzVertical.2.1
        left
        exact Prod.ext hzVertical.1 hy
      · have hcoords := Prod.segment_subset ((0, -2) : ℝ × ℝ) (1, -2) hzSecond
        have hy : z.2 = -2 := by
          simpa only [segment_same, Set.mem_singleton_iff] using hcoords.2
        linarith [hzVertical.2.1]
      · have hcoords := Prod.segment_subset ((1, -2) : ℝ × ℝ)
          (1, Real.sin 1) hzThird
        have hxOne : z.1 = 1 := by
          simpa only [segment_same, Set.mem_singleton_iff] using hcoords.1
        norm_num [hzVertical.1] at hxOne
  · intro hz
    rcases hz with rfl | rfl
    · constructor
      · rw [TopologistsSineCurve.carrier_eq_curve_union_vertical]
        right
        rw [TopologistsSineCurve.mem_vertical_iff]
        have hbounds : (-1 : ℝ) ∈ Icc (-1) 1 := by norm_num
        exact ⟨rfl, hbounds⟩
      · rw [TopologistsSineCurve.mem_brokenLine_iff]
        exact Or.inl (left_mem_segment ℝ _ _)
    · constructor
      · rw [TopologistsSineCurve.carrier_eq_curve_union_vertical]
        left
        have hgraph : ((1 : ℝ), Real.sin (1 / 1)) = (1, Real.sin 1) := by
          norm_num
        exact ⟨1, ⟨zero_lt_one, le_rfl⟩, hgraph⟩
      · rw [TopologistsSineCurve.mem_brokenLine_iff]
        exact Or.inr (Or.inr (right_mem_segment ℝ _ _))

/-- Helper for Exercise 63.3: the sine carrier is contained in the closed
sine-curve carrier. -/
private lemma sineCarrier_subset_closedCarrier :
    TopologistsSineCurve.carrier ⊆ TopologistsSineCurve.closedCarrier := by
  -- The closed carrier is defined by adjoining the broken line.
  intro z hz
  exact (TopologistsSineCurve.mem_closedCarrier_iff z).2 (Or.inl hz)

/-- Helper for Exercise 63.3: the broken line is contained in the closed
sine-curve carrier. -/
private lemma brokenLine_subset_closedCarrier :
    TopologistsSineCurve.brokenLine ⊆ TopologistsSineCurve.closedCarrier := by
  -- The closed carrier contains its adjoined broken-line piece.
  intro z hz
  exact (TopologistsSineCurve.mem_closedCarrier_iff z).2 (Or.inr hz)

/-- Helper for Exercise 63.3: include the sine carrier into the closed
sine-curve carrier. -/
private def sineCarrierToClosedSpace (z : TopologistsSineCurve.Space) :
    TopologistsSineCurve.ClosedSpace :=
  ⟨z.1, sineCarrier_subset_closedCarrier z.2⟩

/-- Helper for Exercise 63.3: the carrier inclusion is continuous. -/
private lemma continuous_sineCarrierToClosedSpace :
    Continuous sineCarrierToClosedSpace := by
  -- Both subspaces use the same ambient planar value.
  exact continuous_subtype_val.subtype_mk
    (fun z ↦ sineCarrier_subset_closedCarrier z.2)

/-- Helper for Exercise 63.3: the carrier inclusion is injective. -/
private lemma injective_sineCarrierToClosedSpace :
    Function.Injective sineCarrierToClosedSpace := by
  -- Equality in the larger subtype determines equality in the smaller one.
  intro z w hzw
  apply Subtype.ext
  exact congrArg (fun u : TopologistsSineCurve.ClosedSpace ↦ u.1) hzw

/-- Helper for Exercise 63.3: every point of the broken-line path belongs to
the planar broken line. -/
private lemma closedSineBrokenLinePath_mem (t : unitInterval) :
    closedSineBrokenLinePath t ∈ TopologistsSineCurve.brokenLine := by
  -- Use the computed path range.
  rw [← range_closedSineBrokenLinePath]
  exact Set.mem_range_self t

/-- Helper for Exercise 63.3: lift the broken-line path to the closed
sine-curve space. -/
private noncomputable def brokenLinePathToClosedSpace (t : unitInterval) :
    TopologistsSineCurve.ClosedSpace :=
  ⟨closedSineBrokenLinePath t,
    brokenLine_subset_closedCarrier (closedSineBrokenLinePath_mem t)⟩

/-- Helper for Exercise 63.3: the lifted broken-line path is continuous. -/
private lemma continuous_brokenLinePathToClosedSpace :
    Continuous brokenLinePathToClosedSpace := by
  -- Lift continuity of the planar path through the subtype constructor.
  exact closedSineBrokenLinePath.continuous.subtype_mk
    (fun t ↦ brokenLine_subset_closedCarrier (closedSineBrokenLinePath_mem t))

/-- Helper for Exercise 63.3: the lifted broken-line path is injective. -/
private lemma injective_brokenLinePathToClosedSpace :
    Function.Injective brokenLinePathToClosedSpace := by
  -- Injectivity reduces to the planar path computation.
  intro s t hst
  exact injective_closedSineBrokenLinePath (congrArg Subtype.val hst)

/-- Helper for Exercise 63.3: the graph branch of the ordered nonvertical spine. -/
private noncomputable def closedSineSpineGraphBranch (t : ℝ) : ℝ × ℝ :=
  (1 / (1 - t), Real.sin (1 - t))

/-- Helper for Exercise 63.3: the broken-line branch of the ordered nonvertical spine. -/
private noncomputable def closedSineSpineBrokenBranch (t : ℝ) : ℝ × ℝ :=
  closedSineBrokenLinePath (Set.projIcc 0 1 zero_le_one (1 / (1 + t)))

/-- Helper for Exercise 63.3: the two spine branches agree at their common parameter zero. -/
private lemma closedSineSpineBranches_zero :
    closedSineSpineGraphBranch 0 = closedSineSpineBrokenBranch 0 := by
  -- Both formulas give the common endpoint `(1, sin 1)`.
  rw [closedSineSpineGraphBranch, closedSineSpineBrokenBranch]
  norm_num

/-- Helper for Exercise 63.3: the piecewise planar parametrization follows the
graph for nonpositive parameters and the broken line for positive parameters. -/
private noncomputable def closedSineSpinePlaneParam (t : ℝ) : ℝ × ℝ :=
  if t ≤ 0 then closedSineSpineGraphBranch t else closedSineSpineBrokenBranch t

/-- Helper for Exercise 63.3: every nonpositive graph-branch parameter lies
in the ordinary sine-curve carrier. -/
private lemma closedSineSpineGraphBranch_mem_carrier {t : ℝ} (ht : t ≤ 0) :
    closedSineSpineGraphBranch t ∈ TopologistsSineCurve.carrier := by
  -- The reciprocal first coordinate lies in `(0,1]`.
  rw [TopologistsSineCurve.carrier_eq_curve_union_vertical]
  left
  have hden : 0 < 1 - t := by linarith
  refine ⟨1 / (1 - t), ⟨one_div_pos.mpr hden, ?_⟩, ?_⟩
  · exact (div_le_one hden).2 (by linarith)
  · apply Prod.ext
    · rfl
    · rw [closedSineSpineGraphBranch]
      congr 2
      field_simp

/-- Helper for Exercise 63.3: every point of the planar spine parametrization
belongs to the closed topologist's sine curve. -/
private lemma closedSineSpinePlaneParam_mem (t : ℝ) :
    closedSineSpinePlaneParam t ∈ TopologistsSineCurve.closedCarrier := by
  -- Each sign branch lies in its corresponding half of the closed carrier.
  by_cases ht : t ≤ 0
  · rw [closedSineSpinePlaneParam, if_pos ht]
    exact sineCarrier_subset_closedCarrier (closedSineSpineGraphBranch_mem_carrier ht)
  · rw [closedSineSpinePlaneParam, if_neg ht]
    apply brokenLine_subset_closedCarrier
    rw [← range_closedSineBrokenLinePath]
    exact Set.mem_range_self (Set.projIcc 0 1 zero_le_one (1 / (1 + t)))

/-- Helper for Exercise 63.3: a real parametrization of the nonvertical spine
inside the closed sine-curve space. -/
private noncomputable def closedSineSpineParam (t : ℝ) :
    TopologistsSineCurve.ClosedSpace :=
  ⟨closedSineSpinePlaneParam t, closedSineSpinePlaneParam_mem t⟩

/-- Helper for Exercise 63.3: the nonvertical-spine parametrization is continuous. -/
private lemma continuous_closedSineSpineParam : Continuous closedSineSpineParam := by
  -- Paste the graph and broken-line branches along their common endpoint.
  have hgraph : ContinuousOn closedSineSpineGraphBranch (Iic (0 : ℝ)) := by
    have hden : ∀ t ∈ Iic (0 : ℝ), 1 - t ≠ 0 := by
      intro t ht
      change t ≤ 0 at ht
      linarith
    have hx : ContinuousOn (fun t : ℝ ↦ 1 / (1 - t)) (Iic (0 : ℝ)) :=
      continuousOn_const.div (continuousOn_const.sub continuousOn_id) hden
    exact hx.prodMk (Real.continuous_sin.comp_continuousOn
      (continuousOn_const.sub continuousOn_id))
  have hbroken : ContinuousOn closedSineSpineBrokenBranch (Ici (0 : ℝ)) := by
    have hden : ∀ t ∈ Ici (0 : ℝ), 1 + t ≠ 0 := by
      intro t ht
      change 0 ≤ t at ht
      linarith
    have hx : ContinuousOn (fun t : ℝ ↦ 1 / (1 + t)) (Ici (0 : ℝ)) :=
      continuousOn_const.div (continuousOn_const.add continuousOn_id) hden
    exact closedSineBrokenLinePath.continuous.comp_continuousOn
      (continuous_projIcc.comp_continuousOn hx)
  have hplane : Continuous closedSineSpinePlaneParam := by
    change Continuous (fun t : ℝ ↦
      if t ≤ 0 then closedSineSpineGraphBranch t else closedSineSpineBrokenBranch t)
    apply continuous_if_le continuous_id continuous_const hgraph hbroken
    intro t ht
    have htZero : t = 0 := by simpa using ht
    rw [htZero]
    exact closedSineSpineBranches_zero
  exact hplane.subtype_mk closedSineSpinePlaneParam_mem

/-- Helper for Exercise 63.3: on the nonnegative half-line the projected
broken-line parameter is the displayed reciprocal. -/
private lemma closedSineSpineBrokenParameter_eq {t : ℝ} (ht : 0 ≤ t) :
    Set.projIcc 0 1 zero_le_one (1 / (1 + t)) =
      (⟨1 / (1 + t), by
        constructor
        · positivity
        · exact (div_le_one (by linarith : 0 < 1 + t)).2 (by linarith)⟩ : unitInterval) := by
  -- Projection fixes points already in the unit interval.
  exact Set.projIcc_of_mem zero_le_one _

/-- Helper for Exercise 63.3: the nonvertical-spine parametrization is injective. -/
private lemma injective_closedSineSpineParam : Function.Injective closedSineSpineParam := by
  -- Each branch is ordered by its first or path parameter, and their interiors are disjoint.
  have hgraphInjective {s t : ℝ} (hs : s ≤ 0) (ht : t ≤ 0)
      (hst : closedSineSpineGraphBranch s = closedSineSpineGraphBranch t) : s = t := by
    have hfst := congrArg Prod.fst hst
    rw [closedSineSpineGraphBranch, closedSineSpineGraphBranch] at hfst
    have hden : 1 - s = 1 - t := by
      apply inv_injective
      simpa only [one_div] using hfst
    linarith
  have hbrokenInjective {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
      (hst : closedSineSpineBrokenBranch s = closedSineSpineBrokenBranch t) : s = t := by
    rw [closedSineSpineBrokenBranch, closedSineSpineBrokenBranch] at hst
    have hparam := injective_closedSineBrokenLinePath hst
    have hval := congrArg Subtype.val hparam
    rw [closedSineSpineBrokenParameter_eq hs,
      closedSineSpineBrokenParameter_eq ht] at hval
    have hden : 1 + s = 1 + t := by
      apply inv_injective
      simpa only [one_div] using hval
    linarith
  have hcross {s t : ℝ} (hs : s ≤ 0) (ht : 0 < t)
      (hst : closedSineSpineGraphBranch s = closedSineSpineBrokenBranch t) : False := by
    have hgraphMem := closedSineSpineGraphBranch_mem_carrier hs
    have hbrokenMem : closedSineSpineBrokenBranch t ∈ TopologistsSineCurve.brokenLine := by
      rw [closedSineSpineBrokenBranch, ← range_closedSineBrokenLinePath]
      exact Set.mem_range_self _
    have hinter : closedSineSpineGraphBranch s ∈
        TopologistsSineCurve.carrier ∩ TopologistsSineCurve.brokenLine :=
      ⟨hgraphMem, hst ▸ hbrokenMem⟩
    rw [sineCarrier_inter_brokenLine] at hinter
    rcases hinter with hleft | hright
    · have hfst := congrArg Prod.fst hleft
      rw [closedSineSpineGraphBranch] at hfst
      have hpos : 0 < 1 / (1 - s) := one_div_pos.mpr (by linarith)
      norm_num at hfst
      linarith
    · have hpathTarget :
          closedSineBrokenLinePath (Set.projIcc 0 1 zero_le_one (1 / (1 + t))) =
            closedSineBrokenLinePath 1 := by
        rw [closedSineBrokenLinePath.target]
        exact hst.symm.trans hright
      have hparam := injective_closedSineBrokenLinePath hpathTarget
      have hval := congrArg Subtype.val hparam
      rw [closedSineSpineBrokenParameter_eq ht.le] at hval
      norm_num at hval
      exact ht.ne' hval
  intro s t hst
  have hplane : closedSineSpinePlaneParam s = closedSineSpinePlaneParam t :=
    congrArg Subtype.val hst
  by_cases hs : s ≤ 0
  · by_cases ht : t ≤ 0
    · simp only [closedSineSpinePlaneParam, if_pos hs, if_pos ht] at hplane
      exact hgraphInjective hs ht hplane
    · simp only [closedSineSpinePlaneParam, if_pos hs, if_neg ht] at hplane
      exact (hcross hs (lt_of_not_ge ht) hplane).elim
  · by_cases ht : t ≤ 0
    · simp only [closedSineSpinePlaneParam, if_neg hs, if_pos ht] at hplane
      exact (hcross ht (lt_of_not_ge hs) hplane.symm).elim
    · simp only [closedSineSpinePlaneParam, if_neg hs, if_neg ht] at hplane
      exact hbrokenInjective (le_of_not_ge hs) (le_of_not_ge ht) hplane

/-- Helper for Exercise 63.3: the real spine parametrization covers exactly
the complement of the limiting vertical interval in the closed sine curve. -/
private lemma range_closedSineSpineParam :
    Set.range closedSineSpineParam =
      {z : TopologistsSineCurve.ClosedSpace |
        z.1 ∉ TopologistsSineCurve.vertical} := by
  -- First check that neither branch enters the limiting vertical interval.
  apply Set.Subset.antisymm
  · rintro z ⟨t, rfl⟩
    by_cases ht : t ≤ 0
    · intro hzVertical
      change closedSineSpinePlaneParam t ∈ TopologistsSineCurve.vertical at hzVertical
      rw [TopologistsSineCurve.mem_vertical_iff] at hzVertical
      rw [closedSineSpinePlaneParam, if_pos ht,
        closedSineSpineGraphBranch] at hzVertical
      have hden : 0 < 1 - t := by linarith
      exact (one_div_pos.mpr hden).ne' hzVertical.1
    · intro hzVertical
      have htpos : 0 < t := lt_of_not_ge ht
      have hbranchBroken : closedSineSpineBrokenBranch t ∈
          TopologistsSineCurve.brokenLine := by
        rw [closedSineSpineBrokenBranch, ← range_closedSineBrokenLinePath]
        exact Set.mem_range_self _
      have hbranchCarrier : closedSineSpineBrokenBranch t ∈
          TopologistsSineCurve.carrier := by
        rw [TopologistsSineCurve.carrier_eq_curve_union_vertical]
        right
        change closedSineSpinePlaneParam t ∈ TopologistsSineCurve.vertical at hzVertical
        rwa [closedSineSpinePlaneParam, if_neg ht] at hzVertical
      have hinter : closedSineSpineBrokenBranch t ∈
          TopologistsSineCurve.carrier ∩ TopologistsSineCurve.brokenLine :=
        ⟨hbranchCarrier, hbranchBroken⟩
      rw [sineCarrier_inter_brokenLine] at hinter
      rcases hinter with hleft | hright
      · have hparam : Set.projIcc 0 1 zero_le_one (1 / (1 + t)) = 0 :=
          injective_closedSineBrokenLinePath
            (hleft.trans closedSineBrokenLinePath.source.symm)
        have hval := congrArg Subtype.val hparam
        rw [closedSineSpineBrokenParameter_eq htpos.le] at hval
        norm_num at hval
        linarith
      · have hparam : Set.projIcc 0 1 zero_le_one (1 / (1 + t)) = 1 :=
          injective_closedSineBrokenLinePath
            (hright.trans closedSineBrokenLinePath.target.symm)
        have hval := congrArg Subtype.val hparam
        rw [closedSineSpineBrokenParameter_eq htpos.le] at hval
        norm_num at hval
        exact htpos.ne' hval
  -- Conversely, split a nonvertical point into its graph or broken-line source.
  · intro z hzVertical
    have hzClosed := z.property
    rw [TopologistsSineCurve.mem_closedCarrier_iff] at hzClosed
    rcases hzClosed with hzCarrier | hzBroken
    · rw [TopologistsSineCurve.carrier_eq_curve_union_vertical] at hzCarrier
      rcases hzCarrier with hzCurve | hzVertical'
      · rcases hzCurve with ⟨x, hx, hxz⟩
        let t : ℝ := 1 - 1 / x
        have ht : t ≤ 0 := by
          have hone : 1 ≤ 1 / x := (le_div_iff₀ hx.1).2 (by nlinarith [hx.2])
          dsimp [t]
          linarith
        refine ⟨t, ?_⟩
        apply Subtype.ext
        change closedSineSpinePlaneParam t = z.1
        rw [closedSineSpinePlaneParam, if_pos ht,
          closedSineSpineGraphBranch, ← hxz]
        apply Prod.ext
        · dsimp [t]
          field_simp [hx.1.ne']
          ring
        · dsimp [t]
          congr 2
          ring
      · exact (hzVertical hzVertical').elim
    · rw [← range_closedSineBrokenLinePath] at hzBroken
      obtain ⟨u, huz⟩ := hzBroken
      have huNonzero : u ≠ 0 := by
        intro hu
        subst u
        apply hzVertical
        rw [← huz, closedSineBrokenLinePath.source,
          TopologistsSineCurve.mem_vertical_iff]
        norm_num
      have hupos : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1
        (fun h ↦ huNonzero (Subtype.ext h.symm))
      let t : ℝ := 1 / (u : ℝ) - 1
      have ht : 0 ≤ t := by
        have hone : 1 ≤ 1 / (u : ℝ) :=
          (le_div_iff₀ hupos).2 (by nlinarith [u.property.2])
        dsimp [t]
        linarith
      by_cases htZero : t = 0
      · refine ⟨t, ?_⟩
        apply Subtype.ext
        change closedSineSpinePlaneParam t = z.1
        rw [htZero, closedSineSpinePlaneParam, if_pos le_rfl,
          closedSineSpineBranches_zero]
        have huOne : u = 1 := by
          have huval : (u : ℝ) = 1 := by
            dsimp [t] at htZero
            field_simp at htZero
            linarith
          exact Subtype.ext huval
        have hbranch : closedSineSpineBrokenBranch 0 =
            closedSineBrokenLinePath u := by
          rw [closedSineSpineBrokenBranch]
          apply congrArg closedSineBrokenLinePath
          apply Subtype.ext
          rw [huOne]
          norm_num
        exact hbranch.trans huz
      · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm htZero)
        refine ⟨t, ?_⟩
        apply Subtype.ext
        change closedSineSpinePlaneParam t = z.1
        rw [closedSineSpinePlaneParam, if_neg (not_le.mpr htpos),
          closedSineSpineBrokenBranch,
          closedSineSpineBrokenParameter_eq htpos.le]
        have hparameter :
            (⟨1 / (1 + t), by
              constructor
              · positivity
              · exact (div_le_one (by linarith : 0 < 1 + t)).2 (by linarith)⟩ :
                unitInterval) = u := by
          apply Subtype.ext
          dsimp [t]
          field_simp
          ring
        rw [hparameter, huz]

/-- Helper for Exercise 63.3: the nonvertical spine is dense in the closed
topologist's sine curve. -/
private lemma denseRange_closedSineSpineParam :
    DenseRange closedSineSpineParam := by
  -- Nonvertical points are already in the range; vertical points are limits
  -- of graph points, which are also in the range.
  rw [denseRange_iff_closure_range]
  ext z
  simp only [Set.mem_univ, iff_true]
  by_cases hzVertical : z.1 ∈ TopologistsSineCurve.vertical
  · rw [closure_subtype]
    have hzCarrier : z.1 ∈ TopologistsSineCurve.carrier := by
      rw [TopologistsSineCurve.carrier_eq_curve_union_vertical]
      exact Or.inr hzVertical
    apply closure_mono _ hzCarrier
    rintro w ⟨x, hx, rfl⟩
    have hwCarrier : (x, Real.sin (1 / x)) ∈
        TopologistsSineCurve.carrier := subset_closure ⟨x, hx, rfl⟩
    let w' : TopologistsSineCurve.ClosedSpace :=
      ⟨(x, Real.sin (1 / x)), sineCarrier_subset_closedCarrier hwCarrier⟩
    have hwNotVertical : w'.1 ∉ TopologistsSineCurve.vertical := by
      intro hwVertical
      rw [TopologistsSineCurve.mem_vertical_iff] at hwVertical
      exact hx.1.ne' hwVertical.1
    have hwRange : w' ∈ Set.range closedSineSpineParam := by
      rw [range_closedSineSpineParam]
      exact hwNotVertical
    exact ⟨w', hwRange, rfl⟩
  · apply subset_closure
    rw [range_closedSineSpineParam]
    exact hzVertical

/-- Helper for Exercise 63.3: separation together with an upper bound of two
complementary components forces exactly two complementary components. -/
private lemma separatesInto_two_of_separates_of_components_le_two
    {X : Type*} [TopologicalSpace X] (A : Set X)
    (hsep : A.Separates)
    (hle : Cardinal.mk (ConnectedComponents (Aᶜ : Set X)) ≤ 2) :
    A.SeparatesInto 2 := by
  -- Separation excludes the only cardinalities strictly below two.
  rw [Set.separatesInto_iff]
  apply le_antisymm hle
  by_contra hnot
  have hlt : Cardinal.mk (ConnectedComponents (Aᶜ : Set X)) < (2 : Cardinal) :=
    lt_of_not_ge hnot
  have hone : Cardinal.mk (ConnectedComponents (Aᶜ : Set X)) ≤ 1 := by
    apply Cardinal.lt_natCast_add_one_iff.mp
    norm_num at hlt ⊢
    exact hlt
  have hsub : Subsingleton (ConnectedComponents (Aᶜ : Set X)) :=
    Cardinal.le_one_iff_subsingleton.mp hone
  have hpre : PreconnectedSpace (Aᶜ : Set X) :=
    preconnectedSpace_iff_connectedComponent.mpr (fun x ↦ by
      apply eq_univ_of_forall
      intro y
      rw [← connectedComponent_eq_iff_mem]
      exact ConnectedComponents.coe_eq_coe.mp
        (@Subsingleton.elim _ hsub (y : ConnectedComponents _) (x : ConnectedComponents _)))
  exact (Set.separates_iff.mp hsep) hpre

/-- Helper for Exercise 63.3: the transported closed sine curve decomposes
into a nonseparating sine-curve carrier and a nonseparating arc meeting it in
two distinct points. -/
private lemma closedSineCurve_pairGeometry
    (C : Set (StandardSphere 2))
    (hC : Nonempty (C ≃ₜ TopologistsSineCurve.ClosedSpace)) :
    ∃ D A : Set (StandardSphere 2), ∃ p q : StandardSphere 2,
      C = D ∪ A ∧ p ≠ q ∧ D ∩ A = {p, q} ∧
      IsClosed D ∧ IsClosed A ∧ IsConnected D ∧ IsConnected A ∧
      ¬ D.Separates ∧ ¬ A.Separates := by
  -- Transport the carrier inclusion and the injective broken-line path through `hC`.
  classical
  obtain ⟨e⟩ := hC
  letI : CompactSpace TopologistsSineCurve.Space :=
    isCompact_iff_compactSpace.mp sineCurveCarrier_isCompact
  let f : TopologistsSineCurve.ClosedSpace → StandardSphere 2 :=
    fun z ↦ (e.symm z).1
  let g : TopologistsSineCurve.Space → StandardSphere 2 :=
    f ∘ sineCarrierToClosedSpace
  let h : unitInterval → StandardSphere 2 :=
    f ∘ brokenLinePathToClosedSpace
  let D : Set (StandardSphere 2) := Set.range g
  let A : Set (StandardSphere 2) := Set.range h
  have hfContinuous : Continuous f :=
    continuous_subtype_val.comp e.symm.continuous
  have hfInjective : Function.Injective f :=
    Subtype.val_injective.comp e.symm.injective
  have hgContinuous : Continuous g :=
    hfContinuous.comp continuous_sineCarrierToClosedSpace
  have hgInjective : Function.Injective g :=
    hfInjective.comp injective_sineCarrierToClosedSpace
  have hhContinuous : Continuous h :=
    hfContinuous.comp continuous_brokenLinePathToClosedSpace
  have hhInjective : Function.Injective h :=
    hfInjective.comp injective_brokenLinePathToClosedSpace
  have hleftCarrier : ((0, -1) : ℝ × ℝ) ∈ TopologistsSineCurve.carrier := by
    rw [TopologistsSineCurve.carrier_eq_curve_union_vertical]
    right
    rw [TopologistsSineCurve.mem_vertical_iff]
    have hbounds : (-1 : ℝ) ∈ Icc (-1) 1 := by norm_num
    exact ⟨rfl, hbounds⟩
  have hrightCarrier : ((1, Real.sin 1) : ℝ × ℝ) ∈
      TopologistsSineCurve.carrier := by
    rw [TopologistsSineCurve.carrier_eq_curve_union_vertical]
    left
    have hgraph : ((1 : ℝ), Real.sin (1 / 1)) = (1, Real.sin 1) := by
      norm_num
    exact ⟨1, ⟨zero_lt_one, le_rfl⟩, hgraph⟩
  let p₀ : TopologistsSineCurve.Space := ⟨(0, -1), hleftCarrier⟩
  let q₀ : TopologistsSineCurve.Space := ⟨(1, Real.sin 1), hrightCarrier⟩
  let p : StandardSphere 2 := g p₀
  let q : StandardSphere 2 := g q₀
  have hpq : p ≠ q := by
    intro hpq
    have hp₀q₀ : p₀ = q₀ := hgInjective hpq
    have hfst := congrArg (fun z : TopologistsSineCurve.Space ↦ z.1.1) hp₀q₀
    norm_num [p₀, q₀] at hfst
  have hhZero : h 0 = p := by
    apply congrArg f
    apply Subtype.ext
    exact closedSineBrokenLinePath.source
  have hhOne : h 1 = q := by
    apply congrArg f
    apply Subtype.ext
    exact closedSineBrokenLinePath.target
  have hUnion : C = D ∪ A := by
    apply Set.Subset.antisymm
    · intro z hzC
      let zC : C := ⟨z, hzC⟩
      let s : TopologistsSineCurve.ClosedSpace := e zC
      have hsClosed : s.1 ∈ TopologistsSineCurve.closedCarrier := s.2
      rw [TopologistsSineCurve.mem_closedCarrier_iff] at hsClosed
      rcases hsClosed with hsCarrier | hsBroken
      · left
        let u : TopologistsSineCurve.Space := ⟨s.1, hsCarrier⟩
        refine ⟨u, ?_⟩
        change (e.symm (sineCarrierToClosedSpace u)).1 = z
        have hus : sineCarrierToClosedSpace u = s := by
          apply Subtype.ext
          rfl
        rw [hus]
        exact congrArg Subtype.val (e.symm_apply_apply zC)
      · right
        rw [← range_closedSineBrokenLinePath] at hsBroken
        obtain ⟨t, hts⟩ := hsBroken
        refine ⟨t, ?_⟩
        change (e.symm (brokenLinePathToClosedSpace t)).1 = z
        have hts' : brokenLinePathToClosedSpace t = s := by
          apply Subtype.ext
          exact hts
        rw [hts']
        exact congrArg Subtype.val (e.symm_apply_apply zC)
    · intro z hz
      rcases hz with hzD | hzA
      · obtain ⟨u, rfl⟩ := hzD
        exact (e.symm (sineCarrierToClosedSpace u)).2
      · obtain ⟨t, rfl⟩ := hzA
        exact (e.symm (brokenLinePathToClosedSpace t)).2
  have hInter : D ∩ A = {p, q} := by
    ext z
    constructor
    · intro hz
      obtain ⟨u, hug⟩ := hz.1
      obtain ⟨t, hth⟩ := hz.2
      have hsource : sineCarrierToClosedSpace u = brokenLinePathToClosedSpace t :=
        hfInjective (hug.trans hth.symm)
      have hplane : u.1 = closedSineBrokenLinePath t :=
        congrArg Subtype.val hsource
      have huInter : u.1 ∈
          TopologistsSineCurve.carrier ∩ TopologistsSineCurve.brokenLine :=
        ⟨u.2, hplane ▸ closedSineBrokenLinePath_mem t⟩
      rw [sineCarrier_inter_brokenLine] at huInter
      rcases huInter with huLeft | huRight
      · left
        have hup₀ : u = p₀ := Subtype.ext huLeft
        exact hug.symm.trans (congrArg g hup₀)
      · right
        have huq₀ : u = q₀ := Subtype.ext huRight
        exact hug.symm.trans (congrArg g huq₀)
    · intro hz
      rcases hz with rfl | rfl
      · exact ⟨⟨p₀, rfl⟩, ⟨0, hhZero⟩⟩
      · exact ⟨⟨q₀, rfl⟩, ⟨1, hhOne⟩⟩
  have hDclosed : IsClosed D := (isCompact_range hgContinuous).isClosed
  have hAclosed : IsClosed A := (isCompact_range hhContinuous).isClosed
  have hDconnected : IsConnected D := by
    have hDrange : D = Set.range g := rfl
    rw [hDrange, ← Set.image_univ]
    exact isConnected_univ.image g hgContinuous.continuousOn
  have hAconnected : IsConnected A := isConnected_range hhContinuous
  have hDnonseparating : ¬ D.Separates := by
    let embedding : Topology.IsEmbedding g :=
      hgContinuous.isClosedEmbedding hgInjective |>.isEmbedding
    exact topologistsSineCurve_not_separates D ⟨embedding.toHomeomorph.symm⟩
  have hAarc : Topology.IsArc A :=
    isArc_range_of_continuous_injective h hhContinuous hhInjective
  letI : Topology.IsArc A := hAarc
  have hAnonseparating : ¬ A.Separates := arc_not_separates A
  exact ⟨D, A, p, q, hUnion, hpq, hInter, hDclosed, hAclosed,
    hDconnected, hAconnected, hDnonseparating, hAnonseparating⟩

/-- Helper for Exercise 63.3: a two-point intersection places both points in
each of the intersecting sets. -/
private lemma pair_mem_of_inter_eq_pair
    {X : Type*} {D A : Set X} {p q : X} (hinter : D ∩ A = {p, q}) :
    p ∈ D ∧ p ∈ A ∧ q ∈ D ∧ q ∈ A := by
  -- Read the membership of each listed point through the intersection equation.
  have hp : p ∈ D ∩ A := by
    rw [hinter]
    simp
  have hq : q ∈ D ∩ A := by
    rw [hinter]
    simp
  exact ⟨hp.1, hp.2, hq.1, hq.2⟩

/-- Helper for Exercise 63.3: a connected set containing two distinct points
also contains a point different from both. -/
private lemma exists_mem_connected_ne_pair
    {X : Type*} [TopologicalSpace X] [T1Space X]
    (S : Set X) (hS : IsConnected S) (p q : X)
    (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) :
    ∃ r ∈ S, r ≠ p ∧ r ≠ q := by
  -- Otherwise the two singleton complements disconnect `S` and separate `p` from `q`.
  by_contra hthird
  have hSsub : S ⊆ {p, q} := by
    intro r hr
    by_cases hrp : r = p
    · exact Or.inl hrp
    · by_cases hrq : r = q
      · exact Or.inr hrq
      · exact (hthird ⟨r, hr, hrp, hrq⟩).elim
  let U : Set X := ({q} : Set X)ᶜ
  let V : Set X := ({p} : Set X)ᶜ
  have hcover : S ⊆ U ∪ V := by
    intro r hr
    by_cases hrp : r = p
    · exact Or.inl (fun hrq ↦ hpq (hrp.symm.trans hrq))
    · exact Or.inr hrp
  have hinterEmpty : S ∩ (U ∩ V) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro r hr
    rcases hSsub hr.1 with hrp | hrq
    · exact hr.2.2 hrp
    · exact hr.2.1 hrq
  obtain hSU | hSV := (isPreconnected_iff_subset_of_disjoint.mp hS.isPreconnected)
    U V isOpen_compl_singleton isOpen_compl_singleton hcover hinterEmpty
  · exact hSU hq rfl
  · exact hSV hp rfl

/-- Helper for Exercise 63.3: the complement preimages of sets meeting at two
punctures cover the twice-punctured space. -/
private lemma pairComplement_preimage_compl_union_eq_univ
    {X : Type*} (D A : Set X) (p q : X) (hinter : D ∩ A = {p, q}) :
    (Subtype.val ⁻¹' Dᶜ : Set ({p, q}ᶜ : Set X)) ∪
        Subtype.val ⁻¹' Aᶜ = Set.univ := by
  -- A point away from the punctures cannot belong to both sets.
  ext x
  simp only [Set.mem_union, Set.mem_preimage, Set.mem_compl_iff, Set.mem_univ, iff_true]
  by_contra h
  push Not at h
  have hx : x.1 ∈ D ∩ A := ⟨h.1, h.2⟩
  rw [hinter] at hx
  exact x.2 hx

/-- Helper for Exercise 63.3: the overlap of the two complement preimages is
the preimage of the complement of their union. -/
private lemma pairComplement_preimage_compl_inter
    {X : Type*} (D A : Set X) (p q : X) :
    (Subtype.val ⁻¹' Dᶜ : Set ({p, q}ᶜ : Set X)) ∩
        Subtype.val ⁻¹' Aᶜ = Subtype.val ⁻¹' (D ∪ A)ᶜ := by
  -- Membership on both sides is the same pair of negated memberships.
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_union,
    not_or]

/-- Helper for Exercise 63.3: forgetting the second puncture produces the
corresponding nested punctured-sphere point. -/
private def pairComplementToNestedPuncture (p q : StandardSphere 2) :
    ({p, q}ᶜ : Set (StandardSphere 2)) →
      {x : ({p}ᶜ : Set (StandardSphere 2)) // x.1 ≠ q} :=
  fun x ↦ ⟨⟨x.1, fun hp ↦ x.2 (Or.inl hp)⟩, fun hq ↦ x.2 (Or.inr hq)⟩

/-- Helper for Exercise 63.3: flattening a nested punctured-sphere point
recovers a point outside the pair. -/
private def nestedPunctureToPairComplement (p q : StandardSphere 2) :
    {x : ({p}ᶜ : Set (StandardSphere 2)) // x.1 ≠ q} →
      ({p, q}ᶜ : Set (StandardSphere 2)) :=
  fun x ↦ ⟨x.1.1, fun h ↦ h.elim x.1.2 x.2⟩

/-- Helper for Exercise 63.3: nesting a twice-punctured point is continuous. -/
private lemma continuous_pairComplementToNestedPuncture (p q : StandardSphere 2) :
    Continuous (pairComplementToNestedPuncture p q) := by
  -- Build continuity through the two subtype constructors.
  have hinner : Continuous (fun x : ({p, q}ᶜ : Set (StandardSphere 2)) ↦
      (⟨x.1, fun hp ↦ x.2 (Or.inl hp)⟩ : ({p}ᶜ : Set (StandardSphere 2)))) :=
    continuous_subtype_val.subtype_mk
      (fun (x : ({p, q}ᶜ : Set (StandardSphere 2))) hp ↦ x.2 (Or.inl hp))
  exact hinner.subtype_mk (fun x hq ↦ x.2 (Or.inr hq))

/-- Helper for Exercise 63.3: flattening a nested punctured point is continuous. -/
private lemma continuous_nestedPunctureToPairComplement (p q : StandardSphere 2) :
    Continuous (nestedPunctureToPairComplement p q) := by
  -- Both subtype projections are continuous.
  exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
    (fun x h ↦ h.elim x.1.2 x.2)

/-- Helper for Exercise 63.3: flattening after nesting fixes every point. -/
private lemma nestedPunctureToPairComplement_leftInverse (p q : StandardSphere 2) :
    Function.LeftInverse (nestedPunctureToPairComplement p q)
      (pairComplementToNestedPuncture p q) := by
  -- Subtype extensionality reduces the equality to the sphere point.
  intro x
  apply Subtype.ext
  rfl

/-- Helper for Exercise 63.3: nesting after flattening fixes every point. -/
private lemma nestedPunctureToPairComplement_rightInverse (p q : StandardSphere 2) :
    Function.RightInverse (nestedPunctureToPairComplement p q)
      (pairComplementToNestedPuncture p q) := by
  -- Two subtype extensionality steps reduce the equality to the sphere point.
  intro x
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- Helper for Exercise 63.3: the pair complement is homeomorphic to a nested
one-point complement. -/
private def pairComplementHomeomorphNestedPuncture (p q : StandardSphere 2) :
    ({p, q}ᶜ : Set (StandardSphere 2)) ≃ₜ
      {x : ({p}ᶜ : Set (StandardSphere 2)) // x.1 ≠ q} :=
  { toFun := pairComplementToNestedPuncture p q
    invFun := nestedPunctureToPairComplement p q
    left_inv := nestedPunctureToPairComplement_leftInverse p q
    right_inv := nestedPunctureToPairComplement_rightInverse p q
    continuous_toFun := continuous_pairComplementToNestedPuncture p q
    continuous_invFun := continuous_nestedPunctureToPairComplement p q }

/-- Helper for Exercise 63.3: the second point lies in the complement of the first. -/
private lemma secondPoint_mem_firstPointComplement
    (p q : StandardSphere 2) (hpq : p ≠ q) : q ∈ ({p}ᶜ : Set (StandardSphere 2)) := by
  -- Complement membership is the reversed distinctness assumption.
  simpa using hpq.symm

/-- Helper for Exercise 63.3: stereographic coordinates identify a punctured
sphere with the complex plane. -/
private noncomputable def puncturedSphereHomeomorphComplex (p : StandardSphere 2) :
    ({p}ᶜ : Set (StandardSphere 2)) ≃ₜ ℂ :=
  (StandardSphere.puncturedHomeomorphPlane p).trans
    Complex.orthonormalBasisOneI.repr.symm.toHomeomorph

/-- Helper for Exercise 63.3: translated stereographic coordinates send the
second puncture to zero. -/
private noncomputable def translatedPuncturedSphereChart
    (p q : StandardSphere 2) (hpq : p ≠ q) :
    ({p}ᶜ : Set (StandardSphere 2)) ≃ₜ ℂ :=
  (puncturedSphereHomeomorphComplex p).trans
    (Homeomorph.subRight
      (puncturedSphereHomeomorphComplex p
        ⟨q, secondPoint_mem_firstPointComplement p q hpq⟩))

/-- Helper for Exercise 63.3: the translated chart is nonzero exactly away
from the second puncture. -/
private lemma translatedPuncturedSphereChart_ne_zero_iff
    (p q : StandardSphere 2) (hpq : p ≠ q)
    (x : ({p}ᶜ : Set (StandardSphere 2))) :
    x.1 ≠ q ↔ translatedPuncturedSphereChart p q hpq x ≠ 0 := by
  -- Translation converts nonvanishing to inequality with the chart image of `q`.
  simp only [translatedPuncturedSphereChart, Homeomorph.trans_apply,
    Homeomorph.subRight_apply, sub_ne_zero]
  rw [(puncturedSphereHomeomorphComplex p).injective.ne_iff]
  simpa using (Subtype.coe_ne_coe (a := x)
    (b := (⟨q, secondPoint_mem_firstPointComplement p q hpq⟩ :
      ({p}ᶜ : Set (StandardSphere 2)))))

/-- Helper for Exercise 63.3: stereographic projection and translation
identify the twice-punctured sphere with the punctured complex plane. -/
private noncomputable def twicePuncturedSphereHomeomorphPuncturedComplexPlane
    (p q : StandardSphere 2) (hpq : p ≠ q) :
    ({p, q}ᶜ : Set (StandardSphere 2)) ≃ₜ {z : ℂ // z ≠ 0} :=
  (pairComplementHomeomorphNestedPuncture p q).trans
    ((translatedPuncturedSphereChart p q hpq).subtype
      (translatedPuncturedSphereChart_ne_zero_iff p q hpq))

/-- Helper for Exercise 63.3: a set inside a containing subtype is
homeomorphic to the same set in the ambient space. -/
private def nestedSubtypeHomeomorph
    {X : Type*} [TopologicalSpace X] (P S : Set X) (hSP : S ⊆ P) :
    (Subtype.val ⁻¹' S : Set P) ≃ₜ S :=
  { toFun := fun x ↦ ⟨x.1.1, x.2⟩
    invFun := fun x ↦ ⟨⟨x.1, hSP x.2⟩, x.2⟩
    left_inv := fun _ ↦ Subtype.ext (Subtype.ext rfl)
    right_inv := fun _ ↦ Subtype.ext rfl
    continuous_toFun :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk (fun x ↦ x.2)
    continuous_invFun :=
      (continuous_subtype_val.subtype_mk (fun x ↦ hSP x.2)).subtype_mk (fun x ↦ x.2) }

/-- Helper for Exercise 63.3: a homeomorphism induces a homeomorphism of
connected-component quotients. -/
private noncomputable def connectedComponentsHomeomorphOfHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    ConnectedComponents X ≃ₜ ConnectedComponents Y :=
  e.isQuotientMap.isCoinducing.connectedComponentsHomeomorph
    (fun y ↦ e.isConnected_preimage.mpr (isConnected_singleton : IsConnected ({y} : Set Y)))

/-- Helper for Exercise 63.3: polar and exponential coordinates identify the
punctured complex plane with the infinite cylinder. -/
private noncomputable def puncturedComplexPlaneHomeomorphInfiniteCylinder :
    {z : ℂ // z ≠ 0} ≃ₜ Circle × ℝ :=
  Complex.polarHomeomorph.symm.trans
    ((Homeomorph.refl Circle).prodCongr Real.expOrderIso.toHomeomorph.symm)

/-- Helper for Exercise 63.3: the infinite cylinder has infinite-cyclic
fundamental group at every basepoint. -/
private lemma fundamentalGroupInfiniteCylinderEquivInt (p : Circle × ℝ) :
    Nonempty (FundamentalGroup (Circle × ℝ) p ≃* Multiplicative ℤ) := by
  -- Contractibility removes the real factor, leaving the circle calculation.
  exact ⟨(FundamentalGroup.prodMulEquivLeftOfSubsingleton p.1 p.2 inferInstance).trans
    ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected p.1 1).trans
      Circle.fundamentalGroupEquivInt)⟩

/-- Helper for Exercise 63.3: the punctured complex plane has infinite-cyclic
fundamental group at every basepoint. -/
private lemma fundamentalGroup_puncturedComplexPlane_equiv_int
    (z : {z : ℂ // z ≠ 0}) :
    Nonempty (FundamentalGroup {z : ℂ // z ≠ 0} z ≃* Multiplicative ℤ) := by
  -- Transport the cylinder calculation through polar and logarithmic coordinates.
  let e := puncturedComplexPlaneHomeomorphInfiniteCylinder
  exact ⟨(e.fundamentalGroupMulEquiv z).trans
    (fundamentalGroupInfiniteCylinderEquivInt (e z)).some⟩

/-- Helper for Exercise 63.3: the twice-punctured sphere has infinite-cyclic
fundamental group at every basepoint. -/
private lemma pairComplementFundamentalGroupEquivInt
    (p q : StandardSphere 2) (hpq : p ≠ q)
    (x : ({p, q}ᶜ : Set (StandardSphere 2))) :
    Nonempty (FundamentalGroup ({p, q}ᶜ : Set (StandardSphere 2)) x ≃*
      Multiplicative ℤ) := by
  -- Transport first to the punctured plane, then use the cylinder calculation.
  let e := twicePuncturedSphereHomeomorphPuncturedComplexPlane p q hpq
  exact ⟨(e.fundamentalGroupMulEquiv x).trans
    (fundamentalGroup_puncturedComplexPlane_equiv_int (e x)).some⟩

/-- Helper for Exercise 63.3: a path in a nonseparating complement lifts to
the corresponding complement inside a twice-punctured sphere. -/
private lemma joinedIn_preimage_compl_pairComplement
    (D : Set (StandardSphere 2)) (hDclosed : IsClosed D)
    (p q : StandardSphere 2) (hp : p ∈ D) (hq : q ∈ D)
    (hDnonseparating : ¬ D.Separates)
    (a b : ({p, q}ᶜ : Set (StandardSphere 2)))
    (ha : a.1 ∈ Dᶜ) (hb : b.1 ∈ Dᶜ) :
    JoinedIn (Subtype.val ⁻¹' Dᶜ) a b := by
  -- Join in the ambient complement and use that both punctures lie in `D`.
  have hab := joinedIn_compl_of_closed_not_separates D hDclosed
    hDnonseparating ha hb
  have hDcomplSubset : Dᶜ ⊆ ({p, q}ᶜ : Set (StandardSphere 2)) := by
    intro z hzD hzPair
    rcases hzPair with hzp | hzq
    · exact hzD (hzp ▸ hp)
    · exact hzD (hzq ▸ hq)
  have himage :
      ((fun z ↦ z.1) '' (Subtype.val ⁻¹' Dᶜ :
        Set ({p, q}ᶜ : Set (StandardSphere 2)))) = Dᶜ := by
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hDcomplSubset]
  apply (Topology.IsInducing.subtypeVal.joinedIn_image
    (F := Subtype.val ⁻¹' Dᶜ) ha hb).mp
  rwa [himage]

/-- Helper for Exercise 63.3: two closed nonseparating subsets of the sphere
meeting in two distinct points have at most two complementary components. -/
private lemma closedPairComplementComponents_le_two
    (D A : Set (StandardSphere 2))
    (hDclosed : IsClosed D) (hAclosed : IsClosed A)
    (hDconnected : IsConnected D) (hAconnected : IsConnected A)
    (p q : StandardSphere 2) (hpq : p ≠ q) (hinter : D ∩ A = {p, q})
    (hDnonseparating : ¬ D.Separates) (hAnonseparating : ¬ A.Separates) :
    Cardinal.mk (ConnectedComponents ((D ∪ A)ᶜ : Set (StandardSphere 2))) ≤ 2 := by
  -- Normalize the complement as the overlap of a cover of the twice-punctured sphere.
  have hpqMem := pair_mem_of_inter_eq_pair hinter
  let P : Set (StandardSphere 2) := {p, q}ᶜ
  let U : Set P := Subtype.val ⁻¹' Dᶜ
  let V : Set P := Subtype.val ⁻¹' Aᶜ
  let W : Set (StandardSphere 2) := (D ∪ A)ᶜ
  have hUopen : IsOpen U := hDclosed.isOpen_compl.preimage continuous_subtype_val
  have hVopen : IsOpen V := hAclosed.isOpen_compl.preimage continuous_subtype_val
  have hcover : U ∪ V = Set.univ :=
    pairComplement_preimage_compl_union_eq_univ D A p q hinter
  have hWinter : U ∩ V = Subtype.val ⁻¹' W :=
    pairComplement_preimage_compl_inter D A p q
  have hWsubset : W ⊆ P := by
    intro z hzW hzPair
    rcases hzPair with hzp | hzq
    · exact hzW (Or.inl (hzp ▸ hpqMem.1))
    · exact hzW (Or.inl (hzq ▸ hpqMem.2.2.1))
  let overlapHomeomorph : (U ∩ V : Set P) ≃ₜ W :=
    (Homeomorph.setCongr hWinter).trans (nestedSubtypeHomeomorph P W hWsubset)
  -- Connectedness supplies points of both pieces away from the punctures.
  have hUcompl : Uᶜ.Nonempty := by
    obtain ⟨r, hrD, hrp, hrq⟩ := exists_mem_connected_ne_pair D hDconnected
      p q hpqMem.1 hpqMem.2.2.1 hpq
    have hrP : r ∈ P := by
      simpa only [P, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] using
        ⟨hrp, hrq⟩
    refine ⟨⟨r, hrP⟩, ?_⟩
    simpa only [U, mem_compl_iff, mem_preimage, not_not] using hrD
  have hVcompl : Vᶜ.Nonempty := by
    obtain ⟨r, hrA, hrp, hrq⟩ := exists_mem_connected_ne_pair A hAconnected
      p q hpqMem.2.1 hpqMem.2.2.2 hpq
    have hrP : r ∈ P := by
      simpa only [P, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] using
        ⟨hrp, hrq⟩
    refine ⟨⟨r, hrP⟩, ?_⟩
    simpa only [V, mem_compl_iff, mem_preimage, not_not] using hrA
  have hWopen : IsOpen W := (hDclosed.union hAclosed).isOpen_compl
  letI : LocallyPathConnectedSpace (StandardSphere 2) :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin 2)) (StandardSphere 2)
  letI : LocallyConnectedSpace W := hWopen.locallyConnectedSpace
  letI : LocallyConnectedSpace (U ∩ V : Set P) :=
    overlapHomeomorph.locallyConnectedSpace
  have hjoinedU : ∀ x y : (U ∩ V : Set P), JoinedIn U x.1 y.1 := by
    intro x y
    exact joinedIn_preimage_compl_pairComplement D hDclosed p q
      hpqMem.1 hpqMem.2.2.1 hDnonseparating x.1 y.1 x.2.1 y.2.1
  have hjoinedV : ∀ x y : (U ∩ V : Set P), JoinedIn V x.1 y.1 := by
    intro x y
    exact joinedIn_preimage_compl_pairComplement A hAclosed p q
      hpqMem.2.1 hpqMem.2.2.2 hAnonseparating x.1 y.1 x.2.2 y.2.2
  have hfundamental : ∀ x : (U ∩ V : Set P),
      Nonempty (FundamentalGroup P x.1 ≃* Multiplicative ℤ) := by
    intro x
    exact pairComplementFundamentalGroupEquivInt p q hpq x.1
  have hoverlapBound :
      Cardinal.mk (ConnectedComponents (U ∩ V : Set P)) ≤ 2 :=
    Theorem901.mk_connectedComponents_inter_le_two_of_windingCover
      U V hUopen hVopen hUcompl hVcompl hcover hjoinedU hjoinedV hfundamental
  -- Transport the overlap bound back to the ambient complement.
  rw [← Cardinal.mk_congr
    (connectedComponentsHomeomorphOfHomeomorph overlapHomeomorph).toEquiv]
  exact hoverlapBound

/-- The first conclusion in part (b) of Exercise 63.3: A subspace of the standard
two-sphere homeomorphic to the closed topologist's sine curve separates it into
exactly two components. -/
theorem closedTopologistsSineCurve_separatesInto
    (C : Set (StandardSphere 2))
    (hC : Nonempty (C ≃ₜ TopologistsSineCurve.ClosedSpace)) :
    C.SeparatesInto 2 := by
  -- Decompose the curve and combine the two-point separation lower bound with
  -- the twice-punctured-sphere upper bound.
  obtain ⟨D, A, p, q, hUnion, hpq, hinter, hDclosed, hAclosed,
      hDconnected, hAconnected, hDnonseparating, hAnonseparating⟩ :=
    closedSineCurve_pairGeometry C hC
  have hseparates : (D ∪ A).Separates :=
    union_separates_of_inter_pair D A p q hpq hinter hDclosed hAclosed
      hDconnected hAconnected
  have hcomponents :
      Cardinal.mk (ConnectedComponents ((D ∪ A)ᶜ : Set (StandardSphere 2))) ≤ 2 :=
    closedPairComplementComponents_le_two D A hDclosed hAclosed
      hDconnected hAconnected p q hpq hinter hDnonseparating hAnonseparating
  rw [hUnion]
  exact separatesInto_two_of_separates_of_components_le_two (D ∪ A)
    hseparates hcomponents

/-- Helper for Exercise 63.3: in a locally connected space, the frontier of a
complementary component of a closed set lies in that set. -/
private lemma frontier_connectedComponentIn_compl_subset
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    (C : Set X) (hCclosed : IsClosed C) (x : (Cᶜ : Set X)) :
    frontier (connectedComponentIn Cᶜ x) ⊆ C := by
  -- An exterior frontier point belongs to an open complementary component,
  -- which must coincide with the component whose closure it meets.
  intro z hz
  have hcomponentOpen : IsOpen (connectedComponentIn Cᶜ x) :=
    hCclosed.isOpen_compl.connectedComponentIn
  have hzNotMem : z ∉ connectedComponentIn Cᶜ x := by
    intro hzMem
    have hzInterior : z ∈ interior (connectedComponentIn Cᶜ x) :=
      hcomponentOpen.interior_eq.symm ▸ hzMem
    exact (mem_frontier_iff_notMem_interior hzMem).mp hz hzInterior
  by_contra hzC
  have hzCompl : z ∈ Cᶜ := hzC
  have hzOwnComponent : z ∈ connectedComponentIn Cᶜ z :=
    mem_connectedComponentIn hzCompl
  have hownOpen : IsOpen (connectedComponentIn Cᶜ z) :=
    hCclosed.isOpen_compl.connectedComponentIn
  have hzClosure : z ∈ closure (connectedComponentIn Cᶜ x) :=
    frontier_subset_closure hz
  rcases mem_closure_iff.mp hzClosure (connectedComponentIn Cᶜ z) hownOpen hzOwnComponent with
    ⟨y, hyOwn, hyComponent⟩
  have heq : connectedComponentIn Cᶜ x = connectedComponentIn Cᶜ z :=
    (connectedComponentIn_eq hyComponent).trans (connectedComponentIn_eq hyOwn).symm
  exact hzNotMem (heq ▸ hzOwnComponent)

/-- Helper for Exercise 63.3: exact complementary-component cardinality two
provides a point outside any prescribed complementary component. -/
private lemma exists_complementPoint_not_mem_component
    (C : Set (StandardSphere 2)) (hCtwo : C.SeparatesInto 2)
    (x : (Cᶜ : Set (StandardSphere 2))) :
    ∃ b : (Cᶜ : Set (StandardSphere 2)),
      (b : StandardSphere 2) ∉ connectedComponentIn Cᶜ x := by
  -- Choose the second quotient class and then choose one of its representatives.
  classical
  have hcomponents : Cardinal.mk (ConnectedComponents (Cᶜ : Set (StandardSphere 2))) = 2 :=
    separatesInto_iff.mp hCtwo
  obtain ⟨q, hqx, -⟩ :=
    (Cardinal.mk_eq_two_iff' (ConnectedComponents.mk x)).mp hcomponents
  obtain ⟨b, rfl⟩ := ConnectedComponents.surjective_coe q
  refine ⟨b, ?_⟩
  intro hb
  rw [connectedComponentIn_eq_image x.property] at hb
  obtain ⟨z, hz, hzb⟩ := hb
  have hzx : b ∈ connectedComponent x := by
    have hzb' : z = b := Subtype.ext hzb
    exact hzb' ▸ hz
  exact hqx (ConnectedComponents.coe_eq_coe'.mpr hzx)

/-- Helper for Exercise 63.3: dense points admitting arbitrarily large closed
nonseparating cores lie in the frontier of every complementary component. -/
private lemma subset_frontier_of_large_nonseparating_cores
    (C : Set (StandardSphere 2)) (hCclosed : IsClosed C)
    (hCtwo : C.SeparatesInto 2)
    (R : Set (StandardSphere 2)) (hRdense : C ⊆ closure R)
    (hcores : ∀ z ∈ R, ∀ N ∈ nhds z,
      ∃ B : Set (StandardSphere 2), IsClosed B ∧ B ⊆ C ∧
        ¬ B.Separates ∧ C \ B ⊆ N)
    (x : (Cᶜ : Set (StandardSphere 2))) :
    C ⊆ frontier (connectedComponentIn Cᶜ x) := by
  letI : LocallyPathConnectedSpace (StandardSphere 2) :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin 2)) (StandardSphere 2)
  classical
  let U : Set (StandardSphere 2) := connectedComponentIn Cᶜ x
  obtain ⟨b, hbU⟩ := exists_complementPoint_not_mem_component C hCtwo x
  -- Every neighborhood of a dense spine point contains a crossing point of the frontier.
  have hRfrontier : R ⊆ closure (frontier U) := by
    intro z hzR
    rw [mem_closure_iff_nhds]
    intro N hN
    obtain ⟨B, hBclosed, hBC, hBnonseparating, hCBN⟩ := hcores z hzR N hN
    have hxB : (x : StandardSphere 2) ∈ Bᶜ := by
      intro hxB
      exact x.property (hBC hxB)
    have hbB : (b : StandardSphere 2) ∈ Bᶜ := by
      intro hbB
      exact b.property (hBC hbB)
    have hjoined := joinedIn_compl_of_closed_not_separates B hBclosed
      hBnonseparating hxB hbB
    let γ : Path (x : StandardSphere 2) (b : StandardSphere 2) := hjoined.somePath
    let S : Set (StandardSphere 2) := Set.range γ
    have hSconnected : IsConnected S := isConnected_range γ.continuous
    have hSU : (S ∩ U).Nonempty :=
      ⟨x, γ.source_mem_range, mem_connectedComponentIn x.property⟩
    have hSUcompl : (S ∩ Uᶜ).Nonempty :=
      ⟨b, γ.target_mem_range, hbU⟩
    obtain ⟨y, hyS, hyFrontier⟩ :=
      hSconnected.inter_frontier_nonempty hSU hSUcompl
    have hyB : y ∈ Bᶜ := by
      obtain ⟨t, rfl⟩ := hyS
      exact hjoined.somePath_mem t
    have hyC : y ∈ C :=
      frontier_connectedComponentIn_compl_subset C hCclosed x hyFrontier
    exact ⟨y, hCBN ⟨hyC, hyB⟩, hyFrontier⟩
  -- Closedness of the frontier extends the dense-spine conclusion to all of `C`.
  have hfrontierClosed : IsClosed (frontier U) := isClosed_frontier
  rw [hfrontierClosed.closure_eq] at hRfrontier
  exact hRdense.trans (closure_minimal hRfrontier hfrontierClosed)

/-- Helper for Exercise 63.3: the affine first coordinate of a graph tail
starting at `c` and ending at one. -/
private noncomputable def closedSineGraphTailX (c : ℝ) (t : unitInterval) : ℝ :=
  c + (1 - c) * (t : ℝ)

/-- Helper for Exercise 63.3: the affine graph-tail coordinate is positive. -/
private lemma closedSineGraphTailX_pos {c : ℝ} (hc : 0 < c)
    (t : unitInterval) : 0 < closedSineGraphTailX c t := by
  -- The affine parameter is bounded below by its positive initial value.
  have hweighted : 0 ≤ c * (1 - (t : ℝ)) :=
    mul_nonneg hc.le (sub_nonneg.mpr t.property.2)
  unfold closedSineGraphTailX
  nlinarith [t.property.1]

/-- Helper for Exercise 63.3: the affine graph-tail coordinate is at most one. -/
private lemma closedSineGraphTailX_le_one {c : ℝ} (hc1 : c ≤ 1)
    (t : unitInterval) : closedSineGraphTailX c t ≤ 1 := by
  -- The affine parameter stays between its two endpoints.
  have hfactor : 0 ≤ 1 - c := sub_nonneg.mpr hc1
  unfold closedSineGraphTailX
  nlinarith [t.property.2]

/-- Helper for Exercise 63.3: graph-tail points belong to the closed sine curve. -/
private lemma closedSineGraphTail_mem {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (t : unitInterval) :
    (closedSineGraphTailX c t, Real.sin (1 / closedSineGraphTailX c t)) ∈
      TopologistsSineCurve.closedCarrier := by
  -- The point lies on the ordinary graph and hence in the enlarged carrier.
  apply sineCarrier_subset_closedCarrier
  rw [TopologistsSineCurve.carrier_eq_curve_union_vertical]
  left
  exact ⟨closedSineGraphTailX c t,
    ⟨closedSineGraphTailX_pos hc t, closedSineGraphTailX_le_one hc1 t⟩, rfl⟩

/-- Helper for Exercise 63.3: the graph tail as a path parametrization in the
closed sine-curve space. -/
private noncomputable def closedSineGraphTailParam
    (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (t : unitInterval) :
    TopologistsSineCurve.ClosedSpace :=
  ⟨(closedSineGraphTailX c t, Real.sin (1 / closedSineGraphTailX c t)),
    closedSineGraphTail_mem hc hc1 t⟩

/-- Helper for Exercise 63.3: the graph-tail parametrization is continuous. -/
private lemma continuous_closedSineGraphTailParam
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    Continuous (closedSineGraphTailParam c hc hc1) := by
  -- Positivity keeps the reciprocal continuous throughout the affine tail.
  apply Continuous.subtype_mk
  have hx : Continuous (closedSineGraphTailX c) := by
    unfold closedSineGraphTailX
    fun_prop
  exact hx.prodMk (Real.continuous_sin.comp
    (continuous_const.div hx (fun t ↦ (closedSineGraphTailX_pos hc t).ne')))

/-- Helper for Exercise 63.3: a nondegenerate graph-tail parametrization is injective. -/
private lemma injective_closedSineGraphTailParam
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    Function.Injective (closedSineGraphTailParam c hc hc1.le) := by
  -- Equality of first coordinates recovers the affine parameter.
  intro s t hst
  have hfst := congrArg (fun z : TopologistsSineCurve.ClosedSpace ↦ z.1.1) hst
  apply Subtype.ext
  dsimp [closedSineGraphTailParam, closedSineGraphTailX] at hfst ⊢
  nlinarith

/-- Helper for Exercise 63.3: the graph tail ends at the terminal point of
the broken line. -/
private lemma closedSineGraphTailParam_one
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    closedSineGraphTailParam c hc hc1 1 = brokenLinePathToClosedSpace 1 := by
  -- Both subtype values reduce to `(1, sin 1)`.
  apply Subtype.ext
  apply Prod.ext
  · simp [closedSineGraphTailParam, closedSineGraphTailX,
      brokenLinePathToClosedSpace, closedSineBrokenLinePath]
  · simp [closedSineGraphTailParam, closedSineGraphTailX,
      brokenLinePathToClosedSpace, closedSineBrokenLinePath]

/-- Helper for Exercise 63.3: the graph tail as a path with its canonical
terminal endpoint. -/
private noncomputable def closedSineGraphTailPath
    (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    Path (closedSineGraphTailParam c hc hc1 0) (brokenLinePathToClosedSpace 1) :=
  ⟨⟨closedSineGraphTailParam c hc hc1,
      continuous_closedSineGraphTailParam hc hc1⟩,
    rfl, closedSineGraphTailParam_one hc hc1⟩

/-- Helper for Exercise 63.3: the lifted broken-line parametrization as a path. -/
private noncomputable def closedSineBrokenLinePathInClosedSpace :
    Path (brokenLinePathToClosedSpace 0) (brokenLinePathToClosedSpace 1) :=
  ⟨⟨brokenLinePathToClosedSpace, continuous_brokenLinePathToClosedSpace⟩,
    rfl, rfl⟩

/-- Helper for Exercise 63.3: an injective path has its source as an endpoint
of its range arc. -/
private lemma Path.source_isEndpoint_range_of_injective
    {X : Type*} [TopologicalSpace X] [T2Space X] {x y : X}
    (g : Path x y) (hginj : Function.Injective g)
    (hArc : Topology.IsArc (Set.range g)) :
    @Topology.IsArc.IsEndpoint (Set.range g) _ hArc
      ⟨g 0, Set.mem_range_self 0⟩ := by
  -- The path embedding identifies its source with zero in the unit interval.
  let embedding : Topology.IsEmbedding g :=
    g.continuous.isClosedEmbedding hginj |>.isEmbedding
  let e : (Set.range g) ≃ₜ unitInterval := embedding.toHomeomorph.symm
  rw [@Topology.IsArc.isEndpoint_iff (Set.range g) _ hArc e]
  left
  apply Subtype.ext
  rfl

/-- Helper for Exercise 63.3: an injective path has its target as an endpoint
of its range arc. -/
private lemma Path.target_isEndpoint_range_of_injective
    {X : Type*} [TopologicalSpace X] [T2Space X] {x y : X}
    (g : Path x y) (hginj : Function.Injective g)
    (hArc : Topology.IsArc (Set.range g)) :
    @Topology.IsArc.IsEndpoint (Set.range g) _ hArc
      ⟨g 1, Set.mem_range_self 1⟩ := by
  -- The path embedding identifies its target with one in the unit interval.
  let embedding : Topology.IsEmbedding g :=
    g.continuous.isClosedEmbedding hginj |>.isEmbedding
  let e : (Set.range g) ≃ₜ unitInterval := embedding.toHomeomorph.symm
  rw [@Topology.IsArc.isEndpoint_iff (Set.range g) _ hArc e]
  right
  apply Subtype.ext
  rfl

/-- Helper for Exercise 63.3: restricting an injective path to a nondegenerate
ordered subinterval remains injective. -/
private lemma Path.injective_subpath_of_lt
    {X : Type*} [TopologicalSpace X] {x y : X}
    (g : Path x y) (hginj : Function.Injective g)
    {u v : unitInterval} (huv : u < v) :
    Function.Injective (g.subpath u v) := by
  -- The affine reparametrization has positive slope `v-u`.
  intro s t hst
  change g (Icc.convexComb u v s) = g (Icc.convexComb u v t) at hst
  have hparam := congrArg Subtype.val (hginj hst)
  apply Subtype.ext
  simp only [Icc.coe_convexComb] at hparam
  have hscaled : (s : ℝ) * ((v : ℝ) - (u : ℝ)) =
      (t : ℝ) * ((v : ℝ) - (u : ℝ)) := by
    linear_combination hparam
  have huvReal : (u : ℝ) < (v : ℝ) := huv
  have hscaled' : ((v : ℝ) - (u : ℝ)) * (s : ℝ) =
      ((v : ℝ) - (u : ℝ)) * (t : ℝ) := by
    simpa only [mul_comm] using hscaled
  exact (mul_right_inj' (sub_ne_zero.mpr huvReal.ne')).mp hscaled'

/-- Helper for Exercise 63.3: a graph tail meets the broken line only at their
common endpoint `(1, sin 1)`. -/
private lemma graphTail_inter_brokenLineRange
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    Set.range (closedSineGraphTailParam c hc hc1) ∩
        Set.range brokenLinePathToClosedSpace =
      {brokenLinePathToClosedSpace 1} := by
  -- Reduce a common point to the two known carrier/broken-line intersections.
  ext z
  constructor
  · rintro ⟨⟨s, hsz⟩, ⟨t, htz⟩⟩
    have hinter : z.1 ∈ TopologistsSineCurve.carrier ∩
        TopologistsSineCurve.brokenLine := by
      constructor
      · rw [← hsz]
        rw [TopologistsSineCurve.carrier_eq_curve_union_vertical]
        left
        exact ⟨closedSineGraphTailX c s,
          ⟨closedSineGraphTailX_pos hc s,
            closedSineGraphTailX_le_one hc1 s⟩, rfl⟩
      · rw [← htz]
        exact closedSineBrokenLinePath_mem t
    rw [sineCarrier_inter_brokenLine] at hinter
    rcases hinter with hleft | hright
    · have hfst := congrArg Prod.fst hleft
      rw [← hsz] at hfst
      change closedSineGraphTailX c s = 0 at hfst
      exact False.elim ((closedSineGraphTailX_pos hc s).ne' hfst)
    · rw [Set.mem_singleton_iff]
      rw [Set.mem_singleton_iff] at hright
      apply Subtype.ext
      exact hright.trans closedSineBrokenLinePath.target.symm
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    constructor
    · exact ⟨1, closedSineGraphTailParam_one hc hc1⟩
    · exact Set.mem_range_self 1

/-- Helper for Exercise 63.3: graph-tail first coordinates are at least the cutoff. -/
private lemma closedSineGraphTailX_ge
    {c : ℝ} (hc1 : c ≤ 1) (t : unitInterval) :
    c ≤ closedSineGraphTailX c t := by
  -- The affine displacement from `c` is nonnegative.
  have hfactor : 0 ≤ 1 - c := sub_nonneg.mpr hc1
  unfold closedSineGraphTailX
  nlinarith [t.property.1]

/-- Helper for Exercise 63.3: the graph-tail range is the ordinary carrier
portion whose first coordinate is at least the cutoff. -/
private lemma range_closedSineGraphTailParam
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    Set.range (closedSineGraphTailParam c hc hc1.le) =
      sineCarrierToClosedSpace ''
        {z : TopologistsSineCurve.Space | c ≤ z.1.1} := by
  -- Forward membership reads off the affine bound; backward membership solves
  -- for the unique affine parameter of a carrier graph point.
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    have hcarrier :
        (closedSineGraphTailX c t,
          Real.sin (1 / closedSineGraphTailX c t)) ∈
          TopologistsSineCurve.carrier := by
      rw [TopologistsSineCurve.carrier_eq_curve_union_vertical]
      left
      exact ⟨closedSineGraphTailX c t,
        ⟨closedSineGraphTailX_pos hc t,
          closedSineGraphTailX_le_one hc1.le t⟩, rfl⟩
    let w : TopologistsSineCurve.Space :=
      ⟨(closedSineGraphTailX c t,
        Real.sin (1 / closedSineGraphTailX c t)), hcarrier⟩
    exact ⟨w, closedSineGraphTailX_ge hc1.le t, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    have hwCurve : w.1 ∈ TopologistsSineCurve.curve := by
      have hwCarrier : w.1 ∈ TopologistsSineCurve.carrier := w.2
      rw [TopologistsSineCurve.carrier_eq_curve_union_vertical] at hwCarrier
      rcases hwCarrier with hwCurve | hwVertical
      · exact hwCurve
      · rw [TopologistsSineCurve.mem_vertical_iff] at hwVertical
        change c ≤ w.1.1 at hw
        linarith [hw, hc]
    rcases hwCurve with ⟨x, hx, hxw⟩
    have hwx : w.1.1 = x := congrArg Prod.fst hxw.symm
    have hfactor : 0 < 1 - c := sub_pos.mpr hc1
    have htMem : (w.1.1 - c) / (1 - c) ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hw) hfactor.le
      · apply (div_le_one hfactor).mpr
        rw [hwx]
        linarith [hx.2]
    let t : unitInterval := ⟨(w.1.1 - c) / (1 - c), htMem⟩
    refine ⟨t, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · change closedSineGraphTailX c t = w.1.1
      dsimp [closedSineGraphTailX, t]
      field_simp
      ring
    · have hsnd : w.1.2 = Real.sin (1 / w.1.1) := by
        rw [hwx]
        exact congrArg Prod.snd hxw.symm
      change Real.sin (1 / closedSineGraphTailX c t) = w.1.2
      rw [hsnd]
      congr 2
      dsimp [closedSineGraphTailX, t]
      field_simp
      ring

/-- Helper for Exercise 63.3: the graph tail followed by the reversed broken
line is a path from the graph cutoff to `(0,-1)`. -/
private noncomputable def closedSineGraphTailBrokenPath
    (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    Path (closedSineGraphTailParam c hc hc1 0)
      (brokenLinePathToClosedSpace 0) :=
  (closedSineGraphTailPath c hc hc1).trans
    closedSineBrokenLinePathInClosedSpace.symm

/-- Helper for Exercise 63.3: the graph-tail/broken-line path has the expected range. -/
private lemma range_closedSineGraphTailBrokenPath
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    Set.range (closedSineGraphTailBrokenPath c hc hc1) =
      Set.range (closedSineGraphTailParam c hc hc1) ∪
        Set.range brokenLinePathToClosedSpace := by
  -- Concatenation contributes the two ranges, and reversal does not change a range.
  rw [closedSineGraphTailBrokenPath, Path.trans_range, Path.symm_range]
  rfl

/-- Helper for Exercise 63.3: the graph-tail/broken-line path is injective. -/
private lemma injective_closedSineGraphTailBrokenPath
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    Function.Injective (closedSineGraphTailBrokenPath c hc hc1.le) := by
  -- The two injective pieces meet only at their common point `(1, sin 1)`.
  apply Path.trans_injective_of_range_inter_eq_singleton
  · exact injective_closedSineGraphTailParam hc hc1
  · intro s t hst
    have hparam := injective_brokenLinePathToClosedSpace hst
    exact unitInterval.symm_bijective.injective hparam
  · rw [Path.symm_range]
    change Set.range (closedSineGraphTailParam c hc hc1.le) ∩
      Set.range brokenLinePathToClosedSpace = {brokenLinePathToClosedSpace 1}
    exact graphTail_inter_brokenLineRange hc hc1.le

/-- Helper for Exercise 63.3: a left sine core meets the graph-tail/broken-line
arc only at the terminal point `(0,-1)`. -/
private lemma closedSineGraphTailBrokenArcData
    {d c : ℝ} (hd : 0 < d) (hdc : d < c) (hc1 : c < 1) :
    let A := Set.range
      (closedSineGraphTailBrokenPath c (hd.trans hdc) hc1.le)
    ∃ hAarc : Topology.IsArc A, ∃ p : A,
      @Topology.IsArc.IsEndpoint A _ hAarc p ∧
        (sineCarrierToClosedSpace '' TopologistsSineCurve.leftCore d) ∩ A =
          {p.1} := by
  -- Parametrize the attached arc and identify its sole intersection with the core.
  dsimp only
  let g := closedSineGraphTailBrokenPath c (hd.trans hdc) hc1.le
  have hginj : Function.Injective g :=
    injective_closedSineGraphTailBrokenPath (hd.trans hdc) hc1
  have hAarc : Topology.IsArc (Set.range g) :=
    isArc_range_of_continuous_injective g g.continuous hginj
  let p : Set.range g := ⟨g 1, Set.mem_range_self 1⟩
  refine ⟨hAarc, p, Path.target_isEndpoint_range_of_injective g hginj hAarc, ?_⟩
  ext z
  constructor
  · rintro ⟨⟨u, huCore, huz⟩, hzA⟩
    rw [range_closedSineGraphTailBrokenPath (hd.trans hdc) hc1.le] at hzA
    rcases hzA with hzGraph | hzBroken
    · obtain ⟨t, htz⟩ := hzGraph
      have hfirst : closedSineGraphTailX c t = u.1.1 := by
        have hval := congrArg Subtype.val (htz.trans huz.symm)
        exact congrArg Prod.fst hval
      have huLe : u.1.1 ≤ d := by
        exact TopologistsSineCurve.mem_leftCore.mp huCore
      have hcLe : c ≤ closedSineGraphTailX c t :=
        closedSineGraphTailX_ge hc1.le t
      exact False.elim (by linarith)
    · obtain ⟨t, htz⟩ := hzBroken
      have hut : sineCarrierToClosedSpace u = brokenLinePathToClosedSpace t :=
        huz.trans htz.symm
      have hinter : u.1 ∈ TopologistsSineCurve.carrier ∩
          TopologistsSineCurve.brokenLine := by
        refine ⟨u.2, ?_⟩
        have hval : u.1 = (brokenLinePathToClosedSpace t).1 :=
          congrArg Subtype.val hut
        rw [hval]
        exact closedSineBrokenLinePath_mem t
      rw [sineCarrier_inter_brokenLine] at hinter
      rcases hinter with hleft | hright
      · rw [Set.mem_singleton_iff]
        apply Subtype.ext
        calc
          z.1 = u.1 := congrArg Subtype.val huz.symm
          _ = (0, -1) := hleft
          _ = (brokenLinePathToClosedSpace 0).1 :=
            closedSineBrokenLinePath.source.symm
          _ = (g 1).1 := congrArg Subtype.val g.target.symm
      · rw [Set.mem_singleton_iff] at hright
        have huOne : u.1.1 = 1 := congrArg Prod.fst hright
        have huLe : u.1.1 ≤ d := by
          exact TopologistsSineCurve.mem_leftCore.mp huCore
        exact False.elim (by linarith)
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    have hleftCarrier : ((0, -1) : ℝ × ℝ) ∈
        TopologistsSineCurve.carrier := by
      rw [TopologistsSineCurve.carrier_eq_curve_union_vertical]
      right
      rw [TopologistsSineCurve.mem_vertical_iff]
      norm_num
    let u : TopologistsSineCurve.Space := ⟨(0, -1), hleftCarrier⟩
    constructor
    · refine ⟨u, ?_, ?_⟩
      · exact TopologistsSineCurve.mem_leftCore.mpr hd.le
      · apply Subtype.ext
        calc
          u.1 = (0, -1) := rfl
          _ = (brokenLinePathToClosedSpace 0).1 :=
            closedSineBrokenLinePath.source.symm
          _ = (g 1).1 := congrArg Subtype.val g.target.symm
    · exact p.2

/-- Helper for Exercise 63.3: the ordinary sine carrier meets an initial
broken-line subarc only at `(0,-1)`. -/
private lemma sineCarrierRange_inter_brokenInitialSubpath
    {u : unitInterval} (hu : u < 1) :
    Set.range sineCarrierToClosedSpace ∩
        Set.range (closedSineBrokenLinePathInClosedSpace.subpath 0 u) =
      {brokenLinePathToClosedSpace 0} := by
  -- The other carrier/broken-line intersection would force the parameter to be one.
  have hzeroLe : (0 : unitInterval) ≤ u := u.property.1
  ext z
  constructor
  · rintro ⟨⟨w, hwz⟩, hzSubpath⟩
    rw [Path.range_subpath_of_le _ _ _ hzeroLe] at hzSubpath
    obtain ⟨t, ht, htz⟩ := hzSubpath
    have hwt : sineCarrierToClosedSpace w = brokenLinePathToClosedSpace t :=
      hwz.trans htz.symm
    have hinter : w.1 ∈ TopologistsSineCurve.carrier ∩
        TopologistsSineCurve.brokenLine := by
      refine ⟨w.2, ?_⟩
      have hval : w.1 = (brokenLinePathToClosedSpace t).1 :=
        congrArg Subtype.val hwt
      rw [hval]
      exact closedSineBrokenLinePath_mem t
    rw [sineCarrier_inter_brokenLine] at hinter
    rcases hinter with hleft | hright
    · rw [Set.mem_singleton_iff]
      apply Subtype.ext
      calc
        z.1 = w.1 := congrArg Subtype.val hwz.symm
        _ = (0, -1) := hleft
        _ = (brokenLinePathToClosedSpace 0).1 :=
          closedSineBrokenLinePath.source.symm
    · rw [Set.mem_singleton_iff] at hright
      have htOne : t = 1 := by
        apply injective_brokenLinePathToClosedSpace
        apply Subtype.ext
        calc
          (brokenLinePathToClosedSpace t).1 = w.1 :=
            (congrArg Subtype.val hwt).symm
          _ = (1, Real.sin 1) := hright
          _ = (brokenLinePathToClosedSpace 1).1 :=
            closedSineBrokenLinePath.target.symm
      have htLe : t ≤ u := ht.2
      rw [htOne] at htLe
      exact False.elim ((not_le_of_gt hu) htLe)
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    have hleftCarrier : ((0, -1) : ℝ × ℝ) ∈
        TopologistsSineCurve.carrier := by
      rw [TopologistsSineCurve.carrier_eq_curve_union_vertical]
      right
      rw [TopologistsSineCurve.mem_vertical_iff]
      norm_num
    let w : TopologistsSineCurve.Space := ⟨(0, -1), hleftCarrier⟩
    constructor
    · refine ⟨w, ?_⟩
      apply Subtype.ext
      exact closedSineBrokenLinePath.source.symm
    · rw [Path.range_subpath_of_le _ _ _ hzeroLe]
      exact ⟨0, ⟨le_rfl, hzeroLe⟩, rfl⟩

/-- Helper for Exercise 63.3: after adjoining an initial broken-line subarc,
the terminal subarc meets the union only at `(1, sin 1)`. -/
private lemma carrierUnionInitial_inter_brokenTerminalSubpath
    {u v : unitInterval} (huv : u < v) :
    (Set.range sineCarrierToClosedSpace ∪
        Set.range (closedSineBrokenLinePathInClosedSpace.subpath 0 u)) ∩
        Set.range (closedSineBrokenLinePathInClosedSpace.subpath v 1) =
      {brokenLinePathToClosedSpace 1} := by
  -- Carrier intersections give the two global endpoints, while the ordered
  -- subarcs themselves are disjoint because `u < v`.
  have hzeroLe : (0 : unitInterval) ≤ u := u.property.1
  have hvOne : v ≤ (1 : unitInterval) := v.property.2
  ext z
  constructor
  · rintro ⟨hzLeft, hzHigh⟩
    rw [Path.range_subpath_of_le _ _ _ hvOne] at hzHigh
    obtain ⟨t, ht, htz⟩ := hzHigh
    rcases hzLeft with hzCarrier | hzLow
    · obtain ⟨w, hwz⟩ := hzCarrier
      have hwt : sineCarrierToClosedSpace w = brokenLinePathToClosedSpace t :=
        hwz.trans htz.symm
      have hinter : w.1 ∈ TopologistsSineCurve.carrier ∩
          TopologistsSineCurve.brokenLine := by
        refine ⟨w.2, ?_⟩
        have hval : w.1 = (brokenLinePathToClosedSpace t).1 :=
          congrArg Subtype.val hwt
        rw [hval]
        exact closedSineBrokenLinePath_mem t
      rw [sineCarrier_inter_brokenLine] at hinter
      rcases hinter with hleft | hright
      · have htZero : t = 0 := by
          apply injective_brokenLinePathToClosedSpace
          apply Subtype.ext
          calc
            (brokenLinePathToClosedSpace t).1 = w.1 :=
              (congrArg Subtype.val hwt).symm
            _ = (0, -1) := hleft
            _ = (brokenLinePathToClosedSpace 0).1 :=
              closedSineBrokenLinePath.source.symm
        have hvLe : v ≤ t := ht.1
        rw [htZero] at hvLe
        exact False.elim ((not_le_of_gt (lt_of_le_of_lt u.property.1 huv)) hvLe)
      · rw [Set.mem_singleton_iff]
        rw [Set.mem_singleton_iff] at hright
        apply Subtype.ext
        exact (congrArg Subtype.val hwz.symm).trans
          (hright.trans closedSineBrokenLinePath.target.symm)
    · rw [Path.range_subpath_of_le _ _ _ hzeroLe] at hzLow
      obtain ⟨s, hs, hsz⟩ := hzLow
      have hst : s = t := injective_brokenLinePathToClosedSpace
        (hsz.trans htz.symm)
      have hsLe : s ≤ u := hs.2
      have hvLe : v ≤ t := ht.1
      exact False.elim (by rw [hst] at hsLe; exact (not_le_of_gt huv) (hvLe.trans hsLe))
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    have hrightCarrier : ((1, Real.sin 1) : ℝ × ℝ) ∈
        TopologistsSineCurve.carrier := by
      rw [TopologistsSineCurve.carrier_eq_curve_union_vertical]
      left
      refine ⟨1, ⟨zero_lt_one, le_rfl⟩, ?_⟩
      norm_num
    let w : TopologistsSineCurve.Space := ⟨(1, Real.sin 1), hrightCarrier⟩
    constructor
    · left
      refine ⟨w, ?_⟩
      apply Subtype.ext
      exact closedSineBrokenLinePath.target.symm
    · rw [Path.range_subpath_of_le _ _ _ hvOne]
      exact ⟨1, ⟨hvOne, le_rfl⟩, rfl⟩

/-- Helper for Exercise 63.3: ordered initial and terminal broken-line
subpaths supply the two endpoint attachments used on the positive spine. -/
private lemma closedSineBrokenEndSubarcsData
    {u v : unitInterval} (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    let L := Set.range (closedSineBrokenLinePathInClosedSpace.subpath 0 u)
    let H := Set.range (closedSineBrokenLinePathInClosedSpace.subpath v 1)
    ∃ hLarc : Topology.IsArc L, ∃ hHarc : Topology.IsArc H,
      ∃ p : L, ∃ q : H,
        @Topology.IsArc.IsEndpoint L _ hLarc p ∧
        @Topology.IsArc.IsEndpoint H _ hHarc q ∧
        Set.range sineCarrierToClosedSpace ∩ L = {p.1} ∧
        (Set.range sineCarrierToClosedSpace ∪ L) ∩ H = {q.1} := by
  -- Each strict subpath is an arc; its outer endpoint gives the attachment point.
  dsimp only
  let P := closedSineBrokenLinePathInClosedSpace
  let gL := P.subpath 0 u
  let gH := P.subpath v 1
  have hPinj : Function.Injective P := injective_brokenLinePathToClosedSpace
  have hLinj : Function.Injective gL :=
    Path.injective_subpath_of_lt P hPinj hu
  have hHinj : Function.Injective gH :=
    Path.injective_subpath_of_lt P hPinj hv
  have hLarc : Topology.IsArc (Set.range gL) :=
    isArc_range_of_continuous_injective gL gL.continuous hLinj
  have hHarc : Topology.IsArc (Set.range gH) :=
    isArc_range_of_continuous_injective gH gH.continuous hHinj
  let p : Set.range gL := ⟨gL 0, Set.mem_range_self 0⟩
  let q : Set.range gH := ⟨gH 1, Set.mem_range_self 1⟩
  refine ⟨hLarc, hHarc, p, q,
    Path.source_isEndpoint_range_of_injective gL hLinj hLarc,
    Path.target_isEndpoint_range_of_injective gH hHinj hHarc, ?_, ?_⟩
  · have hp : (p : TopologistsSineCurve.ClosedSpace) =
        brokenLinePathToClosedSpace 0 := by
      change gL 0 = brokenLinePathToClosedSpace 0
      change (P.subpath 0 u) 0 = brokenLinePathToClosedSpace 0
      rw [Path.source]
      rfl
    rw [hp]
    exact sineCarrierRange_inter_brokenInitialSubpath (huv.trans hv)
  · have hq : (q : TopologistsSineCurve.ClosedSpace) =
        brokenLinePathToClosedSpace 1 := by
      change gH 1 = brokenLinePathToClosedSpace 1
      change (P.subpath v 1) 1 = brokenLinePathToClosedSpace 1
      rw [Path.target]
      rfl
    rw [hq]
    exact carrierUnionInitial_inter_brokenTerminalSubpath huv

/-- Helper for Exercise 63.3: deleting a strict negative spine interval leaves
a closed nonseparating core. -/
private lemma closedSineSpineIntervalCore_of_neg
    (f : TopologistsSineCurve.ClosedSpace → StandardSphere 2)
    (hf : Continuous f) (hfinj : Function.Injective f)
    {a b : ℝ} (hab : a < b) (hb : b < 0) :
    ∃ B : Set (StandardSphere 2), IsClosed B ∧ B ⊆ Set.range f ∧
      ¬ B.Separates ∧
      Set.range f \ B ⊆ (f ∘ closedSineSpineParam) '' Ioo a b := by
  -- Translate the parameter endpoints into graph cutoffs and attach the
  -- graph tail plus the complete broken line to the left nonseparating core.
  classical
  let d : ℝ := 1 / (1 - a)
  let c : ℝ := 1 / (1 - b)
  have hd : 0 < d := by
    dsimp [d]
    exact one_div_pos.mpr (by linarith)
  have hc : 0 < c := by
    dsimp [c]
    exact one_div_pos.mpr (by linarith)
  have hdc : d < c := by
    dsimp [d, c]
    exact one_div_lt_one_div_of_lt (by linarith : 0 < 1 - b)
      (by linarith : 1 - b < 1 - a)
  have hc1 : c < 1 := by
    dsimp [c]
    have hden : (1 : ℝ) < 1 - b := by linarith
    simpa only [div_one] using one_div_lt_one_div_of_lt zero_lt_one hden
  let g : TopologistsSineCurve.Space → StandardSphere 2 :=
    f ∘ sineCarrierToClosedSpace
  let P := closedSineGraphTailBrokenPath c hc hc1.le
  let K₀ : Set TopologistsSineCurve.ClosedSpace :=
    sineCarrierToClosedSpace '' TopologistsSineCurve.leftCore d
  let A₀ : Set TopologistsSineCurve.ClosedSpace := Set.range P
  let K : Set (StandardSphere 2) := f '' K₀
  let A : Set (StandardSphere 2) := f '' A₀
  obtain ⟨hA₀arc, p, hpEndpoint, hinter₀⟩ :=
    closedSineGraphTailBrokenArcData hd hdc hc1
  have hgContinuous : Continuous g := hf.comp continuous_sineCarrierToClosedSpace
  have hgInjective : Function.Injective g :=
    hfinj.comp injective_sineCarrierToClosedSpace
  have hKclosed : IsClosed K := by
    letI : CompactSpace TopologistsSineCurve.Space :=
      isCompact_iff_compactSpace.mp sineCurveCarrier_isCompact
    have hcompact := ((TopologistsSineCurve.isClosed_leftCore d).isCompact.image
      continuous_sineCarrierToClosedSpace).image hf
    exact hcompact.isClosed
  have hKnonseparating : ¬ K.Separates := by
    have hnonsep := sineLeftCore_not_separates g hgContinuous hgInjective
      d hd (hdc.trans hc1).le
    have hK_eq : K = g '' TopologistsSineCurve.leftCore d := by
      ext z
      constructor
      · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
        exact ⟨u, hu, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨sineCarrierToClosedSpace u, ⟨u, hu, rfl⟩, rfl⟩
    rw [hK_eq]
    exact hnonsep
  have hAclosed : IsClosed A := by
    have hcompact : IsCompact A₀ := by
      exact isCompact_range P.continuous
    exact (hcompact.image hf).isClosed
  have hAarc : Topology.IsArc A :=
    isArc_image_of_continuous_injective f hf hfinj A₀ hA₀arc
  let q : A := ⟨f p.1, ⟨p.1, p.2, rfl⟩⟩
  have hqEndpoint : @Topology.IsArc.IsEndpoint A _ hAarc q :=
    isEndpoint_image_of_continuous_injective f hf hfinj A₀ hA₀arc
      hAarc p hpEndpoint
  have hinter : K ∩ A = {(q : StandardSphere 2)} := by
    dsimp only [K, A, K₀, A₀]
    rw [← Set.image_inter hfinj, hinter₀,
      Set.image_singleton]
  refine ⟨K ∪ A, hKclosed.union hAclosed, ?_,
    union_not_separates_of_arc_endpoint K A hKclosed hKnonseparating
      hAarc ⟨q, hqEndpoint, hinter⟩, ?_⟩
  · -- Both pieces are explicitly images under `f`.
    rintro z (hzK | hzA)
    · obtain ⟨w, -, rfl⟩ := hzK
      exact Set.mem_range_self w
    · obtain ⟨w, -, rfl⟩ := hzA
      exact Set.mem_range_self w
  · -- A point omitted by the core lies on the graph strictly between the cutoffs.
    rintro z ⟨hzRange, hzB⟩
    obtain ⟨w, rfl⟩ := hzRange
    have hwK : f w ∉ K := fun hwK ↦ hzB (Or.inl hwK)
    have hwA : f w ∉ A := fun hwA ↦ hzB (Or.inr hwA)
    have hwA₀ : w ∉ A₀ := fun hw ↦ hwA ⟨w, hw, rfl⟩
    have hwCarrier : w.1 ∈ TopologistsSineCurve.carrier := by
      have hwClosed := w.property
      rw [TopologistsSineCurve.mem_closedCarrier_iff] at hwClosed
      rcases hwClosed with hwCarrier | hwBroken
      · exact hwCarrier
      · exfalso
        rw [← range_closedSineBrokenLinePath] at hwBroken
        obtain ⟨t, htw⟩ := hwBroken
        apply hwA₀
        change w ∈ Set.range
          (closedSineGraphTailBrokenPath c hc hc1.le)
        rw [range_closedSineGraphTailBrokenPath hc hc1.le]
        right
        refine ⟨t, ?_⟩
        apply Subtype.ext
        exact htw
    let u : TopologistsSineCurve.Space := ⟨w.1, hwCarrier⟩
    have huNotCore : u ∉ TopologistsSineCurve.leftCore d := by
      intro hu
      apply hwK
      refine ⟨sineCarrierToClosedSpace u, ⟨u, hu, rfl⟩, ?_⟩
      apply congrArg f
      apply Subtype.ext
      rfl
    have hdx : d < u.1.1 := by
      exact lt_of_not_ge (fun h ↦ huNotCore
        (TopologistsSineCurve.mem_leftCore.mpr h))
    have hxc : u.1.1 < c := by
      by_contra hnot
      have hcx : c ≤ u.1.1 := le_of_not_gt hnot
      apply hwA₀
      change w ∈ Set.range
        (closedSineGraphTailBrokenPath c hc hc1.le)
      rw [range_closedSineGraphTailBrokenPath hc hc1.le]
      left
      rw [range_closedSineGraphTailParam hc hc1]
      refine ⟨u, hcx, ?_⟩
      apply Subtype.ext
      rfl
    have hxpos : 0 < u.1.1 := hd.trans hdx
    have hrecipD : 1 / u.1.1 < 1 / d :=
      one_div_lt_one_div_of_lt hd hdx
    have hrecipC : 1 / c < 1 / u.1.1 :=
      one_div_lt_one_div_of_lt hxpos hxc
    have hinvD : 1 / d = 1 - a := by
      dsimp [d]
      field_simp
    have hinvC : 1 / c = 1 - b := by
      dsimp [c]
      field_simp
    let t : ℝ := 1 - 1 / u.1.1
    have hat : a < t := by
      dsimp [t]
      rw [hinvD] at hrecipD
      linarith
    have htb : t < b := by
      dsimp [t]
      rw [hinvC] at hrecipC
      linarith
    have htneg : t ≤ 0 := by linarith [htb, hb]
    have hwCurve : u.1 ∈ TopologistsSineCurve.curve := by
      have huCarrier : u.1 ∈ TopologistsSineCurve.carrier := u.2
      rw [TopologistsSineCurve.carrier_eq_curve_union_vertical] at huCarrier
      rcases huCarrier with huCurve | huVertical
      · exact huCurve
      · rw [TopologistsSineCurve.mem_vertical_iff] at huVertical
        exact False.elim (hxpos.ne' huVertical.1)
    rcases hwCurve with ⟨x, hx, hxw⟩
    have hux : u.1.1 = x := congrArg Prod.fst hxw.symm
    have hsnd : w.1.2 = Real.sin (1 / u.1.1) := by
      change u.1.2 = Real.sin (1 / u.1.1)
      rw [hux]
      exact congrArg Prod.snd hxw.symm
    have hspine : closedSineSpineParam t = w := by
      apply Subtype.ext
      change closedSineSpinePlaneParam t = w.1
      rw [closedSineSpinePlaneParam, if_pos htneg,
        closedSineSpineGraphBranch]
      apply Prod.ext
      · dsimp [t]
        field_simp [hxpos.ne']
        ring
      · rw [hsnd]
        dsimp [t]
        congr 2
        field_simp [hxpos.ne']
        ring
    refine ⟨t, ⟨hat, htb⟩, ?_⟩
    exact congrArg f hspine

/-- Helper for Exercise 63.3: deleting a strict positive spine interval leaves
a closed nonseparating core. -/
private lemma closedSineSpineIntervalCore_of_pos
    (f : TopologistsSineCurve.ClosedSpace → StandardSphere 2)
    (hf : Continuous f) (hfinj : Function.Injective f)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ B : Set (StandardSphere 2), IsClosed B ∧ B ⊆ Set.range f ∧
      ¬ B.Separates ∧
      Set.range f \ B ⊆ (f ∘ closedSineSpineParam) '' Ioo a b := by
  -- Convert the spine endpoints to ordered parameters on the broken-line path.
  classical
  have hb : 0 < b := ha.trans hab
  have huPos : 0 < 1 / (1 + b) := one_div_pos.mpr (by linarith)
  have hvPos : 0 < 1 / (1 + a) := one_div_pos.mpr (by linarith)
  have huLtOne : 1 / (1 + b) < 1 := by
    have hden : (1 : ℝ) < 1 + b := by linarith
    simpa only [div_one] using one_div_lt_one_div_of_lt zero_lt_one hden
  have hvLtOne : 1 / (1 + a) < 1 := by
    have hden : (1 : ℝ) < 1 + a := by linarith
    simpa only [div_one] using one_div_lt_one_div_of_lt zero_lt_one hden
  have huvReal : 1 / (1 + b) < 1 / (1 + a) :=
    one_div_lt_one_div_of_lt (by linarith : 0 < 1 + a) (by linarith)
  let u : unitInterval := ⟨1 / (1 + b), ⟨huPos.le, huLtOne.le⟩⟩
  let v : unitInterval := ⟨1 / (1 + a), ⟨hvPos.le, hvLtOne.le⟩⟩
  have hu : (0 : unitInterval) < u := huPos
  have huv : u < v := huvReal
  have hv : v < (1 : unitInterval) := hvLtOne
  let P := closedSineBrokenLinePathInClosedSpace
  let S₀ : Set TopologistsSineCurve.ClosedSpace := Set.range sineCarrierToClosedSpace
  let L₀ : Set TopologistsSineCurve.ClosedSpace := Set.range (P.subpath 0 u)
  let H₀ : Set TopologistsSineCurve.ClosedSpace := Set.range (P.subpath v 1)
  let g : TopologistsSineCurve.Space → StandardSphere 2 :=
    f ∘ sineCarrierToClosedSpace
  let K : Set (StandardSphere 2) := f '' S₀
  let L : Set (StandardSphere 2) := f '' L₀
  let H : Set (StandardSphere 2) := f '' H₀
  obtain ⟨hL₀arc, hH₀arc, p, q, hpEndpoint, hqEndpoint,
      hinterL₀, hinterH₀⟩ := closedSineBrokenEndSubarcsData hu huv hv
  have hgContinuous : Continuous g := hf.comp continuous_sineCarrierToClosedSpace
  have hgInjective : Function.Injective g :=
    hfinj.comp injective_sineCarrierToClosedSpace
  letI : CompactSpace TopologistsSineCurve.Space :=
    isCompact_iff_compactSpace.mp sineCurveCarrier_isCompact
  have hKclosed : IsClosed K := by
    -- The ordinary sine carrier is compact before transport through `f`.
    have hcompact : IsCompact S₀ := by
      change IsCompact (Set.range sineCarrierToClosedSpace)
      exact isCompact_range continuous_sineCarrierToClosedSpace
    exact (hcompact.image hf).isClosed
  have hKnonseparating : ¬ K.Separates := by
    -- The cutoff-one left core is the entire ordinary sine carrier.
    have hcoord (z : TopologistsSineCurve.Space) : z.1.1 ≤ 1 := by
      have hzCarrier : z.1 ∈ TopologistsSineCurve.carrier := z.2
      rw [TopologistsSineCurve.carrier_eq_curve_union_vertical] at hzCarrier
      rcases hzCarrier with hzCurve | hzVertical
      · rcases hzCurve with ⟨x, hx, hxz⟩
        have hzx : z.1.1 = x := congrArg Prod.fst hxz.symm
        rw [hzx]
        exact hx.2
      · rw [TopologistsSineCurve.mem_vertical_iff] at hzVertical
        rw [hzVertical.1]
        norm_num
    have hK_eq : K = g '' TopologistsSineCurve.leftCore 1 := by
      ext z
      constructor
      · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, TopologistsSineCurve.mem_leftCore.mpr (hcoord x), rfl⟩
      · rintro ⟨x, -, rfl⟩
        exact ⟨sineCarrierToClosedSpace x, ⟨x, rfl⟩, rfl⟩
    rw [hK_eq]
    exact sineLeftCore_not_separates g hgContinuous hgInjective
      1 zero_lt_one le_rfl
  have hLclosed : IsClosed L := by
    -- A path range is compact, and continuous transport preserves compactness.
    exact ((isCompact_range (P.subpath 0 u).continuous).image hf).isClosed
  have hHclosed : IsClosed H := by
    -- The terminal path range is compact for the same reason.
    exact ((isCompact_range (P.subpath v 1).continuous).image hf).isClosed
  have hLarc : Topology.IsArc L :=
    isArc_image_of_continuous_injective f hf hfinj L₀ hL₀arc
  have hHarc : Topology.IsArc H :=
    isArc_image_of_continuous_injective f hf hfinj H₀ hH₀arc
  let p' : L := ⟨f p.1, ⟨p.1, p.2, rfl⟩⟩
  let q' : H := ⟨f q.1, ⟨q.1, q.2, rfl⟩⟩
  have hp'Endpoint : @Topology.IsArc.IsEndpoint L _ hLarc p' :=
    isEndpoint_image_of_continuous_injective f hf hfinj L₀ hL₀arc
      hLarc p hpEndpoint
  have hq'Endpoint : @Topology.IsArc.IsEndpoint H _ hHarc q' :=
    isEndpoint_image_of_continuous_injective f hf hfinj H₀ hH₀arc
      hHarc q hqEndpoint
  have hinterL : K ∩ L = {(p' : StandardSphere 2)} := by
    dsimp only [K, L, S₀, L₀]
    rw [← Set.image_inter hfinj, hinterL₀, Set.image_singleton]
  have hKLnonseparating : ¬ (K ∪ L).Separates :=
    union_not_separates_of_arc_endpoint K L hKclosed hKnonseparating
      hLarc ⟨p', hp'Endpoint, hinterL⟩
  have hinterH : (K ∪ L) ∩ H = {(q' : StandardSphere 2)} := by
    dsimp only [K, L, H, S₀, L₀, H₀]
    rw [← Set.image_union, ← Set.image_inter hfinj, hinterH₀,
      Set.image_singleton]
  refine ⟨(K ∪ L) ∪ H, (hKclosed.union hLclosed).union hHclosed, ?_,
    union_not_separates_of_arc_endpoint (K ∪ L) H
      (hKclosed.union hLclosed) hKLnonseparating hHarc
      ⟨q', hq'Endpoint, hinterH⟩, ?_⟩
  · -- Every retained piece is an explicit image under `f`.
    rintro z ((hzK | hzL) | hzH)
    · obtain ⟨w, -, rfl⟩ := hzK
      exact Set.mem_range_self w
    · obtain ⟨w, -, rfl⟩ := hzL
      exact Set.mem_range_self w
    · obtain ⟨w, -, rfl⟩ := hzH
      exact Set.mem_range_self w
  · -- An omitted point lies on the middle open subarc, whose reciprocal
    -- parameter is exactly a point of the requested positive spine interval.
    rintro z ⟨hzRange, hzB⟩
    obtain ⟨w, rfl⟩ := hzRange
    have hwK : f w ∉ K := fun hwK ↦ hzB (Or.inl (Or.inl hwK))
    have hwL : f w ∉ L := fun hwL ↦ hzB (Or.inl (Or.inr hwL))
    have hwH : f w ∉ H := fun hwH ↦ hzB (Or.inr hwH)
    have hwS₀ : w ∉ S₀ := fun hw ↦ hwK ⟨w, hw, rfl⟩
    have hwL₀ : w ∉ L₀ := fun hw ↦ hwL ⟨w, hw, rfl⟩
    have hwH₀ : w ∉ H₀ := fun hw ↦ hwH ⟨w, hw, rfl⟩
    have hwBroken : w.1 ∈ TopologistsSineCurve.brokenLine := by
      have hwClosed : w.1 ∈ TopologistsSineCurve.closedCarrier := w.2
      rw [TopologistsSineCurve.mem_closedCarrier_iff] at hwClosed
      rcases hwClosed with hwCarrier | hwBroken
      · exfalso
        let x : TopologistsSineCurve.Space := ⟨w.1, hwCarrier⟩
        apply hwS₀
        refine ⟨x, ?_⟩
        apply Subtype.ext
        rfl
      · exact hwBroken
    rw [← range_closedSineBrokenLinePath] at hwBroken
    obtain ⟨r, hrw⟩ := hwBroken
    have hwr : w = brokenLinePathToClosedSpace r := by
      apply Subtype.ext
      exact hrw.symm
    have hur : u < r := by
      apply lt_of_not_ge
      intro hru
      apply hwL₀
      change w ∈ Set.range (P.subpath 0 u)
      rw [Path.range_subpath_of_le _ _ _ u.property.1]
      exact ⟨r, ⟨r.property.1, hru⟩, hwr.symm⟩
    have hrv : r < v := by
      apply lt_of_not_ge
      intro hvr
      apply hwH₀
      change w ∈ Set.range (P.subpath v 1)
      rw [Path.range_subpath_of_le _ _ _ v.property.2]
      exact ⟨r, ⟨hvr, r.property.2⟩, hwr.symm⟩
    have hrPos : 0 < (r : ℝ) := huPos.trans hur
    have hrecipV : 1 / (v : ℝ) < 1 / (r : ℝ) :=
      one_div_lt_one_div_of_lt hrPos hrv
    have hrecipU : 1 / (r : ℝ) < 1 / (u : ℝ) :=
      one_div_lt_one_div_of_lt huPos hur
    have hinvV : 1 / (v : ℝ) = 1 + a := by
      dsimp [v]
      field_simp [show 1 + a ≠ 0 by linarith]
    have hinvU : 1 / (u : ℝ) = 1 + b := by
      dsimp [u]
      field_simp [show 1 + b ≠ 0 by linarith]
    let t : ℝ := 1 / (r : ℝ) - 1
    have hat : a < t := by
      dsimp [t]
      rw [hinvV] at hrecipV
      linarith
    have htb : t < b := by
      dsimp [t]
      rw [hinvU] at hrecipU
      linarith
    have htPos : 0 < t := ha.trans hat
    have hspine : closedSineSpineParam t = w := by
      apply Subtype.ext
      change closedSineSpinePlaneParam t = w.1
      rw [closedSineSpinePlaneParam, if_neg (not_le.mpr htPos),
        closedSineSpineBrokenBranch,
        closedSineSpineBrokenParameter_eq htPos.le, hwr]
      apply congrArg closedSineBrokenLinePath
      apply Subtype.ext
      dsimp [t]
      field_simp [hrPos.ne']
      ring
    refine ⟨t, ⟨hat, htb⟩, ?_⟩
    exact congrArg f hspine

/-- Helper for Exercise 63.3: deleting an open interval from the ordered
nonvertical spine leaves a closed nonseparating core of the embedded closed
sine curve. -/
private lemma closedSineSpineIntervalCore
    (f : TopologistsSineCurve.ClosedSpace → StandardSphere 2)
    (hf : Continuous f) (hfinj : Function.Injective f)
    {a b : ℝ} (hab : a < b) :
    ∃ B : Set (StandardSphere 2), IsClosed B ∧ B ⊆ Set.range f ∧
      ¬ B.Separates ∧
      Set.range f \ B ⊆ (f ∘ closedSineSpineParam) '' Ioo a b := by
  -- Route correction: only a smaller one-sided interval must be omitted, so
  -- crossing-zero and degenerate endpoint arcs are unnecessary.
  classical
  by_cases ha : a < 0
  · -- Refine below zero and invoke the strict graph-side construction.
    have hamin : a < min b 0 := lt_min hab ha
    obtain ⟨b', hab', hb'min⟩ := exists_between hamin
    obtain ⟨a', haa', ha'b'⟩ := exists_between hab'
    have hb' : b' < 0 := hb'min.trans_le (min_le_right b 0)
    have hb'b : b' < b := hb'min.trans_le (min_le_left b 0)
    obtain ⟨B, hBclosed, hBrange, hBnonseparating, hBmissing⟩ :=
      closedSineSpineIntervalCore_of_neg f hf hfinj ha'b' hb'
    refine ⟨B, hBclosed, hBrange, hBnonseparating, ?_⟩
    exact hBmissing.trans (Set.image_mono (fun _ ht ↦
      ⟨haa'.trans ht.1, ht.2.trans hb'b⟩))
  · -- Refine strictly above zero and use the two endpoint attachments.
    have haNonneg : 0 ≤ a := le_of_not_gt ha
    obtain ⟨a', haa', ha'b⟩ := exists_between hab
    obtain ⟨b', ha'b', hb'b⟩ := exists_between ha'b
    have ha' : 0 < a' := lt_of_le_of_lt haNonneg haa'
    obtain ⟨B, hBclosed, hBrange, hBnonseparating, hBmissing⟩ :=
      closedSineSpineIntervalCore_of_pos f hf hfinj ha' ha'b'
    refine ⟨B, hBclosed, hBrange, hBnonseparating, ?_⟩
    exact hBmissing.trans (Set.image_mono (fun _ ht ↦
      ⟨haa'.trans ht.1, ht.2.trans hb'b⟩))

/-- Helper for Exercise 63.3: the nonvertical spine of an embedded closed sine
curve is dense and admits arbitrarily large closed nonseparating cores. -/
private lemma closedSineCurve_largeNonseparatingCores
    (C : Set (StandardSphere 2))
    (hC : Nonempty (C ≃ₜ TopologistsSineCurve.ClosedSpace)) :
    ∃ R : Set (StandardSphere 2), C ⊆ closure R ∧
      ∀ z ∈ R, ∀ N ∈ nhds z,
        ∃ B : Set (StandardSphere 2), IsClosed B ∧ B ⊆ C ∧
          ¬ B.Separates ∧ C \ B ⊆ N := by
  -- Route correction: continuity of the injective spine parametrization is
  -- enough to pull back neighborhoods; no inverse-coordinate homeomorphism is needed.
  -- Transport the ordered dense spine through the supplied homeomorphism.
  classical
  obtain ⟨e⟩ := hC
  let f : TopologistsSineCurve.ClosedSpace → StandardSphere 2 :=
    fun u ↦ (e.symm u).1
  let F : ℝ → StandardSphere 2 := f ∘ closedSineSpineParam
  let R : Set (StandardSphere 2) := Set.range F
  have hfContinuous : Continuous f :=
    continuous_subtype_val.comp e.symm.continuous
  have hfInjective : Function.Injective f :=
    Subtype.val_injective.comp e.symm.injective
  have hfRange : Set.range f = C := by
    apply Set.Subset.antisymm
    · rintro y ⟨u, rfl⟩
      exact (e.symm u).2
    · intro y hy
      refine ⟨e ⟨y, hy⟩, ?_⟩
      simp only [f, e.symm_apply_apply]
  have hFContinuous : Continuous F :=
    hfContinuous.comp continuous_closedSineSpineParam
  have himageRange : f '' Set.range closedSineSpineParam = R := by
    apply Set.Subset.antisymm
    · rintro y ⟨u, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
    · rintro y ⟨t, rfl⟩
      exact ⟨closedSineSpineParam t, ⟨t, rfl⟩, rfl⟩
  refine ⟨R, ?_, ?_⟩
  · -- Continuity carries density of the source spine to density in `C`.
    rw [← hfRange]
    intro y hy
    obtain ⟨u, rfl⟩ := hy
    have hu : u ∈ closure (Set.range closedSineSpineParam) := by
      rw [denseRange_iff_closure_range.mp denseRange_closedSineSpineParam]
      exact Set.mem_univ u
    have hfu : f u ∈ closure (f '' Set.range closedSineSpineParam) :=
      image_closure_subset_closure_image hfContinuous ⟨u, hu, rfl⟩
    rwa [himageRange] at hfu
  · intro z hzR N hN
    obtain ⟨t, rfl⟩ := hzR
    -- Pull the requested neighborhood back to a real interval around `t`.
    have hpreimage : F ⁻¹' N ∈ nhds t :=
      hFContinuous.continuousAt.preimage_mem_nhds hN
    obtain ⟨a, b, ht, habN⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp hpreimage
    obtain ⟨B, hBclosed, hBrange, hBnonseparating, hmissing⟩ :=
      closedSineSpineIntervalCore f hfContinuous hfInjective (ht.1.trans ht.2)
    refine ⟨B, hBclosed, ?_, hBnonseparating, ?_⟩
    · -- The interval core stays inside the transported closed sine curve.
      rwa [← hfRange]
    · -- Every omitted point has a spine parameter in the pulled-back interval.
      intro y hy
      have hyRange : y ∈ Set.range f := by
        rw [hfRange]
        exact hy.1
      obtain ⟨s, hs, rfl⟩ := hmissing ⟨hyRange, hy.2⟩
      exact habN hs

/-- Exercise 63.3 (3): Every complementary component of a closed topologist's
sine curve in the standard two-sphere has the curve as its frontier. -/
theorem closedTopologistsSineCurve_frontier_component
    (C : Set (StandardSphere 2))
    (hC : Nonempty (C ≃ₜ TopologistsSineCurve.ClosedSpace))
    (x : (Cᶜ : Set (StandardSphere 2))) :
    frontier (connectedComponentIn Cᶜ x) = C := by
  -- The easy inclusion uses closedness; dense large nonseparating cores force
  -- the reverse inclusion by crossing the chosen complementary component.
  letI : LocallyPathConnectedSpace (StandardSphere 2) :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin 2)) (StandardSphere 2)
  have hCclosed := isClosed_of_homeomorphic_closedSineCurve C hC
  have hCtwo := closedTopologistsSineCurve_separatesInto C hC
  obtain ⟨R, hRdense, hcores⟩ := closedSineCurve_largeNonseparatingCores C hC
  apply Set.Subset.antisymm
  · exact frontier_connectedComponentIn_compl_subset C hCclosed x
  · exact subset_frontier_of_large_nonseparating_cores C hCclosed hCtwo
      R hRdense hcores x
