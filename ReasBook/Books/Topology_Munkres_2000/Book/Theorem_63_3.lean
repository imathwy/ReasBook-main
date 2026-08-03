module

public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Topology_Munkres_2000.Book.Definition_61_1.Separation
public import Topology_Munkres_2000.Book.Proposition_61_1.Stereographic
public import Topology_Munkres_2000.Book.Theorem_63_1
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

public section

open Set

/-- Helper for Theorem 63.3: two points outside a closed nonseparating subset of
the two-sphere can be joined through its complement. -/
private lemma joinedIn_compl_of_closed_not_separates
    (D : Set (StandardSphere 2)) (hDclosed : IsClosed D)
    (hDnonseparating : ¬ D.Separates) {x y : StandardSphere 2}
    (hx : x ∈ Dᶜ) (hy : y ∈ Dᶜ) : JoinedIn Dᶜ x y := by
  -- The empty-set case follows directly from path connectedness of the sphere.
  by_cases hDempty : D = ∅
  · rw [hDempty] at hx hy ⊢
    have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
      exact Module.one_lt_rank_of_one_lt_finrank (by norm_num)
    have hxyAmbient : JoinedIn (Metric.sphere
        (0 : EuclideanSpace ℝ (Fin 3)) 1) x.1 y.1 := by
      exact (isPathConnected_sphere hrank
        (0 : EuclideanSpace ℝ (Fin 3)) (show (0 : ℝ) ≤ 1 by norm_num)).joinedIn
          x.1 x.2 y.1 y.2
    have hxySphere : JoinedIn (Set.univ : Set (StandardSphere 2)) x y := by
      have himage :
          ((fun z : StandardSphere 2 ↦ z.1) '' Set.univ) =
            Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
        rw [Set.image_univ, Subtype.range_coe]
      apply (Topology.IsInducing.subtypeVal.joinedIn_image
        (F := Set.univ) (Set.mem_univ x) (Set.mem_univ y)).mp
      rwa [himage]
    simpa only [compl_empty] using hxySphere
  · obtain ⟨p, hp⟩ := D.nonempty_iff_ne_empty.mpr hDempty
    have hDcompl_subset_puncture : Dᶜ ⊆ ({p}ᶜ : Set (StandardSphere 2)) := by
      intro z hzD hzp
      exact hzD (hzp ▸ hp)
    let chart := StandardSphere.puncturedHomeomorphPlane p
    let chartDomain : Set ({p}ᶜ : Set (StandardSphere 2)) := Subtype.val ⁻¹' Dᶜ
    have hchartDomain_image : ((fun z ↦ z.1) '' chartDomain) = Dᶜ := by
      rw [Subtype.image_preimage_coe, inter_eq_right.mpr hDcompl_subset_puncture]
    have hchartDomain_open : IsOpen chartDomain := by
      exact hDclosed.isOpen_compl.preimage continuous_subtype_val
    have hchartDomain_nonempty : chartDomain.Nonempty := by
      exact ⟨⟨x, hDcompl_subset_puncture hx⟩, hx⟩
    -- Nonseparation gives connectedness; the planar chart upgrades it to path connectedness.
    have hDcompl_preconnected : IsPreconnected Dᶜ := by
      apply isPreconnected_iff_preconnectedSpace.mpr
      by_contra hpre
      exact hDnonseparating (Set.separates_iff.mpr hpre)
    have hchartDomain_preconnected : IsPreconnected chartDomain := by
      apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      rw [hchartDomain_image]
      exact hDcompl_preconnected
    have hchartDomain_connected : IsConnected chartDomain :=
      ⟨hchartDomain_nonempty, hchartDomain_preconnected⟩
    have hchartImage_open : IsOpen (chart '' chartDomain) :=
      chart.isOpenMap chartDomain hchartDomain_open
    have hchartImage_connected : IsConnected (chart '' chartDomain) :=
      chart.isConnected_image.mpr hchartDomain_connected
    have hchartImage_pathConnected : IsPathConnected (chart '' chartDomain) :=
      (hchartImage_open.isConnected_iff_isPathConnected).mp hchartImage_connected
    have hchartDomain_pathConnected : IsPathConnected chartDomain :=
      chart.isPathConnected_image.mp hchartImage_pathConnected
    have hxy_punctured : JoinedIn chartDomain
        (⟨x, hDcompl_subset_puncture hx⟩ : ({p}ᶜ : Set (StandardSphere 2)))
        (⟨y, hDcompl_subset_puncture hy⟩ : ({p}ᶜ : Set (StandardSphere 2))) := by
      exact hchartDomain_pathConnected.joinedIn _ hx _ hy
    -- Mapping the chart-domain path back to the sphere gives the required path.
    have hxy_sphere := hxy_punctured.map continuous_subtype_val
    rwa [hchartDomain_image] at hxy_sphere

/-- Helper for Theorem 63.3: an open non-preconnected set splits into two
nonempty disjoint open subsets. -/
private lemma exists_disjoint_open_partition_of_open_not_isPreconnected
    {X : Type*} [TopologicalSpace X] (s : Set X) (hsopen : IsOpen s)
    (hsnot : ¬ IsPreconnected s) :
    ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ A.Nonempty ∧ B.Nonempty ∧
      Disjoint A B ∧ s = A ∪ B := by
  -- Negating the open-cover characterization provides two sides meeting `s` disjointly.
  rw [isPreconnected_iff_subset_of_disjoint] at hsnot
  push Not at hsnot
  obtain ⟨u, v, huopen, hvopen, hcover, hinter, hnotu, hnotv⟩ := hsnot
  let A := s ∩ u
  let B := s ∩ v
  have hAopen : IsOpen A := hsopen.inter huopen
  have hBopen : IsOpen B := hsopen.inter hvopen
  have hAnonempty : A.Nonempty := by
    obtain ⟨a, has, hav⟩ := not_subset.mp hnotv
    exact ⟨a, has, (hcover has).resolve_right hav⟩
  have hBnonempty : B.Nonempty := by
    obtain ⟨b, hbs, hbu⟩ := not_subset.mp hnotu
    exact ⟨b, hbs, (hcover hbs).resolve_left hbu⟩
  have hAB : Disjoint A B := by
    rw [Set.disjoint_left]
    intro z hzA hzB
    have hzempty : z ∈ s ∩ (u ∩ v) := ⟨hzA.1, hzA.2, hzB.2⟩
    rw [hinter] at hzempty
    exact hzempty
  have hs_union : s = A ∪ B := by
    rw [← inter_union_distrib_left, inter_eq_left.mpr hcover]
  exact ⟨A, B, hAopen, hBopen, hAnonempty, hBnonempty, hAB, hs_union⟩

/-- Helper for Theorem 63.3: a path in a subset lifts to the corresponding
preimage inside any containing subtype. -/
private lemma joinedIn_subtype_preimage_of_subset
    {X : Type*} [TopologicalSpace X] {F S : Set X} (hFS : F ⊆ S)
    (x y : S) (hx : x.1 ∈ F) (hy : y.1 ∈ F)
    (hxy : JoinedIn F x.1 y.1) : JoinedIn (Subtype.val ⁻¹' F) x y := by
  -- The subtype embedding identifies the preimage with `F` because `F ⊆ S`.
  have himage :
      ((fun z ↦ z.1) '' (Subtype.val ⁻¹' F : Set S)) = F := by
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hFS]
  apply (Topology.IsInducing.subtypeVal.joinedIn_image
    (F := Subtype.val ⁻¹' F) hx hy).mp
  rwa [himage]

/-- Theorem 63.3 (A general nonseparation theorem): Let `D₁` and `D₂` be closed
subsets of the standard two-sphere such that the complement of `D₁ ∩ D₂` is
simply connected. If neither `D₁` nor `D₂` separates the sphere, then neither
does `D₁ ∪ D₂`. -/
theorem union_not_separates_of_compl_inter_simplyConnected
    (D₁ D₂ : Set (StandardSphere 2))
    (hD₁closed : IsClosed D₁) (hD₂closed : IsClosed D₂)
    (hinter : IsSimplyConnected ((D₁ ∩ D₂)ᶜ))
    (hD₁nonseparating : ¬ D₁.Separates)
    (hD₂nonseparating : ¬ D₂.Separates) :
    ¬ (D₁ ∪ D₂).Separates := by
  -- Work in the simply connected complement of the intersection.
  let P := ((D₁ ∩ D₂)ᶜ : Set (StandardSphere 2))
  let U : Set P := Subtype.val ⁻¹' D₁ᶜ
  let V : Set P := Subtype.val ⁻¹' D₂ᶜ
  have hUopen : IsOpen U := hD₁closed.isOpen_compl.preimage continuous_subtype_val
  have hVopen : IsOpen V := hD₂closed.isOpen_compl.preimage continuous_subtype_val
  have hcover : U ∪ V = Set.univ := by
    ext z
    simp only [U, V, Set.mem_union, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_univ, iff_true]
    exact not_and_or.mp z.2
  have hoverlap : U ∩ V = Subtype.val ⁻¹' (D₁ ∪ D₂)ᶜ := by
    ext z
    simp only [U, V, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_union, not_or]
  have hunionCompl_subset : (D₁ ∪ D₂)ᶜ ⊆ (D₁ ∩ D₂)ᶜ := by
    intro z hz hzi
    exact hz (Or.inl hzi.1)
  have hoverlap_image : ((fun z ↦ z.1) '' (U ∩ V)) = (D₁ ∪ D₂)ᶜ := by
    rw [hoverlap, Subtype.image_preimage_coe,
      inter_eq_right.mpr hunionCompl_subset]
  intro hseparates
  have hoverlap_not_preconnected : ¬ IsPreconnected (U ∩ V) := by
    intro hoverlap_preconnected
    have himage := hoverlap_preconnected.image Subtype.val continuous_subtype_val.continuousOn
    rw [hoverlap_image] at himage
    exact (Set.separates_iff.mp hseparates)
      (isPreconnected_iff_preconnectedSpace.mp himage)
  have hoverlap_open : IsOpen (U ∩ V) := hUopen.inter hVopen
  obtain ⟨A, B, hAopen, hBopen, hAnonempty, hBnonempty, hAB, hoverlap_partition⟩ :=
    exists_disjoint_open_partition_of_open_not_isPreconnected
      (U ∩ V) hoverlap_open hoverlap_not_preconnected
  obtain ⟨a, ha⟩ := hAnonempty
  obtain ⟨b, hb⟩ := hBnonempty
  have ha_overlap : a ∈ U ∩ V := by
    rw [hoverlap_partition]
    exact Or.inl ha
  have hb_overlap : b ∈ U ∩ V := by
    rw [hoverlap_partition]
    exact Or.inr hb
  -- Nonseparation of each closed set supplies the two crossing paths.
  have hD₁compl_subset : D₁ᶜ ⊆ (D₁ ∩ D₂)ᶜ := by
    intro z hz hzi
    exact hz hzi.1
  have hD₂compl_subset : D₂ᶜ ⊆ (D₁ ∩ D₂)ᶜ := by
    intro z hz hzi
    exact hz hzi.2
  have hjoinedU : JoinedIn U a b := by
    exact joinedIn_subtype_preimage_of_subset hD₁compl_subset a b
      ha_overlap.1 hb_overlap.1
      (joinedIn_compl_of_closed_not_separates D₁ hD₁closed hD₁nonseparating
        ha_overlap.1 hb_overlap.1)
  have hjoinedV : JoinedIn V b a := by
    exact joinedIn_subtype_preimage_of_subset hD₂compl_subset b a
      hb_overlap.2 ha_overlap.2
      (joinedIn_compl_of_closed_not_separates D₂ hD₂closed hD₂nonseparating
        hb_overlap.2 ha_overlap.2)
  let α : Path a b := hjoinedU.somePath
  let β : Path b a := hjoinedV.somePath
  have hloopOrder :
      orderOf (FundamentalGroup.fromPath (.mk (α.trans β))) = 0 := by
    exact crossingLoopClass_orderOf_eq_zero U V A B α β hUopen hVopen hAopen hBopen
      hcover hoverlap_partition hAB ha hb
      (fun t ↦ hjoinedU.somePath_mem t) (fun t ↦ hjoinedV.somePath_mem t)
  -- In a simply connected space every loop class is the identity, whose order is one.
  letI : SimplyConnectedSpace P := hinter.simplyConnectedSpace
  have hloopOne : FundamentalGroup.fromPath (.mk (α.trans β)) = 1 :=
    Subsingleton.elim _ _
  rw [hloopOne, orderOf_one] at hloopOrder
  norm_num at hloopOrder
