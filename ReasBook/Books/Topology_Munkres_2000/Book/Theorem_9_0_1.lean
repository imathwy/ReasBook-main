module

public import Topology_Munkres_2000.Book.Definition_61_1.Separation
public import Topology_Munkres_2000.Book.Definition_61_2.Arc
public import Topology_Munkres_2000.Book.Definition_61_3.SimpleClosedCurve
public import Topology_Munkres_2000.Book.Definition_25_1.ComponentIn
public import Topology_Munkres_2000.Book.Theorem_9_0_1.ArcNonseparation
public import Topology_Munkres_2000.Book.Theorem_9_0_1.BorsukExtension
public import Topology_Munkres_2000.Book.Theorem_9_0_1.BorsukNoRetraction
public import Topology_Munkres_2000.Book.Theorem_9_0_1.CrossingComponents
public import Topology_Munkres_2000.Book.Theorem_9_0_1.Nullhomotopy
public import Topology_Munkres_2000.Book.Theorem_9_0_1.OpenCoverWinding
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Topology.ContinuousMap.Interval
public import Mathlib.Topology.Homotopy.Lifting

public section

open Set
open scoped Topology

universe u

/-- Helper for Theorem 9.0.1: the ambient Euclidean space of
`StandardSphere n` has dimension `n + 1`. -/
private lemma finrank_standardSphereAmbient (n : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1 := by
  -- Euclidean coordinates are indexed by `Fin (n + 1)`.
  simp

/-- Helper for Theorem 9.0.1: stereographic projection on `StandardSphere n`
uses its canonical ambient-dimension certificate. -/
private instance standardSphereAmbientFinrankFact (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_standardSphereAmbient n⟩

-- Route correction: the earlier planar two-arc route stalled at Jordan separation;
-- the following API isolates the homeomorphism transport needed by the spherical route.

/-- Helper for Theorem 9.0.1: a homeomorphism carries a simple closed curve
to a simple closed curve. -/
private lemma isSimpleClosedCurve_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (A : Set X) [Topology.IsSimpleClosedCurve A] :
    Topology.IsSimpleClosedCurve (e '' A) := by
  -- Compose the inverse image homeomorphism with the given circle model.
  obtain ⟨hA⟩ := Topology.IsSimpleClosedCurve.homeomorphic_circle (X := A)
  exact ⟨⟨(e.image A).symm.trans hA⟩⟩

/-- Helper for Theorem 9.0.1: a homeomorphism restricts to a homeomorphism
between the complements of a set and its image. -/
private def complementImageHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (A : Set X) :
    (Aᶜ : Set X) ≃ₜ ((e '' A)ᶜ : Set Y) :=
  (e.image Aᶜ).trans (Homeomorph.setCongr (e.image_compl A))

/-- Helper for Theorem 9.0.1: a homeomorphism induces an equivalence of
connected-component quotients. -/
private noncomputable def connectedComponentsHomeomorphOfHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    ConnectedComponents X ≃ₜ ConnectedComponents Y :=
  e.isQuotientMap.isCoinducing.connectedComponentsHomeomorph
    (fun y ↦ e.isConnected_preimage.mpr (isConnected_singleton : IsConnected ({y} : Set Y)))

/-- Helper for Theorem 9.0.1: the number of complementary components is
invariant under an ambient homeomorphism. -/
private lemma separatesInto_image_iff
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (A : Set X) (n : ℕ) :
    (e '' A).SeparatesInto n ↔ A.SeparatesInto n := by
  -- Restrict the ambient homeomorphism to the complements, then pass to `π₀`.
  rw [Set.separatesInto_iff, Set.separatesInto_iff]
  let hComplement := complementImageHomeomorph e A
  let hComponents := connectedComponentsHomeomorphOfHomeomorph hComplement
  have hCardinal : Cardinal.mk (ConnectedComponents (Aᶜ : Set X)) =
      Cardinal.mk (ConnectedComponents ((e '' A)ᶜ : Set Y)) :=
    Cardinal.mk_congr hComponents.toEquiv
  exact ⟨fun h ↦ hCardinal.trans h, fun h ↦ hCardinal.symm.trans h⟩

/-- Helper for Theorem 9.0.1: the common-frontier conclusion transports
through an ambient homeomorphism. -/
private lemma frontier_connectedComponentIn_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (A : Set X) (x : (Aᶜ : Set X))
    (hfrontier : frontier (connectedComponentIn Aᶜ x) = A) :
    frontier (connectedComponentIn (e '' A)ᶜ (e x)) = e '' A := by
  -- First transport the component, then transport its frontier.
  calc
    frontier (connectedComponentIn (e '' A)ᶜ (e x)) =
        frontier (e '' connectedComponentIn Aᶜ x) := by
          rw [← e.image_compl A, e.image_connectedComponentIn x.property]
    _ = e '' frontier (connectedComponentIn Aᶜ x) :=
      (e.image_frontier (connectedComponentIn Aᶜ x)).symm
    _ = e '' A := congrArg (e '' ·) hfrontier

/-- Helper for Theorem 9.0.1: a planar simple closed curve is closed. -/
private lemma isClosed_of_isSimpleClosedCurve
    (C : Set (EuclideanSpace ℝ (Fin 2))) [Topology.IsSimpleClosedCurve C] :
    IsClosed C := by
  -- Transport compactness from the circle to the curve subtype.
  classical
  obtain ⟨e⟩ := Topology.IsSimpleClosedCurve.homeomorphic_circle (X := C)
  letI : CompactSpace C := e.symm.compactSpace
  have hCcompact : IsCompact C := isCompact_iff_compactSpace.mpr inferInstance
  -- Compact subsets of the Euclidean plane are closed.
  exact hCcompact.isClosed

/-- Helper for Theorem 9.0.1: in a locally connected space, the frontier of a
complementary component of a closed set lies in that set. -/
private lemma frontier_connectedComponentIn_compl_subset
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    (A : Set X) (hA : IsClosed A) (x : (Aᶜ : Set X)) :
    frontier (connectedComponentIn Aᶜ x) ⊆ A := by
  -- Complementary components are open because the plane is locally connected.
  intro z hz
  have hcomponentOpen : IsOpen (connectedComponentIn Aᶜ x) :=
    hA.isOpen_compl.connectedComponentIn
  have hzNotMem : z ∉ connectedComponentIn Aᶜ x := by
    intro hzMem
    have hzInterior : z ∈ interior (connectedComponentIn Aᶜ x) :=
      hcomponentOpen.interior_eq.symm ▸ hzMem
    exact (mem_frontier_iff_notMem_interior hzMem).mp hz hzInterior
  -- A frontier point outside `A` would lie in another open complementary component.
  by_contra hzA
  have hzCompl : z ∈ Aᶜ := hzA
  have hzOwnComponent : z ∈ connectedComponentIn Aᶜ z :=
    mem_connectedComponentIn hzCompl
  have hownOpen : IsOpen (connectedComponentIn Aᶜ z) :=
    hA.isOpen_compl.connectedComponentIn
  have hzClosure : z ∈ closure (connectedComponentIn Aᶜ x) :=
    frontier_subset_closure hz
  rcases mem_closure_iff.mp hzClosure (connectedComponentIn Aᶜ z) hownOpen hzOwnComponent with
    ⟨y, hyOwn, hyComponent⟩
  -- Intersecting connected components coincide, contradicting `z ∉` the first one.
  have heq : connectedComponentIn Aᶜ x = connectedComponentIn Aᶜ z :=
    (connectedComponentIn_eq hyComponent).trans (connectedComponentIn_eq hyOwn).symm
  exact hzNotMem (heq ▸ hzOwnComponent)

/-- Helper for Theorem 9.0.1: a preconnected set meeting a set and the
complement of its closure also meets its frontier. -/
private lemma IsPreconnected.inter_frontier_nonempty_of_mem_of_mem_compl_closure
    {X : Type*} [TopologicalSpace X] {S W : Set X} (hS : IsPreconnected S)
    (hSW : (S ∩ W).Nonempty) (hSclosure : (S ∩ (closure W)ᶜ).Nonempty) :
    (S ∩ frontier W).Nonempty := by
  -- A point outside the closure is in particular outside the original set.
  have hScompl : (S ∩ Wᶜ).Nonempty := by
    obtain ⟨x, hxS, hxClosure⟩ := hSclosure
    exact ⟨x, hxS, fun hxW ↦ hxClosure (subset_closure hxW)⟩
  -- If the frontier were avoided, preconnectedness would force `S` into one
  -- of the two disjoint open interiors, contradicting one of the witnesses.
  by_contra hfrontier
  rw [Set.not_nonempty_iff_eq_empty] at hfrontier
  have hdisjoint : Disjoint S (frontier W) :=
    Set.disjoint_iff_inter_eq_empty.mpr hfrontier
  have hcover : S ⊆ interior W ∪ interior Wᶜ := by
    rw [← compl_frontier_eq_union_interior]
    exact hdisjoint.subset_compl_right
  have hinteriors : Disjoint (interior W) (interior Wᶜ) :=
    disjoint_compl_right.mono interior_subset interior_subset
  obtain hSin | hSin :=
    hS.subset_or_subset isOpen_interior isOpen_interior hinteriors hcover
  · obtain ⟨x, hxS, hxCompl⟩ := hScompl
    exact hxCompl (interior_subset (hSin hxS))
  · obtain ⟨x, hxS, hxW⟩ := hSW
    exact (interior_subset (hSin hxS)) hxW

/-- Helper for Theorem 9.0.1: stereographic projection identifies a punctured
standard two-sphere with the Euclidean plane. -/
private noncomputable def puncturedSphereHomeomorphPlane
    (b : StandardSphere 2) :
    ({b}ᶜ : Set (StandardSphere 2)) ≃ₜ EuclideanSpace ℝ (Fin 2) :=
  ((Homeomorph.setCongr (stereographic'_source (n := 2) b).symm).trans
    (stereographic' 2 b).toHomeomorphSourceTarget).trans
      ((Homeomorph.setCongr (stereographic'_target (n := 2) b)).trans
        (Homeomorph.Set.univ _))

/-- Helper for Theorem 9.0.1: stereographic projection identifies a punctured
standard `n`-sphere with `EuclideanSpace ℝ (Fin n)`. -/
private noncomputable def puncturedStandardSphereHomeomorphEuclidean
    (n : ℕ) (p : StandardSphere n) :
    ({p}ᶜ : Set (StandardSphere n)) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  ((Homeomorph.setCongr (stereographic'_source (n := n) p).symm).trans
    (stereographic' n p).toHomeomorphSourceTarget).trans
      ((Homeomorph.setCongr (stereographic'_target (n := n) p)).trans
        (Homeomorph.Set.univ _))

/-- Helper for Theorem 9.0.1: positive dilation carries the Euclidean unit
closed ball onto the closed ball of the dilation radius. -/
private lemma smulTorsor_mem_closedBall_iff
    {n : ℕ} {r : ℝ} (hr : 0 < r) (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ Metric.closedBall 0 1 ↔
      DilationEquiv.smulTorsor (0 : EuclideanSpace ℝ (Fin n)) hr.ne' x ∈
        Metric.closedBall 0 r := by
  -- Norm scaling reduces both memberships to the same inequality.
  simp only [Metric.mem_closedBall, DilationEquiv.smulTorsor_apply, vadd_eq_add,
    add_zero, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  rw [mul_comm r ‖x‖, mul_le_iff_le_one_left hr]

/-- Helper for Theorem 9.0.1: a positive-radius Euclidean closed ball is
homeomorphic to the unit closed ball. -/
private noncomputable def closedBallHomeomorphUnitBall
    (n : ℕ) (r : ℝ) (hr : 0 < r) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r ≃ₜ
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  ((DilationEquiv.smulTorsor (0 : EuclideanSpace ℝ (Fin n)) hr.ne').toHomeomorph.subtype
    (smulTorsor_mem_closedBall_iff hr)).symm

/-- Helper for Theorem 9.0.1: every neighborhood of a point on an embedded
standard sphere contains the portion left outside a closed-ball core. -/
private lemma existsClosedBallCoreOfMemNhds
    {X : Type*} [TopologicalSpace X] (n : ℕ) (C : Set X)
    (hC : Nonempty (C ≃ₜ StandardSphere n)) (c : C)
    {U : Set X} (hU : U ∈ 𝓝 (c : X)) :
    ∃ B : Set X,
      B ⊆ C ∧
        Nonempty (B ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) ∧
        C \ B ⊆ U := by
  classical
  -- Work in an open ambient neighborhood and transport its compact complement.
  obtain ⟨e⟩ := hC
  obtain ⟨O, hOU, hOopen, hcO⟩ := mem_nhds_iff.mp hU
  let p : StandardSphere n := e c
  let V : Set (StandardSphere n) :=
    (fun q ↦ ((e.symm q : C) : X)) ⁻¹' O
  have hVopen : IsOpen V :=
    hOopen.preimage (continuous_subtype_val.comp e.symm.continuous)
  have hpV : p ∈ V := by
    simpa [p, V] using hcO
  have hKcompact : IsCompact Vᶜ := hVopen.isClosed_compl.isCompact
  have hKpunct : Vᶜ ⊆ ({p}ᶜ : Set (StandardSphere n)) := by
    intro q hqK hqp
    exact hqK (Set.mem_singleton_iff.mp hqp ▸ hpV)
  letI : CompactSpace (Vᶜ : Set (StandardSphere n)) :=
    isCompact_iff_compactSpace.mp hKcompact
  -- Enclose the compact stereographic image in a positive-radius ball.
  let punctured := puncturedStandardSphereHomeomorphEuclidean n p
  let kToPunct : (Vᶜ : Set (StandardSphere n)) →
      ({p}ᶜ : Set (StandardSphere n)) :=
    fun q ↦ ⟨q, hKpunct q.property⟩
  have hkToPunctContinuous : Continuous kToPunct :=
    continuous_subtype_val.subtype_mk _
  let chartOnK : (Vᶜ : Set (StandardSphere n)) → EuclideanSpace ℝ (Fin n) :=
    fun q ↦ punctured (kToPunct q)
  have hchartOnKContinuous : Continuous chartOnK :=
    punctured.continuous.comp hkToPunctContinuous
  have hchartRangeCompact : IsCompact (Set.range chartOnK) :=
    isCompact_range hchartOnKContinuous
  obtain ⟨r, hr, hchartRange⟩ :=
    hchartRangeCompact.isBounded.subset_closedBall_lt 0
      (0 : EuclideanSpace ℝ (Fin n))
  -- Pull the ball back to the embedded copy of the sphere.
  let D : Set ({p}ᶜ : Set (StandardSphere n)) :=
    punctured ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r
  let embeddedPuncture : ({p}ᶜ : Set (StandardSphere n)) → X :=
    fun q ↦ (e.symm q : X)
  have hembeddedPuncture : Topology.IsEmbedding embeddedPuncture :=
    Topology.IsEmbedding.subtypeVal.comp
      (e.symm.isEmbedding.comp Topology.IsEmbedding.subtypeVal)
  let B : Set X := embeddedPuncture '' D
  let DHomeomorphBall :
      D ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r :=
    punctured.subtype (fun _ ↦ Iff.rfl)
  let DHomeomorphB : D ≃ₜ B :=
    hembeddedPuncture.homeomorphImage D
  have hBball : Nonempty
      (B ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    ⟨DHomeomorphB.symm.trans
      (DHomeomorphBall.trans (closedBallHomeomorphUnitBall n r hr))⟩
  refine ⟨B, ?_, hBball, ?_⟩
  · rintro y ⟨q, -, rfl⟩
    exact (e.symm q).property
  · rintro y ⟨hyC, hyB⟩
    apply hOU
    by_contra hyO
    let q : StandardSphere n := e ⟨y, hyC⟩
    have hqK : q ∈ Vᶜ := by
      intro hqV
      apply hyO
      simpa [q, V] using hqV
    let qK : (Vᶜ : Set (StandardSphere n)) := ⟨q, hqK⟩
    let qPunct : ({p}ᶜ : Set (StandardSphere n)) := kToPunct qK
    have hqBall : punctured qPunct ∈
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r := by
      apply hchartRange
      exact ⟨qK, rfl⟩
    apply hyB
    refine ⟨qPunct, hqBall, ?_⟩
    have hrecover := congrArg Subtype.val (e.symm_apply_apply ⟨y, hyC⟩)
    simpa only [embeddedPuncture, qPunct, kToPunct, qK, q] using hrecover

/-- Helper for Theorem 9.0.1: a punctured-space homeomorphism exchanges the
preimage of a complement with the complement of the image. -/
private lemma imagePreimageComplEqComplImage
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (C : Set X) (b : X) (h : ({b}ᶜ : Set X) ≃ₜ Y) :
    h '' (Subtype.val ⁻¹' Cᶜ) = (h '' (Subtype.val ⁻¹' C))ᶜ := by
  -- Represent a target point by its unique preimage and compare membership.
  ext y
  obtain ⟨x, rfl⟩ := h.surjective y
  constructor
  · rintro ⟨z, hz, hzx⟩ ⟨w, hw, hwx⟩
    have hzw : z = w := h.injective (hzx.trans hwx.symm)
    exact hz (hzw ▸ hw)
  · intro hx
    refine ⟨x, ?_, rfl⟩
    intro hxC
    exact hx ⟨x, hxC, rfl⟩

/-- Helper for Theorem 9.0.1: a complementary component avoiding the
stereographic pole becomes a bounded planar complementary component. -/
private lemma puncturedSphereComponentImageBounded
    (C U : Set (StandardSphere 2)) (b : StandardSphere 2)
    (h : ({b}ᶜ : Set (StandardSphere 2)) ≃ₜ EuclideanSpace ℝ (Fin 2))
    (hC : IsCompact C) (hb : b ∉ C)
    (hU : IsConnectedComponentIn Cᶜ U) (hbU : b ∉ U) :
    IsConnectedComponentIn (h '' (Subtype.val ⁻¹' C))ᶜ
        (h '' (Subtype.val ⁻¹' U)) ∧
      Bornology.IsBounded (h '' (Subtype.val ⁻¹' U)) := by
  letI : LocallyPathConnectedSpace (StandardSphere 2) :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin 2)) (StandardSphere 2)
  -- Distinct open components keep the pole away from the closure of `U`.
  have hCopen : IsOpen Cᶜ := hC.isClosed.isOpen_compl
  have hbC : b ∈ Cᶜ := hb
  let B := connectedComponentIn Cᶜ b
  have hBcomponent : IsConnectedComponentIn Cᶜ B :=
    IsConnectedComponentIn.of_mem hbC
  have hBopen : IsOpen B := by
    rw [hBcomponent.eq_connectedComponentIn (mem_connectedComponentIn hbC)]
    exact hCopen.connectedComponentIn
  have hUB : U ≠ B := by
    intro hEq
    exact hbU (hEq ▸ mem_connectedComponentIn hbC)
  have hdisjoint : Disjoint U B := by
    rw [Set.disjoint_left]
    intro x hxU hxB
    apply hUB
    calc
      U = connectedComponentIn Cᶜ x := hU.eq_connectedComponentIn hxU
      _ = B := (hBcomponent.eq_connectedComponentIn hxB).symm
  have hdisjointClosure : Disjoint (closure U) B :=
    hdisjoint.closure_left hBopen
  have hbClosure : b ∉ closure U := by
    intro hbcl
    exact Set.disjoint_left.mp hdisjointClosure hbcl (mem_connectedComponentIn hbC)
  have hclosureSubset : closure U ⊆ ({b}ᶜ : Set (StandardSphere 2)) := by
    intro x hx
    simp only [mem_compl_iff, mem_singleton_iff]
    intro hxb
    exact hbClosure (hxb ▸ hx)
  have hcompactClosure : IsCompact (closure U) := isClosed_closure.isCompact
  have hcompactPreimage : IsCompact
      (Subtype.val ⁻¹' closure U : Set ({b}ᶜ : Set (StandardSphere 2))) := by
    rw [Topology.IsEmbedding.isCompact_iff Topology.IsEmbedding.subtypeVal]
    simpa [Subtype.image_preimage_coe, inter_eq_right.mpr hclosureSubset] using
      hcompactClosure
  have hcompactImage : IsCompact (h '' (Subtype.val ⁻¹' closure U)) :=
    hcompactPreimage.image h.continuous
  have hbounded : Bornology.IsBounded (h '' (Subtype.val ⁻¹' U)) :=
    hcompactImage.isBounded.subset (image_mono (preimage_mono subset_closure))
  -- Removing the omitted pole preserves `U` and its maximal connectedness.
  have hPconnected : IsConnected
      (Subtype.val ⁻¹' U : Set ({b}ᶜ : Set (StandardSphere 2))) := by
    apply hU.isConnected.preimage_of_isOpenMap Subtype.val_injective
      isOpen_compl_singleton.isOpenMap_subtype_val
    intro x hx
    have hxb : x ∈ ({b}ᶜ : Set (StandardSphere 2)) := by
      intro hxb
      exact hbU (hxb ▸ hx)
    exact ⟨⟨x, hxb⟩, rfl⟩
  obtain ⟨x, hxP⟩ := hPconnected.nonempty
  have hxC : x ∈ Subtype.val ⁻¹' Cᶜ := hU.subset hxP
  have hPeq : (Subtype.val ⁻¹' U : Set ({b}ᶜ : Set (StandardSphere 2))) =
      connectedComponentIn (Subtype.val ⁻¹' Cᶜ) x := by
    apply Set.Subset.antisymm
    · exact hPconnected.isPreconnected.subset_connectedComponentIn hxP
        (preimage_mono hU.subset)
    · intro y hy
      have hImageConnected : IsPreconnected
          (Subtype.val '' connectedComponentIn (Subtype.val ⁻¹' Cᶜ) x) :=
        isPreconnected_connectedComponentIn.image Subtype.val
          continuous_subtype_val.continuousOn
      have hImageSubset : Subtype.val '' connectedComponentIn
          (Subtype.val ⁻¹' Cᶜ) x ⊆ Cᶜ := by
        rintro z ⟨w, hw, rfl⟩
        exact connectedComponentIn_subset (Subtype.val ⁻¹' Cᶜ) x hw
      have hImageInU : Subtype.val '' connectedComponentIn
          (Subtype.val ⁻¹' Cᶜ) x ⊆ U := by
        rw [hU.eq_connectedComponentIn hxP]
        exact hImageConnected.subset_connectedComponentIn
          (mem_image_of_mem Subtype.val (mem_connectedComponentIn hxC)) hImageSubset
      exact hImageInU ⟨y, hy, rfl⟩
  have hImageEq : h '' (Subtype.val ⁻¹' U) =
      connectedComponentIn (h '' (Subtype.val ⁻¹' Cᶜ)) (h x) := by
    rw [hPeq]
    exact h.image_connectedComponentIn hxC
  rw [imagePreimageComplEqComplImage C b h] at hImageEq
  have hImageComponent : IsConnectedComponentIn
      (h '' (Subtype.val ⁻¹' C))ᶜ (h '' (Subtype.val ⁻¹' U)) := by
    rw [hImageEq]
    apply IsConnectedComponentIn.of_mem
    rw [← imagePreimageComplEqComplImage C b h]
    exact mem_image_of_mem h hxC
  exact ⟨hImageComponent, hbounded⟩

/-- Helper for Theorem 9.0.1: adjoining a complementary component to a closed
set gives a closed subset of the ambient space. -/
private lemma isClosed_componentUnion
    {E : Type*} [TopologicalSpace E] (K U : Set E) (hK : IsClosed K)
    (hU : IsConnectedComponentIn Kᶜ U) : IsClosed (U ∪ K) := by
  -- Express the component through the corresponding component of the complement subtype.
  obtain ⟨x, hxU⟩ := hU.nonempty
  have hxK : x ∈ Kᶜ := hU.subset hxU
  rw [hU.eq_connectedComponentIn hxU, ← isOpen_compl_iff]
  have hRelativeOpen :
      IsOpen ((connectedComponent (⟨x, hxK⟩ : {y : E // y ∉ K}) :
        Set {y : E // y ∉ K})ᶜ) :=
    isClosed_connectedComponent.isOpen_compl
  have hAmbientOpen :
      IsOpen (Subtype.val '' ((connectedComponent
        (⟨x, hxK⟩ : {y : E // y ∉ K}) : Set {y : E // y ∉ K})ᶜ)) :=
    hK.isOpen_compl.isOpenEmbedding_subtypeVal.isOpenMap _ hRelativeOpen
  convert hAmbientOpen using 1
  ext y
  constructor
  · intro hy
    have hyK : y ∉ K := by
      intro hyK
      exact hy (Or.inr hyK)
    refine ⟨⟨y, hyK⟩, ?_, rfl⟩
    intro hyComponent
    apply hy
    apply Or.inl
    rw [connectedComponentIn_eq_image hxK]
    exact ⟨⟨y, hyK⟩, hyComponent, rfl⟩
  · rintro ⟨z, hzComponent, rfl⟩ hy
    rcases hy with hyU | hyKmem
    · rw [connectedComponentIn_eq_image hxK] at hyU
      obtain ⟨w, hw, hwz⟩ := hyU
      have hwEq : w = z := Subtype.ext hwz
      exact hzComponent (hwEq ▸ hw)
    · exact z.property hyKmem

/-- Helper for Theorem 9.0.1: a nullhomotopic compact embedding induces the
ambient inclusion on its image, with the same nullhomotopy. -/
private lemma existsNullhomotopicRangeInclusion
    {X E : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace E] [T2Space E] (Y : Set E) (f : C(X, Y))
    (hfInjective : Function.Injective f) (hfNullhomotopic : f.Nullhomotopic) :
    ∃ j : C(Set.range (fun x : X ↦ (f x : E)), Y),
      (∀ x, (j x : E) = x) ∧ j.Nullhomotopic := by
  -- Identify the compact source with the range of its ambient embedding.
  let ambient : C(X, E) :=
    ⟨fun x ↦ (f x : E), continuous_subtype_val.comp (map_continuous f)⟩
  have hAmbientInjective : Function.Injective ambient := by
    intro x y hxy
    apply hfInjective
    exact Subtype.ext hxy
  have hEmbedding : Topology.IsEmbedding ambient :=
    ((map_continuous ambient).isClosedEmbedding hAmbientInjective).isEmbedding
  let rangeHomeomorph : X ≃ₜ Set.range (fun x : X ↦ (f x : E)) :=
    hEmbedding.toHomeomorph
  let inverse : C(Set.range (fun x : X ↦ (f x : E)), X) :=
    ⟨rangeHomeomorph.symm, rangeHomeomorph.symm.continuous⟩
  let j : C(Set.range (fun x : X ↦ (f x : E)), Y) := f.comp inverse
  refine ⟨j, ?_, hfNullhomotopic.comp_left inverse⟩
  intro x
  exact congrArg Subtype.val (rangeHomeomorph.apply_symm_apply x)

/-- Helper for Theorem 9.0.1: a nullhomotopic identity map on a closed planar
set extends over its union with a complementary component. -/
private lemma existsNullhomotopicComponentUnionExtension
    (K U : Set (EuclideanSpace ℝ (Fin 2))) (p : EuclideanSpace ℝ (Fin 2))
    (hK : IsClosed K)
    (j : C(K, ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))))
    (hjNull : j.Nullhomotopic)
    (hjId : ∀ x, (j x : EuclideanSpace ℝ (Fin 2)) = x) :
    ∃ k : C({x : EuclideanSpace ℝ (Fin 2) // x ∈ U ∪ K},
        ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))),
      ∀ x : K, (k ⟨x, Or.inr x.property⟩ : EuclideanSpace ℝ (Fin 2)) = x := by
  -- Regard `K` as the closed subspace of the component union.
  let KInUnion : Set {x : EuclideanSpace ℝ (Fin 2) // x ∈ U ∪ K} :=
    {x | (x : EuclideanSpace ℝ (Fin 2)) ∈ K}
  have hKInUnionClosed : IsClosed KInUnion :=
    hK.preimage continuous_subtype_val
  have hToKContinuous : Continuous (fun x : KInUnion ↦
      (⟨(x : EuclideanSpace ℝ (Fin 2)), x.property⟩ : K)) := by
    fun_prop
  let toK : C(KInUnion, K) :=
    ⟨fun x ↦ ⟨x, x.property⟩, hToKContinuous⟩
  let jOnUnion : C(KInUnion, ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) :=
    j.comp toK
  have hjOnUnionNull : jOnUnion.Nullhomotopic := hjNull.comp_left toK
  obtain ⟨k, hk, -⟩ :=
    existsNullhomotopicExtensionIntoOpenEuclidean isOpen_compl_singleton
      hKInUnionClosed jOnUnion hjOnUnionNull
  refine ⟨k, ?_⟩
  intro x
  let xu : {y : EuclideanSpace ℝ (Fin 2) // y ∈ U ∪ K} :=
    ⟨x, Or.inr x.property⟩
  let xk : KInUnion := ⟨xu, x.property⟩
  have hkx : k xu = jOnUnion xk :=
    congrFun (congrArg DFunLike.coe hk) xk
  exact congrArg Subtype.val hkx |>.trans (hjId x)

/-- Helper for Theorem 9.0.1: a puncture-avoiding map on a component union
that fixes the closed boundary pastes with the ambient identity. -/
private lemma existsPunctureAvoidingMapEqOnCompl
    (K U : Set (EuclideanSpace ℝ (Fin 2))) (p : EuclideanSpace ℝ (Fin 2))
    (hpU : p ∈ U) (hUOpen : IsOpen U) (hUnionClosed : IsClosed (U ∪ K))
    (k : C({x : EuclideanSpace ℝ (Fin 2) // x ∈ U ∪ K},
      ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))))
    (hkId : ∀ x : K,
      (k ⟨x, Or.inr x.property⟩ : EuclideanSpace ℝ (Fin 2)) = x) :
    ∃ h : C(EuclideanSpace ℝ (Fin 2),
        ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))),
      Set.EqOn (fun x ↦ (h x : EuclideanSpace ℝ (Fin 2))) id Uᶜ := by
  classical
  -- Use the extension on `U ∪ K` and the identity off that closed set.
  let g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun x ↦
    if hx : x ∈ U ∪ K then k ⟨x, hx⟩ else x
  have hgUnion : ContinuousOn g (U ∪ K) := by
    rw [continuousOn_iff_continuous_restrict]
    have hRestrict : (U ∪ K).restrict g =
        fun x ↦ (k x : EuclideanSpace ℝ (Fin 2)) := by
      funext x
      exact dif_pos x.property
    rw [hRestrict]
    exact continuous_subtype_val.comp (map_continuous k)
  have hgComplEq : Set.EqOn g id Uᶜ := by
    intro x hx
    by_cases hxUnion : x ∈ U ∪ K
    · have hxK : x ∈ K := hxUnion.resolve_left hx
      have hgx : g x = (k ⟨x, hxUnion⟩ : EuclideanSpace ℝ (Fin 2)) :=
        dif_pos hxUnion
      rw [hgx]
      have hSubtype :
          (⟨x, hxUnion⟩ : {y : EuclideanSpace ℝ (Fin 2) // y ∈ U ∪ K}) =
            ⟨x, Or.inr hxK⟩ := Subtype.ext rfl
      rw [hSubtype]
      exact hkId ⟨x, hxK⟩
    · exact dif_neg hxUnion
  have hgCompl : ContinuousOn g Uᶜ := continuousOn_id.congr hgComplEq
  have hgContinuousOn : ContinuousOn g ((U ∪ K) ∪ Uᶜ) :=
    hgUnion.union_of_isClosed hgCompl hUnionClosed hUOpen.isClosed_compl
  have hCover : (U ∪ K) ∪ Uᶜ = Set.univ := by
    ext x
    by_cases hx : x ∈ U
    · simp [hx]
    · simp [hx]
  have hgContinuous : Continuous g := by
    rw [hCover] at hgContinuousOn
    exact continuousOn_univ.mp hgContinuousOn
  have hgAvoids : ∀ x, g x ∈ ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro x
    by_cases hxUnion : x ∈ U ∪ K
    · have hgx : g x = (k ⟨x, hxUnion⟩ : EuclideanSpace ℝ (Fin 2)) :=
        dif_pos hxUnion
      rw [hgx]
      exact (k ⟨x, hxUnion⟩).property
    · simp only [mem_compl_iff, mem_singleton_iff]
      intro hxp
      apply hxUnion
      have hgIdentity : g x = x := dif_neg hxUnion
      have hxp' : x = p := hgIdentity.symm.trans hxp
      exact Or.inl (hxp' ▸ hpU)
  have hContinuous : Continuous (fun x ↦
      (⟨g x, hgAvoids x⟩ : ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2))))) :=
    hgContinuous.subtype_mk _
  let h : C(EuclideanSpace ℝ (Fin 2),
      ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) :=
    ⟨fun x ↦ ⟨g x, hgAvoids x⟩, hContinuous⟩
  refine ⟨h, ?_⟩
  intro x hx
  exact hgComplEq hx

/-- Helper for Theorem 9.0.1: radial normalization of a puncture-avoiding map
fixing the unit circle gives a retraction of the closed unit disk. -/
private lemma punctureAvoidingMapFixedOnUnitSphereIsRetract
    (h : C(EuclideanSpace ℝ (Fin 2),
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))))
    (hFix : ∀ x, x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      (h x : EuclideanSpace ℝ (Fin 2)) = x) :
    Set.IsRetract (StandardSphere.boundary 1) := by
  -- Normalize the nonzero image of each point of the closed disk.
  have hNormalizeContinuous : Continuous (fun x : ClosedUnitBall 1 ↦
      NormedSpace.normalize (h x : EuclideanSpace ℝ (Fin 2))) := by
    unfold NormedSpace.normalize
    have hAmbientContinuous : Continuous (fun x : ClosedUnitBall 1 ↦
        (h x : EuclideanSpace ℝ (Fin 2))) :=
      continuous_subtype_val.comp (map_continuous h |>.comp continuous_subtype_val)
    have hNormContinuous : Continuous (fun x : ClosedUnitBall 1 ↦
        ‖(h x : EuclideanSpace ℝ (Fin 2))‖) :=
      continuous_norm.comp hAmbientContinuous
    have hNormNe : ∀ x : ClosedUnitBall 1,
        ‖(h x : EuclideanSpace ℝ (Fin 2))‖ ≠ 0 := by
      intro x hx
      exact (h x).property (norm_eq_zero.mp hx)
    exact (hNormContinuous.inv₀ hNormNe).smul hAmbientContinuous
  have hNormalizeNorm : ∀ x : ClosedUnitBall 1,
      ‖NormedSpace.normalize (h x : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    intro x
    apply NormedSpace.norm_normalize
    exact (h x).property
  have hNormalizeClosedBall : ∀ x : ClosedUnitBall 1,
      NormedSpace.normalize (h x : EuclideanSpace ℝ (Fin 2)) ∈
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro x
    rw [Metric.mem_closedBall, dist_zero_right, hNormalizeNorm]
  have hToClosedBallContinuous : Continuous (fun x : ClosedUnitBall 1 ↦
      (⟨NormedSpace.normalize (h x : EuclideanSpace ℝ (Fin 2)),
        hNormalizeClosedBall x⟩ : ClosedUnitBall 1)) :=
    hNormalizeContinuous.subtype_mk _
  have hNormalizeBoundary : ∀ x : ClosedUnitBall 1,
      (⟨NormedSpace.normalize (h x : EuclideanSpace ℝ (Fin 2)),
        hNormalizeClosedBall x⟩ : ClosedUnitBall 1) ∈ StandardSphere.boundary 1 := by
    intro x
    exact (StandardSphere.mem_boundary_iff_norm_eq 1 _).mpr (hNormalizeNorm x)
  have hRetractionContinuous : Continuous (fun x : ClosedUnitBall 1 ↦
      (⟨⟨NormedSpace.normalize (h x : EuclideanSpace ℝ (Fin 2)),
        hNormalizeClosedBall x⟩, hNormalizeBoundary x⟩ :
        StandardSphere.boundary 1)) :=
    hToClosedBallContinuous.subtype_mk _
  let r : C(ClosedUnitBall 1, StandardSphere.boundary 1) :=
    ⟨fun x ↦ ⟨⟨NormedSpace.normalize (h x : EuclideanSpace ℝ (Fin 2)),
      hNormalizeClosedBall x⟩, hNormalizeBoundary x⟩, hRetractionContinuous⟩
  rw [Set.isRetract_iff]
  refine ⟨r, ?_⟩
  -- On the boundary, both the map and radial normalization fix the point.
  rintro ⟨x, hxBoundary⟩
  have hxNorm := (StandardSphere.mem_boundary_iff_norm_eq 1 x).mp hxBoundary
  apply Subtype.ext
  apply Subtype.ext
  have hxSphere : (x : EuclideanSpace ℝ (Fin 2)) ∈ Metric.sphere 0 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using hxNorm
  simp only [r, ContinuousMap.coe_mk]
  rw [hFix x hxSphere]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one hxNorm

/-- Helper for Theorem 9.0.1: no puncture-avoiding planar map can agree with
the identity outside a bounded set containing its omitted point. -/
private lemma notExistsPunctureAvoidingMapEqOnComplBounded
    (p : EuclideanSpace ℝ (Fin 2)) (U : Set (EuclideanSpace ℝ (Fin 2)))
    (hU : Bornology.IsBounded U) :
    ¬ ∃ h : C(EuclideanSpace ℝ (Fin 2),
        ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))),
      Set.EqOn (fun x ↦ (h x : EuclideanSpace ℝ (Fin 2))) id Uᶜ := by
  rintro ⟨h, hEq⟩
  -- Translate the puncture to zero and dilate beyond the bounded support.
  obtain ⟨R, hRPositive, hUSubset⟩ := hU.subset_ball_lt 0 p
  have hRNe : R ≠ 0 := ne_of_gt hRPositive
  have hNormalizedAvoids : ∀ x : EuclideanSpace ℝ (Fin 2),
      R⁻¹ • ((h (p + R • x) : EuclideanSpace ℝ (Fin 2)) - p) ∈
        ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro x
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hx
    have hDifferenceZero :
        (h (p + R • x) : EuclideanSpace ℝ (Fin 2)) - p = 0 :=
      (smul_eq_zero.mp hx).resolve_left (inv_ne_zero hRNe)
    exact (h (p + R • x)).property (sub_eq_zero.mp hDifferenceZero)
  have hNormalizedContinuous : Continuous (fun x : EuclideanSpace ℝ (Fin 2) ↦
      (⟨R⁻¹ • ((h (p + R • x) : EuclideanSpace ℝ (Fin 2)) - p),
        hNormalizedAvoids x⟩ : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2))))) := by
    fun_prop
  let normalized : C(EuclideanSpace ℝ (Fin 2),
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) :=
    ⟨fun x ↦ ⟨R⁻¹ • ((h (p + R • x) : EuclideanSpace ℝ (Fin 2)) - p),
      hNormalizedAvoids x⟩, hNormalizedContinuous⟩
  have hNormalizedFix : ∀ x,
      x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      (normalized x : EuclideanSpace ℝ (Fin 2)) = x := by
    intro x hxSphere
    have hxNorm : ‖x‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using hxSphere
    have hAffineOutside : p + R • x ∈ Uᶜ := by
      rw [Set.mem_compl_iff]
      intro hxU
      have hxBall := hUSubset hxU
      rw [Metric.mem_ball, dist_eq_norm] at hxBall
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hRPositive, hxNorm, mul_one] at hxBall
      exact (lt_irrefl R) hxBall
    have hIdentity :
        (h (p + R • x) : EuclideanSpace ℝ (Fin 2)) = p + R • x :=
      hEq hAffineOutside
    simp only [normalized, ContinuousMap.coe_mk]
    rw [hIdentity, add_sub_cancel_left, ← mul_smul, inv_mul_cancel₀ hRNe, one_smul]
  exact closedUnitDiskBoundary_not_isRetract
    (punctureAvoidingMapFixedOnUnitSphereIsRetract normalized hNormalizedFix)

/-- Helper for Theorem 9.0.1: a nullhomotopic compact embedding in a
twice-punctured two-sphere cannot separate the two punctures. -/
private lemma borsukEmbeddingPointsSameComponent
    {A : Type*} [TopologicalSpace A] [CompactSpace A]
    (a b : StandardSphere 2)
    (f : C(A, ({a, b}ᶜ : Set (StandardSphere 2))))
    (hfInjective : Function.Injective f) (hfNullhomotopic : f.Nullhomotopic) :
    b ∈ connectedComponentIn
      (Set.range (fun x : A ↦ (f x : StandardSphere 2)))ᶜ a := by
  -- Coincident punctures require only membership in the image complement.
  by_cases hab : a = b
  · subst b
    apply mem_connectedComponentIn
    rintro ⟨x, hx⟩
    have hForbidden : (f x : StandardSphere 2) ∈
        ({a, a} : Set (StandardSphere 2)) := by
      simp [hx]
    exact (f x).2 hForbidden
  -- Assume the second puncture misses the first puncture's component.
  let K : Set (StandardSphere 2) :=
    Set.range (fun x : A ↦ (f x : StandardSphere 2))
  have hKCompact : IsCompact K :=
    isCompact_range (continuous_subtype_val.comp (map_continuous f))
  have haK : a ∉ K := by
    rintro ⟨x, hx⟩
    have hForbidden : (f x : StandardSphere 2) ∈
        ({a, b} : Set (StandardSphere 2)) := by
      simp [hx]
    exact (f x).2 hForbidden
  have hbK : b ∉ K := by
    rintro ⟨x, hx⟩
    have hForbidden : (f x : StandardSphere 2) ∈
        ({a, b} : Set (StandardSphere 2)) := by
      simp [hx]
    exact (f x).2 hForbidden
  let U : Set (StandardSphere 2) := connectedComponentIn Kᶜ a
  have hUComponent : IsConnectedComponentIn Kᶜ U :=
    IsConnectedComponentIn.of_mem haK
  by_contra hbU
  -- Stereographic projection at `b` turns `U` into a bounded plane component.
  let stereographic := puncturedSphereHomeomorphPlane b
  obtain ⟨hPlanarComponent, hPlanarBounded⟩ :=
    puncturedSphereComponentImageBounded K U b stereographic hKCompact hbK
      hUComponent hbU
  have haPunctured : a ∈ ({b}ᶜ : Set (StandardSphere 2)) := by
    simpa using hab
  let aInPunctured : ({b}ᶜ : Set (StandardSphere 2)) := ⟨a, haPunctured⟩
  let p : EuclideanSpace ℝ (Fin 2) := stereographic aInPunctured
  have hAvoidB : ∀ x : ({a, b}ᶜ : Set (StandardSphere 2)),
      (x : StandardSphere 2) ∈ ({b}ᶜ : Set (StandardSphere 2)) := by
    intro x
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hxb
    have hForbidden : (x : StandardSphere 2) ∈
        ({a, b} : Set (StandardSphere 2)) := by
      simp [hxb]
    exact x.property hForbidden
  have hToPuncturedContinuous : Continuous
      (fun x : ({a, b}ᶜ : Set (StandardSphere 2)) ↦
        (⟨x, hAvoidB x⟩ : ({b}ᶜ : Set (StandardSphere 2)))) := by
    fun_prop
  let toPunctured : C(({a, b}ᶜ : Set (StandardSphere 2)),
      ({b}ᶜ : Set (StandardSphere 2))) :=
    ⟨fun x ↦ ⟨x, hAvoidB x⟩, hToPuncturedContinuous⟩
  have hTransportAvoids : ∀ x : ({a, b}ᶜ : Set (StandardSphere 2)),
      stereographic (toPunctured x) ∈
        ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro x
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hx
    have hxSphere : (x : StandardSphere 2) = a :=
      congrArg Subtype.val (stereographic.injective hx)
    have hForbidden : (x : StandardSphere 2) ∈
        ({a, b} : Set (StandardSphere 2)) := by
      simp [hxSphere]
    exact x.property hForbidden
  have hTransportContinuous : Continuous
      (fun x : ({a, b}ᶜ : Set (StandardSphere 2)) ↦
        (⟨stereographic (toPunctured x), hTransportAvoids x⟩ :
          ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2))))) := by
    fun_prop
  let transport : C(({a, b}ᶜ : Set (StandardSphere 2)),
      ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) :=
    ⟨fun x ↦ ⟨stereographic (toPunctured x), hTransportAvoids x⟩,
      hTransportContinuous⟩
  let q : C(A, ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) := transport.comp f
  have hqInjective : Function.Injective q := by
    intro x y hxy
    apply hfInjective
    apply Subtype.ext
    have hAmbient : (q x : EuclideanSpace ℝ (Fin 2)) = q y :=
      congrArg
        (fun z : ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) ↦
          (z : EuclideanSpace ℝ (Fin 2))) hxy
    have hPunctured : toPunctured (f x) = toPunctured (f y) :=
      stereographic.injective hAmbient
    exact congrArg
      (fun z : ({b}ᶜ : Set (StandardSphere 2)) ↦ (z : StandardSphere 2)) hPunctured
  have hqNullhomotopic : q.Nullhomotopic :=
    hfNullhomotopic.comp_right transport
  let planarK : Set (EuclideanSpace ℝ (Fin 2)) :=
    Set.range (fun x : A ↦ (q x : EuclideanSpace ℝ (Fin 2)))
  let planarU : Set (EuclideanSpace ℝ (Fin 2)) :=
    stereographic '' (Subtype.val ⁻¹' U)
  have hPlanarRange : planarK = stereographic '' (Subtype.val ⁻¹' K) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨toPunctured (f x), ?_, ?_⟩
      · exact ⟨x, rfl⟩
      · rfl
    · rintro ⟨z, hzK, rfl⟩
      obtain ⟨x, hx⟩ := hzK
      refine ⟨x, ?_⟩
      simp only [q, transport, toPunctured, ContinuousMap.comp_apply,
        ContinuousMap.coe_mk]
      exact congrArg stereographic (Subtype.ext hx)
  have hPlanarComponent' : IsConnectedComponentIn planarKᶜ planarU := by
    rwa [hPlanarRange]
  have hPlanarBounded' : Bornology.IsBounded planarU := hPlanarBounded
  have hpPlanarU : p ∈ planarU := by
    refine ⟨aInPunctured, ?_, rfl⟩
    exact mem_connectedComponentIn haK
  have hPlanarKClosed : IsClosed planarK :=
    (isCompact_range
      (continuous_subtype_val.comp (map_continuous q))).isClosed
  have hPlanarUOpen : IsOpen planarU := by
    obtain ⟨x, hx⟩ := hPlanarComponent'.nonempty
    rw [hPlanarComponent'.eq_connectedComponentIn hx]
    exact hPlanarKClosed.isOpen_compl.connectedComponentIn
  -- Extend the range inclusion, paste it to the identity, and contradict no retraction.
  obtain ⟨j, hjId, hjNull⟩ :=
    existsNullhomotopicRangeInclusion
      ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) q hqInjective hqNullhomotopic
  obtain ⟨k, hkId⟩ :=
    existsNullhomotopicComponentUnionExtension planarK planarU p
      hPlanarKClosed j hjNull hjId
  obtain ⟨h, hEq⟩ :=
    existsPunctureAvoidingMapEqOnCompl planarK planarU p hpPlanarU hPlanarUOpen
      (isClosed_componentUnion planarK planarU hPlanarKClosed hPlanarComponent')
      k hkId
  exact notExistsPunctureAvoidingMapEqOnComplBounded p planarU hPlanarBounded'
    ⟨h, hEq⟩

/-- Helper for Theorem 9.0.1: every arc in the standard two-sphere has
preconnected complement and therefore does not separate the sphere. -/
private lemma sphereArc_not_separates
    (A : Set (StandardSphere 2)) [Topology.IsArc A] : ¬ A.Separates := by
  classical
  -- Compactness of an arc lets the Borsuk bridge apply to its inclusion.
  obtain ⟨arcHomeomorph⟩ := Topology.IsArc.homeomorphic_unitInterval (X := A)
  letI : CompactSpace A := arcHomeomorph.symm.compactSpace
  apply not_separates_of_pairwise_mem_connectedComponentIn A
  intro a ha b hb
  obtain ⟨inclusion, hInjective, hNullhomotopic, hRange⟩ :=
    arcInclusion_nullhomotopic A ha hb
  rw [← hRange]
  exact borsukEmbeddingPointsSameComponent a b inclusion hInjective hNullhomotopic

/-- Helper for Theorem 9.0.1: the two points in an intersection equal to
`{p, q}` belong to both sets. -/
private lemma pair_mem_of_inter_eq_pair
    {X : Type*} {C₁ C₂ : Set X} {p q : X} (hinter : C₁ ∩ C₂ = {p, q}) :
    p ∈ C₁ ∧ p ∈ C₂ ∧ q ∈ C₁ ∧ q ∈ C₂ := by
  -- Rewrite each endpoint through the stated intersection equation.
  have hp : p ∈ C₁ ∩ C₂ := by
    rw [hinter]
    simp
  have hq : q ∈ C₁ ∩ C₂ := by
    rw [hinter]
    simp
  exact ⟨hp.1, hp.2, hq.1, hq.2⟩

/-- Helper for Theorem 9.0.1: inside the twice-punctured space, the
complements of two sets meeting exactly at the punctures form a cover. -/
private lemma pairComplement_preimage_compl_union_eq_univ
    {X : Type*} (C₁ C₂ : Set X) (p q : X) (hinter : C₁ ∩ C₂ = {p, q}) :
    (Subtype.val ⁻¹' C₁ᶜ : Set ({p, q}ᶜ : Set X)) ∪
        Subtype.val ⁻¹' C₂ᶜ = Set.univ := by
  -- A point outside `{p, q}` cannot lie in both closed sets.
  ext x
  simp only [Set.mem_union, Set.mem_preimage, Set.mem_compl_iff, Set.mem_univ, iff_true]
  by_contra h
  push Not at h
  have hx : x.1 ∈ C₁ ∩ C₂ := ⟨h.1, h.2⟩
  rw [hinter] at hx
  exact x.2 hx

/-- Helper for Theorem 9.0.1: the overlap of the two complement preimages
is the preimage of the complement of the union. -/
private lemma pairComplement_preimage_compl_inter
    {X : Type*} (C₁ C₂ : Set X) (p q : X) :
    (Subtype.val ⁻¹' C₁ᶜ : Set ({p, q}ᶜ : Set X)) ∩
        Subtype.val ⁻¹' C₂ᶜ = Subtype.val ⁻¹' (C₁ ∪ C₂)ᶜ := by
  -- Both sides record the same pair of nonmembership conditions.
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_union,
    not_or]

/-- Helper for Theorem 9.0.1: forgetting the second puncture produces the
nested punctured-sphere point. -/
private def pairComplementToNestedPuncture (p q : StandardSphere 2) :
    ({p, q}ᶜ : Set (StandardSphere 2)) →
      {x : ({p}ᶜ : Set (StandardSphere 2)) // x.1 ≠ q} :=
  fun x ↦ ⟨⟨x.1, fun hp ↦ x.2 (Or.inl hp)⟩, fun hq ↦ x.2 (Or.inr hq)⟩

/-- Helper for Theorem 9.0.1: flattening a nested puncture produces a point
outside the two-point set. -/
private def nestedPunctureToPairComplement (p q : StandardSphere 2) :
    {x : ({p}ᶜ : Set (StandardSphere 2)) // x.1 ≠ q} →
      ({p, q}ᶜ : Set (StandardSphere 2)) :=
  fun x ↦ ⟨x.1.1, fun h ↦ h.elim x.1.2 x.2⟩

/-- Helper for Theorem 9.0.1: nesting a point outside two punctures is
continuous. -/
private lemma continuous_pairComplementToNestedPuncture (p q : StandardSphere 2) :
    Continuous (pairComplementToNestedPuncture p q) := by
  -- Build continuity through the two successive subtype constructors.
  have hinner : Continuous (fun x : ({p, q}ᶜ : Set (StandardSphere 2)) ↦
      (⟨x.1, fun hp ↦ x.2 (Or.inl hp)⟩ : ({p}ᶜ : Set (StandardSphere 2)))) :=
    continuous_subtype_val.subtype_mk
      (fun (x : ({p, q}ᶜ : Set (StandardSphere 2))) hp ↦ x.2 (Or.inl hp))
  exact hinner.subtype_mk (fun x hq ↦ x.2 (Or.inr hq))

/-- Helper for Theorem 9.0.1: flattening a nested puncture is continuous. -/
private lemma continuous_nestedPunctureToPairComplement (p q : StandardSphere 2) :
    Continuous (nestedPunctureToPairComplement p q) := by
  -- The ambient value is a composite of subtype projections.
  exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
    (fun x h ↦ h.elim x.1.2 x.2)

/-- Helper for Theorem 9.0.1: flattening after nesting fixes every point. -/
private lemma nestedPunctureToPairComplement_leftInverse (p q : StandardSphere 2) :
    Function.LeftInverse (nestedPunctureToPairComplement p q)
      (pairComplementToNestedPuncture p q) := by
  -- Subtype extensionality reduces the claim to the ambient point.
  intro x
  apply Subtype.ext
  rfl

/-- Helper for Theorem 9.0.1: nesting after flattening fixes every nested
puncture point. -/
private lemma nestedPunctureToPairComplement_rightInverse (p q : StandardSphere 2) :
    Function.RightInverse (nestedPunctureToPairComplement p q)
      (pairComplementToNestedPuncture p q) := by
  -- The underlying punctured-sphere point is unchanged.
  intro x
  apply Subtype.ext
  rfl

/-- Helper for Theorem 9.0.1: the complement of two sphere points is the
second-point complement inside the first puncture. -/
private def pairComplementHomeomorphNestedPuncture (p q : StandardSphere 2) :
    ({p, q}ᶜ : Set (StandardSphere 2)) ≃ₜ
      {x : ({p}ᶜ : Set (StandardSphere 2)) // x.1 ≠ q} :=
  { toFun := pairComplementToNestedPuncture p q
    invFun := nestedPunctureToPairComplement p q
    left_inv := nestedPunctureToPairComplement_leftInverse p q
    right_inv := nestedPunctureToPairComplement_rightInverse p q
    continuous_toFun := continuous_pairComplementToNestedPuncture p q
    continuous_invFun := continuous_nestedPunctureToPairComplement p q }

/-- Helper for Theorem 9.0.1: distinctness places the second point in the
complement of the first. -/
private lemma secondPoint_mem_firstPointComplement
    (p q : StandardSphere 2) (hpq : p ≠ q) : q ∈ ({p}ᶜ : Set (StandardSphere 2)) := by
  -- Singleton-complement membership is reversed inequality.
  simpa using hpq.symm

/-- Helper for Theorem 9.0.1: stereographic projection followed by canonical
Euclidean-complex coordinates identifies a punctured sphere with `ℂ`. -/
private noncomputable def puncturedSphereHomeomorphComplex (p : StandardSphere 2) :
    ({p}ᶜ : Set (StandardSphere 2)) ≃ₜ ℂ :=
  (puncturedSphereHomeomorphPlane p).trans
    Complex.orthonormalBasisOneI.repr.symm.toHomeomorph

/-- Helper for Theorem 9.0.1: translating stereographic coordinates sends
the second puncture to zero. -/
private noncomputable def translatedPuncturedSphereChart
    (p q : StandardSphere 2) (hpq : p ≠ q) :
    ({p}ᶜ : Set (StandardSphere 2)) ≃ₜ ℂ :=
  (puncturedSphereHomeomorphComplex p).trans
    (Homeomorph.subRight
      (puncturedSphereHomeomorphComplex p
        ⟨q, secondPoint_mem_firstPointComplement p q hpq⟩))

/-- Helper for Theorem 9.0.1: the translated chart is nonzero precisely
away from the second puncture. -/
private lemma translatedPuncturedSphereChart_ne_zero_iff
    (p q : StandardSphere 2) (hpq : p ≠ q)
    (x : ({p}ᶜ : Set (StandardSphere 2))) :
    x.1 ≠ q ↔ translatedPuncturedSphereChart p q hpq x ≠ 0 := by
  -- Translation turns nonvanishing into inequality with the image of `q`.
  simp only [translatedPuncturedSphereChart, Homeomorph.trans_apply,
    Homeomorph.subRight_apply, sub_ne_zero]
  rw [(puncturedSphereHomeomorphComplex p).injective.ne_iff]
  simpa using (Subtype.coe_ne_coe (a := x)
    (b := (⟨q, secondPoint_mem_firstPointComplement p q hpq⟩ :
      ({p}ᶜ : Set (StandardSphere 2)))))

/-- Helper for Theorem 9.0.1: stereographic projection and translation
identify the twice-punctured sphere with the punctured complex plane. -/
private noncomputable def twicePuncturedSphereHomeomorphPuncturedComplexPlane
    (p q : StandardSphere 2) (hpq : p ≠ q) :
    ({p, q}ᶜ : Set (StandardSphere 2)) ≃ₜ {z : ℂ // z ≠ 0} :=
  (pairComplementHomeomorphNestedPuncture p q).trans
    ((translatedPuncturedSphereChart p q hpq).subtype
      (translatedPuncturedSphereChart_ne_zero_iff p q hpq))

/-- Helper for Theorem 9.0.1: the standard complex exponential period is
nonzero. -/
private lemma complexExponentialPeriod_ne_zero :
    (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
  -- Each factor in the standard period is nonzero.
  norm_num [Real.pi_ne_zero, Complex.I_ne_zero]

/-- Helper for Theorem 9.0.1: integer multiples of the standard complex
exponential period define points of its deck subgroup. -/
private noncomputable def complexExponentialPeriodMultiple
    (k : ℤ) : AddSubgroup.zmultiples (2 * Real.pi * Complex.I) :=
  ⟨k • (2 * Real.pi * Complex.I), AddSubgroup.zsmul_mem_zmultiples _ k⟩

/-- Helper for Theorem 9.0.1: distinct integers give distinct multiples of
the standard complex exponential period. -/
private lemma complexExponentialPeriodMultiple_injective :
    Function.Injective complexExponentialPeriodMultiple := by
  -- Cancel the nonzero period after comparing ambient complex values.
  intro k l hkl
  apply smul_left_injective ℤ complexExponentialPeriod_ne_zero
  exact congrArg Subtype.val hkl

/-- Helper for Theorem 9.0.1: the standard exponential deck subgroup is
infinite. -/
private instance complexExponentialDeckGroupInfinite :
    Infinite (AddSubgroup.zmultiples (2 * Real.pi * Complex.I)) :=
  Infinite.of_injective complexExponentialPeriodMultiple
    complexExponentialPeriodMultiple_injective

/-- Helper for Theorem 9.0.1: the standard period generates its entire deck
subgroup. -/
private lemma complexExponentialPeriodGenerator_spans :
    AddSubgroup.zmultiples
      (⟨2 * Real.pi * Complex.I, AddSubgroup.mem_zmultiples _⟩ :
        AddSubgroup.zmultiples (2 * Real.pi * Complex.I)) = ⊤ := by
  -- Every deck transformation is, by definition, an integer period multiple.
  apply top_unique
  intro x _
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp x.property
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, Subtype.ext hk⟩

/-- Helper for Theorem 9.0.1: the deck group of the complex exponential
cover is multiplicatively equivalent to `Multiplicative ℤ`. -/
private noncomputable def complexExponentialDeckGroupEquivInt :
    Multiplicative (AddSubgroup.zmultiples (2 * Real.pi * Complex.I)) ≃*
      Multiplicative ℤ :=
  (AddEquiv.toMultiplicative
    (intEquivOfZMultiplesEqTop
      ⟨2 * Real.pi * Complex.I, AddSubgroup.mem_zmultiples _⟩
      complexExponentialPeriodGenerator_spans)).symm

/-- Helper for Theorem 9.0.1: the punctured complex plane has infinite-cyclic
fundamental group at every basepoint. -/
private lemma fundamentalGroup_puncturedComplexPlane_equiv_int
    (z : {z : ℂ // z ≠ 0}) :
    Nonempty (FundamentalGroup {z : ℂ // z ≠ 0} z ≃* Multiplicative ℤ) := by
  -- Choose the logarithm as a point of the exponential fiber over `z`.
  let exponential : ℂ → {z : ℂ // z ≠ 0} :=
    fun w ↦ ⟨Complex.exp w, Complex.exp_ne_zero w⟩
  have hlog : exponential (Complex.log z) = z := by
    apply Subtype.ext
    exact Complex.exp_log z.2
  let fiberPoint : exponential ⁻¹' {z} := ⟨Complex.log z, hlog⟩
  let deckOppositeEquiv :
      (Multiplicative (AddSubgroup.zmultiples (2 * Real.pi * Complex.I)))ᵐᵒᵖ ≃*
        Multiplicative ℤ :=
    (MulOpposite.opMulEquiv.symm).trans complexExponentialDeckGroupEquivInt
  -- The simply connected total space identifies the base fundamental group
  -- with the deck group, and the preceding equivalence removes the opposite.
  exact ⟨(Complex.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv fiberPoint).trans
    deckOppositeEquiv⟩

/-- Helper for Theorem 9.0.1: the fundamental-group maps induced by a
homeomorphism and its inverse compose to the identity on the source. -/
private lemma homeomorphFundamentalGroupMap_leftInverse
    {X : Type u} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) (p : FundamentalGroup X x) :
    FundamentalGroup.mapOfEq (e.symm : C(Y, X)) (e.symm_apply_apply x)
      (FundamentalGroup.map (e : C(X, Y)) x p) = p := by
  -- Combine the two quotient maps and compare a representative path pointwise.
  rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply]
  induction p using Quotient.ind
  case _ γ =>
    apply Quotient.sound
    suffices hpath : (fun path ↦ path.cast (e.symm_apply_apply x).symm
        (e.symm_apply_apply x).symm)
        ((fun path ↦ path.map e.symm.continuous)
          ((fun path ↦ path.map e.continuous) γ)) = γ by
      rw [hpath]
    ext t
    exact e.symm_apply_apply (γ t)

/-- Helper for Theorem 9.0.1: the fundamental-group maps induced by an
inverse homeomorphism and the original map compose to the target identity. -/
private lemma homeomorphFundamentalGroupMap_rightInverse
    {X : Type u} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) (p : FundamentalGroup Y (e x)) :
    FundamentalGroup.map (e : C(X, Y)) x
      (FundamentalGroup.mapOfEq (e.symm : C(Y, X))
        (e.symm_apply_apply x) p) = p := by
  -- Push the forward map through the endpoint cast, then compare representatives.
  rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply,
    Path.Homotopic.Quotient.map_cast]
  induction p using Quotient.ind
  case _ γ =>
    apply Quotient.sound
    suffices hpath : (fun path ↦ path.cast
        (congrArg e (e.symm_apply_apply x).symm)
        (congrArg e (e.symm_apply_apply x).symm))
        ((fun path ↦ path.map e.continuous)
          ((fun path ↦ path.map e.symm.continuous) γ)) = γ by
      rw [hpath]
    ext t
    exact e.apply_symm_apply (γ t)

/-- Helper for Theorem 9.0.1: a homeomorphism induces a multiplicative
equivalence of fundamental groups at corresponding basepoints. -/
private noncomputable def fundamentalGroupMulEquivOfHomeomorph
    {X : Type u} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) :=
  let forward : FundamentalGroup X x →* FundamentalGroup Y (e x) :=
    FundamentalGroup.map (e : C(X, Y)) x
  let inverse : FundamentalGroup Y (e x) →* FundamentalGroup X x :=
    FundamentalGroup.mapOfEq (e.symm : C(Y, X)) (e.symm_apply_apply x)
  MulEquiv.mk'
    { toFun := forward
      invFun := inverse
      left_inv := homeomorphFundamentalGroupMap_leftInverse e x
      right_inv := homeomorphFundamentalGroupMap_rightInverse e x }
    forward.map_mul

/-- Helper for Theorem 9.0.1: the twice-punctured sphere has infinite-cyclic
fundamental group at every basepoint. -/
private lemma fundamentalGroup_twicePuncturedSphere_equiv_int
    (p q : StandardSphere 2) (hpq : p ≠ q)
    (x : ({p, q}ᶜ : Set (StandardSphere 2))) :
    Nonempty (FundamentalGroup ({p, q}ᶜ : Set (StandardSphere 2)) x ≃*
      Multiplicative ℤ) := by
  -- Transport the punctured-plane calculation through the normalized chart.
  let e := twicePuncturedSphereHomeomorphPuncturedComplexPlane p q hpq
  exact ⟨(fundamentalGroupMulEquivOfHomeomorph e x).trans
    (fundamentalGroup_puncturedComplexPlane_equiv_int (e x)).some⟩

/-- Helper for Theorem 9.0.1: a nonseparating closed complement remains
path-joinable after restriction to a sphere with two points removed. -/
private lemma joinedIn_preimage_compl_pairComplement
    (D : Set (StandardSphere 2)) (hDclosed : IsClosed D)
    (p q : StandardSphere 2) (hp : p ∈ D) (hq : q ∈ D)
    (hDnonseparating : ¬ D.Separates)
    (a b : ({p, q}ᶜ : Set (StandardSphere 2)))
    (ha : a.1 ∈ Dᶜ) (hb : b.1 ∈ Dᶜ) :
    JoinedIn (Subtype.val ⁻¹' Dᶜ) a b := by
  -- Use the chart centered at `p` to upgrade connectedness to path connectedness.
  have hDcompl_subset_puncture : Dᶜ ⊆ ({p}ᶜ : Set (StandardSphere 2)) := by
    intro x hxD hxp
    exact hxD (hxp ▸ hp)
  let chart := puncturedSphereHomeomorphPlane p
  let chartDomain : Set ({p}ᶜ : Set (StandardSphere 2)) := Subtype.val ⁻¹' Dᶜ
  have hchartDomain_image : ((fun x ↦ x.1) '' chartDomain) = Dᶜ := by
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hDcompl_subset_puncture]
  have hchartDomain_open : IsOpen chartDomain :=
    hDclosed.isOpen_compl.preimage continuous_subtype_val
  have hchartDomain_nonempty : chartDomain.Nonempty :=
    ⟨⟨a.1, hDcompl_subset_puncture ha⟩, ha⟩
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
  have hab_punctured : JoinedIn chartDomain
      (⟨a.1, hDcompl_subset_puncture ha⟩ : ({p}ᶜ : Set (StandardSphere 2)))
      (⟨b.1, hDcompl_subset_puncture hb⟩ : ({p}ᶜ : Set (StandardSphere 2))) :=
    hchartDomain_pathConnected.joinedIn _ ha _ hb
  have hab_sphere : JoinedIn Dᶜ a.1 b.1 := by
    have himage := hab_punctured.map continuous_subtype_val
    rw [hchartDomain_image] at himage
    exact himage
  -- Lift the sphere path back into the twice-punctured subtype.
  have hpair_subset : Dᶜ ⊆ ({p, q}ᶜ : Set (StandardSphere 2)) := by
    intro x hxD hxpair
    rcases hxpair with hxp | hxq
    · exact hxD (hxp ▸ hp)
    · exact hxD (hxq ▸ hq)
  have hpair_image :
      ((fun x ↦ x.1) '' (Subtype.val ⁻¹' Dᶜ :
        Set ({p, q}ᶜ : Set (StandardSphere 2)))) = Dᶜ := by
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hpair_subset]
  apply (Topology.IsInducing.subtypeVal.joinedIn_image
    (F := Subtype.val ⁻¹' Dᶜ) ha hb).mp
  rwa [hpair_image]

/-- Helper for Theorem 9.0.1: separation and an upper bound of two
complementary components force exactly two complementary components. -/
private lemma separatesInto_two_of_separates_of_components_le_two
    {X : Type*} [TopologicalSpace X] (A : Set X) (hsep : A.Separates)
    (hle : Cardinal.mk (ConnectedComponents (Aᶜ : Set X)) ≤ 2) :
    A.SeparatesInto 2 := by
  -- Separation excludes the only smaller finite cardinal possibilities.
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

/-- Helper for Theorem 9.0.1: a spherical arc is a closed connected subset
of the standard two-sphere. -/
private lemma isClosed_and_isConnected_of_isArc
    (A : Set (StandardSphere 2)) [Topology.IsArc A] :
    IsClosed A ∧ IsConnected A := by
  -- Transport compactness and connectedness from the unit interval model.
  classical
  obtain ⟨e⟩ := Topology.IsArc.homeomorphic_unitInterval (X := A)
  letI : CompactSpace A := e.symm.compactSpace
  letI : ConnectedSpace A :=
    e.symm.surjective.connectedSpace e.symm.continuous
  have hcompact : IsCompact A := isCompact_iff_compactSpace.mpr inferInstance
  exact ⟨hcompact.isClosed, isConnected_iff_connectedSpace.mpr inferInstance⟩

/-- Helper for Theorem 9.0.1: an arc contains a point distinct from any
prescribed pair of its points. -/
private lemma exists_mem_arc_ne_pair
    (A : Set (StandardSphere 2)) [Topology.IsArc A]
    (p q : StandardSphere 2) (hp : p ∈ A) (hq : q ∈ A) :
    ∃ r ∈ A, r ≠ p ∧ r ≠ q := by
  classical
  -- Transfer infinitude from the unit interval and avoid the two selected
  -- subtype points.
  obtain ⟨e⟩ := Topology.IsArc.homeomorphic_unitInterval (X := A)
  letI : Infinite unitInterval := Set.Icc.infinite (by norm_num)
  letI : Infinite A := e.toEquiv.infinite_iff.mpr inferInstance
  let pA : A := ⟨p, hp⟩
  let qA : A := ⟨q, hq⟩
  obtain ⟨r, hr⟩ := Infinite.exists_notMem_finset ({pA, qA} : Finset A)
  refine ⟨r, r.2, ?_, ?_⟩
  · intro hrp
    apply hr
    exact Finset.mem_insert.mpr (Or.inl (Subtype.ext hrp))
  · intro hrq
    apply hr
    exact Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton.mpr (Subtype.ext hrq)))

/-- Helper for Theorem 9.0.1: a set cut out inside a larger subtype is
homeomorphic to the same set viewed in the ambient space. -/
private def nestedSubtypeHomeomorph
    {X : Type*} [TopologicalSpace X] (P S : Set X) (hSP : S ⊆ P) :
    (Subtype.val ⁻¹' S : Set P) ≃ₜ S :=
  { toFun := fun x ↦ ⟨x.1.1, x.2⟩
    invFun := fun x ↦ ⟨⟨x.1, hSP x.2⟩, x.2⟩
    left_inv := fun x ↦ by simp only [Subtype.coe_eta]
    right_inv := fun x ↦ by simp only [Subtype.coe_eta]
    continuous_toFun :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk fun x ↦ x.2
    continuous_invFun :=
      (continuous_subtype_val.subtype_mk fun x ↦ hSP x.2).subtype_mk fun x ↦ x.2 }

/-- Helper for Theorem 9.0.1: deleting a point preserves connectedness when
the point has a connected punctured neighborhood inside the connected set. -/
private lemma isConnectedSdiffSingletonOfConnectedPuncturedNhds
    {X : Type*} [TopologicalSpace X] [T1Space X] {U W : Set X} {b : X}
    (hU : IsConnected U) (hbU : b ∈ U) (hW : W ∈ nhds b) (hWU : W ⊆ U)
    (hWconn : IsConnected (W \ {b})) : IsConnected (U \ {b}) := by
  -- The punctured neighborhood supplies nonemptiness after deletion.
  have hpunctureSubset : W \ {b} ⊆ U \ {b} :=
    sdiff_subset_sdiff hWU (Subset.refl _)
  refine ⟨hWconn.nonempty.mono hpunctureSubset, ?_⟩
  intro A B hA hB hcover hAn hBn
  by_contra hmeet
  have hWcover : W \ {b} ⊆ A ∪ B := hpunctureSubset.trans hcover
  have hWside : W \ {b} ⊆ A ∨ W \ {b} ⊆ B := by
    by_cases hWA : ((W \ {b}) ∩ A).Nonempty
    · by_cases hWB : ((W \ {b}) ∩ B).Nonempty
      · obtain ⟨x, hxW, hxAB⟩ :=
          hWconn.isPreconnected A B hA hB hWcover hWA hWB
        exact False.elim (hmeet ⟨x, hpunctureSubset hxW, hxAB.1, hxAB.2⟩)
      · have hsubsetA : W \ {b} ⊆ A := by
          intro x hxW
          rcases hWcover hxW with hxA | hxB
          · exact hxA
          · exact False.elim (hWB ⟨x, hxW, hxB⟩)
        exact Or.inl hsubsetA
    · have hsubsetB : W \ {b} ⊆ B := by
        intro x hxW
        rcases hWcover hxW with hxA | hxB
        · exact False.elim (hWA ⟨x, hxW, hxA⟩)
        · exact hxB
      exact Or.inr hsubsetB
  obtain ⟨V, hVW, hVopen, hbV⟩ := mem_nhds_iff.mp hW
  rcases hWside with hWA | hWB
  · -- Add a neighborhood of `b` to the `A` side and delete `b` from `B`.
    have hUcover : U ⊆ (A ∪ V) ∪ (B \ {b}) := by
      intro x hxU
      by_cases hxb : x = b
      · exact Or.inl (Or.inr (hxb ▸ hbV))
      · rcases hcover ⟨hxU, hxb⟩ with hxA | hxB
        · exact Or.inl (Or.inl hxA)
        · exact Or.inr ⟨hxB, hxb⟩
    have hleft : (U ∩ (A ∪ V)).Nonempty :=
      ⟨b, hbU, Or.inr hbV⟩
    have hright : (U ∩ (B \ {b})).Nonempty := by
      obtain ⟨x, hxU, hxB⟩ := hBn
      exact ⟨x, hxU.1, hxB, hxU.2⟩
    obtain ⟨x, hxU, hxLeft, hxRight⟩ := hU.isPreconnected
      (A ∪ V) (B \ {b}) (hA.union hVopen) (hB.sdiff isClosed_singleton)
      hUcover hleft hright
    rcases hxLeft with hxA | hxV
    · exact hmeet ⟨x, ⟨hxU, hxRight.2⟩, hxA, hxRight.1⟩
    · exact hmeet ⟨x, ⟨hxU, hxRight.2⟩,
        hWA ⟨hVW hxV, hxRight.2⟩, hxRight.1⟩
  · -- The symmetric separation gives the same contradiction.
    have hUcover : U ⊆ (B ∪ V) ∪ (A \ {b}) := by
      intro x hxU
      by_cases hxb : x = b
      · exact Or.inl (Or.inr (hxb ▸ hbV))
      · rcases hcover ⟨hxU, hxb⟩ with hxA | hxB
        · exact Or.inr ⟨hxA, hxb⟩
        · exact Or.inl (Or.inl hxB)
    have hleft : (U ∩ (B ∪ V)).Nonempty :=
      ⟨b, hbU, Or.inr hbV⟩
    have hright : (U ∩ (A \ {b})).Nonempty := by
      obtain ⟨x, hxU, hxA⟩ := hAn
      exact ⟨x, hxU.1, hxA, hxU.2⟩
    obtain ⟨x, hxU, hxLeft, hxRight⟩ := hU.isPreconnected
      (B ∪ V) (A \ {b}) (hB.union hVopen) (hA.sdiff isClosed_singleton)
      hUcover hleft hright
    rcases hxLeft with hxB | hxV
    · exact hmeet ⟨x, ⟨hxU, hxRight.2⟩, hxRight.1, hxB⟩
    · exact hmeet ⟨x, ⟨hxU, hxRight.2⟩, hxRight.1,
        hWB ⟨hVW hxV, hxRight.2⟩⟩

/-- Helper for Theorem 9.0.1: every point of an open subset of the standard
two-sphere has a connected punctured neighborhood inside that subset. -/
private lemma existsConnectedPuncturedNhdsStandardSphere
    {U : Set (StandardSphere 2)} {b : StandardSphere 2}
    (hU : IsOpen U) (hbU : b ∈ U) :
    ∃ W ∈ nhds b, W ⊆ U ∧ IsConnected (W \ {b}) := by
  -- Pull a small Euclidean ball back through a manifold chart at `b`.
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) b b
  have hchartNhds : chartAt (EuclideanSpace ℝ (Fin 2)) b ''
      (U ∩ (chartAt (EuclideanSpace ℝ (Fin 2)) b).source) ∈ nhds c := by
    apply (chartAt (EuclideanSpace ℝ (Fin 2)) b).image_mem_nhds
      (mem_chart_source (EuclideanSpace ℝ (Fin 2)) b)
    exact Filter.inter_mem (hU.mem_nhds hbU)
      (chart_source_mem_nhds (EuclideanSpace ℝ (Fin 2)) b)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hchartNhds
  let e := (OpenPartialHomeomorph.univBall c r).trans
    (chartAt (EuclideanSpace ℝ (Fin 2)) b).symm
  let W := e '' Set.univ
  have hesource : e.source = Set.univ := by
    ext x
    simp only [e, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.univBall_source, mem_inter_iff, mem_univ, true_and,
      mem_preimage]
    have hxsource : x ∈ (OpenPartialHomeomorph.univBall c r).source := by
      simp
    have hxball : OpenPartialHomeomorph.univBall c r x ∈ Metric.ball c r := by
      rw [← OpenPartialHomeomorph.univBall_target c hr]
      exact (OpenPartialHomeomorph.univBall c r).map_source hxsource
    let z := (hrsub hxball).choose
    have hz := (hrsub hxball).choose_spec
    rw [← hz.2]
    exact iff_true_intro
      ((chartAt (EuclideanSpace ℝ (Fin 2)) b).map_source hz.1.2)
  have hezero : e 0 = b := by
    simp only [e, OpenPartialHomeomorph.trans_apply,
      OpenPartialHomeomorph.univBall_apply_zero, c]
    exact (chartAt (EuclideanSpace ℝ (Fin 2)) b).left_inv
      (mem_chart_source (EuclideanSpace ℝ (Fin 2)) b)
  have hWnhds : W ∈ nhds b := by
    rw [← hezero]
    exact e.image_mem_nhds (hesource ▸ Set.mem_univ 0) Filter.univ_mem
  have hWU : W ⊆ U := by
    rintro y ⟨x, -, hxy⟩
    have hxsource : x ∈ (OpenPartialHomeomorph.univBall c r).source := by
      simp
    have hxball : OpenPartialHomeomorph.univBall c r x ∈ Metric.ball c r := by
      rw [← OpenPartialHomeomorph.univBall_target c hr]
      exact (OpenPartialHomeomorph.univBall c r).map_source hxsource
    let z := (hrsub hxball).choose
    have hz := (hrsub hxball).choose_spec
    have hzEq : e x = z := by
      calc
        e x = (chartAt (EuclideanSpace ℝ (Fin 2)) b).symm
            (OpenPartialHomeomorph.univBall c r x) := rfl
        _ = (chartAt (EuclideanSpace ℝ (Fin 2)) b).symm
            (chartAt (EuclideanSpace ℝ (Fin 2)) b z) := congrArg _ hz.2.symm
        _ = z := (chartAt (EuclideanSpace ℝ (Fin 2)) b).left_inv hz.1.2
    rw [← hxy, hzEq]
    exact hz.1.1
  have hpuncture : W \ {b} = e '' (Set.univ \ {0}) := by
    change (e '' Set.univ) \ {b} = e '' (Set.univ \ {0})
    rw [Set.image_sdiff]
    · rw [image_singleton, hezero]
    · intro x y hxy
      apply e.injOn (hesource ▸ Set.mem_univ x) (hesource ▸ Set.mem_univ y) hxy
  have hplanePuncture : IsConnected
      ((Set.univ : Set (EuclideanSpace ℝ (Fin 2))) \ {0}) := by
    have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
      rw [← Module.finrank_eq_rank]
      norm_num
    have hset : (Set.univ : Set (EuclideanSpace ℝ (Fin 2))) \ {0} = ({0}ᶜ) := by
      ext x
      simp only [mem_sdiff, mem_univ, true_and, mem_singleton_iff, mem_compl_iff]
    rw [hset]
    exact isConnected_compl_singleton_of_one_lt_rank hrank
      (0 : EuclideanSpace ℝ (Fin 2))
  have hWconn : IsConnected (W \ {b}) := by
    rw [hpuncture]
    exact hplanePuncture.image e
      (e.continuousOn.mono fun x _ ↦ hesource ▸ Set.mem_univ x)
  exact ⟨W, hWnhds, hWU, hWconn⟩

/-- Helper for Theorem 9.0.1: an open connected subset of the standard
two-sphere stays connected after restriction to a punctured sphere. -/
private lemma isConnectedPreimageOpenConnectedStandardSphere
    {U : Set (StandardSphere 2)} {b : StandardSphere 2}
    (hUopen : IsOpen U) (hU : IsConnected U) :
    IsConnected (Subtype.val ⁻¹' U : Set ({b}ᶜ : Set (StandardSphere 2))) := by
  by_cases hbU : b ∈ U
  · obtain ⟨W, hWnhds, hWU, hWconn⟩ :=
      existsConnectedPuncturedNhdsStandardSphere hUopen hbU
    have hpunctured : IsConnected (U \ {b}) :=
      isConnectedSdiffSingletonOfConnectedPuncturedNhds
        hU hbU hWnhds hWU hWconn
    have hpreimage : (Subtype.val ⁻¹' U : Set ({b}ᶜ : Set (StandardSphere 2))) =
        Subtype.val ⁻¹' (U \ {b}) := by
      ext x
      constructor
      · intro hx
        exact ⟨hx, x.property⟩
      · exact fun hx ↦ hx.1
    rw [hpreimage]
    apply hpunctured.preimage_of_isOpenMap Subtype.val_injective
      isOpen_compl_singleton.isOpenMap_subtype_val
    intro x hx
    exact ⟨⟨x, hx.2⟩, rfl⟩
  · apply hU.preimage_of_isOpenMap Subtype.val_injective
      isOpen_compl_singleton.isOpenMap_subtype_val
    intro x hx
    have hxb : x ∈ ({b}ᶜ : Set (StandardSphere 2)) := by
      intro hxb
      exact hbU (hxb ▸ hx)
    exact ⟨⟨x, hxb⟩, rfl⟩

/-- Helper for Theorem 9.0.1: puncturing a spherical complementary component
and applying a plane chart preserves its connected-component status. -/
private lemma puncturedSphereComponentImage_isConnectedComponent
    (C U : Set (StandardSphere 2)) (b : StandardSphere 2)
    (h : ({b}ᶜ : Set (StandardSphere 2)) ≃ₜ EuclideanSpace ℝ (Fin 2))
    (hC : IsCompact C) (hU : IsConnectedComponentIn Cᶜ U) :
    IsConnectedComponentIn (h '' (Subtype.val ⁻¹' C))ᶜ
      (h '' (Subtype.val ⁻¹' U)) := by
  -- The punctured component remains connected; maximality is checked after
  -- mapping any larger punctured component back to the sphere.
  letI : LocallyPathConnectedSpace (StandardSphere 2) :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin 2)) (StandardSphere 2)
  have hCopen : IsOpen Cᶜ := hC.isClosed.isOpen_compl
  have hUopen : IsOpen U := by
    obtain ⟨x, hxU⟩ := hU.nonempty
    rw [hU.eq_connectedComponentIn hxU]
    exact hCopen.connectedComponentIn
  have hPconnected : IsConnected
      (Subtype.val ⁻¹' U : Set ({b}ᶜ : Set (StandardSphere 2))) :=
    isConnectedPreimageOpenConnectedStandardSphere hUopen hU.isConnected
  obtain ⟨x, hxP⟩ := hPconnected.nonempty
  have hxC : x ∈ Subtype.val ⁻¹' Cᶜ := hU.subset hxP
  have hPeq : (Subtype.val ⁻¹' U : Set ({b}ᶜ : Set (StandardSphere 2))) =
      connectedComponentIn (Subtype.val ⁻¹' Cᶜ) x := by
    apply Set.Subset.antisymm
    · exact hPconnected.isPreconnected.subset_connectedComponentIn hxP
        (preimage_mono hU.subset)
    · intro y hy
      have hImageConnected : IsPreconnected
          (Subtype.val '' connectedComponentIn (Subtype.val ⁻¹' Cᶜ) x) :=
        isPreconnected_connectedComponentIn.image Subtype.val
          continuous_subtype_val.continuousOn
      have hImageSubset : Subtype.val '' connectedComponentIn
          (Subtype.val ⁻¹' Cᶜ) x ⊆ Cᶜ := by
        rintro z ⟨w, hw, rfl⟩
        exact connectedComponentIn_subset (Subtype.val ⁻¹' Cᶜ) x hw
      have hImageInU : Subtype.val '' connectedComponentIn
          (Subtype.val ⁻¹' Cᶜ) x ⊆ U := by
        rw [hU.eq_connectedComponentIn hxP]
        exact hImageConnected.subset_connectedComponentIn
          (mem_image_of_mem Subtype.val (mem_connectedComponentIn hxC)) hImageSubset
      exact hImageInU ⟨y, hy, rfl⟩
  have hImageEq : h '' (Subtype.val ⁻¹' U) =
      connectedComponentIn (h '' (Subtype.val ⁻¹' Cᶜ)) (h x) := by
    rw [hPeq]
    exact h.image_connectedComponentIn hxC
  rw [imagePreimageComplEqComplImage C b h] at hImageEq
  rw [hImageEq]
  apply IsConnectedComponentIn.of_mem
  rw [← imagePreimageComplEqComplImage C b h]
  exact mem_image_of_mem h hxC

/-- Helper for Theorem 9.0.1: the plane-chart image of the punctured
component containing the chart point has compact complement. -/
private lemma puncturedSphereComponentImage_compl_isCompact
    (C U : Set (StandardSphere 2)) (b : StandardSphere 2)
    (h : ({b}ᶜ : Set (StandardSphere 2)) ≃ₜ EuclideanSpace ℝ (Fin 2))
    (hC : IsCompact C) (hU : IsConnectedComponentIn Cᶜ U) (hbU : b ∈ U) :
    IsCompact ((h '' (Subtype.val ⁻¹' U))ᶜ) := by
  -- The complement of the open spherical component is compact and avoids the
  -- puncture, so its chart image is compact.
  letI : LocallyPathConnectedSpace (StandardSphere 2) :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin 2)) (StandardSphere 2)
  have hCopen : IsOpen Cᶜ := hC.isClosed.isOpen_compl
  have hUopen : IsOpen U := by
    obtain ⟨x, hxU⟩ := hU.nonempty
    rw [hU.eq_connectedComponentIn hxU]
    exact hCopen.connectedComponentIn
  have hcompactCompl : IsCompact Uᶜ := hUopen.isClosed_compl.isCompact
  have hcomplSubset : Uᶜ ⊆ ({b}ᶜ : Set (StandardSphere 2)) := by
    intro x hx
    simp only [mem_compl_iff, mem_singleton_iff] at hx ⊢
    intro hxb
    exact hx (hxb ▸ hbU)
  have hcompactPreimage : IsCompact
      (Subtype.val ⁻¹' Uᶜ : Set ({b}ᶜ : Set (StandardSphere 2))) := by
    rw [Topology.IsEmbedding.isCompact_iff Topology.IsEmbedding.subtypeVal]
    simpa [Subtype.image_preimage_coe, inter_eq_right.mpr hcomplSubset] using
      hcompactCompl
  have hcompactImage : IsCompact (h '' (Subtype.val ⁻¹' Uᶜ)) :=
    hcompactPreimage.image h.continuous
  have hcomplement : h '' (Subtype.val ⁻¹' Uᶜ) =
      (h '' (Subtype.val ⁻¹' U))ᶜ :=
    imagePreimageComplEqComplImage U b h
  rwa [hcomplement] at hcompactImage

/-- Helper for Theorem 9.0.1: a subset of a nontrivial normed real vector
space with bounded complement is unbounded. -/
private lemma not_isBounded_of_isBounded_compl
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    {S : Set E} (hSc : Bornology.IsBounded Sᶜ) : ¬ Bornology.IsBounded S := by
  -- Boundedness of both complementary pieces would make the whole vector
  -- space bounded.
  intro hS
  have huniv : Bornology.IsBounded (Set.univ : Set E) := by
    rw [← union_compl_self S]
    exact hS.union hSc
  exact NormedSpace.unbounded_univ ℝ E huniv

/-- Helper for Theorem 9.0.1: the chart image of every point of the spherical
component containing the puncture lies in the canonical unbounded planar
component. -/
private lemma puncturedSphereComponentAtUnbounded
    (C U : Set (StandardSphere 2)) (b : StandardSphere 2)
    (h : ({b}ᶜ : Set (StandardSphere 2)) ≃ₜ EuclideanSpace ℝ (Fin 2))
    (hC : IsCompact C) (hU : IsConnectedComponentIn Cᶜ U) (hbU : b ∈ U)
    (x : ({b}ᶜ : Set (StandardSphere 2))) (hxU : x.1 ∈ U) :
    ¬ Bornology.IsBounded
      (connectedComponentIn (h '' (Subtype.val ⁻¹' C))ᶜ (h x)) := by
  have hcomponent :=
    puncturedSphereComponentImage_isConnectedComponent C U b h hC hU
  have hunbounded : ¬ Bornology.IsBounded (h '' (Subtype.val ⁻¹' U)) :=
    not_isBounded_of_isBounded_compl
      (puncturedSphereComponentImage_compl_isCompact C U b h hC hU hbU).isBounded
  -- Component uniqueness normalizes the unbounded set at the chosen point.
  have hxImage : h x ∈ h '' (Subtype.val ⁻¹' U) := ⟨x, hxU, rfl⟩
  rw [← hcomponent.eq_connectedComponentIn hxImage]
  exact hunbounded

/-- Helper for Theorem 9.0.1: a compact map into a distinctly twice-punctured
sphere is nullhomotopic when the two punctures lie in one component of the
complement of its ambient range. -/
private lemma compactMapIntoDistinctPairComplement_nullhomotopic
    {Z : Type u} [TopologicalSpace Z] [CompactSpace Z]
    (p q : StandardSphere 2) (hpq : p ≠ q)
    (f : C(Z, ({p, q}ᶜ : Set (StandardSphere 2))))
    (hpqComponent : q ∈ connectedComponentIn
      (Set.range (fun z : Z ↦ (f z : StandardSphere 2)))ᶜ p) :
    f.Nullhomotopic := by
  -- Use the chart punctured at `q`; the component containing both punctures
  -- becomes the unbounded component required by the planar nullhomotopy.
  have hfAvoidsPair (z : Z) :
      (f z : StandardSphere 2) ≠ p ∧ (f z : StandardSphere 2) ≠ q := by
    simpa only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] using
      (f z).property
  let C : Set (StandardSphere 2) :=
    Set.range (fun z : Z ↦ (f z : StandardSphere 2))
  have hC : IsCompact C := by
    apply isCompact_range
    fun_prop
  have hpC : p ∈ Cᶜ := by
    rintro ⟨z, hz⟩
    exact (hfAvoidsPair z).1 hz
  let U : Set (StandardSphere 2) := connectedComponentIn Cᶜ p
  have hU : IsConnectedComponentIn Cᶜ U :=
    IsConnectedComponentIn.of_mem hpC
  have hpU : p ∈ U := mem_connectedComponentIn hpC
  have hqU : q ∈ U := hpqComponent
  let h := puncturedSphereHomeomorphPlane q
  have hpPuncture : p ∈ ({q}ᶜ : Set (StandardSphere 2)) := by
    simpa only [mem_compl_iff, mem_singleton_iff] using hpq
  let pp : ({q}ᶜ : Set (StandardSphere 2)) := ⟨p, hpPuncture⟩
  let origin : EuclideanSpace ℝ (Fin 2) := h pp
  have hfAvoidsQ (z : Z) : (f z : StandardSphere 2) ∈
      ({q}ᶜ : Set (StandardSphere 2)) := by
    simpa only [mem_compl_iff, mem_singleton_iff] using (hfAvoidsPair z).2
  let fq : C(Z, ({q}ᶜ : Set (StandardSphere 2))) :=
    ⟨fun z ↦ ⟨(f z : StandardSphere 2), hfAvoidsQ z⟩,
      continuous_subtype_val.comp f.continuous |>.subtype_mk _⟩
  have hgAvoids (z : Z) : h (fq z) ∈
      ({origin}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro hz
    simp only [mem_singleton_iff] at hz
    have hfqEq : fq z = pp := h.injective hz
    exact (hfAvoidsPair z).1 (congrArg Subtype.val hfqEq)
  let g : C(Z, ({origin}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) :=
    ⟨fun z ↦ ⟨h (fq z), hgAvoids z⟩,
      (h.continuous.comp fq.continuous).subtype_mk _⟩
  have hgRange : Set.range
      (fun z : Z ↦ (g z : EuclideanSpace ℝ (Fin 2))) =
      h '' (Subtype.val ⁻¹' C) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨fq z, ⟨z, rfl⟩, rfl⟩
    · rintro ⟨z, hzC, rfl⟩
      obtain ⟨w, hw⟩ := hzC
      refine ⟨w, ?_⟩
      apply congrArg h
      exact Subtype.ext hw
  have hplanarUnbounded : ¬ Bornology.IsBounded
      (connectedComponentIn
        (Set.range (fun z : Z ↦ (g z : EuclideanSpace ℝ (Fin 2))))ᶜ origin) := by
    rw [hgRange]
    exact puncturedSphereComponentAtUnbounded C U q h hC hU hqU pp hpU
  have hgNull : g.Nullhomotopic :=
    Theorem901.nullhomotopicIntoPuncturedNormedSpaceOfUnboundedComponent
      origin g hplanarUnbounded
  -- Map the planar puncture complement back to the sphere and recover `f`.
  have htransportAvoids
      (y : ({origin}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) :
      (h.symm y.1).1 ∈ ({p, q}ᶜ : Set (StandardSphere 2)) := by
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    constructor
    · intro hpy
      have hpreimageEq : h.symm y.1 = pp := by
        apply Subtype.ext
        exact hpy
      have hyOrigin : y.1 = origin := by
        calc
          y.1 = h (h.symm y.1) := (h.apply_symm_apply y.1).symm
          _ = h pp := congrArg h hpreimageEq
          _ = origin := rfl
      exact y.property (by simpa only [mem_singleton_iff] using hyOrigin)
    · simpa only [mem_compl_iff, mem_singleton_iff] using (h.symm y.1).property
  let transport : C(({origin}ᶜ : Set (EuclideanSpace ℝ (Fin 2))),
      ({p, q}ᶜ : Set (StandardSphere 2))) :=
    ⟨fun y ↦ ⟨(h.symm y.1).1, htransportAvoids y⟩,
      (continuous_subtype_val.comp
        (h.symm.continuous.comp continuous_subtype_val)).subtype_mk _⟩
  have htransportComp : transport.comp g = f := by
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    have hrecover := congrArg Subtype.val (h.symm_apply_apply (fq z))
    calc
      ((transport.comp g) z : StandardSphere 2) =
          (h.symm (h (fq z))).1 := rfl
      _ = (fq z).1 := hrecover
      _ = (f z : StandardSphere 2) := rfl
  have htransportedNull : (transport.comp g).Nullhomotopic :=
    hgNull.comp_right transport
  rwa [htransportComp] at htransportedNull

/-- Helper for Theorem 9.0.1: a constant continuous map induces the trivial
fundamental-group homomorphism. -/
private lemma fundamentalGroupMap_const_eq_one
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) :
    FundamentalGroup.map (ContinuousMap.const X y) x = 1 := by
  -- Reduce each loop class to a representative; its constant image is the
  -- constant loop.
  ext p
  induction p using Path.Homotopic.Quotient.ind with
  | mk path =>
      rw [FundamentalGroup.map_apply, MonoidHom.one_apply,
        FundamentalGroup.one_def, ← Path.Homotopic.Quotient.mk_map]
      congr 1

open CategoryTheory in
/-- Helper for Theorem 9.0.1: homotopic maps induce fundamental-group maps
related by basepoint change along the basepoint trace. -/
private lemma fundamentalGroupMap_eq_basepointChange_comp_of_homotopy
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : f.Homotopy g) (x : X) :
    FundamentalGroup.map g x =
      (FundamentalGroup.fundamentalGroupMulEquivOfPath (H.evalAt x)).toMonoidHom.comp
        (FundamentalGroup.map f x) := by
  -- Naturality of the fundamental-groupoid map moves each loop across the
  -- path traced by the source basepoint.
  ext p
  let alpha : FundamentalGroupoid.mk (f x) ⟶ FundamentalGroupoid.mk (g x) :=
    ⟦H.evalAt x⟧
  have naturality : (FundamentalGroup.map f x) p ≫ alpha =
      alpha ≫ (FundamentalGroup.map g x) p :=
    (FundamentalGroupoidFunctor.homotopicMapsNatIso H).naturality p
  have hloop : (FundamentalGroup.map g x) p =
      Groupoid.inv alpha ≫ (FundamentalGroup.map f x) p ≫ alpha := by
    calc
      (FundamentalGroup.map g x) p =
          Groupoid.inv alpha ≫ alpha ≫ (FundamentalGroup.map g x) p := by simp
      _ = Groupoid.inv alpha ≫ ((FundamentalGroup.map f x) p ≫ alpha) := by
        rw [naturality]
  exact hloop.trans rfl

/-- Helper for Theorem 9.0.1: every nullhomotopic map induces the trivial
fundamental-group homomorphism at every source basepoint. -/
private lemma fundamentalGroupMap_eq_one_of_nullhomotopic
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (hf : f.Nullhomotopic) :
    FundamentalGroup.map f x = 1 := by
  obtain ⟨y, ⟨H⟩⟩ := hf
  have hconst := fundamentalGroupMap_const_eq_one x y
  have hnatural :=
    fundamentalGroupMap_eq_basepointChange_comp_of_homotopy H x
  let e := FundamentalGroup.fundamentalGroupMulEquivOfPath (H.evalAt x)
  -- The basepoint-change equivalence is injective, so triviality of the
  -- constant map forces triviality of the original map.
  ext p
  have hp := congrArg (fun F ↦ F p) hnatural
  rw [hconst, MonoidHom.one_apply, MonoidHom.comp_apply] at hp
  apply e.injective
  calc
    e ((FundamentalGroup.map f x) p) = 1 := hp.symm
    _ = e 1 := e.map_one.symm

/-- Helper for Theorem 9.0.1: the standard unit interval traverses the unit
additive circle once continuously. -/
private lemma continuous_unitAddCircleLoop :
    Continuous (fun t : unitInterval ↦ ((t : ℝ) : UnitAddCircle)) := by
  -- Compose the interval inclusion with the additive-circle quotient map.
  exact continuous_quotient_mk'.comp continuous_subtype_val

/-- Helper for Theorem 9.0.1: the once-around additive-circle path starts at
the additive identity. -/
private lemma unitAddCircleLoop_source : (((0 : unitInterval) : ℝ) : UnitAddCircle) = 0 := by
  simp

/-- Helper for Theorem 9.0.1: one real period returns the once-around
additive-circle path to the additive identity. -/
private lemma unitAddCircleLoop_target : (((1 : unitInterval) : ℝ) : UnitAddCircle) = 0 := by
  simpa only [Set.Icc.coe_one] using (AddCircle.coe_period (1 : ℝ))

/-- Helper for Theorem 9.0.1: the canonical based loop traversing
`UnitAddCircle` once. -/
private def unitAddCircleLoop : Path (0 : UnitAddCircle) 0 :=
  { toFun := fun t ↦ ((t : ℝ) : UnitAddCircle)
    continuous_toFun := continuous_unitAddCircleLoop
    source' := unitAddCircleLoop_source
    target' := unitAddCircleLoop_target }

/-- Helper for Theorem 9.0.1: an endpoint-compatible loop descends
continuously from the interval to `UnitAddCircle`. -/
private lemma continuous_loopToUnitAddCircleMap
    {X : Type*} [TopologicalSpace X] {x : X} (gamma : Path x x) :
    Continuous (AddCircle.liftIco 1 0
      (gamma.toContinuousMap.comp ContinuousMap.projIccCM)) := by
  apply AddCircle.liftIco_zero_continuous
  · simp [ContinuousMap.projIccCM, Set.projIcc, gamma.source, gamma.target]
  · exact (gamma.toContinuousMap.comp ContinuousMap.projIccCM).continuous.continuousOn

/-- Helper for Theorem 9.0.1: the continuous map on `UnitAddCircle`
obtained by identifying the endpoints of a loop. -/
private noncomputable def loopToUnitAddCircleMap
    {X : Type*} [TopologicalSpace X] {x : X} (gamma : Path x x) :
    C(UnitAddCircle, X) :=
  ⟨AddCircle.liftIco 1 0
      (gamma.toContinuousMap.comp ContinuousMap.projIccCM),
    continuous_loopToUnitAddCircleMap gamma⟩

/-- Helper for Theorem 9.0.1: the descended loop is definitionally the
half-open interval quotient lift. -/
private lemma loopToUnitAddCircleMap_apply
    {X : Type*} [TopologicalSpace X] {x : X} (gamma : Path x x)
    (z : UnitAddCircle) :
    loopToUnitAddCircleMap gamma z =
      AddCircle.liftIco 1 0
        (gamma.toContinuousMap.comp ContinuousMap.projIccCM) z := by
  rfl

/-- Helper for Theorem 9.0.1: away from the identified upper endpoint, the
descended loop agrees with its interval representative. -/
private lemma loopToUnitAddCircleMap_coe_apply
    {X : Type*} [TopologicalSpace X] {x : X} (gamma : Path x x)
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    loopToUnitAddCircleMap gamma (t : UnitAddCircle) =
      gamma ⟨t, ht.1, ht.2.le⟩ := by
  rw [loopToUnitAddCircleMap_apply,
    AddCircle.liftIco_zero_coe_apply ht]
  exact ContinuousMap.IccExtendCM_of_mem ⟨ht.1, ht.2.le⟩

/-- Helper for Theorem 9.0.1: the descended loop takes the additive-circle
basepoint to the original loop basepoint. -/
private lemma loopToUnitAddCircleMap_apply_zero
    {X : Type*} [TopologicalSpace X] {x : X} (gamma : Path x x) :
    loopToUnitAddCircleMap gamma (0 : UnitAddCircle) = x := by
  calc
    loopToUnitAddCircleMap gamma (0 : UnitAddCircle) = gamma (0 : unitInterval) :=
      loopToUnitAddCircleMap_coe_apply gamma ⟨le_rfl, zero_lt_one⟩
    _ = x := gamma.source

/-- Helper for Theorem 9.0.1: pulling the descended map back along the
once-around additive-circle loop recovers the original loop. -/
private lemma unitAddCircleLoop_map_loopToUnitAddCircleMap
    {X : Type*} [TopologicalSpace X] {x : X} (gamma : Path x x) :
    (unitAddCircleLoop.map (loopToUnitAddCircleMap gamma).continuous).cast
      (loopToUnitAddCircleMap_apply_zero gamma).symm
      (loopToUnitAddCircleMap_apply_zero gamma).symm = gamma := by
  ext t
  rw [Path.cast_coe]
  by_cases ht : (t : ℝ) < 1
  · exact loopToUnitAddCircleMap_coe_apply gamma ⟨t.2.1, ht⟩
  · have htOne : t = 1 := by
      apply Subtype.ext
      exact le_antisymm t.2.2 (not_lt.mp ht)
    subst t
    calc
      loopToUnitAddCircleMap gamma (((1 : unitInterval) : ℝ) : UnitAddCircle) =
          loopToUnitAddCircleMap gamma (0 : UnitAddCircle) := by
            rw [unitAddCircleLoop_target]
      _ = gamma (0 : unitInterval) := by
        exact loopToUnitAddCircleMap_coe_apply gamma ⟨le_rfl, zero_lt_one⟩
      _ = gamma (1 : unitInterval) := gamma.source.trans gamma.target.symm

/-- Helper for Theorem 9.0.1: inclusion of the complement of a connected
set containing both punctures induces the trivial fundamental-group map into
the twice-punctured sphere. -/
private lemma fundamentalGroupMap_pairComplementInclusion_eq_one
    (A : Set (StandardSphere 2)) (hAconnected : IsConnected A)
    (p q : StandardSphere 2) (hp : p ∈ A) (hq : q ∈ A) (hpq : p ≠ q)
    (x : (Subtype.val ⁻¹' Aᶜ : Set ({p, q}ᶜ : Set (StandardSphere 2)))) :
    FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C((Subtype.val ⁻¹' Aᶜ : Set ({p, q}ᶜ : Set (StandardSphere 2))),
          ({p, q}ᶜ : Set (StandardSphere 2)))) x = 1 := by
  let inclusion : C((Subtype.val ⁻¹' Aᶜ :
      Set ({p, q}ᶜ : Set (StandardSphere 2))),
      ({p, q}ᶜ : Set (StandardSphere 2))) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  -- It suffices to nullhomotope the compact circle map associated to each
  -- representative loop.
  apply MonoidHom.ext
  intro z
  rw [MonoidHom.one_apply]
  induction z using Path.Homotopic.Quotient.ind with
  | mk gamma =>
      let descended := loopToUnitAddCircleMap gamma
      let circleMap : C(UnitAddCircle,
          ({p, q}ᶜ : Set (StandardSphere 2))) := inclusion.comp descended
      have hAsubset : A ⊆
          (Set.range (fun t : UnitAddCircle ↦
            (circleMap t : StandardSphere 2)))ᶜ := by
        rintro y hy ⟨t, rfl⟩
        exact (descended t).2 hy
      have hpComplement : p ∈
          (Set.range (fun t : UnitAddCircle ↦
            (circleMap t : StandardSphere 2)))ᶜ := hAsubset hp
      have hqComponent : q ∈ connectedComponentIn
          (Set.range (fun t : UnitAddCircle ↦
            (circleMap t : StandardSphere 2)))ᶜ p :=
        hAconnected.isPreconnected.subset_connectedComponentIn
          hp hAsubset hq
      have hcircleNull : circleMap.Nullhomotopic :=
        compactMapIntoDistinctPairComplement_nullhomotopic
          p q hpq circleMap hqComponent
      have hcircleMap :=
        fundamentalGroupMap_eq_one_of_nullhomotopic
          circleMap (0 : UnitAddCircle) hcircleNull
      have hclass := congrArg
        (fun F ↦ F (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk unitAddCircleLoop))) hcircleMap
      rw [FundamentalGroup.map_apply, MonoidHom.one_apply,
        FundamentalGroup.one_def, ← Path.Homotopic.Quotient.mk_map] at hclass
      have hbase : circleMap (0 : UnitAddCircle) = inclusion x := by
        exact congrArg inclusion (loopToUnitAddCircleMap_apply_zero gamma)
      have hpath : (unitAddCircleLoop.map circleMap.continuous).cast
          hbase.symm hbase.symm = gamma.map inclusion.continuous := by
        apply DFunLike.ext _ _
        intro t
        rw [Path.cast_coe]
        have hrecover := DFunLike.congr_fun
          (unitAddCircleLoop_map_loopToUnitAddCircleMap gamma) t
        exact congrArg inclusion hrecover
      rw [FundamentalGroup.map_apply, FundamentalGroup.one_def,
        ← Path.Homotopic.Quotient.mk_map]
      calc
        Path.Homotopic.Quotient.mk (gamma.map inclusion.continuous) =
            Path.Homotopic.Quotient.mk
              ((unitAddCircleLoop.map circleMap.continuous).cast
                hbase.symm hbase.symm) := congrArg _ hpath.symm
        _ = (Path.Homotopic.Quotient.mk
              (unitAddCircleLoop.map circleMap.continuous)).cast
                hbase.symm hbase.symm :=
              Path.Homotopic.Quotient.mk_cast _ _ _
        _ = (Path.Homotopic.Quotient.refl (circleMap 0)).cast
              hbase.symm hbase.symm := congrArg
                (fun z : Path.Homotopic.Quotient (circleMap 0) (circleMap 0) ↦
                  z.cast hbase.symm hbase.symm) hclass
        _ = Path.Homotopic.Quotient.refl (inclusion x) := by
          rw [← Path.Homotopic.Quotient.mk_refl,
            ← Path.Homotopic.Quotient.mk_cast]
          congr 1
          apply DFunLike.ext _ _
          intro t
          rw [Path.cast_coe]
          exact hbase


/-- Helper for Theorem 9.0.1: induced fundamental-group maps respect
composition of continuous maps. -/
private lemma fundamentalGroupMap_comp_eq
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (x : X) :
    FundamentalGroup.map (g.comp f) x =
      (FundamentalGroup.map g (f x)).comp (FundamentalGroup.map f x) := by
  -- Compare the two homomorphisms on a representative loop and compose its
  -- two quotient-level images.
  ext loop
  simp only [FundamentalGroup.map_apply]
  exact Path.Homotopic.Quotient.map_comp

/-- Helper for Theorem 9.0.1: two spherical arcs meeting exactly at two
distinct endpoints have a separating union. -/
private lemma sphereArcPair_union_separates
    (A₁ A₂ : Set (StandardSphere 2)) [Topology.IsArc A₁] [Topology.IsArc A₂]
    (p q : StandardSphere 2) (hpq : p ≠ q) (hinter : A₁ ∩ A₂ = {p, q}) :
    (A₁ ∪ A₂).Separates := by
  classical
  -- Route correction: specializing the former closed-connected helper to arcs
  -- makes both members of the punctured-sphere cover path connected, so the
  -- logarithmic lifts can be normalized and glued directly.
  rw [Set.separates_iff]
  intro hpreconnected
  have hA₁geometry := isClosed_and_isConnected_of_isArc A₁
  have hA₂geometry := isClosed_and_isConnected_of_isArc A₂
  have hpqMem := pair_mem_of_inter_eq_pair hinter
  let P : Set (StandardSphere 2) := {p, q}ᶜ
  let U : Set P := Subtype.val ⁻¹' A₁ᶜ
  let V : Set P := Subtype.val ⁻¹' A₂ᶜ
  let W : Set (StandardSphere 2) := (A₁ ∪ A₂)ᶜ
  have hUopen : IsOpen U :=
    hA₁geometry.1.isOpen_compl.preimage continuous_subtype_val
  have hVopen : IsOpen V :=
    hA₂geometry.1.isOpen_compl.preimage continuous_subtype_val
  have hcover : U ∪ V = Set.univ :=
    pairComplement_preimage_compl_union_eq_univ A₁ A₂ p q hinter
  have hWinter : U ∩ V = Subtype.val ⁻¹' W :=
    pairComplement_preimage_compl_inter A₁ A₂ p q
  have hWsubset : W ⊆ P := by
    intro x hxW hxPair
    rcases hxPair with hxp | hxq
    · exact hxW (Or.inl (hxp ▸ hpqMem.1))
    · exact hxW (Or.inl (hxq ▸ hpqMem.2.2.1))
  let overlapHomeomorph : (U ∩ V : Set P) ≃ₜ W :=
    (Homeomorph.setCongr hWinter).trans (nestedSubtypeHomeomorph P W hWsubset)
  let chart := twicePuncturedSphereHomeomorphPuncturedComplexPlane p q hpq
  let chartMap : C(P, {z : ℂ // z ≠ 0}) := chart
  let exponential : C(ℂ, {z : ℂ // z ≠ 0}) :=
    ⟨fun z ↦ ⟨Complex.exp z, Complex.exp_ne_zero z⟩,
      Complex.continuous_exp.subtype_mk _⟩
  -- Each arc supplies a point on the opposite side of the cover, so
  -- connectedness of the twice-punctured sphere forces a nonempty overlap.
  have hUcompl : Uᶜ.Nonempty := by
    obtain ⟨r, hrA₁, hrp, hrq⟩ :=
      exists_mem_arc_ne_pair A₁ p q hpqMem.1 hpqMem.2.2.1
    let rP : P := ⟨r, by simpa only [P, mem_compl_iff, mem_insert_iff,
      mem_singleton_iff, not_or] using ⟨hrp, hrq⟩⟩
    refine ⟨rP, ?_⟩
    simpa only [U, mem_compl_iff, mem_preimage, not_not] using hrA₁
  have hVcompl : Vᶜ.Nonempty := by
    obtain ⟨r, hrA₂, hrp, hrq⟩ :=
      exists_mem_arc_ne_pair A₂ p q hpqMem.2.1 hpqMem.2.2.2
    let rP : P := ⟨r, by simpa only [P, mem_compl_iff, mem_insert_iff,
      mem_singleton_iff, not_or] using ⟨hrp, hrq⟩⟩
    refine ⟨rP, ?_⟩
    simpa only [V, mem_compl_iff, mem_preimage, not_not] using hrA₂
  letI : PathConnectedSpace {z : ℂ // z ≠ 0} :=
    (show Function.Surjective exponential from fun z ↦
      ⟨Complex.log z, Subtype.ext (Complex.exp_log z.2)⟩).pathConnectedSpace
        exponential.continuous
  letI : PathConnectedSpace P :=
    chart.symm.surjective.pathConnectedSpace chart.symm.continuous
  have hoverlap : (U ∩ V).Nonempty := by
    by_contra hempty
    have hdisjoint : Disjoint U V := Set.disjoint_iff_inter_eq_empty.mpr
      (Set.not_nonempty_iff_eq_empty.mp hempty)
    obtain hPU | hPV := isPreconnected_univ.subset_or_subset
      hUopen hVopen hdisjoint (by rw [hcover])
    · obtain ⟨x, hx⟩ := hUcompl
      exact hx (hPU (mem_univ x))
    · obtain ⟨x, hx⟩ := hVcompl
      exact hx (hPV (mem_univ x))
  obtain ⟨x₀, hx₀⟩ := hoverlap
  let xOverlap : (U ∩ V : Set P) := ⟨x₀, hx₀⟩
  let overlapToU : C((U ∩ V : Set P), U) :=
    ⟨fun x ↦ ⟨x.1, x.2.1⟩, continuous_subtype_val.subtype_mk _⟩
  let overlapToV : C((U ∩ V : Set P), V) :=
    ⟨fun x ↦ ⟨x.1, x.2.2⟩, continuous_subtype_val.subtype_mk _⟩
  let xU : U := overlapToU xOverlap
  let xV : V := overlapToV xOverlap
  let inclusionU : C(U, P) := ⟨Subtype.val, continuous_subtype_val⟩
  let inclusionV : C(V, P) := ⟨Subtype.val, continuous_subtype_val⟩
  let chartU : C(U, {z : ℂ // z ≠ 0}) := chartMap.comp inclusionU
  let chartV : C(V, {z : ℂ // z ≠ 0}) := chartMap.comp inclusionV
  let z₀ : ℂ := Complex.log (chartMap x₀)
  have hexponentialU : exponential z₀ = chartU xU := by
    apply Subtype.ext
    exact Complex.exp_log (chartMap x₀).2
  have hexponentialV : exponential z₀ = chartV xV := by
    apply Subtype.ext
    exact Complex.exp_log (chartMap x₀).2
  -- Openness gives local path connectedness, while arc nonseparation joins
  -- every pair of points in each cover member.
  letI : LocallyPathConnectedSpace (StandardSphere 2) :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin 2)) (StandardSphere 2)
  have hPopen : IsOpen P := by
    dsimp only [P]
    exact ((Set.finite_singleton q).insert p).isClosed.isOpen_compl
  letI : LocallyPathConnectedSpace P := hPopen.locallyPathConnectedSpace
  letI : LocallyPathConnectedSpace U := hUopen.locallyPathConnectedSpace
  letI : LocallyPathConnectedSpace V := hVopen.locallyPathConnectedSpace
  letI : PathConnectedSpace U :=
    { nonempty := ⟨xU⟩
      joined := fun a b ↦ by
        simpa only [Subtype.coe_eta] using
          (joinedIn_preimage_compl_pairComplement A₁ hA₁geometry.1 p q
            hpqMem.1 hpqMem.2.2.1 (sphereArc_not_separates A₁)
            a.1 b.1 a.2 b.2).joined_subtype }
  letI : PathConnectedSpace V :=
    { nonempty := ⟨xV⟩
      joined := fun a b ↦ by
        simpa only [Subtype.coe_eta] using
          (joinedIn_preimage_compl_pairComplement A₂ hA₂geometry.1 p q
            hpqMem.2.1 hpqMem.2.2.2 (sphereArc_not_separates A₂)
            a.1 b.1 a.2 b.2).joined_subtype }
  -- The compact-circle argument above makes each inclusion-induced map
  -- trivial; functoriality transfers that fact to the two chart restrictions.
  have hinclusionU : FundamentalGroup.map inclusionU xU = 1 :=
    fundamentalGroupMap_pairComplementInclusion_eq_one A₁ hA₁geometry.2
      p q hpqMem.1 hpqMem.2.2.1 hpq xU
  have hinclusionV : FundamentalGroup.map inclusionV xV = 1 :=
    fundamentalGroupMap_pairComplementInclusion_eq_one A₂ hA₂geometry.2
      p q hpqMem.2.1 hpqMem.2.2.2 hpq xV
  have hchartUmap : FundamentalGroup.map chartU xU = 1 := by
    calc
      FundamentalGroup.map chartU xU =
          (FundamentalGroup.map chartMap (inclusionU xU)).comp
            (FundamentalGroup.map inclusionU xU) :=
        fundamentalGroupMap_comp_eq inclusionU chartMap xU
      _ = (FundamentalGroup.map chartMap (inclusionU xU)).comp 1 :=
        congrArg ((FundamentalGroup.map chartMap (inclusionU xU)).comp ·)
          hinclusionU
      _ = 1 := by ext z; simp
  have hchartVmap : FundamentalGroup.map chartV xV = 1 := by
    calc
      FundamentalGroup.map chartV xV =
          (FundamentalGroup.map chartMap (inclusionV xV)).comp
            (FundamentalGroup.map inclusionV xV) :=
        fundamentalGroupMap_comp_eq inclusionV chartMap xV
      _ = (FundamentalGroup.map chartMap (inclusionV xV)).comp 1 :=
        congrArg ((FundamentalGroup.map chartMap (inclusionV xV)).comp ·)
          hinclusionV
      _ = 1 := by ext z; simp
  have hUrange : (FundamentalGroup.map chartU xU).range ≤
      (FundamentalGroup.mapOfEq exponential hexponentialU).range := by
    rintro z ⟨w, rfl⟩
    rw [hchartUmap, MonoidHom.one_apply]
    exact Subgroup.one_mem _
  have hVrange : (FundamentalGroup.map chartV xV).range ≤
      (FundamentalGroup.mapOfEq exponential hexponentialV).range := by
    rintro z ⟨w, rfl⟩
    rw [hchartVmap, MonoidHom.one_apply]
    exact Subgroup.one_mem _
  obtain ⟨liftU, hliftU, -⟩ :=
    Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts_of_range_le
      hexponentialU hUrange
  obtain ⟨liftV, hliftV, -⟩ :=
    Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts_of_range_le
      hexponentialV hVrange
  -- The assumed preconnected complement identifies the two normalized lifts
  -- on the overlap by uniqueness for the exponential covering.
  letI : PreconnectedSpace W := by simpa only [W] using hpreconnected
  letI : PreconnectedSpace (U ∩ V : Set P) :=
    overlapHomeomorph.symm.surjective.denseRange.preconnectedSpace
      overlapHomeomorph.symm.continuous
  let liftUOverlap : C((U ∩ V : Set P), ℂ) := liftU.comp overlapToU
  let liftVOverlap : C((U ∩ V : Set P), ℂ) := liftV.comp overlapToV
  have hoverlapProjection : exponential ∘ liftUOverlap =
      exponential ∘ liftVOverlap := by
    funext x
    calc
      exponential (liftUOverlap x) = chartU (overlapToU x) :=
        congrFun hliftU.2 (overlapToU x)
      _ = chartMap x.1 := rfl
      _ = chartV (overlapToV x) := rfl
      _ = exponential (liftVOverlap x) :=
        (congrFun hliftV.2 (overlapToV x)).symm
  have hoverlapBase : liftUOverlap xOverlap = liftVOverlap xOverlap :=
    hliftU.1.trans hliftV.1.symm
  have hliftOverlapEq : (liftUOverlap : (U ∩ V : Set P) → ℂ) = liftVOverlap :=
    Complex.isCoveringMap_exp.eq_of_comp_eq liftUOverlap.continuous
      liftVOverlap.continuous hoverlapProjection xOverlap hoverlapBase
  have hcompatible (x : (U ∩ V : Set P)) :
      liftU ⟨x.1, x.2.1⟩ = liftV ⟨x.1, x.2.2⟩ :=
    congrFun hliftOverlapEq x
  let globalLift : C(P, ℂ) :=
    ContinuousMap.pasteOpen hUopen hVopen hcover liftU liftV hcompatible
  -- Pasting preserves both local projection equations, so the chart factors
  -- globally through the contractible complex plane.
  have hglobalProjection : exponential.comp globalLift = chartMap := by
    apply ContinuousMap.ext
    intro x
    have hx : x ∈ U ∨ x ∈ V := by
      rw [← mem_union, hcover]
      exact mem_univ x
    rcases hx with hxU | hxV
    · let xu : U := ⟨x, hxU⟩
      have hpaste := DFunLike.congr_fun
        (ContinuousMap.pasteOpen_restrict_left
          hUopen hVopen hcover liftU liftV hcompatible) xu
      calc
        exponential (globalLift x) = exponential (liftU xu) :=
          congrArg exponential hpaste
        _ = chartU xu := congrFun hliftU.2 xu
        _ = chartMap x := rfl
    · let xv : V := ⟨x, hxV⟩
      have hpaste := DFunLike.congr_fun
        (ContinuousMap.pasteOpen_restrict_right
          hUopen hVopen hcover liftU liftV hcompatible) xv
      calc
        exponential (globalLift x) = exponential (liftV xv) :=
          congrArg exponential hpaste
        _ = chartV xv := congrFun hliftV.2 xv
        _ = chartMap x := rfl
  have hglobalNull : globalLift.Nullhomotopic := by
    simpa using (id_nullhomotopic ℂ).comp_left globalLift
  have hchartNull : chartMap.Nullhomotopic := by
    have hfactorNull := hglobalNull.comp_right exponential
    rwa [hglobalProjection] at hfactorNull
  -- A nullhomotopic chart has trivial induced map, contradicting the
  -- injective map induced by the twice-punctured-sphere homeomorphism.
  have hchartMapOne :=
    fundamentalGroupMap_eq_one_of_nullhomotopic chartMap x₀ hchartNull
  let cyclic := (fundamentalGroup_twicePuncturedSphere_equiv_int p q hpq x₀).some
  let generator : FundamentalGroup P x₀ := cyclic.symm (Multiplicative.ofAdd (1 : ℤ))
  have hgenerator_ne_one : generator ≠ 1 := by
    intro hgenerator
    have hone : Multiplicative.ofAdd (1 : ℤ) = 1 := by
      simpa only [generator, MulEquiv.apply_symm_apply, map_one] using
        congrArg cyclic hgenerator
    norm_num at hone
  have hgeneratorImage : FundamentalGroup.map chartMap x₀ generator = 1 := by
    simpa only [MonoidHom.one_apply] using
      congrArg (fun F ↦ F generator) hchartMapOne
  let induced := fundamentalGroupMulEquivOfHomeomorph chart x₀
  have hgeneratorEq : generator = 1 :=
    induced.injective (hgeneratorImage.trans induced.map_one.symm)
  exact hgenerator_ne_one hgeneratorEq

/-- Helper for Theorem 9.0.1: the complement of two spherical arcs meeting
at exactly two distinct endpoints has at most two connected components. -/
private lemma mk_connectedComponents_compl_arcPair_le_two
    (A₁ A₂ : Set (StandardSphere 2)) [Topology.IsArc A₁] [Topology.IsArc A₂]
    (p q : StandardSphere 2) (hpq : p ≠ q) (hinter : A₁ ∩ A₂ = {p, q}) :
    Cardinal.mk (ConnectedComponents ((A₁ ∪ A₂)ᶜ : Set (StandardSphere 2))) ≤ 2 := by
  -- Normalize the arc-pair complement as the overlap of the canonical cover
  -- of the twice-punctured sphere.
  have hA₁geometry := isClosed_and_isConnected_of_isArc A₁
  have hA₂geometry := isClosed_and_isConnected_of_isArc A₂
  have hpqMem := pair_mem_of_inter_eq_pair hinter
  let P : Set (StandardSphere 2) := {p, q}ᶜ
  let U : Set P := Subtype.val ⁻¹' A₁ᶜ
  let V : Set P := Subtype.val ⁻¹' A₂ᶜ
  let W : Set (StandardSphere 2) := (A₁ ∪ A₂)ᶜ
  have hUopen : IsOpen U :=
    hA₁geometry.1.isOpen_compl.preimage continuous_subtype_val
  have hVopen : IsOpen V :=
    hA₂geometry.1.isOpen_compl.preimage continuous_subtype_val
  have hcover : U ∪ V = Set.univ :=
    pairComplement_preimage_compl_union_eq_univ A₁ A₂ p q hinter
  have hWinter : U ∩ V = Subtype.val ⁻¹' W :=
    pairComplement_preimage_compl_inter A₁ A₂ p q
  have hWsubset : W ⊆ P := by
    intro x hxW hxPair
    rcases hxPair with hxp | hxq
    · exact hxW (Or.inl (hxp ▸ hpqMem.1))
    · exact hxW (Or.inl (hxq ▸ hpqMem.2.2.1))
  let overlapHomeomorph : (U ∩ V : Set P) ≃ₜ W :=
    (Homeomorph.setCongr hWinter).trans (nestedSubtypeHomeomorph P W hWsubset)
  -- Each cover complement contains an interior point of the corresponding arc.
  have hUcompl : Uᶜ.Nonempty := by
    obtain ⟨r, hrA₁, hrp, hrq⟩ :=
      exists_mem_arc_ne_pair A₁ p q hpqMem.1 hpqMem.2.2.1
    let rP : P := ⟨r, by simpa only [P, mem_compl_iff, mem_insert_iff,
      mem_singleton_iff, not_or] using ⟨hrp, hrq⟩⟩
    refine ⟨rP, ?_⟩
    simpa only [U, mem_compl_iff, mem_preimage, not_not] using hrA₁
  have hVcompl : Vᶜ.Nonempty := by
    obtain ⟨r, hrA₂, hrp, hrq⟩ :=
      exists_mem_arc_ne_pair A₂ p q hpqMem.2.1 hpqMem.2.2.2
    let rP : P := ⟨r, by simpa only [P, mem_compl_iff, mem_insert_iff,
      mem_singleton_iff, not_or] using ⟨hrp, hrq⟩⟩
    refine ⟨rP, ?_⟩
    simpa only [V, mem_compl_iff, mem_preimage, not_not] using hrA₂
  have hWopen : IsOpen W :=
    (hA₁geometry.1.union hA₂geometry.1).isOpen_compl
  letI : LocallyPathConnectedSpace (StandardSphere 2) :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin 2)) (StandardSphere 2)
  letI : LocallyConnectedSpace W := hWopen.locallyConnectedSpace
  letI : LocallyConnectedSpace (U ∩ V : Set P) :=
    overlapHomeomorph.locallyConnectedSpace
  have hjoinedU : ∀ x y : (U ∩ V : Set P), JoinedIn U x.1 y.1 := by
    intro x y
    exact joinedIn_preimage_compl_pairComplement A₁ hA₁geometry.1 p q
      hpqMem.1 hpqMem.2.2.1 (sphereArc_not_separates A₁)
      x.1 y.1 x.2.1 y.2.1
  have hjoinedV : ∀ x y : (U ∩ V : Set P), JoinedIn V x.1 y.1 := by
    intro x y
    exact joinedIn_preimage_compl_pairComplement A₂ hA₂geometry.1 p q
      hpqMem.2.1 hpqMem.2.2.2 (sphereArc_not_separates A₂)
      x.1 y.1 x.2.2 y.2.2
  have hfundamental : ∀ x : (U ∩ V : Set P),
      Nonempty (FundamentalGroup P x.1 ≃* Multiplicative ℤ) := by
    intro x
    exact fundamentalGroup_twicePuncturedSphere_equiv_int p q hpq x.1
  have hoverlapBound :
      Cardinal.mk (ConnectedComponents (U ∩ V : Set P)) ≤ 2 :=
    Theorem901.mk_connectedComponents_inter_le_two_of_windingCover
      U V hUopen hVopen hUcompl hVcompl hcover hjoinedU hjoinedV hfundamental
  -- Transport the overlap bound back to the ambient complementary set.
  have hWbound : Cardinal.mk (ConnectedComponents W) ≤ 2 := by
    rw [← Cardinal.mk_congr
      (connectedComponentsHomeomorphOfHomeomorph overlapHomeomorph).toEquiv]
    exact hoverlapBound
  exact hWbound

/-- Helper for Theorem 9.0.1: two spherical arcs meeting exactly at two
distinct endpoints have a complement with exactly two connected components. -/
private lemma sphereArcPair_separatesInto_two
    (A₁ A₂ : Set (StandardSphere 2)) [Topology.IsArc A₁] [Topology.IsArc A₂]
    (p q : StandardSphere 2) (hpq : p ≠ q) (hinter : A₁ ∩ A₂ = {p, q}) :
    (A₁ ∪ A₂).SeparatesInto 2 := by
  -- Route correction: the earlier opaque crossing detector is now replaced by
  -- `OpenCoverWindingCoordinate.pathPairCoordinate_eq_sub`, which computes all
  -- three crossing values through one normalized lift.  Assemble the independent
  -- lower separation result and upper component bound after recording arc geometry.
  have hseparates : (A₁ ∪ A₂).Separates :=
    sphereArcPair_union_separates A₁ A₂ p q hpq hinter
  have hcomponents :
      Cardinal.mk (ConnectedComponents ((A₁ ∪ A₂)ᶜ : Set (StandardSphere 2))) ≤ 2 :=
    mk_connectedComponents_compl_arcPair_le_two A₁ A₂ p q hpq hinter
  exact separatesInto_two_of_separates_of_components_le_two
    (A₁ ∪ A₂) hseparates hcomponents

/-- Helper for Theorem 9.0.1: every circle-like subset of a Hausdorff space is the
union of two closed connected arcs meeting exactly at their distinct endpoints. -/
private lemma exists_twoArcDecomposition
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (D : Set X) [Topology.IsSimpleClosedCurve D] :
    ∃ D₁ D₂ : Set X, ∃ p q : X,
      p ≠ q ∧ D = D₁ ∪ D₂ ∧ D₁ ∩ D₂ = {p, q} ∧
        IsClosed D₁ ∧ IsClosed D₂ ∧ IsConnected D₁ ∧ IsConnected D₂ ∧
        Topology.IsArc D₁ ∧ Topology.IsArc D₂ := by
  classical
  -- Transport the two canonical circle paths between antipodal points into `D`.
  obtain ⟨e⟩ := Topology.IsSimpleClosedCurve.homeomorphic_circle (X := D)
  let f : Circle → X := fun z ↦ (e.symm z : X)
  let p : X := f 1
  let q : X := f (-1)
  let D₁ : Set X := Set.range (f ∘ Circle.path 1 (-1))
  let D₂ : Set X := Set.range (f ∘ Circle.path (-1) 1)
  have hfContinuous : Continuous f := continuous_subtype_val.comp e.symm.continuous
  have hfInjective : Function.Injective f :=
    Subtype.val_injective.comp e.symm.injective
  have hpq : p ≠ q := by
    intro hpq
    exact (Circle.neg_ne_self 1).symm (hfInjective hpq)
  have hRange : Set.range f = D := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, rfl⟩
      exact (e.symm y).property
    · intro x hx
      have hfx : f (e ⟨x, hx⟩) = x := by
        simp [f]
      exact ⟨e ⟨x, hx⟩, hfx⟩
  have hpath₁Continuous : Continuous (f ∘ Circle.path 1 (-1)) :=
    hfContinuous.comp (Circle.path 1 (-1)).continuous
  have hpath₂Continuous : Continuous (f ∘ Circle.path (-1) 1) :=
    hfContinuous.comp (Circle.path (-1) 1).continuous
  have hpath₁Injective : Function.Injective (f ∘ Circle.path 1 (-1)) :=
    hfInjective.comp (Circle.path_injective_of_ne (Circle.neg_ne_self 1).symm)
  have hpath₂Injective : Function.Injective (f ∘ Circle.path (-1) 1) :=
    hfInjective.comp (Circle.path_injective_of_ne (Circle.neg_ne_self 1))
  -- Compact-domain embeddings identify each path range with the unit interval.
  have hD₁Arc : Topology.IsArc D₁ := by
    let hEmbedding : Topology.IsEmbedding (f ∘ Circle.path 1 (-1)) :=
      hpath₁Continuous.isClosedEmbedding hpath₁Injective |>.isEmbedding
    exact ⟨⟨hEmbedding.toHomeomorph.symm⟩⟩
  have hD₂Arc : Topology.IsArc D₂ := by
    let hEmbedding : Topology.IsEmbedding (f ∘ Circle.path (-1) 1) :=
      hpath₂Continuous.isClosedEmbedding hpath₂Injective |>.isEmbedding
    exact ⟨⟨hEmbedding.toHomeomorph.symm⟩⟩
  have hD₁image : D₁ = f '' Set.range (Circle.path 1 (-1)) := by
    simp [D₁, Set.range_comp]
  have hD₂image : D₂ = f '' Set.range (Circle.path (-1) 1) := by
    simp [D₂, Set.range_comp]
  -- The complementary circle paths cover the circle and meet only at endpoints.
  have hUnion : D = D₁ ∪ D₂ := by
    rw [hD₁image, hD₂image, ← Set.image_union,
      Circle.range_path_union_range_path (Circle.neg_ne_self 1).symm, Set.image_univ]
    exact hRange.symm
  have hInter : D₁ ∩ D₂ = {p, q} := by
    rw [hD₁image, hD₂image, ← Set.image_inter hfInjective,
      Circle.range_path_inter_range_path (Circle.neg_ne_self 1).symm, Set.image_pair]
  -- Continuity from the compact interval supplies closedness and connectedness.
  refine ⟨D₁, D₂, p, q, hpq, hUnion, hInter, ?_, ?_, ?_, ?_, hD₁Arc, hD₂Arc⟩
  · exact (isCompact_range hpath₁Continuous).isClosed
  · exact (isCompact_range hpath₂Continuous).isClosed
  · exact isConnected_range hpath₁Continuous
  · exact isConnected_range hpath₂Continuous

/-- Helper for Theorem 9.0.1: a spherical simple closed curve has exactly two
complementary components. -/
private lemma jordanCurveSphere_separatesInto
    (D : Set (StandardSphere 2)) [Topology.IsSimpleClosedCurve D] :
    D.SeparatesInto 2 := by
  -- Decompose the curve into its two canonical arcs and apply the global invariant.
  obtain ⟨D₁, D₂, p, q, hpq, hUnion, hInter, -, -, -, -, hD₁Arc, hD₂Arc⟩ :=
    exists_twoArcDecomposition D
  letI : Topology.IsArc D₁ := hD₁Arc
  letI : Topology.IsArc D₂ := hD₂Arc
  rw [hUnion]
  exact sphereArcPair_separatesInto_two D₁ D₂ p q hpq hInter

/-- Helper for Theorem 9.0.1: an embedding carries a simple closed curve to
a simple closed curve in its codomain. -/
private lemma isSimpleClosedCurve_image_isEmbedding
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Topology.IsEmbedding f) (A : Set X)
    [Topology.IsSimpleClosedCurve A] : Topology.IsSimpleClosedCurve (f '' A) := by
  -- Restrict the embedding to `A` and compose its image homeomorphism with the circle model.
  obtain ⟨hA⟩ := Topology.IsSimpleClosedCurve.homeomorphic_circle (X := A)
  exact ⟨⟨(hf.homeomorphImage A).symm.trans hA⟩⟩

/-- Helper for Theorem 9.0.1: the first coordinate unit vector is a point of
the standard two-sphere. -/
private lemma stereographicPole_mem_standardSphere :
    EuclideanSpace.single 0 (1 : ℝ) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  -- Its Euclidean norm is one.
  rw [Metric.mem_sphere, dist_zero_right]
  simp

/-- Helper for Theorem 9.0.1: a fixed pole used to identify the punctured
standard two-sphere with the plane. -/
private noncomputable def stereographicPole : StandardSphere 2 :=
  ⟨EuclideanSpace.single 0 (1 : ℝ), stereographicPole_mem_standardSphere⟩

/-- Helper for Theorem 9.0.1: deleting a point outside a closed subset of the
two-sphere preserves the connected-component count of its complement. -/
private lemma puncturedSphere_complement_componentCount
    (D : Set (StandardSphere 2)) (hD : IsClosed D) (b : StandardSphere 2)
    (_hb : b ∉ D) :
    Cardinal.mk (ConnectedComponents
      (((Subtype.val ⁻¹' D : Set ({b}ᶜ : Set (StandardSphere 2)))ᶜ :
        Set ({b}ᶜ : Set (StandardSphere 2))))) =
      Cardinal.mk (ConnectedComponents (Dᶜ : Set (StandardSphere 2))) := by
  classical
  -- The puncture inclusion meets every component, and each intersection stays connected.
  letI : LocallyPathConnectedSpace (StandardSphere 2) :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin 2)) (StandardSphere 2)
  let P := (Subtype.val ⁻¹' Dᶜ : Set ({b}ᶜ : Set (StandardSphere 2)))
  let Q := (Dᶜ : Set (StandardSphere 2))
  let j : P → Q := fun x ↦ ⟨x.1.1, x.2⟩
  have hj : Continuous j := by
    change Continuous (fun x : P ↦ (⟨x.1.1, x.2⟩ : Q))
    have hval : Continuous (fun x : P ↦ x.1.1 : P → StandardSphere 2) := by
      fun_prop
    exact hval.subtype_mk fun x ↦ x.2
  have hjbij : Function.Bijective hj.connectedComponentsMap := by
    constructor
    · -- Connected representatives in one spherical component remain connected after puncturing.
      intro a₁ a₂ ha
      obtain ⟨x₁, rfl⟩ := ConnectedComponents.surjective_coe a₁
      obtain ⟨x₂, rfl⟩ := ConnectedComponents.surjective_coe a₂
      rw [Continuous.connectedComponentsMap_mk,
        Continuous.connectedComponentsMap_mk] at ha
      rw [ConnectedComponents.coe_eq_coe'] at ha ⊢
      have hsame : x₁.1.1 ∈ connectedComponentIn Dᶜ x₂.1.1 := by
        rw [connectedComponentIn_eq_image (F := Dᶜ) (x := x₂.1.1) x₂.2]
        exact ⟨j x₁, ha, rfl⟩
      have hUopen : IsOpen (connectedComponentIn Dᶜ x₂.1.1) :=
        hD.isOpen_compl.connectedComponentIn
      have hPconn : IsConnected
          (Subtype.val ⁻¹' connectedComponentIn Dᶜ x₂.1.1 :
            Set ({b}ᶜ : Set (StandardSphere 2))) :=
        isConnectedPreimageOpenConnectedStandardSphere hUopen
          (isConnected_connectedComponentIn_iff.mpr x₂.2)
      have hsubsetP : Subtype.val ⁻¹' connectedComponentIn Dᶜ x₂.1.1 ⊆ P :=
        preimage_mono (connectedComponentIn_subset Dᶜ x₂.1.1)
      have hx₁ : x₁.1 ∈ Subtype.val ⁻¹' connectedComponentIn Dᶜ x₂.1.1 := hsame
      have hx₂ : x₂.1 ∈ Subtype.val ⁻¹' connectedComponentIn Dᶜ x₂.1.1 :=
        mem_connectedComponentIn x₂.2
      have hPopen : IsOpen P :=
        hD.isOpen_compl.preimage continuous_subtype_val
      have hinsideP : IsConnected
          (Subtype.val ⁻¹' (Subtype.val ⁻¹' connectedComponentIn Dᶜ x₂.1.1) :
            Set P) := by
        apply hPconn.preimage_of_isOpenMap Subtype.val_injective
          hPopen.isOpenMap_subtype_val
        intro y hy
        exact ⟨⟨y, hsubsetP hy⟩, rfl⟩
      exact hinsideP.isPreconnected.subset_connectedComponent hx₂ hx₁
    · -- Every spherical component has a nonempty puncture and hence a preimage class.
      intro a
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
      have hUopen : IsOpen (connectedComponentIn Dᶜ x.1) :=
        hD.isOpen_compl.connectedComponentIn
      have hPconn : IsConnected
          (Subtype.val ⁻¹' connectedComponentIn Dᶜ x.1 :
            Set ({b}ᶜ : Set (StandardSphere 2))) :=
        isConnectedPreimageOpenConnectedStandardSphere hUopen
          (isConnected_connectedComponentIn_iff.mpr x.2)
      obtain ⟨y, hy⟩ := hPconn.nonempty
      have hyD : y.1 ∈ Dᶜ := connectedComponentIn_subset Dᶜ x.1 hy
      let yp : P := ⟨y, hyD⟩
      refine ⟨ConnectedComponents.mk yp, ?_⟩
      rw [Continuous.connectedComponentsMap_mk, ConnectedComponents.coe_eq_coe']
      rw [connectedComponentIn_eq_image x.2] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      have hzEq : z = j yp := Subtype.ext hzy
      exact hzEq ▸ hz
  let eP : ConnectedComponents P ≃ ConnectedComponents Q :=
    Equiv.ofBijective hj.connectedComponentsMap hjbij
  have hComplement :
      ((Subtype.val ⁻¹' D : Set ({b}ᶜ : Set (StandardSphere 2)))ᶜ :
        Set ({b}ᶜ : Set (StandardSphere 2))) = P := by
    ext x
    simp [P]
  rw [hComplement]
  exact Cardinal.mk_congr eP

/-- Helper for Theorem 9.0.1: the spherical component theorem transports
through stereographic projection to the Euclidean plane. -/
private lemma jordanCurvePlane_separatesInto
    (C : Set (EuclideanSpace ℝ (Fin 2))) [Topology.IsSimpleClosedCurve C] :
    C.SeparatesInto 2 := by
  classical
  -- Embed the planar curve into the punctured sphere and apply the spherical theorem.
  let e := puncturedSphereHomeomorphPlane stereographicPole
  let j : EuclideanSpace ℝ (Fin 2) → StandardSphere 2 :=
    fun x ↦ (e.symm x : StandardSphere 2)
  let D : Set (StandardSphere 2) := j '' C
  have hjEmbedding : Topology.IsEmbedding j :=
    Topology.IsEmbedding.subtypeVal.comp e.symm.isEmbedding
  letI : Topology.IsSimpleClosedCurve D :=
    isSimpleClosedCurve_image_isEmbedding j hjEmbedding C
  have hDclosed : IsClosed D := by
    obtain ⟨hCircle⟩ := Topology.IsSimpleClosedCurve.homeomorphic_circle (X := D)
    letI : CompactSpace D := hCircle.symm.compactSpace
    exact (isCompact_iff_compactSpace.mpr inferInstance).isClosed
  have hpoleNot : stereographicPole ∉ D := by
    rintro ⟨x, -, hx⟩
    have hPoleMem : (e.symm x : StandardSphere 2) ∈
        ({stereographicPole} : Set (StandardSphere 2)) := by
      simpa [j] using hx
    exact (e.symm x).property hPoleMem
  have hSphere : Cardinal.mk (ConnectedComponents (Dᶜ : Set (StandardSphere 2))) = 2 :=
    Set.separatesInto_iff.mp (jordanCurveSphere_separatesInto D)
  let Dp : Set ({stereographicPole}ᶜ : Set (StandardSphere 2)) :=
    Subtype.val ⁻¹' D
  have hPunctured : Dp.SeparatesInto 2 := by
    rw [Set.separatesInto_iff]
    exact (puncturedSphere_complement_componentCount D hDclosed stereographicPole
      hpoleNot).trans hSphere
  have hImage : e '' Dp = C := by
    ext y
    constructor
    · rintro ⟨x, hxD, rfl⟩
      obtain ⟨z, hzC, hz⟩ := hxD
      have hx : x = e.symm z := Subtype.ext hz.symm
      simpa [hx] using hzC
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      exact ⟨y, hy, rfl⟩
  rw [← hImage]
  exact (separatesInto_image_iff e Dp 2).mpr hPunctured

/-- Helper for Theorem 9.0.1: having exactly two complementary components
implies separation. -/
private lemma separates_of_separatesInto_two
    {X : Type*} [TopologicalSpace X] (A : Set X) (hA : A.SeparatesInto 2) :
    A.Separates := by
  -- A preconnected complement would have at most one connected component.
  rw [Set.separates_iff]
  intro hpre
  letI : PreconnectedSpace (Aᶜ : Set X) := hpre
  have hle : Cardinal.mk (ConnectedComponents (Aᶜ : Set X)) ≤ 1 :=
    Cardinal.le_one_iff_subsingleton.mpr inferInstance
  rw [Set.separatesInto_iff] at hA
  rw [hA] at hle
  norm_num at hle

/-- Helper for Theorem 9.0.1: a planar simple closed curve separates the
plane. -/
private lemma isSimpleClosedCurve_separates
    (C : Set (EuclideanSpace ℝ (Fin 2))) [Topology.IsSimpleClosedCurve C] :
    C.Separates := by
  -- The transported exact component count rules out a preconnected complement.
  exact separates_of_separatesInto_two C (jordanCurvePlane_separatesInto C)

/-- Helper for Theorem 9.0.1: the complement of a planar simple closed curve
has at most two connected components. -/
private lemma mk_connectedComponents_compl_le_two_of_isSimpleClosedCurve
    (C : Set (EuclideanSpace ℝ (Fin 2))) [Topology.IsSimpleClosedCurve C] :
    Cardinal.mk (ConnectedComponents (Cᶜ : Set (EuclideanSpace ℝ (Fin 2)))) ≤ 2 := by
  -- The transported exact count immediately supplies the required upper bound.
  have hCount := jordanCurvePlane_separatesInto C
  rw [Set.separatesInto_iff] at hCount
  exact le_of_eq hCount

/-- Helper for Theorem 9.0.1: when a closed set has exactly two complementary
components, every chosen component has a point outside its closure. -/
private lemma existsComplementPointNotMemComponentClosure
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    (A : Set X) (hA : IsClosed A)
    (hcomponents : Cardinal.mk (ConnectedComponents (Aᶜ : Set X)) = 2)
    (x : (Aᶜ : Set X)) :
    ∃ b : (Aᶜ : Set X), (b : X) ∉ closure (connectedComponentIn Aᶜ x) := by
  classical
  -- Select a representative of the component class distinct from that of `x`.
  obtain ⟨q, hqx, -⟩ :=
    (Cardinal.mk_eq_two_iff' (ConnectedComponents.mk x)).mp hcomponents
  obtain ⟨b, rfl⟩ := ConnectedComponents.surjective_coe q
  have hbNotMem : (b : X) ∉ connectedComponentIn Aᶜ x := by
    intro hb
    rw [connectedComponentIn_eq_image x.property] at hb
    obtain ⟨z, hz, hzb⟩ := hb
    have hzx : b ∈ connectedComponent x := by
      have hzb' : z = b := Subtype.ext hzb
      exact hzb' ▸ hz
    exact hqx (ConnectedComponents.coe_eq_coe'.mpr hzx)
  refine ⟨b, ?_⟩
  -- The other component is an open neighborhood disjoint from the chosen component.
  intro hbClosure
  have hbOwn : (b : X) ∈ connectedComponentIn Aᶜ b :=
    mem_connectedComponentIn b.property
  have hbOwnOpen : IsOpen (connectedComponentIn Aᶜ b) :=
    hA.isOpen_compl.connectedComponentIn
  rcases mem_closure_iff.mp hbClosure (connectedComponentIn Aᶜ b)
      hbOwnOpen hbOwn with ⟨y, hyOwn, hyComponent⟩
  have heq : connectedComponentIn Aᶜ x = connectedComponentIn Aᶜ b :=
    (connectedComponentIn_eq hyComponent).trans
      (connectedComponentIn_eq hyOwn).symm
  exact hbNotMem (heq ▸ hbOwn)

/-- Helper for Theorem 9.0.1: canonical Euclidean-complex coordinates preserve
the unit-sphere predicate. -/
private lemma euclideanPlaneCoordinates_memSphere
    (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
      Complex.orthonormalBasisOneI.repr.symm x ∈ Metric.sphere (0 : ℂ) 1 := by
  -- Both memberships say that the norm is one.
  simp only [Metric.mem_sphere, dist_zero_right]
  exact (Complex.orthonormalBasisOneI.repr.symm.norm_map x).symm ▸ Iff.rfl

/-- Helper for Theorem 9.0.1: canonical Euclidean-complex coordinates
identify the standard one-sphere with `Circle`. -/
private noncomputable def standardSphereOneHomeomorphCircle :
    StandardSphere 1 ≃ₜ Circle :=
  Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.subtype
    euclideanPlaneCoordinates_memSphere

/-- Helper for Theorem 9.0.1: at most one connected-component class forces
the ambient space to be preconnected. -/
private lemma preconnectedSpaceOfComponentCardinalLeOne
    {X : Type*} [TopologicalSpace X]
    (hle : Cardinal.mk (ConnectedComponents X) ≤ 1) : PreconnectedSpace X := by
  -- Cardinality at most one is exactly subsingletonness of the component quotient.
  have hsub : Subsingleton (ConnectedComponents X) :=
    Cardinal.le_one_iff_subsingleton.mp hle
  rw [preconnectedSpace_iff_connectedComponent]
  intro x
  apply eq_univ_of_forall
  intro y
  rw [← connectedComponent_eq_iff_mem]
  exact ConnectedComponents.coe_eq_coe.mp
    (@Subsingleton.elim _ hsub (y : ConnectedComponents X)
      (x : ConnectedComponents X))

/-- Helper for Theorem 9.0.1: a compact contractible subset of the standard
two-sphere has preconnected complement. -/
private lemma sphereCompactContractible_compl_isPreconnected
    (B : Set (StandardSphere 2)) [CompactSpace B] [ContractibleSpace B] :
    IsPreconnected Bᶜ := by
  -- Apply the local Borsuk bridge to the subtype inclusion for each exterior pair.
  apply isPreconnected_of_pairwise_mem_connectedComponentIn
  intro a ha b hb
  have inclusionMem : ∀ x : B,
      (x : StandardSphere 2) ∈ ({a, b}ᶜ : Set (StandardSphere 2)) := by
    intro x
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun hxa ↦ ha (hxa ▸ x.property),
      fun hxb ↦ hb (hxb ▸ x.property)⟩
  have inclusionContinuous : Continuous (fun x : B ↦
      (⟨x, inclusionMem x⟩ : ({a, b}ᶜ : Set (StandardSphere 2)))) :=
    continuous_subtype_val.subtype_mk _
  let inclusion : C(B, ({a, b}ᶜ : Set (StandardSphere 2))) :=
    ⟨fun x ↦ ⟨x, inclusionMem x⟩, inclusionContinuous⟩
  have inclusionInjective : Function.Injective inclusion := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg
      (fun z : ({a, b}ᶜ : Set (StandardSphere 2)) ↦ (z : StandardSphere 2)) hxy
  have inclusionNullhomotopic : inclusion.Nullhomotopic := by
    simpa only [ContinuousMap.comp_id] using
      (id_nullhomotopic B).comp_right inclusion
  have inclusionRange :
      Set.range (fun x : B ↦ (inclusion x : StandardSphere 2)) = B := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact x.property
    · intro hz
      exact ⟨⟨z, hz⟩, rfl⟩
  rw [← inclusionRange]
  exact borsukEmbeddingPointsSameComponent a b inclusion inclusionInjective
    inclusionNullhomotopic

/-- Helper for Theorem 9.0.1: a compact contractible planar subset does not
separate the plane. -/
private lemma planarCompactContractible_not_separates
    (B : Set (EuclideanSpace ℝ (Fin 2))) [CompactSpace B] [ContractibleSpace B] :
    ¬ B.Separates := by
  classical
  -- Compactify the plane and transport compactness and contractibility to the image.
  let e := puncturedSphereHomeomorphPlane stereographicPole
  let j : EuclideanSpace ℝ (Fin 2) → StandardSphere 2 :=
    fun x ↦ (e.symm x : StandardSphere 2)
  let D : Set (StandardSphere 2) := j '' B
  have hjEmbedding : Topology.IsEmbedding j :=
    Topology.IsEmbedding.subtypeVal.comp e.symm.isEmbedding
  let hBD : B ≃ₜ D := hjEmbedding.homeomorphImage B
  letI : CompactSpace D := hBD.compactSpace
  letI : ContractibleSpace D := hBD.symm.contractibleSpace
  have hDclosed : IsClosed D :=
    (isCompact_iff_compactSpace.mpr inferInstance).isClosed
  have hpoleNot : stereographicPole ∉ D := by
    rintro ⟨x, -, hx⟩
    have hPoleMem : (e.symm x : StandardSphere 2) ∈
        ({stereographicPole} : Set (StandardSphere 2)) := by
      simpa [j] using hx
    exact (e.symm x).property hPoleMem
  have hSpherePre : IsPreconnected Dᶜ :=
    sphereCompactContractible_compl_isPreconnected D
  have hSphereSpace : PreconnectedSpace (Dᶜ : Set (StandardSphere 2)) :=
    Subtype.preconnectedSpace hSpherePre
  have hSphereLe : Cardinal.mk
      (ConnectedComponents (Dᶜ : Set (StandardSphere 2))) ≤ 1 := by
    letI : PreconnectedSpace (Dᶜ : Set (StandardSphere 2)) := hSphereSpace
    exact Cardinal.le_one_iff_subsingleton.mpr inferInstance
  let Dp : Set ({stereographicPole}ᶜ : Set (StandardSphere 2)) :=
    Subtype.val ⁻¹' D
  have hPuncturedLe : Cardinal.mk (ConnectedComponents (Dpᶜ : Set _)) ≤ 1 := by
    rw [puncturedSphere_complement_componentCount D hDclosed stereographicPole
      hpoleNot]
    exact hSphereLe
  have hPuncturedSpace : PreconnectedSpace (Dpᶜ : Set _) :=
    preconnectedSpaceOfComponentCardinalLeOne hPuncturedLe
  have hPuncturedPre : IsPreconnected Dpᶜ :=
    isPreconnected_iff_preconnectedSpace.mpr hPuncturedSpace
  have hImage : e '' Dp = B := by
    ext y
    constructor
    · rintro ⟨x, hxD, rfl⟩
      obtain ⟨z, hzB, hz⟩ := hxD
      have hx : x = e.symm z := Subtype.ext hz.symm
      simpa [hx] using hzB
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      exact ⟨y, hy, rfl⟩
  have hImagePre : IsPreconnected (e '' Dpᶜ) :=
    e.isPreconnected_image.mpr hPuncturedPre
  have hComplementImage : e '' Dpᶜ = Bᶜ := by
    rw [e.image_compl, hImage]
  have hBpre : IsPreconnected Bᶜ := by
    rwa [hComplementImage] at hImagePre
  intro hBseparates
  exact (Set.separates_iff.mp hBseparates) (Subtype.preconnectedSpace hBpre)

/-- Helper for Theorem 9.0.1: every neighborhood of a point on a planar
simple closed curve contains the part left after removing a nonseparating
closed-ball core. -/
private lemma existsNonseparatingClosedBallCore
    (C : Set (EuclideanSpace ℝ (Fin 2))) [Topology.IsSimpleClosedCurve C]
    {z : EuclideanSpace ℝ (Fin 2)} (hz : z ∈ C)
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : U ∈ 𝓝 z) :
    ∃ B : Set (EuclideanSpace ℝ (Fin 2)),
      B ⊆ C ∧ ¬ B.Separates ∧ C \ B ⊆ U := by
  -- Convert the circle model to `StandardSphere 1` and choose a closed-ball core.
  obtain ⟨hCircle⟩ := Topology.IsSimpleClosedCurve.homeomorphic_circle (X := C)
  have hStandardSphere : Nonempty (C ≃ₜ StandardSphere 1) :=
    ⟨hCircle.trans standardSphereOneHomeomorphCircle.symm⟩
  obtain ⟨B, hBC, ⟨hBball⟩, hCBU⟩ :=
    existsClosedBallCoreOfMemNhds 1 C hStandardSphere ⟨z, hz⟩ hU
  letI : CompactSpace B := hBball.symm.compactSpace
  have hRadius : (0 : ℝ) ≤ 1 := by
    norm_num
  letI : ContractibleSpace
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
    Metric.contractibleSpace_closedBall hRadius
  letI : ContractibleSpace B := hBball.contractibleSpace
  -- Borsuk nonseparation of compact contractible sets supplies the planar crossing set.
  exact ⟨B, hBC, planarCompactContractible_not_separates B, hCBU⟩

/-- Helper for Theorem 9.0.1: near each point of a planar simple closed curve,
there is a preconnected set crossing a chosen complementary component whose
frontier intersections remain in the prescribed neighborhood. -/
private lemma exists_preconnected_frontierCrossing_subset_nhds
    (C : Set (EuclideanSpace ℝ (Fin 2))) [Topology.IsSimpleClosedCurve C]
    (x : (Cᶜ : Set (EuclideanSpace ℝ (Fin 2)))) {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ C) {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : U ∈ 𝓝 z) :
    ∃ S : Set (EuclideanSpace ℝ (Fin 2)),
      IsPreconnected S ∧
        (S ∩ connectedComponentIn Cᶜ x).Nonempty ∧
        (S ∩ (closure (connectedComponentIn Cᶜ x))ᶜ).Nonempty ∧
        S ∩ frontier (connectedComponentIn Cᶜ x) ⊆ U := by
  -- Choose the other complementary component and a large nonseparating arc core.
  have hCclosed : IsClosed C := isClosed_of_isSimpleClosedCurve C
  have hcomponents :
      Cardinal.mk (ConnectedComponents (Cᶜ : Set (EuclideanSpace ℝ (Fin 2)))) = 2 :=
    Set.separatesInto_iff.mp (jordanCurvePlane_separatesInto C)
  obtain ⟨b, hbClosure⟩ :=
    existsComplementPointNotMemComponentClosure C hCclosed hcomponents x
  obtain ⟨B, hBC, hBnonseparating, hCBU⟩ :=
    existsNonseparatingClosedBallCore C hz hU
  have hBpreconnectedSpace : PreconnectedSpace
      (Bᶜ : Set (EuclideanSpace ℝ (Fin 2))) := by
    rw [Set.separates_iff] at hBnonseparating
    exact not_not.mp hBnonseparating
  have hBpreconnected : IsPreconnected Bᶜ :=
    isPreconnected_iff_preconnectedSpace.mpr hBpreconnectedSpace
  have hxB : (x : EuclideanSpace ℝ (Fin 2)) ∈ Bᶜ := by
    intro hx
    exact x.property (hBC hx)
  have hbB : (b : EuclideanSpace ℝ (Fin 2)) ∈ Bᶜ := by
    intro hb
    exact b.property (hBC hb)
  refine ⟨Bᶜ, hBpreconnected, ?_, ?_, ?_⟩
  · exact ⟨x, hxB, mem_connectedComponentIn x.property⟩
  · exact ⟨b, hbB, hbClosure⟩
  · rintro y ⟨hyB, hyFrontier⟩
    have hyC := frontier_connectedComponentIn_compl_subset C hCclosed x hyFrontier
    exact hCBU ⟨hyC, hyB⟩

/-- Helper for Theorem 9.0.1: every point of a planar simple closed curve lies
in the frontier of each complementary component. -/
private lemma subset_frontier_connectedComponentIn_compl_of_isSimpleClosedCurve
    (C : Set (EuclideanSpace ℝ (Fin 2))) [Topology.IsSimpleClosedCurve C]
    (x : (Cᶜ : Set (EuclideanSpace ℝ (Fin 2)))) :
    C ⊆ frontier (connectedComponentIn Cᶜ x) := by
  -- It suffices to make every neighborhood of a curve point meet the frontier,
  -- since frontiers are closed.
  intro z hz
  apply isClosed_frontier.closure_subset
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨S, hSpre, hScomponent, hSoutside, hSfrontier⟩ :=
    exists_preconnected_frontierCrossing_subset_nhds C x hz hU
  -- The abstract crossing lemma supplies a frontier point, and the source-facing
  -- construction places every such point inside the chosen neighborhood.
  obtain ⟨y, hyS, hyFrontier⟩ :=
    IsPreconnected.inter_frontier_nonempty_of_mem_of_mem_compl_closure
      hSpre hScomponent hSoutside
  exact ⟨y, hSfrontier ⟨hyS, hyFrontier⟩, hyFrontier⟩

/-- Theorem 9.0.1 (1): Every simple closed curve in the plane has a complement
with exactly two connected components. -/
theorem jordanCurve_complement_components (C : Set (EuclideanSpace ℝ (Fin 2)))
    [Topology.IsSimpleClosedCurve C] : C.SeparatesInto 2 := by
  -- Combine the Jordan separation lower bound with the independent upper bound.
  exact separatesInto_two_of_separates_of_components_le_two C
    (isSimpleClosedCurve_separates C)
    (mk_connectedComponents_compl_le_two_of_isSimpleClosedCurve C)

/-- Theorem 9.0.1 (2): Every component of the complement of a simple closed
curve has the curve as its frontier. -/
theorem jordanCurve_frontier_component (C : Set (EuclideanSpace ℝ (Fin 2)))
    [Topology.IsSimpleClosedCurve C]
    (x : (Cᶜ : Set (EuclideanSpace ℝ (Fin 2)))) :
    frontier (connectedComponentIn Cᶜ x) = C := by
  -- Combine the general closed-set inclusion with Jordan boundary incidence.
  apply Set.Subset.antisymm
  · exact frontier_connectedComponentIn_compl_subset C
      (isClosed_of_isSimpleClosedCurve C) x
  · exact subset_frontier_connectedComponentIn_compl_of_isSimpleClosedCurve C x
