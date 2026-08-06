import Mathlib.Algebra.Group.Defs
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Topology.Homotopy.Contractible
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_2_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Corollary_3_7_11
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Theorem_3_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_8_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Theorem_3_8_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Theorem_3_8_10
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Lemma_3_8_11
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Theorem_7_6_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_5_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Lemma_9_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Lemma_9_4_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.ZerothHomotopyMap
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Lemma_10_4_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Refinement_10_5_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Theorem_10_3_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Theorem_10_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.KPiOne

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold Topology TopCat Topology.Homotopy
open Path.Homotopic.Quotient
open CategoryTheory CategoryTheory.Limits

universe u v w z

-- The generalized-loop/path-component comparison is imported from Remark 9.4.13.  Keeping one
-- public owner avoids restating the same theorem here under an identical global name.

/-- Helper for Problem 15.3.2: the Section 9.5 sphere-fiber model identifies `π_ q(X, x)` with
the path components of the corresponding evaluation fiber. -/
noncomputable def homotopyGroupEquivSphereBasepointFiberZeroth
    {X : Type z} [TopologicalSpace X] (q : ℕ) (x : X) :
    π_ q X x ≃ ZerothHomotopy (sphereBasepointFiber q x) :=
  let e := Classical.choice (sphereBasepointFiber_homeomorphic_iteratedLoopSpace q x)
  -- Compare `π_ q` with iterated loops, then transport along the chosen sphere-fiber model.
  (homotopyGroupEquivZerothHomotopyGenLoop q x).trans
    (zerothHomotopyEquivOfHomotopyEquiv e.symm.toHomotopyEquiv)

/-- Helper for Problem 15.3.2: a path between basepoints transports the path components of the
Section 9.5 sphere-evaluation fibers. -/
noncomputable def generalSphereBasepointFiberZerothEquivOfPath
    {X : Type z} [TopologicalSpace X]
    [CompactlyGeneratedWeakHausdorffSpace.{z, z} X]
    (q : ℕ) {x x' : X} (β : Path x x') :
    ZerothHomotopy (sphereBasepointFiber q x) ≃ ZerothHomotopy (sphereBasepointFiber q x') :=
  -- Use the Section 9.5 transport on May's k-ified mapping-space owner.
  sphereBasepointFiberZerothEquivOfPathClass q (mk β)

/-- Helper for Problem 15.3.2: a path between basepoints induces an equivalence on all homotopy
groups. -/
noncomputable def homotopyGroupBasepointChangeEquiv
    {X : Type z} [TopologicalSpace X]
    [CompactlyGeneratedWeakHausdorffSpace.{z, z} X]
    (q : ℕ) {x x' : X} (β : Path x x') :
    π_ q X x ≃ π_ q X x' :=
  -- Move both homotopy groups through the common sphere-fiber model and translate along `β`.
  (homotopyGroupEquivSphereBasepointFiberZeroth q x).trans
    ((generalSphereBasepointFiberZerothEquivOfPath q β).trans
      (homotopyGroupEquivSphereBasepointFiberZeroth q x').symm)

/-- Helper for Problem 15.3.2: subsingleton homotopy groups transport along a path between
basepoints. -/
theorem homotopyGroupSubsingleton_of_path
    {X : Type z} [TopologicalSpace X]
    [CompactlyGeneratedWeakHausdorffSpace.{z, z} X]
    (q : ℕ) {x x' : X} (β : Path x x')
    [Subsingleton (π_ q X x)] :
    Subsingleton (π_ q X x') := by
  let e := homotopyGroupBasepointChangeEquiv q β
  -- Pull the subsingleton structure across the basepoint-change equivalence.
  exact Equiv.subsingleton e.symm

/-- Helper for Problem 15.3.2: a colimit of locally path connected spaces is locally path
connected. -/
private theorem locPathConnectedSpaceOfTopCatColimit {J : Type*} [Category J] {F : J ⥤ TopCat}
    (c : Cocone F) (hc : IsColimit c) (hF : ∀ j, LocPathConnectedSpace (F.obj j)) :
    LocPathConnectedSpace c.pt := by
  let _ : ∀ j, LocPathConnectedSpace (F.obj j) := hF
  let desc : (Σ j, F.obj j) → c.pt := fun x ↦ c.ι.app x.1 x.2
  have hsurj : Function.Surjective desc := by
    intro x
    obtain ⟨j, y, rfl⟩ :=
      CategoryTheory.Limits.Types.jointly_surjective_of_isColimit
        (F := F ⋙ forget TopCat) (t := (forget TopCat).mapCocone c)
        (isColimitOfPreserves (forget TopCat) hc) x
    exact ⟨⟨j, y⟩, rfl⟩
  have hquot : Topology.IsQuotientMap desc := by
    rw [Topology.isQuotientMap_iff]
    constructor
    · exact hsurj
    · intro U
      -- Openness on the sigma source is checked stagewise by the colimit topology criterion.
      rw [isOpen_sigma_iff, TopCat.isOpen_iff_of_isColimit _ hc]
      refine forall_congr' fun j ↦ ?_
      change IsOpen ((fun x : F.obj j ↦ desc ⟨j, x⟩) ⁻¹' U) ↔ IsOpen ((c.ι.app j) ⁻¹' U)
      simp [desc]
  -- The colimit is a quotient of the sigma coproduct of the locally path connected stages.
  exact hquot.locPathConnectedSpace

/-- Helper for Problem 15.3.2: each disk in the abstract-CW attachment data is locally path
connected. -/
private theorem topCatDisk_locPathConnectedSpace (n : ℕ) :
    LocPathConnectedSpace (TopCat.disk n) := by
  -- The closed-ball model of the disk is convex, hence locally path connected.
  let _ : LocPathConnectedSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).locPathConnectedSpace
  -- The `ULift` wrapper used in `TopCat.disk` preserves the topology up to homeomorphism.
  simpa [TopCat.disk] using
    (Homeomorph.ulift.isOpenEmbedding.locPathConnectedSpace :
      LocPathConnectedSpace (ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)))

/-- Helper for Problem 15.3.2: attaching locally path connected cells preserves local path
connectedness. -/
private theorem locPathConnectedSpaceOfAttachCells {α : Type*} {A B : α → TopCat}
    (g : ∀ a, A a ⟶ B a) {X₁ X₂ : TopCat} {f : X₁ ⟶ X₂}
    (c : HomotopicalAlgebra.AttachCells g f) (hX₁ : LocPathConnectedSpace X₁)
    (hB : ∀ a, LocPathConnectedSpace (B a)) : LocPathConnectedSpace X₂ := by
  let _ : LocPathConnectedSpace X₁ := hX₁
  let _ : ∀ a, LocPathConnectedSpace (B a) := hB
  let inlMap : X₁ ⟶ TopCat.of (X₁ ⊕ c.cofan₂.pt) :=
    TopCat.ofHom ⟨Sum.inl, by continuity⟩
  let inrMap : c.cofan₂.pt ⟶ TopCat.of (X₁ ⊕ c.cofan₂.pt) :=
    TopCat.ofHom ⟨Sum.inr, by continuity⟩
  let qLeft : c.cofan₁.pt ⟶ TopCat.of (X₁ ⊕ c.cofan₂.pt) := c.g₁ ≫ inlMap
  let qRight : c.cofan₁.pt ⟶ TopCat.of (X₁ ⊕ c.cofan₂.pt) := c.m ≫ inrMap
  let t : TopCat.of (X₁ ⊕ c.cofan₂.pt) ⟶ X₂ :=
    TopCat.ofHom
      { toFun := Sum.elim f c.g₂
        continuous_toFun := by
          continuity }
  have hcofork :
      CategoryTheory.Limits.IsColimit
        (Cofork.ofπ (f := qLeft) (g := qRight) t
          (by
            simpa [qLeft, qRight, t, inlMap, inrMap] using c.isPushout.w)) := by
    -- The coequalizer on the explicit sum coproduct restates the pushout universal property.
    refine CategoryTheory.Limits.Cofork.IsColimit.mk' _ ?_
    intro s
    let l : X₂ ⟶ s.pt :=
      c.isPushout.desc
        (inlMap ≫ s.π)
        (inrMap ≫ s.π)
        (by
          simpa using s.condition)
    refine ⟨l, ?_, ?_⟩
    · -- The descended map coequalizes the explicit sum map by the pushout equations.
      ext x
      cases x with
      | inl x =>
          exact ConcreteCategory.congr_hom
            (c.isPushout.inl_desc (inlMap ≫ s.π) (inrMap ≫ s.π) (by simpa using s.condition)) x
      | inr x =>
          exact ConcreteCategory.congr_hom
            (c.isPushout.inr_desc (inlMap ≫ s.π) (inrMap ≫ s.π) (by simpa using s.condition)) x
    · intro m hm
      apply c.isPushout.hom_ext
      · have hmInl : f ≫ m = inlMap ≫ s.π := by
          simpa [t, inlMap] using congrArg (fun k ↦ inlMap ≫ k) hm
        have hlInl : f ≫ l = inlMap ≫ s.π :=
          c.isPushout.inl_desc (inlMap ≫ s.π) (inrMap ≫ s.π) (by simpa using s.condition)
        exact hmInl.trans hlInl.symm
      · have hmInr : c.g₂ ≫ m = inrMap ≫ s.π := by
          simpa [t, inrMap] using congrArg (fun k ↦ inrMap ≫ k) hm
        have hlInr : c.g₂ ≫ l = inrMap ≫ s.π :=
          c.isPushout.inr_desc (inlMap ≫ s.π) (inrMap ≫ s.π) (by simpa using s.condition)
        exact hmInr.trans hlInr.symm
  have hcoprod₂ : LocPathConnectedSpace c.cofan₂.pt := by
    -- The cell coproduct is itself a colimit of the locally path connected cell spaces.
    exact locPathConnectedSpaceOfTopCatColimit c.cofan₂ c.isColimit₂ (fun i ↦ hB (c.π i.as))
  let _ : LocPathConnectedSpace (TopCat.of (X₁ ⊕ c.cofan₂.pt)) := by
    -- The pushout is a quotient of a disjoint union of locally path connected spaces.
    change LocPathConnectedSpace (X₁ ⊕ c.cofan₂.pt)
    infer_instance
  exact (TopCat.isQuotientMap_of_isColimit_cofork _ hcofork).locPathConnectedSpace

/-- Helper for Problem 15.3.2: every stage in an abstract CW complex is locally path connected. -/
private theorem abstractCwStage_locPathConnectedSpace {Y : TopCat} (hY : TopCat.CWComplex Y) :
    ∀ n : ℕ, LocPathConnectedSpace (hY.F.obj n)
  | 0 => by
      let e : hY.F.obj 0 ≅ TopCat.of PEmpty :=
        hY.isoBot ≪≫ TopCat.initialIsoPEmpty
      have hEmpty : IsEmpty (hY.F.obj 0) := by
        refine ⟨fun x ↦ ?_⟩
        exact (e.hom x).elim
      -- The initial stage is empty, hence trivially locally path connected.
      let _ : LocPathConnectedSpace (hY.F.obj 0) := by
        rw [locPathConnectedSpace_iff_isOpen_pathComponentIn]
        intro x
        exact (hEmpty.false x).elim
      infer_instance
  | n + 1 => by
      have hn : ¬ IsMax n := not_isMax_iff.mpr ⟨n + 1, Nat.lt_succ_self n⟩
      -- The successor stage is obtained by attaching `n`-disks to the previous stage.
      simpa using
        locPathConnectedSpaceOfAttachCells
          (g := TopCat.RelativeCWComplex.basicCell n) (c := hY.attachCells n hn)
          (abstractCwStage_locPathConnectedSpace hY n) (fun _ ↦ topCatDisk_locPathConnectedSpace n)

/-- Helper for Problem 15.3.2: an abstract CW-complex is locally path connected. -/
theorem locPathConnectedSpace_of_abstractCwComplex {Y : TopCat} (hY : TopCat.CWComplex Y) :
    LocPathConnectedSpace Y := by
  -- Use the abstract CW colimit witness directly instead of rebuilding a classical CW model.
  simpa using
    locPathConnectedSpaceOfTopCatColimit (c := Cocone.mk Y hY.incl) hY.isColimit
      (abstractCwStage_locPathConnectedSpace hY)

/-- Helper for Problem 15.3.2: a `K(π,1)` witness already supplies local path connectedness via
its abstract CW structure. -/
theorem locPathConnectedSpace_of_kPiOne {π : Type u} [Group π] {X : TopCat.{z}} {x : X}
    (hX : IsKPiOne π X x) : LocPathConnectedSpace X := by
  rcases hX.cwComplex with ⟨hCW⟩
  -- The `K(π,1)` data already contains the required abstract CW witness.
  exact locPathConnectedSpace_of_abstractCwComplex hCW

-- Chapter 15 already uses `IsKPiOne` as the source-facing `K(π,1)` owner. For Problem 15.3.2,
-- the source-faithful necessary condition is the explicit absence of nontrivial finite-order
-- elements in the fundamental group.

section

variable {π : Type u} [Group π]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type w} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type z} [TopologicalSpace M] [CompactSpace M] [T2Space M]
  [ChartedSpace H M] [IsManifold I 0 M]

omit [CompactSpace M] [T2Space M] in
/-- Helper for Problem 15.3.2: higher-homotopy vanishing transports across any path-connected
covering by the canonical isomorphism on `π_n` for `n > 1`. -/
theorem coveringHigherHomotopySubsingleton [ConnectedSpace M]
    {E' : Type z} [TopologicalSpace E'] (p : C(E', M))
    (hp : IsPathConnectedCoveringMap p) (u : E')
    (h_aspherical : ∀ n : ℕ, 1 < n → Subsingleton (π_ n M (p u))) :
    ∀ n : ℕ, 1 < n → Subsingleton (π_ n E' u) := by
  intro n hn
  -- For `n > 1`, a covering induces a bijection on `π_n`.
  have hbij : Function.Bijective (p.eStar n u) :=
    hp.isCoveringMap.bijective_homotopyGroupMap n (Nat.succ_le_of_lt hn) u
  have hsub : Subsingleton (π_ n M (p u)) := h_aspherical n hn
  -- Pull the target subsingleton structure back through the injective comparison map.
  refine ⟨fun a b ↦ hbij.injective (hsub.elim _ _)⟩

/-- Helper for Problem 15.3.2: once a universal cover is based over `x`, the covering-map
isomorphism on higher homotopy groups transports the asphericity hypothesis to the total space. -/
theorem universalCoverHigherHomotopySubsingleton [ConnectedSpace M] (x : M)
    {X : CategoryTheory.Over (TopCat.of M)} (hX : IsUniversalCoveringMap X.hom)
    (u : X.hom.hom ⁻¹' ({x} : Set M))
    (h_aspherical : ∀ n : ℕ, 1 < n → Subsingleton (π_ n M x)) :
    ∀ n : ℕ, 1 < n → Subsingleton (π_ n X.left u.1) := by
  intro n hn
  rcases u with ⟨u, hu⟩
  cases hu
  let p := X.hom.hom
  -- After fixing a point above `x`, the covering map induces a bijection on `π_n` for `n > 1`.
  have hbij : Function.Bijective (p.eStar n u) :=
    hX.isCoveringMap.bijective_homotopyGroupMap n (Nat.succ_le_of_lt hn) u
  -- Injectivity pulls the target subsingleton structure back to the universal cover.
  have hsub : Subsingleton (π_ n M (p u)) := by
    simpa using h_aspherical n hn
  refine ⟨fun a b ↦ hbij.injective (hsub.elim _ _)⟩

/-- Helper for Problem 15.3.2: a boundaryless finite-dimensional manifold inherits local path
connectedness from the Euclidean model space through its charts. -/
theorem compactManifold_locPathConnected
    {E' : Type v} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type w} [TopologicalSpace H'] (I' : ModelWithCorners ℝ E' H') [I'.Boundaryless]
    {M' : Type z} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 0 M'] :
    LocPathConnectedSpace M' := by
  -- The boundaryless model space is homeomorphic to the ambient vector space, hence locally
  -- path-connected.
  have hEmb := I'.toHomeomorph.isOpenEmbedding
  let _ : LocPathConnectedSpace H' :=
    hEmb.locPathConnectedSpace
  -- Once the chart model is locally path-connected, the charted space is too.
  exact ChartedSpace.locPathConnectedSpace H' M'

/-- Helper for Problem 15.3.2: every point admits an open neighborhood that is homeomorphic to an
open ball in the model vector space, hence contractible. -/
theorem compactManifold_exists_contractibleNeighborhood
    {E' : Type v} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type w} [TopologicalSpace H'] (I' : ModelWithCorners ℝ E' H') [I'.Boundaryless]
    {M' : Type z} [TopologicalSpace M'] [CompactSpace M'] [T2Space M']
    [ChartedSpace H' M'] [IsManifold I' 0 M'] (x : M') :
    ∃ U : Set M', U ∈ 𝓝 x ∧ IsOpen U ∧ ContractibleSpace U := by
  let e := (chartAt H' x).transHomeomorph I'.toHomeomorph
  let y : E' := e x
  have hxsource : x ∈ e.source := by
    exact mem_chart_source H' x
  -- Shrink the chart target to a metric ball around the chart image of `x`.
  have htarget : e.target ∈ 𝓝 y := e.open_target.mem_nhds (e.map_source hxsource)
  rcases Metric.mem_nhds_iff.mp htarget with ⟨r, hrpos, hrball⟩
  let V : Set E' := Metric.ball y r
  let U : Set M' := e.symm '' V
  have hVsubset : V ⊆ e.target := hrball
  have hUopen : IsOpen U := by
    exact e.isOpen_image_symm_of_subset_target Metric.isOpen_ball hVsubset
  have hxU : x ∈ U := by
    refine ⟨y, Metric.mem_ball_self hrpos, ?_⟩
    simpa [y] using e.left_inv hxsource
  have hUcontractible : ContractibleSpace U := by
    let hUV : V ≃ₜ U :=
      e.symm.homeomorphOfImageSubsetSource hVsubset rfl
    let _ : ContractibleSpace V := Metric.contractibleSpace_ball hrpos
    exact hUV.symm.contractibleSpace
  -- The resulting neighborhood is open, contains `x`, and is contractible.
  exact ⟨U, hUopen.mem_nhds hxU, hUopen, hUcontractible⟩

/-- Helper for Problem 15.3.2: compact boundaryless manifolds are semilocally simply connected
because each point has a contractible chart neighborhood. -/
theorem compactManifold_semilocallySimplyConnected
    {E' : Type v} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type w} [TopologicalSpace H'] (I' : ModelWithCorners ℝ E' H') [I'.Boundaryless]
    {M' : Type z} [TopologicalSpace M'] [CompactSpace M'] [T2Space M']
    [ChartedSpace H' M'] [IsManifold I' 0 M'] :
    SemilocallySimplyConnectedSpace M' := by
  refine ⟨fun x ↦ ?_⟩
  rcases compactManifold_exists_contractibleNeighborhood I' x with
    ⟨U, hUnhds, hUopen, hUcontractible⟩
  have hxU : x ∈ U := mem_of_mem_nhds hUnhds
  let Ux : TopologicalSpace.OpenNhdsOf x := ⟨⟨U, hUopen⟩, hxU⟩
  let i : C(Ux, M') := Ux.subtypeVal
  -- A contractible neighborhood has null-homotopic identity, so its inclusion is null-homotopic.
  have hnull : i.Nullhomotopic := by
    let _ : ContractibleSpace Ux := hUcontractible
    simpa using (id_nullhomotopic Ux).comp_right i
  exact ⟨Ux, hnull.fundamentalGroup_map_eq_one ⟨x, Ux.mem⟩⟩

/-- Helper for Problem 15.3.2: a nontrivial finite-order element generates a finite nontrivial
cyclic subgroup. -/
theorem torsionCyclicSubgroup_finite_nontrivial {G : Type*} [Group G] {γ : G}
    (hγ : γ ≠ 1) (hfin : IsOfFinOrder γ) :
    Finite (Subgroup.zpowers γ) ∧ Nontrivial (Subgroup.zpowers γ) := by
  constructor
  · -- Finite order makes the set of integer powers finite, hence the subgroup finite.
    exact hfin.finite_zpowers.to_subtype
  · -- The generator itself witnesses that the cyclic subgroup is not trivial.
    rw [Subgroup.nontrivial_iff_ne_bot]
    exact Subgroup.zpowers_ne_bot.2 hγ
include I

/-- Helper for Problem 15.3.2: a compact boundaryless aspherical manifold admits a universal
cover with a chosen point over `x`, and the universal cover inherits the higher-homotopy
subsingleton property at that point. -/
theorem compactManifoldUniversalCoverData [ConnectedSpace M] (x : M)
    (h_aspherical : ∀ n : ℕ, 1 < n → Subsingleton (π_ n M x)) :
    ∃ (X : CategoryTheory.Over (TopCat.of M)) (u : X.left), X.hom u = x ∧
      IsUniversalCoveringMap X.hom ∧
        ∀ n : ℕ, 1 < n → Subsingleton (π_ n X.left u) := by
  let _ : LocPathConnectedSpace M := compactManifold_locPathConnected I
  let _ : SemilocallySimplyConnectedSpace M := compactManifold_semilocallySimplyConnected I
  -- Choose a universal covering object and then choose one lift above the basepoint `x`.
  rcases exists_universalCoveringMap (B := M) with ⟨X, hX⟩
  rcases hX.surjective x with ⟨u, hu⟩
  have hu' : u ∈ X.hom.hom ⁻¹' ({x} : Set M) := by
    simpa [Set.mem_preimage, Set.mem_singleton_iff] using hu
  -- The previously established covering-space isomorphism on `π_n` transports the asphericity
  -- hypothesis upstairs.
  refine ⟨X, u, hu, hX, ?_⟩
  simpa using universalCoverHigherHomotopySubsingleton x hX ⟨u, hu'⟩ h_aspherical

omit I

/-- Helper for Problem 15.3.2: a multiplicative equivalence preserves finite-order elements in
both directions. -/
theorem isOfFinOrder_mulEquiv_iff {G H : Type*} [Group G] [Group H] (e : G ≃* H) {g : G} :
    IsOfFinOrder (e g) ↔ IsOfFinOrder g := by
  constructor
  · -- Pull a finite-order witness back along the inverse equivalence.
    intro hg
    simpa using e.symm.toMonoidHom.isOfFinOrder hg
  · -- Push a finite-order witness forward along the equivalence.
    intro hg
    exact e.toMonoidHom.isOfFinOrder hg

/-- Helper for Problem 15.3.2: a deck transformation of a universal cover that fixes one point is
already the identity. -/
theorem coveringSpaceAut_eq_one_of_fixedPoint
    {B : Type u} [TopologicalSpace B] {E' : Type u} [TopologicalSpace E']
    [LocPathConnectedSpace E'] {p : C(E', B)} (hp : IsUniversalCoveringMap p) (u y : E')
    {α : CoveringSpaceAut p} (hfix : α • y = y) : α = 1 := by
  let eγ := IsUniversalCoveringMap.coveringSpaceAutMulEquivFundamentalGroup hp u
  -- Local instance justification (canonical deck action): the freeness of the universal-cover
  -- deck action is packaged as `IsCancelSMul`, and `eq_one_of_smul` consumes that instance.
  letI : IsCancelSMul (FundamentalGroup B (p u)) E' :=
    IsUniversalCoveringMap.universalCoverDeck_isCancelSMul (p := p) (hp := hp) u
  -- Transport the fixed-point equation through the deck/fundamental-group identification.
  have hdeck : eγ α • y = y := by
    simpa [eγ, IsUniversalCoveringMap.universalCoverDeck_smul_def (p := p) (hp := hp)] using hfix
  have hγ : eγ α = 1 := IsCancelSMul.eq_one_of_smul hdeck
  -- Injectivity of the deck/fundamental-group equivalence brings the identity back to `α`.
  apply eγ.injective
  simpa using hγ

/-- Helper for Problem 15.3.2: every covering-space automorphism acts on the total space by a
self-homeomorphism. -/
noncomputable def coveringSpaceAutHomeomorph
    {B : Type u} [TopologicalSpace B] {E' : Type u} [TopologicalSpace E']
    {p : C(E', B)} (α : CoveringSpaceAut p) :
    E' ≃ₜ E' :=
  TopCat.homeoOfIso
    { hom := α.hom.left
      inv := α.inv.left
      hom_inv_id := CategoryTheory.Over.hom_left_inv_left α
      inv_hom_id := CategoryTheory.Over.inv_left_hom_left α }

/-- Helper for Problem 15.3.2: the homeomorphism underlying a deck transformation evaluates by
the same formula as the deck action. -/
@[simp] theorem coveringSpaceAutHomeomorph_apply
    {B : Type u} [TopologicalSpace B] {E' : Type u} [TopologicalSpace E']
    {p : C(E', B)} (α : CoveringSpaceAut p) (x : E') :
    coveringSpaceAutHomeomorph α x = α • x := by
  rfl

/-- Helper for Problem 15.3.2: deck transformations act on the total space through the induced
permutation of the underlying type. -/
noncomputable def coveringSpaceAutToPerm
    {B : Type u} [TopologicalSpace B] {E' : Type u} [TopologicalSpace E']
    {p : C(E', B)} :
    CoveringSpaceAut p →* Equiv.Perm E' where
  toFun α := (coveringSpaceAutHomeomorph α).toEquiv
  map_one' := by
    -- The identity deck transformation induces the identity permutation.
    ext x
    rfl
  map_mul' β γ := by
    -- Composition in `CoveringSpaceAut p` becomes composition of the induced permutations.
    ext x
    rfl

/-- Helper for Problem 15.3.2: finite order survives after passing from a deck transformation to
its underlying permutation of the total space. -/
theorem isOfFinOrder_coveringSpaceAutHomeomorph_toEquiv
    {B : Type u} [TopologicalSpace B] {E' : Type u} [TopologicalSpace E']
    {p : C(E', B)} {α : CoveringSpaceAut p} (hfin : IsOfFinOrder α) :
    IsOfFinOrder (coveringSpaceAutHomeomorph α).toEquiv := by
  -- Apply the induced permutation homomorphism once, then reuse the transported finite-order
  -- witness in the homeomorphism theorem.
  exact MonoidHom.isOfFinOrder (coveringSpaceAutToPerm (p := p)) hfin

/-- Helper for Problem 15.3.2: a nontrivial finite-order element has a nontrivial prime-order
power. -/
theorem existsPrimeOrderPower_of_isOfFinOrder {G : Type*} [Group G] {g : G}
    (hfin : IsOfFinOrder g) (hne : g ≠ 1) :
    ∃ p k : ℕ, Fact p.Prime ∧
      let β := g ^ k
      β ^ p = 1 ∧ β ≠ 1 := by
  have horder_pos : 0 < orderOf g := hfin.orderOf_pos
  have horder_ne_one : orderOf g ≠ 1 := by
    intro horder
    apply hne
    exact orderOf_eq_one_iff.mp horder
  have horder_ne_zero : orderOf g ≠ 0 := horder_pos.ne'
  obtain ⟨p, hp, hpdvd⟩ := Nat.ne_one_iff_exists_prime_dvd.mp horder_ne_one
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨p, orderOf g / p, inferInstance, ?_⟩
  -- The canonical power `g^(|g|/p)` has order exactly `p`, so it is the required prime-order
  -- witness.
  dsimp
  have hβord : orderOf (g ^ (orderOf g / p)) = p :=
    orderOf_pow_orderOf_div horder_ne_zero hpdvd
  exact orderOf_eq_prime_iff.mp hβord

/-- Helper for Problem 15.3.2: a finite nontrivial subgroup of the deck group of a universal
cover contains a nontrivial deck transformation of prime order. -/
theorem existsPrimeOrderDeckAut_of_finiteNontrivialSubgroup [ConnectedSpace M]
    {E' : Type z} [TopologicalSpace E'] [LocPathConnectedSpace E'] (p : C(E', M)) (u : E')
    (hp : IsUniversalCoveringMap p)
    (K : Subgroup (FundamentalGroup M (p u))) [Finite K] [Nontrivial K] :
    ∃ q : ℕ, Fact q.Prime ∧ ∃ α : CoveringSpaceAut p, α ^ q = 1 ∧ α ≠ 1 := by
  let eγ := IsUniversalCoveringMap.coveringSpaceAutMulEquivFundamentalGroup hp u
  obtain ⟨δ, hδ⟩ := exists_ne (1 : K)
  have hδfin : IsOfFinOrder δ := isOfFinOrder_of_finite δ
  obtain ⟨q, k, hq, hβpow, hβne⟩ :=
    existsPrimeOrderPower_of_isOfFinOrder hδfin hδ
  let β : K := δ ^ k
  let α : CoveringSpaceAut p := eγ.symm β
  have hβpow' : (β : FundamentalGroup M (p u)) ^ q = 1 := by
    -- Coerce the prime-order relation from the subgroup `K` back to the ambient deck group.
    simpa [β] using congrArg (fun x : K ↦ (x : FundamentalGroup M (p u))) hβpow
  have hβne' : (β : FundamentalGroup M (p u)) ≠ 1 := by
    -- The chosen prime-order element stays nontrivial after forgetting membership in `K`.
    intro hβ
    apply hβne
    exact Subtype.ext hβ
  refine ⟨q, hq, α, ?_, ?_⟩
  · -- Apply the deck/fundamental-group equivalence to reduce the power identity to `K`.
    apply eγ.injective
    simpa [α] using hβpow'
  · -- Nontriviality also transports back across the same equivalence.
    intro hα
    apply hβne'
    simpa [α] using congrArg eγ hα
include I

/-- Helper for Problem 15.3.2: the orbit cover attached to a subgroup of the deck group realizes
that subgroup as the fundamental group at the canonical orbit point. -/
theorem subgroupCoverFundamentalGroupIso [ConnectedSpace M]
    {E' : Type z} [TopologicalSpace E'] [LocPathConnectedSpace E'] (p : C(E', M)) (u : E')
    (hp : IsUniversalCoveringMap p)
    (K : Subgroup (FundamentalGroup M (p u))) :
    Nonempty
      (FundamentalGroup (IsUniversalCoveringMap.universalCoverOrbit u K)
          (IsUniversalCoveringMap.universalCoverOrbitPoint u K) ≃* K) := by
  letI : IsUniversalCoveringMap p := hp
  letI : LocPathConnectedSpace M := compactManifold_locPathConnected I
  letI : PathConnectedSpace E' := hp.pathConnectedSpace
  let q : C(IsUniversalCoveringMap.universalCoverOrbit u K, M) :=
    IsUniversalCoveringMap.universalCoverOrbitProjection u K
  let y : IsUniversalCoveringMap.universalCoverOrbit u K :=
    IsUniversalCoveringMap.universalCoverOrbitPoint u K
  let f : FundamentalGroup (IsUniversalCoveringMap.universalCoverOrbit u K) y →*
      FundamentalGroup M (q y) :=
    FundamentalGroup.map q y
  have hf_inj : Function.Injective f := by
    -- The orbit projection is still a covering map, so its induced map on `π₁` is injective.
    simpa [f, q] using
      (IsPathConnectedCoveringMap.isCoveringMap
        (p := q) (inferInstance : IsPathConnectedCoveringMap q)).fundamentalGroup_map_injective y
  have hrange : f.range = K := by
    -- Chapter 3 already computes the associated subgroup of the canonical orbit cover.
    simpa [f, q, y] using
      (IsUniversalCoveringMap.universalCoverOrbitProjection_associatedSubgroup_eq
        (p := p) u K)
  let fRange : FundamentalGroup (IsUniversalCoveringMap.universalCoverOrbit u K) y →* f.range :=
    f.codRestrict f.range (fun γ ↦ ⟨γ, rfl⟩)
  have hfRange_bij : Function.Bijective fRange := by
    constructor
    · -- Injectivity is inherited from the covering-space map `f`.
      intro a b hab
      apply hf_inj
      exact congrArg Subtype.val hab
    · -- Surjectivity is tautological because the codomain is the image subgroup.
      intro g
      rcases g.2 with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      ext
      exact ha
  -- Package the image identification and then rewrite the image subgroup to the prescribed `K`.
  exact ⟨(MulEquiv.ofBijective fRange hfRange_bij).trans (MulEquiv.subgroupCongr hrange)⟩

/-- Helper for Problem 15.3.2: the canonical orbit cover of a universal cover inherits the
vanishing of higher homotopy groups from the aspherical base. -/
theorem orbitCoverHigherHomotopySubsingleton [ConnectedSpace M]
    {E' : Type z} [TopologicalSpace E'] [LocPathConnectedSpace E'] (p : C(E', M)) (u : E')
    (hp : IsUniversalCoveringMap p)
    (K : Subgroup (FundamentalGroup M (p u)))
    (h_aspherical : ∀ n : ℕ, 1 < n → Subsingleton (π_ n M (p u))) :
    ∀ n : ℕ, 1 < n →
      Subsingleton
        (π_ n (IsUniversalCoveringMap.universalCoverOrbit u K)
          (IsUniversalCoveringMap.universalCoverOrbitPoint u K)) := by
  letI : IsUniversalCoveringMap p := hp
  -- Local instance justification (covering total-space topology): the orbit-cover API is stated
  -- for locally path-connected total spaces, so we first recover that structure on the compact
  -- manifold base and then lift it along the universal covering map `p`.
  let _ : LocPathConnectedSpace M := compactManifold_locPathConnected I
  let q : C(IsUniversalCoveringMap.universalCoverOrbit u K, M) :=
    IsUniversalCoveringMap.universalCoverOrbitProjection u K
  let y0 : IsUniversalCoveringMap.universalCoverOrbit u K :=
    IsUniversalCoveringMap.universalCoverOrbitPoint u K
  intro n hn
  -- The orbit projection is again a path-connected covering, so higher homotopy groups agree in
  -- every degree `n > 1`.
  simpa [q, y0] using
    coveringHigherHomotopySubsingleton (M := M) q
      (inferInstance : IsPathConnectedCoveringMap q) y0
      (fun m hm ↦ by simpa [q, y0] using h_aspherical m hm) n hn

/-- Helper for Problem 15.3.2: the fundamental group of the canonical orbit cover is finite and
nontrivial whenever the chosen subgroup `K ≤ π₁(M, p u)` is finite and nontrivial. -/
theorem orbitCoverFundamentalGroupFiniteNontrivial [ConnectedSpace M]
    {E' : Type z} [TopologicalSpace E'] [LocPathConnectedSpace E'] (p : C(E', M)) (u : E')
    (hp : IsUniversalCoveringMap p)
    (K : Subgroup (FundamentalGroup M (p u))) [Finite K] [Nontrivial K] :
    Finite
        (FundamentalGroup (IsUniversalCoveringMap.universalCoverOrbit u K)
          (IsUniversalCoveringMap.universalCoverOrbitPoint u K)) ∧
      Nontrivial
        (FundamentalGroup (IsUniversalCoveringMap.universalCoverOrbit u K)
          (IsUniversalCoveringMap.universalCoverOrbitPoint u K)) := by
  letI : IsUniversalCoveringMap p := hp
  -- Local instance justification (covering total-space topology): the subgroup-cover
  -- fundamental-group identification is formulated for locally path-connected total spaces, and
  -- the universal covering map `p` lifts that structure from the compact manifold base.
  let _ : LocPathConnectedSpace M := compactManifold_locPathConnected I
  let e :
      FundamentalGroup (IsUniversalCoveringMap.universalCoverOrbit u K)
          (IsUniversalCoveringMap.universalCoverOrbitPoint u K) ≃* K :=
    Classical.choice (subgroupCoverFundamentalGroupIso (I := I) (M := M) p u hp K)
  constructor
  · -- Transport finiteness back across the subgroup-cover fundamental-group equivalence.
    exact Finite.of_equiv K e.toEquiv.symm
  · -- Nontriviality is likewise preserved by multiplicative equivalence.
    exact e.toEquiv.nontrivial

/-- Helper for Problem 15.3.2: the universal cover of a compact boundaryless aspherical manifold is
weakly contractible in the explicit sense that every based homotopy group vanishes. -/
theorem universalCoverHomotopySubsingleton_of_compactManifoldAspherical [ConnectedSpace M]
    {E' : Type z} [TopologicalSpace E'] (p : C(E', M)) (u : E')
    (hp : IsUniversalCoveringMap p)
    (h_aspherical : ∀ n : ℕ, 1 < n → Subsingleton (π_ n M (p u))) :
    ∀ n : ℕ, Subsingleton (π_ n E' u) := by
  intro n
  cases n with
  | zero =>
      -- Degree `0` vanishes because the universal cover is simply connected, hence path connected.
      let _ : SimplyConnectedSpace E' := hp.toSimplyConnectedSpace
      let _ : NConnectedSpace 1 E' := NConnectedSpace.of_simplyConnectedSpace (X := E')
      let _ : NConnectedSpace 0 E' :=
        NConnectedSpace.of_le (X := E') (n := 1) (q := 0) (by simp)
      simpa using (show Subsingleton (π_ 0 E' u) from inferInstance)
  | succ n =>
      cases n with
      | zero =>
          -- Degree `1` is the defining fundamental-group part of simple connectedness.
          let _ : SimplyConnectedSpace E' := hp.toSimplyConnectedSpace
          let _ : NConnectedSpace 1 E' := NConnectedSpace.of_simplyConnectedSpace (X := E')
          simpa using (show Subsingleton (π_ 1 E' u) from inferInstance)
      | succ k =>
          -- In all higher degrees, coverings preserve the homotopy groups of the base.
          simpa using
            coveringHigherHomotopySubsingleton (M := M) p hp.isPathConnectedCoveringMap u
              h_aspherical (k + 2) (by omega)

/-- Helper for Problem 15.3.2: a weak equivalence pulls subsingleton homotopy groups back along the
induced map on `π_ n`. -/
theorem homotopyGroupSubsingleton_of_weakEquivalence
    {Y : Type*} [TopologicalSpace Y] {Z : Type*} [TopologicalSpace Z]
    (e : C(Y, Z)) (n : ℕ) (y : Y)
    (hsub : Subsingleton (π_ n Z (e y))) [IsWeakEquivalence e] :
    Subsingleton (π_ n Y y) := by
  have hbij : Function.Bijective (e.eStar n y) :=
    (show IsNEquivalence (n + 1) e from inferInstance).bijective y (Nat.lt_succ_self n)
  -- Injectivity of the weak-equivalence comparison map pulls the triviality of `π_ n` back to
  -- the source.
  exact ⟨fun a b ↦ hbij.injective (hsub.elim _ _)⟩

/-- Helper for Problem 15.3.2: if every based homotopy group of both source and target is
subsingleton, then any continuous map between them is automatically a weak equivalence. -/
theorem isWeakEquivalence_of_allHomotopyGroupsSubsingleton
    {Y : Type*} [TopologicalSpace Y] {Z : Type*} [TopologicalSpace Z]
    (e : C(Y, Z))
    (hY : ∀ y : Y, ∀ n : ℕ, Subsingleton (π_ n Y y))
    (hZ : ∀ z : Z, ∀ n : ℕ, Subsingleton (π_ n Z z)) :
    IsWeakEquivalence e := by
  constructor
  intro n
  refine ⟨?_, ?_⟩
  · intro y q hq a b hab
    -- Injectivity is vacuous because the source homotopy group already has one element.
    exact (hY y q).elim a b
  · intro y q hq z
    -- Surjectivity is equally vacuous because every target homotopy group is already trivial.
    refine ⟨(⟦(GenLoop.const : Ω^ (Fin q) Y y)⟧ : π_ q Y y), ?_⟩
    exact (hZ (e y) q).elim _ _

/-- Helper for Problem 15.3.2: if all based homotopy groups of `X` are subsingleton, then the
constant map `X ⟶ Unit` is a weak equivalence. -/
theorem constUnit_isWeakEquivalence_of_allHomotopyGroupsSubsingleton
    {X : Type u} [TopologicalSpace X]
    (hπ : ∀ x : X, ∀ n : ℕ, Subsingleton (π_ n X x)) :
    IsWeakEquivalence (ContinuousMap.const X ()) := by
  constructor
  intro n
  refine ⟨?_, ?_⟩
  · intro x q hq a b
    -- Injectivity is immediate because the source homotopy group is already trivial.
    exact fun hab ↦ (hπ x q).elim a b
  · intro x q hq z
    refine ⟨(⟦(GenLoop.const : Ω^ (Fin q) X x)⟧ : π_ q X x), ?_⟩
    -- Surjectivity follows because every homotopy group of `Unit` is already trivial.
    let hUnit : Subsingleton (π_ q Unit (((ContinuousMap.const X ()) x))) := by
      simpa using
        homotopyGroup_subsingleton_of_contractible q (((ContinuousMap.const X ()) x)
          : Unit)
    exact hUnit.elim _ _

/-- Helper for Problem 15.3.2: a classical CW complex with trivial homotopy groups at every
basepoint is contractible. -/
theorem classicalCwContractible_of_allHomotopyGroupsSubsingleton
    {X : Type u} [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)]
    (hπ : ∀ x : X, ∀ n : ℕ, Subsingleton (π_ n X x)) :
    ContractibleSpace X := by
  -- This is the classical Whitehead consequence for a weakly contractible CW complex.  Keep the
  -- theorem at its source-faithful level; the previous term accidentally inherited unrelated
  -- manifold model parameters from the surrounding section and therefore did not elaborate.
  sorry

/-- Helper for Problem 15.3.2: once one basepoint of the universal cover has trivial homotopy
groups, the same is true at every basepoint. -/
theorem universalCoverAllBasepointHomotopySubsingleton_of_compactManifoldAspherical
    [ConnectedSpace M] {E' : Type z} [TopologicalSpace E'] (p : C(E', M)) (u : E')
    (hp : IsUniversalCoveringMap p)
    (h_aspherical : ∀ n : ℕ, 1 < n → Subsingleton (π_ n M (p u))) :
    ∀ v : E', ∀ n : ℕ, Subsingleton (π_ n E' v) := by
  intro v n
  let _ : PathConnectedSpace E' := hp.pathConnectedSpace
  let β : Path u v := PathConnectedSpace.somePath u v
  letI : LocallyCompactSpace M := inferInstance
  letI : CompactlyGeneratedWeakHausdorffSpace.{z, z} M :=
    instCompactlyGeneratedWeakHausdorffSpaceOfLocallyCompact
  have h_aspherical_v :
      ∀ k : ℕ, 1 < k → Subsingleton (π_ k M (p v)) := by
    intro k hk
    let _ : Subsingleton (π_ k M (p u)) := h_aspherical k hk
    exact homotopyGroupSubsingleton_of_path k (β.map p.continuous)
  -- Apply the chosen-basepoint universal-cover argument directly at `v`; only the base
  -- homotopy groups need transport, and the compact manifold is a May space.
  exact universalCoverHomotopySubsingleton_of_compactManifoldAspherical
    (E := E) (H := H) (I := I) (M := M) p v hp h_aspherical_v n

/-- Helper for Problem 15.3.2: a classical CW complex with exactly one `0`-cell has singleton
`0`-skeleton. -/
noncomputable abbrev zeroSkeletonUnique_of_singleZeroCell
    {X : Type u} [TopologicalSpace X]
    (cw : Topology.CWComplex (Set.univ : Set X))
    (h0 : Nat.card (cw.cell 0) = 1) :
    Unique (Topology.CWComplex.skeleton (Set.univ : Set X) 0) := by
  letI : Topology.CWComplex (Set.univ : Set X) := cw
  let _ : T2Space X := inferInstance
  rcases Nat.card_eq_one_iff_unique.mp h0 with ⟨hsub, hnonempty⟩
  letI : Unique (cw.cell 0) :=
    ⟨⟨Classical.choice hnonempty⟩, fun a ↦ hsub.elim a _⟩
  refine ⟨⟨Topology.RelCWComplex.map (C := (Set.univ : Set X)) 0 default ![], ?_⟩, ?_⟩
  · -- The chosen `0`-cell point lies in the `0`-skeleton by the standard closed-cell inclusion.
    exact Topology.CWComplex.closedCell_subset_skeleton (C := (Set.univ : Set X)) 0 default (by
      rw [Topology.CWComplex.closedCell_zero_eq_singleton]
      simp)
  · intro x
    apply Subtype.ext
    have hx : x.1 ∈ (Topology.CWComplex.skeletonLT (Set.univ : Set X) 1 : Set X) := by
      simpa using x.2
    -- Every point of the `0`-skeleton lies in some open `0`-cell, and there is only one such
    -- cell index.
    rw [← Topology.CWComplex.iUnion_openCell_eq_skeletonLT (C := (Set.univ : Set X))
      (n := (1 : ℕ∞))] at hx
    rcases Set.mem_iUnion.mp hx with ⟨m, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hm, hx⟩
    have hm' : m < 1 := (ENat.coe_lt_coe).mp hm
    have hm0 : m = 0 := Nat.lt_one_iff.mp hm'
    subst hm0
    rcases Set.mem_iUnion.mp hx with ⟨j, hxj⟩
    have hj : j = default := Subsingleton.elim _ _
    subst hj
    rw [Topology.CWComplex.openCell_zero_eq_singleton] at hxj
    simpa using hxj

/-- Helper for Problem 15.3.2: a classical CW complex with exactly one `0`-cell is nonempty. -/
theorem nonempty_of_singleZeroCell
    {X : Type*} [TopologicalSpace X]
    (cw : Topology.CWComplex (Set.univ : Set X))
    (h0 : Nat.card (cw.cell 0) = 1) :
    Nonempty X := by
  let _ : Topology.CWComplex (Set.univ : Set X) := cw
  rcases Nat.card_eq_one_iff_unique.mp h0 with ⟨_, hcell_nonempty⟩
  let j : Topology.CWComplex.cell (Set.univ : Set X) 0 := Classical.choice hcell_nonempty
  -- Evaluating the unique `0`-cell map at the disk center produces a point of the space.
  exact ⟨Topology.CWComplex.map (C := (Set.univ : Set X)) 0 j ![]⟩

/-- Helper for Problem 15.3.2: the prime-order deck witness extracted from a finite subgroup
already has the exact fixed-point shape needed in the direct `K(π, 1)` contradiction, provided
the universal cover is weakly contractible at every basepoint. -/
theorem primeOrderDeckTransformation_hasFixedPoint_of_weaklyContractibleUniversalCover
    [ConnectedSpace M] {E' : Type z} [TopologicalSpace E']
    {p : C(E', M)} (hp : IsUniversalCoveringMap p) {q : ℕ} [Fact q.Prime]
    {α : CoveringSpaceAut p} (hαpow : α ^ q = 1)
    (hWeak : ∀ y : E', ∀ n : ℕ, Subsingleton (π_ n E' y)) :
    ∃ y : E', α • y = y := by
  have hαperm : (coveringSpaceAutHomeomorph α).toEquiv ^ q = 1 := by
    -- Transport the prime-order relation from the deck group to the underlying homeomorphism.
    simpa using congrArg (coveringSpaceAutToPerm (p := p)) hαpow
  -- TODO: the file no longer keeps the dead contractibility/CW branch alive. The remaining blocker
  -- is exactly the prime-order fixed-point primitive: either a named theorem saying that a
  -- prime-order self-homeomorphism of a weakly contractible manifold has a fixed point, or the
  -- planned orbit-cover contradiction replacing this step altogether.
  let _ : (coveringSpaceAutHomeomorph α).toEquiv ^ q = 1 := hαperm
  let _ : ∀ y : E', ∀ n : ℕ, Subsingleton (π_ n E' y) := hWeak
  sorry

/-- Helper for Problem 15.3.2: on the chosen universal cover of a compact manifold `K(π, 1)`,
no nontrivial prime-order deck transformation can survive. -/
theorem nontrivialPrimeOrderDeckAut_not_of_compactManifoldKPiOne (x : M)
    [hM : IsKPiOne π (TopCat.of M) x]
    {E' : Type z} [TopologicalSpace E'] (p : C(E', M)) (u : E') (hu : p u = x)
    (hp : IsUniversalCoveringMap p) {q : ℕ} [Fact q.Prime] {α : CoveringSpaceAut p}
    (hαpow : α ^ q = 1) (hαne : α ≠ 1) :
    False := by
  -- Route correction: the contradiction happens directly on the chosen universal cover, without
  -- normalizing through an orbit cover or a stronger arbitrary-aspherical theorem.
  let _ : ConnectedSpace M := hM.toConnectedSpace
  let _ : LocPathConnectedSpace M := compactManifold_locPathConnected I
  let _ : LocPathConnectedSpace E' :=
    IsUniversalCoveringMap.IsPathConnectedCoveringMap.locPathConnectedSpace_totalSpace
      (B := M) hp.isPathConnectedCoveringMap
  have hWeak : ∀ y : E', ∀ n : ℕ, Subsingleton (π_ n E' y) := by
    -- Reuse the already stabilized universal-cover weak-contractibility frontier directly.
    have hHigher : ∀ n : ℕ, 1 < n → Subsingleton (π_ n M (p u)) := by
      intro n hn
      simpa [hu] using hM.higherHomotopySubsingleton n hn
    exact
      universalCoverAllBasepointHomotopySubsingleton_of_compactManifoldAspherical
        (E := E) (H := H) (I := I) (M := M) p u hp hHigher
  obtain ⟨y, hfix⟩ :=
    primeOrderDeckTransformation_hasFixedPoint_of_weaklyContractibleUniversalCover
      (E := E) (H := H) (I := I) (M := M) (p := p) (q := q) (α := α) hp hαpow hWeak
  -- A fixed point forces a deck transformation of a universal cover to be trivial.
  exact hαne (coveringSpaceAut_eq_one_of_fixedPoint hp u y hfix)

/-- Helper for Problem 15.3.2: the remaining obstruction is the finite nontrivial subgroup of the
deck group acting on the weakly contractible universal cover. -/
theorem finiteNontrivialOrbitSubgroup_not_of_compactManifoldAspherical
    [ConnectedSpace M] {E' : Type z} [TopologicalSpace E'] (p : C(E', M)) (u : E')
    (hp : IsUniversalCoveringMap p)
    (K : Subgroup (FundamentalGroup M (p u))) [Finite K] [Nontrivial K]
    (h_aspherical : ∀ n : ℕ, 1 < n → Subsingleton (π_ n M (p u))) :
    False := by
  -- Route correction: the orbit-cover normalization was not the real endgame. The contradiction
  -- lives on the universal cover itself, where a finite subgroup yields a nontrivial prime-order
  -- deck transformation.
  -- Local instance justification (covering total-space topology): the deck-group equivalence and
  -- the freeness theorem are stated for locally path-connected total spaces, so we recover that
  -- instance from the universal-cover hypothesis once here.
  let _ : LocPathConnectedSpace M := compactManifold_locPathConnected I
  let _ : LocPathConnectedSpace E' :=
    IsUniversalCoveringMap.IsPathConnectedCoveringMap.locPathConnectedSpace_totalSpace
      (B := M) hp.isPathConnectedCoveringMap
  obtain ⟨q, _hq, α, hαpow, hαne⟩ :=
    existsPrimeOrderDeckAut_of_finiteNontrivialSubgroup
      (M := M) p u hp K
  have hWeak : ∀ y : E', ∀ n : ℕ, Subsingleton (π_ n E' y) :=
    universalCoverAllBasepointHomotopySubsingleton_of_compactManifoldAspherical
      (E := E) (H := H) (I := I) (M := M) p u hp h_aspherical
  obtain ⟨y, hfix⟩ :=
    primeOrderDeckTransformation_hasFixedPoint_of_weaklyContractibleUniversalCover
      (E := E) (H := H) (I := I) (M := M) (p := p) (q := q) (α := α) hp hαpow hWeak
  -- A fixed point forces a deck transformation of a universal cover to be the identity, which
  -- contradicts the chosen nontrivial element.
  exact hαne (coveringSpaceAut_eq_one_of_fixedPoint hp u y hfix)

/-- Helper for Problem 15.3.2: the remaining content is to show that the fundamental group of a
compact aspherical manifold has no nontrivial finite-order element. -/
theorem fundamentalGroup_isMulTorsionFree_of_compactManifoldAspherical [ConnectedSpace M] (x : M)
    (h_aspherical : ∀ n : ℕ, 1 < n → Subsingleton (π_ n M x)) :
    ∀ ⦃γ : FundamentalGroup M x⦄, γ ≠ 1 → ¬ IsOfFinOrder γ := by
  intro γ hγ hfin
  -- Route correction: replace the dead prime-order fixed-point branch by the subgroup-cover
  -- obstruction attached to the finite cyclic subgroup generated by `γ`.
  rcases compactManifoldUniversalCoverData (E := E) (H := H) (I := I) (M := M) x h_aspherical with
    ⟨X, u, hu, hX, _hHigher⟩
  subst x
  let p : C(X.left, M) := CategoryTheory.ConcreteCategory.hom X.hom
  have hp : IsUniversalCoveringMap p := by
    simpa [p] using hX
  let K : Subgroup (FundamentalGroup M (p u)) := Subgroup.zpowers γ
  have hK : Finite K ∧ Nontrivial K :=
    torsionCyclicSubgroup_finite_nontrivial hγ hfin
  let _ : Finite K := hK.1
  let _ : Nontrivial K := hK.2
  -- The remaining contradiction is now concentrated in the finite subgroup orbit cover.
  exact
    finiteNontrivialOrbitSubgroup_not_of_compactManifoldAspherical
      (E := E) (H := H) (I := I) (M := M) p u hp K h_aspherical

/-- Bridge form of Problem 15.3.2 stated directly with a fundamental-group identification and
vanishing higher homotopy groups. -/
theorem isMulTorsionFree_of_compactManifold_fundamentalGroup [ConnectedSpace M] (x : M)
    (hπ : Nonempty (FundamentalGroup M x ≃* π))
    (h_aspherical : ∀ n : ℕ, 1 < n → Subsingleton (π_ n M x)) :
    ∀ ⦃γ : π⦄, γ ≠ 1 → ¬ IsOfFinOrder γ := by
  rcases hπ with ⟨e⟩
  intro γ hγ hfin
  -- Transport the problem back to `FundamentalGroup M x`, where the main theorem applies.
  have hpre_ne : e.symm γ ≠ 1 := by
    intro hpre
    apply hγ
    simpa using congrArg e hpre
  have hpre_fin : IsOfFinOrder (e.symm γ) := by
    exact (isOfFinOrder_mulEquiv_iff e.symm).2 hfin
  have hcore : ∀ ⦃δ : FundamentalGroup M x⦄, δ ≠ 1 → ¬ IsOfFinOrder δ :=
    fundamentalGroup_isMulTorsionFree_of_compactManifoldAspherical
      (E := E) (H := H) (I := I) (M := M) x h_aspherical
  exact hcore hpre_ne hpre_fin

/-- Problem 15.3.2: if a group `π` is realized as the fundamental group of a compact manifold
of type `K(π, 1)`, then `π` is torsion-free. -/
theorem isMulTorsionFree_of_compactManifold_kPiOne (x : M)
    [hM : IsKPiOne π (TopCat.of M) x] : ∀ ⦃γ : π⦄, γ ≠ 1 → ¬ IsOfFinOrder γ := by
  -- Route correction: work on one chosen universal cover over `x` and extract a prime-order deck
  -- transformation directly, instead of routing the proof through the stronger aspherical bridge.
  let _ : ConnectedSpace M := hM.toConnectedSpace
  let _ : LocPathConnectedSpace M := locPathConnectedSpace_of_kPiOne hM
  rcases compactManifoldUniversalCoverData (E := E) (H := H) (I := I) (M := M)
      x hM.higherHomotopySubsingleton with
    ⟨X, u, hu, hX, _hHigher⟩
  subst x
  let p : C(X.left, M) := CategoryTheory.ConcreteCategory.hom X.hom
  have hp : IsUniversalCoveringMap p := by
    simpa [p] using hX
  let _ : LocPathConnectedSpace X.left :=
    IsUniversalCoveringMap.IsPathConnectedCoveringMap.locPathConnectedSpace_totalSpace
      (B := M) hp.isPathConnectedCoveringMap
  rcases hM.fundamentalGroupIso with ⟨e⟩
  intro γ hγ hfin
  -- Transport the torsion witness from `π` back to the actual deck group of the chosen cover.
  have hpre_ne : e.symm γ ≠ 1 := by
    intro hpre
    apply hγ
    simpa using congrArg e hpre
  have hpre_fin : IsOfFinOrder (e.symm γ) := by
    exact (isOfFinOrder_mulEquiv_iff e.symm).2 hfin
  let K : Subgroup (FundamentalGroup M (p u)) := Subgroup.zpowers (e.symm γ)
  have hK : Finite K ∧ Nontrivial K :=
    torsionCyclicSubgroup_finite_nontrivial hpre_ne hpre_fin
  let _ : Finite K := hK.1
  let _ : Nontrivial K := hK.2
  -- The finite cyclic subgroup yields a nontrivial prime-order deck transformation.
  obtain ⟨q, hq, α, hαpow, hαne⟩ :=
    existsPrimeOrderDeckAut_of_finiteNontrivialSubgroup
      (M := M) p u hp K
  let _ : Fact q.Prime := hq
  -- The direct universal-cover contradiction now closes the torsion argument.
  exact
    nontrivialPrimeOrderDeckAut_not_of_compactManifoldKPiOne
      (E := E) (H := H) (I := I) (M := M) (π := π) (x := p u) p u rfl hp hαpow hαne

namespace IsKPiOne

/-- A compact manifold `K(π, 1)` witness forces `π` to be torsion-free. -/
theorem isMulTorsionFreeOfCompactManifold {x : M} (hM : IsKPiOne π (TopCat.of M) x) :
    ∀ ⦃γ : π⦄, γ ≠ 1 → ¬ IsOfFinOrder γ := by
  -- Reuse the pointwise theorem with the supplied `K(π, 1)` witness.
  let _ : IsKPiOne π (TopCat.of M) x := hM
  let _ : ConnectedSpace M := hM.toConnectedSpace
  have htorsion : ∀ ⦃γ : π⦄, γ ≠ 1 → ¬ IsOfFinOrder γ :=
    isMulTorsionFree_of_compactManifold_kPiOne
      (E := E) (H := H) (I := I) (M := M) (π := π) x
  exact htorsion

end IsKPiOne

end
