module

public import Topology_Munkres_2000.Book.Corollary_50_3
public import Topology_Munkres_2000.Book.Example_50_2
public import Topology_Munkres_2000.Book.Example_50_6.ComponentOmission
public import Topology_Munkres_2000.Book.Example_50_6.LinearGraph
public import Topology_Munkres_2000.Book.Example_50_6.Realization
public import Topology_Munkres_2000.Book.Theorem_63_4
public import Topology_Munkres_2000.Book.Theorem_63_5
public import Mathlib.Topology.Compactification.OnePoint.Sphere

public section

universe u v

open scoped Sym2

/-- Helper for Example 50.6: deleting a point of `unitInterval` leaves a connected
space exactly when that point is an endpoint. -/
private lemma unitInterval_isConnected_compl_singleton_iff (p : unitInterval) :
    IsConnected (({p} : Set unitInterval)ᶜ) ↔ p = 0 ∨ p = 1 := by
  constructor
  · intro hp
    -- An interior deleted point lies between two surviving endpoints, contradicting
    -- interval convexity of a connected subset of a linear order.
    by_contra hp_endpoint
    rw [not_or] at hp_endpoint
    have hzero : (0 : unitInterval) ∈ (({p} : Set unitInterval)ᶜ) := by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact fun h ↦ hp_endpoint.1 h.symm
    have hone : (1 : unitInterval) ∈ (({p} : Set unitInterval)ᶜ) := by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact fun h ↦ hp_endpoint.2 h.symm
    have hp_mem : p ∈ Set.Icc (0 : unitInterval) 1 := ⟨bot_le, le_top⟩
    have hp_compl := hp.Icc_subset hzero hone hp_mem
    exact hp_compl (Set.mem_singleton_iff.mpr rfl)
  · rintro (rfl | rfl)
    · -- The complement of the left endpoint is the connected half-open interval `(0, 1]`.
      have hcompl : (({0} : Set unitInterval)ᶜ) = Set.Ioc 0 1 := by
        ext x
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_Ioc]
        constructor
        · intro hx
          exact ⟨unitInterval.pos_iff_ne_zero.mpr hx, unitInterval.le_one'⟩
        · intro hx
          exact unitInterval.pos_iff_ne_zero.mp hx.1
      rw [hcompl]
      exact isConnected_Ioc zero_lt_one
    · -- The complement of the right endpoint is the connected half-open interval `[0, 1)`.
      have hcompl : (({1} : Set unitInterval)ᶜ) = Set.Ico 0 1 := by
        ext x
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_Ico]
        constructor
        · intro hx
          exact ⟨unitInterval.nonneg', unitInterval.lt_one_iff_ne_one.mpr hx⟩
        · intro hx
          exact unitInterval.lt_one_iff_ne_one.mp hx.2
      rw [hcompl]
      exact isConnected_Ico zero_lt_one

/-- The endpoint characterization in Example 50.6 (1): under a chosen homeomorphism
from `unitInterval`, a point of an arc is an endpoint exactly when deleting it leaves
a connected space. -/
theorem isConnected_compl_singleton_iff_arcEndpoint
    {A : Type u} [TopologicalSpace A] (e : unitInterval ≃ₜ A) (p : A) :
    IsConnected (({p} : Set A)ᶜ) ↔ p = e 0 ∨ p = e 1 := by
  -- Pull the punctured arc back to `unitInterval`, apply the endpoint calculation,
  -- and translate the resulting coordinate equations through the homeomorphism.
  rw [← e.symm.isConnected_image, e.symm.image_compl, Set.image_singleton,
    unitInterval_isConnected_compl_singleton_iff]
  have coordinate_eq (x : unitInterval) : e.symm p = x ↔ p = e x :=
    e.symm.toEquiv.apply_eq_iff_eq_symm_apply
  rw [coordinate_eq 0, coordinate_eq 1]

/- Example 50.6 defines a finite linear graph as a Hausdorff space covered by finitely
many arcs whose distinct edge sets meet in at most one common endpoint. -/
#check FiniteLinearGraph
#check FiniteLinearGraph.edgeSet
#check FiniteLinearGraph.vertexSet

/-- The edge closedness assertion of Example 50.6 (2): every edge set in a finite
linear graph is closed. -/
theorem finiteLinearGraph_edgeSet_isClosed
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (G : FiniteLinearGraph.{u, v} X) (i : G.Edge) :
    IsClosed (G.edgeSet i) := by
  -- The edge is the compact image of `unitInterval`; Hausdorffness then makes it closed.
  rw [G.edgeSet_def]
  exact (isCompact_range (G.edgeEmbedding i).continuous).isClosed

/-- Helper for Example 50.6: a covering-dimension bound is transported by a
homeomorphism. -/
private lemma hasCoveringDimensionLE_homeomorph
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) {n : ℕ} (h : HasCoveringDimensionLE A n) :
    HasCoveringDimensionLE B n := by
  -- Pull a target cover back to the source, where the assumed dimension bound applies.
  rw [hasCoveringDimensionLE_iff_pointwise] at h ⊢
  intro 𝒰 h𝒰open h𝒰cover
  let 𝒰' : Set (Set A) := (fun U : Set B ↦ e ⁻¹' U) '' 𝒰
  have h𝒰'open : ∀ U ∈ 𝒰', IsOpen U := by
    rintro U ⟨V, hV, rfl⟩
    exact (h𝒰open V hV).preimage e.continuous
  have h𝒰'cover : ⋃₀ 𝒰' = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : e x ∈ ⋃₀ 𝒰 := h𝒰cover.symm ▸ Set.mem_univ (e x)
    rw [Set.mem_sUnion] at hx ⊢
    obtain ⟨V, hV, hxV⟩ := hx
    exact ⟨e ⁻¹' V, ⟨V, hV, rfl⟩, hxV⟩
  obtain ⟨𝒱, h𝒱refines, h𝒱cover, h𝒱order⟩ := h 𝒰' h𝒰'open h𝒰'cover
  let 𝒱' : Set (Set B) := (fun U : Set A ↦ e '' U) '' 𝒱
  refine ⟨𝒱', ?_, ?_, ?_⟩
  · -- Push the source refinement forward into the original target cover.
    rw [isOpenRefinement_iff, isRefinement_iff]
    constructor
    · rintro V ⟨U, hU, rfl⟩
      obtain ⟨W, hW, hUW⟩ := h𝒱refines.subset_of_mem hU
      obtain ⟨Z, hZ, rfl⟩ := hW
      refine ⟨Z, hZ, ?_⟩
      rintro y ⟨x, hxU, rfl⟩
      exact hUW hxU
    · rintro V ⟨U, hU, rfl⟩
      exact e.isOpen_image.mpr (h𝒱refines.isOpen_of_mem hU)
  · -- Surjectivity transports the source refinement's covering equation.
    apply Set.eq_univ_of_forall
    intro y
    have hy : e.symm y ∈ ⋃₀ 𝒱 := h𝒱cover.symm ▸ Set.mem_univ (e.symm y)
    rw [Set.mem_sUnion] at hy ⊢
    obtain ⟨U, hU, hyU⟩ := hy
    exact ⟨e '' U, ⟨U, hU, rfl⟩, ⟨e.symm y, hyU, e.apply_symm_apply y⟩⟩
  · -- Incidence with a point is preserved injectively by taking homeomorphic images.
    intro y
    let incident : Set (Set A) := {U ∈ 𝒱 | e.symm y ∈ U}
    have hincident : {V ∈ 𝒱' | y ∈ V} = (fun U : Set A ↦ e '' U) '' incident := by
      ext V
      constructor
      · rintro ⟨⟨U, hU, rfl⟩, hyU⟩
        obtain ⟨x, hxU, hxy⟩ := hyU
        have hx : x = e.symm y := by
          simpa using congrArg e.symm hxy
        exact ⟨U, ⟨hU, hx ▸ hxU⟩, rfl⟩
      · rintro ⟨U, ⟨hU, hyU⟩, rfl⟩
        exact ⟨⟨U, hU, rfl⟩, ⟨e.symm y, hyU, e.apply_symm_apply y⟩⟩
    rw [hincident, e.injective.image_injective.encard_image]
    exact h𝒱order (e.symm y)

/-- Helper for Example 50.6: every strict covering-dimension bound is transported
by a homeomorphism. -/
private lemma hasCoveringDimensionLT_homeomorph
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) {n : ℕ} (h : HasCoveringDimensionLT A n) :
    HasCoveringDimensionLT B n := by
  -- Separate the empty-space bound from successor bounds represented by `HasCoveringDimensionLE`.
  cases n with
  | zero =>
      constructor
      intro y
      exact h.false (e.symm y)
  | succ n =>
      exact hasCoveringDimensionLE_homeomorph e h

/-- Helper for Example 50.6: covering dimension is invariant under a homeomorphism. -/
private lemma coveringDimension_eq_of_homeomorph
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) : coveringDimension A = coveringDimension B := by
  -- The defining families of strict bounds agree after transport in both directions.
  unfold coveringDimension
  apply congrArg sInf
  ext d
  constructor
  · intro hd n hdn
    exact hasCoveringDimensionLT_homeomorph e (hd n hdn)
  · intro hd n hdn
    exact hasCoveringDimensionLT_homeomorph e.symm (hd n hdn)

/-- Helper for Example 50.6: every edge subtype of a finite linear graph has
covering dimension one. -/
private lemma edgeSet_coveringDimension_eq_one
    {X : Type u} [TopologicalSpace X] (G : FiniteLinearGraph.{u, v} X) (i : G.Edge) :
    coveringDimension (G.edgeSet i) = 1 := by
  -- The stored edge embedding identifies `unitInterval` homeomorphically with its range.
  rw [G.edgeSet_def]
  exact (coveringDimension_eq_of_homeomorph (G.edgeEmbedding i).toHomeomorph).symm.trans
    unitInterval_coveringDimension

/-- The dimension assertion of Example 50.6 (3): a finite linear graph presentation
with at least one edge has covering dimension one. -/
theorem finiteLinearGraph_coveringDimension_eq_one
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (G : FiniteLinearGraph.{u, v} X) (h_edge : Nonempty G.Edge) :
    coveringDimension X = 1 := by
  classical
  letI : Finite G.Edge := G.edgeFinite
  letI : Fintype G.Edge := Fintype.ofFinite G.Edge
  -- Apply the finite closed-cover formula to the edge sets.
  rw [coveringDimension_iUnion_closed G.edgeSet
    (fun i ↦ finiteLinearGraph_edgeSet_isClosed G i) G.iUnion_edgeSet]
  -- Every member has dimension one, and the edge index is nonempty.
  obtain ⟨i⟩ := h_edge
  have huniv : (Finset.univ : Finset G.Edge).Nonempty := ⟨i, Finset.mem_univ i⟩
  simp_rw [edgeSet_coveringDimension_eq_one G]
  exact Finset.sup_const huniv 1

/-- Helper for Example 50.6: every embedding into the real plane induces an
embedding into the standard two-sphere. -/
private lemma existsSphereEmbeddingOfPlaneEmbedding
    {X : Type u} [TopologicalSpace X] (f : X → ℝ × ℝ) (hf : Topology.IsEmbedding f) :
    ∃ F : X → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      Topology.IsEmbedding F := by
  let planeEquiv : ℝ × ℝ ≃ₜ EuclideanSpace ℝ (Fin 2) :=
    ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
      (EuclideanSpace.equiv (Fin 2) ℝ).symm).toHomeomorph
  have hfinrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) + 1 =
      Fintype.card (Fin 3) := by
    simp
  let compactificationSphere :
      OnePoint (EuclideanSpace ℝ (Fin 2)) ≃ₜ
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    onePointEquivSphereOfFinrankEq hfinrank
  let F : X → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    fun x ↦ compactificationSphere (planeEquiv (f x) : OnePoint (EuclideanSpace ℝ (Fin 2)))
  refine ⟨F, ?_⟩
  -- Each map in the composite is an embedding: the plane coordinate
  -- homeomorphism, the open inclusion, and the compactification homeomorphism.
  exact compactificationSphere.isEmbedding.comp
    (OnePoint.isOpenEmbedding_coe.isEmbedding.comp (planeEquiv.isEmbedding.comp hf))

/-- Helper for Example 50.6: concatenating two injective paths that meet only at
their common endpoint gives an injective path. -/
private lemma injective_pathTrans_of_range_inter_eq_singleton
    {X : Type u} [TopologicalSpace X] {a b c : X}
    (gamma : Path a b) (delta : Path b c)
    (hgamma : Function.Injective gamma) (hdelta : Function.Injective delta)
    (hinter : Set.range gamma ∩ Set.range delta = {b}) :
    Function.Injective (gamma.trans delta) := by
  -- On equal halves, injectivity of the corresponding path piece recovers the
  -- parameter; on opposite halves, the range intersection forces the midpoint.
  intro s t hst
  by_cases hs : (s : ℝ) ≤ 1 / 2
  · by_cases ht : (t : ℝ) ≤ 1 / 2
    · rw [Path.trans_apply, dif_pos hs, Path.trans_apply, dif_pos ht] at hst
      have huv := hgamma hst
      apply Subtype.ext
      have huvVal := congrArg Subtype.val huv
      norm_num at huvVal
      linarith
    · rw [Path.trans_apply, dif_pos hs, Path.trans_apply, dif_neg ht] at hst
      have hsu : 2 * (s : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · linarith [s.2.1]
        · linarith
      have htv : 2 * (t : ℝ) - 1 ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · linarith
        · linarith [t.2.2]
      let su : unitInterval := ⟨2 * (s : ℝ), hsu⟩
      let tv : unitInterval := ⟨2 * (t : ℝ) - 1, htv⟩
      have hst' : gamma su = delta tv := hst
      have hmem : gamma su ∈ Set.range gamma ∩ Set.range delta := by
        exact ⟨Set.mem_range_self su, tv, hst'.symm⟩
      rw [hinter] at hmem
      have hgammaEndpoint : gamma su = b := Set.mem_singleton_iff.mp hmem
      have hdeltaEndpoint : delta tv = b := hst'.symm.trans hgammaEndpoint
      have htvZero := hdelta (hdeltaEndpoint.trans delta.source.symm)
      have htvVal := congrArg Subtype.val htvZero
      change 2 * (t : ℝ) - 1 = 0 at htvVal
      exfalso
      exact ht (by linarith)
  · by_cases ht : (t : ℝ) ≤ 1 / 2
    · rw [Path.trans_apply, dif_neg hs, Path.trans_apply, dif_pos ht] at hst
      have hsu : 2 * (s : ℝ) - 1 ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · linarith
        · linarith [s.2.2]
      have htv : 2 * (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · linarith [t.2.1]
        · linarith
      let su : unitInterval := ⟨2 * (s : ℝ) - 1, hsu⟩
      let tv : unitInterval := ⟨2 * (t : ℝ), htv⟩
      have hst' : delta su = gamma tv := hst
      have hmem : gamma tv ∈ Set.range gamma ∩ Set.range delta := by
        exact ⟨Set.mem_range_self tv, su, hst'⟩
      rw [hinter] at hmem
      have hgammaEndpoint : gamma tv = b := Set.mem_singleton_iff.mp hmem
      have hdeltaEndpoint : delta su = b := hst'.trans hgammaEndpoint
      have hsuZero := hdelta (hdeltaEndpoint.trans delta.source.symm)
      have hsuVal := congrArg Subtype.val hsuZero
      change 2 * (s : ℝ) - 1 = 0 at hsuVal
      exfalso
      exact hs (by linarith)
    · rw [Path.trans_apply, dif_neg hs, Path.trans_apply, dif_neg ht] at hst
      have huv := hdelta hst
      apply Subtype.ext
      have huvVal := congrArg Subtype.val huv
      norm_num at huvVal
      linarith

/-- Helper for Example 50.6: two embedded interval arcs meeting only at the
terminal endpoint of the first form one embedded interval arc. -/
private lemma existsEmbeddedArc_union_of_endpoint_inter_singleton
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (a b : unitInterval → X) (ha : Topology.IsEmbedding a)
    (hb : Topology.IsEmbedding b) (hend : a 1 = b 0)
    (hinter : Set.range a ∩ Set.range b = {a 1}) :
    ∃ gamma : unitInterval → X, Topology.IsEmbedding gamma ∧
      gamma 0 = a 0 ∧ gamma 1 = b 1 ∧
        Set.range gamma = Set.range a ∪ Set.range b := by
  let alpha : Path (a 0) (a 1) :=
    { toContinuousMap := ⟨a, ha.continuous⟩
      source' := rfl
      target' := rfl }
  let rawBeta : Path (b 0) (b 1) :=
    { toContinuousMap := ⟨b, hb.continuous⟩
      source' := rfl
      target' := rfl }
  let beta : Path (a 1) (b 1) := rawBeta.cast hend rfl
  let gamma : Path (a 0) (b 1) := alpha.trans beta
  -- Casting the second path only aligns its endpoint type and does not change
  -- its underlying map or range.
  have halphaCoe : (alpha : unitInterval → X) = a := rfl
  have hbetaCoe : (beta : unitInterval → X) = b := by
    exact Path.cast_coe rawBeta hend rfl
  have hbetaEmbedding : Topology.IsEmbedding beta := by
    rw [hbetaCoe]
    exact hb
  have hinter' : Set.range alpha ∩ Set.range beta = {a 1} := by
    rw [halphaCoe, hbetaCoe]
    exact hinter
  have hgammaInjective : Function.Injective gamma :=
    injective_pathTrans_of_range_inter_eq_singleton alpha beta
      (halphaCoe.symm ▸ ha.injective)
      hbetaEmbedding.injective hinter'
  refine ⟨gamma, gamma.continuous.isClosedEmbedding hgammaInjective |>.isEmbedding, ?_, ?_, ?_⟩
  · exact gamma.source
  · exact gamma.target
  · -- The concatenation has precisely the union of the original two ranges.
    rw [Path.trans_range, halphaCoe, hbetaCoe]

/-- Helper for Example 50.6: a realized combinatorial edge can be parameterized
from either chosen endpoint to the other without changing its range. -/
private lemma existsOrientedRealizedEdge
    {V : Type u} {G : SimpleGraph V} (R : G.LinearRealization)
    {a b : V} (hab : a ≠ b) (e : G.edgeSet) (he : e.1 = s(a, b)) :
    ∃ gamma : unitInterval → R.Carrier, Topology.IsEmbedding gamma ∧
      gamma 0 = R.vertex a ∧ gamma 1 = R.vertex b ∧
        Set.range gamma = R.finiteLinearGraph.edgeSet (R.edgeEquiv e) := by
  let raw := R.finiteLinearGraph.edge (R.edgeEquiv e)
  have haMem : a ∈ e.1 := by
    rw [he]
    exact Sym2.mem_mk_left a b
  have hbMem : b ∈ e.1 := by
    rw [he]
    exact Sym2.mem_mk_right a b
  have haEndpoint := (R.incident_iff_endpoint e a).mp haMem
  have hbEndpoint := (R.incident_iff_endpoint e b).mp hbMem
  have hvertexNe : R.vertex a ≠ R.vertex b := R.vertex_injective.ne hab
  have hrawEmbedding : Topology.IsEmbedding raw :=
    R.finiteLinearGraph.edgeEmbedding (R.edgeEquiv e)
  -- The two distinct vertices occupy opposite parameter endpoints; use the
  -- original parameterization in one orientation and interval symmetry in the other.
  rcases haEndpoint with haZero | haOne
  · rcases hbEndpoint with hbZero | hbOne
    · exact (hvertexNe (haZero.trans hbZero.symm)).elim
    · refine ⟨raw, hrawEmbedding, haZero.symm, hbOne.symm, ?_⟩
      exact (R.finiteLinearGraph.edgeSet_def (R.edgeEquiv e)).symm
  · rcases hbEndpoint with hbZero | hbOne
    · let gamma : unitInterval → R.Carrier := fun t ↦ raw (unitInterval.symm t)
      refine ⟨gamma, hrawEmbedding.comp unitInterval.symmHomeomorph.isEmbedding, ?_, ?_, ?_⟩
      · simpa [gamma] using haOne.symm
      · simpa [gamma] using hbZero.symm
      · rw [R.finiteLinearGraph.edgeSet_def]
        -- Symmetry is surjective, so reversing the parameter does not alter the range.
        apply Set.Subset.antisymm
        · rintro _ ⟨t, rfl⟩
          exact Set.mem_range_self (unitInterval.symm t)
        · rintro _ ⟨t, rfl⟩
          exact ⟨unitInterval.symm t, by simp [gamma, raw]⟩
    · exact (hvertexNe (haOne.trans hbOne.symm)).elim

/-- Helper for Example 50.6: an incident realized vertex belongs to the range of
the corresponding realized edge. -/
private lemma realizedVertex_mem_edgeSet
    {V : Type u} {G : SimpleGraph V} (R : G.LinearRealization)
    (e : G.edgeSet) {a : V} (ha : a ∈ e.1) :
    R.vertex a ∈ R.finiteLinearGraph.edgeSet (R.edgeEquiv e) := by
  rw [R.finiteLinearGraph.edgeSet_def]
  -- Incidence identifies the vertex with one of the two parameter endpoints.
  rcases (R.incident_iff_endpoint e a).mp ha with haZero | haOne
  · exact ⟨0, haZero.symm⟩
  · exact ⟨1, haOne.symm⟩

/-- Helper for Example 50.6: the two parameter endpoints of a realized edge are
exactly the realized endpoints of its underlying combinatorial edge. -/
private lemma realizedEdge_endpointPair
    {V : Type u} {G : SimpleGraph V} (R : G.LinearRealization)
    {a b : V} (hab : a ≠ b) (e : G.edgeSet) (he : e.1 = s(a, b)) :
    ({R.finiteLinearGraph.edge (R.edgeEquiv e) 0,
        R.finiteLinearGraph.edge (R.edgeEquiv e) 1} : Set R.Carrier) =
      {R.vertex a, R.vertex b} := by
  have haMem : a ∈ e.1 := he ▸ Sym2.mem_mk_left a b
  have hbMem : b ∈ e.1 := he ▸ Sym2.mem_mk_right a b
  have haEndpoint := (R.incident_iff_endpoint e a).mp haMem
  have hbEndpoint := (R.incident_iff_endpoint e b).mp hbMem
  have hvertexNe : R.vertex a ≠ R.vertex b := R.vertex_injective.ne hab
  -- Distinctness rules out assigning both graph vertices to the same endpoint.
  rcases haEndpoint with haZero | haOne
  · rcases hbEndpoint with hbZero | hbOne
    · exact (hvertexNe (haZero.trans hbZero.symm)).elim
    · rw [haZero, hbOne]
  · rcases hbEndpoint with hbZero | hbOne
    · rw [haOne, hbZero, Set.pair_comm]
    · exact (hvertexNe (haOne.trans hbOne.symm)).elim

/-- Helper for Example 50.6: distinct realized edges sharing a combinatorial
vertex meet, after an ambient embedding, exactly at that vertex. -/
private lemma embeddedRealizedEdge_inter_eq_singleton
    {V : Type u} {G : SimpleGraph V} (R : G.LinearRealization)
    {Y : Type v} [TopologicalSpace Y] (F : R.Carrier → Y)
    (hF : Function.Injective F) {e d : G.edgeSet} (hed : e ≠ d)
    {a : V} (hae : a ∈ e.1) (had : a ∈ d.1) :
    F '' R.finiteLinearGraph.edgeSet (R.edgeEquiv e) ∩
        F '' R.finiteLinearGraph.edgeSet (R.edgeEquiv d) = {F (R.vertex a)} := by
  have hvertexE := realizedVertex_mem_edgeSet R e hae
  have hvertexD := realizedVertex_mem_edgeSet R d had
  have hedgeNe : R.edgeEquiv e ≠ R.edgeEquiv d := R.edgeEquiv.injective.ne hed
  have hinterSubsingleton := R.finiteLinearGraph.inter_subsingleton hedgeNe
  -- Pull a common ambient point back through the embedding and use the
  -- presentation's subsingleton intersection against the shared vertex.
  apply Set.Subset.antisymm
  · rintro y ⟨⟨x, hxE, rfl⟩, ⟨z, hzD, hxz⟩⟩
    have hzx : z = x := hF hxz
    have hxVertex : x = R.vertex a :=
      hinterSubsingleton ⟨hxE, hzx ▸ hzD⟩ ⟨hvertexE, hvertexD⟩
    exact Set.mem_singleton_iff.mpr (congrArg F hxVertex)
  · intro y
    rw [Set.mem_singleton_iff]
    rintro rfl
    exact ⟨⟨R.vertex a, hvertexE, rfl⟩, ⟨R.vertex a, hvertexD, rfl⟩⟩

/-- Helper for Example 50.6: ambient images of realized edges with disjoint
combinatorial endpoint pairs are disjoint. -/
private lemma embeddedRealizedEdge_inter_eq_empty
    {V : Type u} {G : SimpleGraph V} (R : G.LinearRealization)
    {Y : Type v} [TopologicalSpace Y] (F : R.Carrier → Y)
    (hF : Function.Injective F) {a b c d : V} (hab : a ≠ b) (hcd : c ≠ d)
    (e k : G.edgeSet) (he : e.1 = s(a, b)) (hk : k.1 = s(c, d))
    (hed : e ≠ k) (hdisjoint : ({a, b} : Set V) ∩ {c, d} = ∅) :
    F '' R.finiteLinearGraph.edgeSet (R.edgeEquiv e) ∩
        F '' R.finiteLinearGraph.edgeSet (R.edgeEquiv k) = ∅ := by
  have hedgeNe : R.edgeEquiv e ≠ R.edgeEquiv k := R.edgeEquiv.injective.ne hed
  have hinterEndpoints := R.finiteLinearGraph.inter_subset_endpoints hedgeNe
  have heEndpoints := realizedEdge_endpointPair R hab e he
  have hkEndpoints := realizedEdge_endpointPair R hcd k hk
  -- A hypothetical common ambient point pulls back to a common edge endpoint,
  -- hence to a common combinatorial vertex, contradicting disjointness.
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro y ⟨⟨x, hxE, rfl⟩, ⟨z, hzK, hxz⟩⟩
  have hzx : z = x := hF hxz
  have hxEndpoints := hinterEndpoints ⟨hxE, hzx ▸ hzK⟩
  rw [heEndpoints, hkEndpoints] at hxEndpoints
  rcases hxEndpoints with ⟨ha | hb, hc | hd⟩
  · have hac : a = c := R.vertex_injective (ha.symm.trans hc)
    have : a ∈ ({a, b} : Set V) ∩ {c, d} := by simp [hac]
    rw [hdisjoint] at this
    exact this
  · have had : a = d := R.vertex_injective (ha.symm.trans hd)
    have : a ∈ ({a, b} : Set V) ∩ {c, d} := by simp [had]
    rw [hdisjoint] at this
    exact this
  · have hbc : b = c := R.vertex_injective (hb.symm.trans hc)
    have : b ∈ ({a, b} : Set V) ∩ {c, d} := by simp [hbc]
    rw [hdisjoint] at this
    exact this
  · have hbd : b = d := R.vertex_injective (hb.symm.trans hd)
    have : b ∈ ({a, b} : Set V) ∩ {c, d} := by simp [hbd]
    rw [hdisjoint] at this
    exact this

/-- Helper for Example 50.6: orienting a realized edge commutes with embedding
the graph carrier into an ambient space. -/
private lemma existsOrientedEmbeddedRealizedEdge
    {V : Type u} {G : SimpleGraph V} (R : G.LinearRealization)
    {Y : Type v} [TopologicalSpace Y] (F : R.Carrier → Y)
    (hF : Topology.IsEmbedding F) {a b : V} (hab : a ≠ b)
    (e : G.edgeSet) (he : e.1 = s(a, b)) :
    ∃ gamma : unitInterval → Y, Topology.IsEmbedding gamma ∧
      gamma 0 = F (R.vertex a) ∧ gamma 1 = F (R.vertex b) ∧
        Set.range gamma = F '' R.finiteLinearGraph.edgeSet (R.edgeEquiv e) := by
  obtain ⟨edge, hedge, hzero, hone, hrange⟩ :=
    existsOrientedRealizedEdge R hab e he
  refine ⟨F ∘ edge, hF.comp hedge, ?_, ?_, ?_⟩
  · exact congrArg F hzero
  · exact congrArg F hone
  · -- The range of a composite is the image of the inner range.
    rw [Set.range_comp, hrange]

/-- Helper for Example 50.6: the range of an embedded interval is closed and
connected in a Hausdorff ambient space. -/
private lemma embeddedArcRangeIsClosedAndConnected
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (a : unitInterval → X) (ha : Topology.IsEmbedding a) :
    IsClosed (Set.range a) ∧ IsConnected (Set.range a) := by
  constructor
  · -- Compactness of the parameter interval makes its embedded range closed.
    exact (isCompact_range ha.continuous).isClosed
  · -- Connectedness is preserved by the continuous parameterization.
    exact isConnected_range ha.continuous

/-- Helper for Example 50.6: both endpoints of an embedded interval arc are
limits of points in its endpoint-deleted range. -/
private lemma embeddedArc_endpoints_mem_closure_interiorRange
    {X : Type u} [TopologicalSpace X]
    (a : unitInterval → X) (ha : Topology.IsEmbedding a) :
    a 0 ∈ closure (Set.range a \ {a 0, a 1}) ∧
      a 1 ∈ closure (Set.range a \ {a 0, a 1}) := by
  have hinteriorRange :
      Set.range a \ {a 0, a 1} = a '' Set.Ioo 0 1 := by
    ext x
    constructor
    · rintro ⟨⟨t, rfl⟩, ht⟩
      have htZero : t ≠ 0 := by
        intro h
        exact ht (Set.mem_insert_iff.mpr (Or.inl (congrArg a h)))
      have htOne : t ≠ 1 := by
        intro h
        exact ht (Set.mem_insert_iff.mpr
          (Or.inr (Set.mem_singleton_iff.mpr (congrArg a h))))
      exact ⟨t, ⟨unitInterval.pos_iff_ne_zero.mpr htZero,
        unitInterval.lt_one_iff_ne_one.mpr htOne⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨Set.mem_range_self t, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ha.injective.ne (ne_of_gt ht.1),
        ha.injective.ne (ne_of_lt ht.2)⟩
  have hzeroClosure : (0 : unitInterval) ∈ closure (Set.Ioo 0 1) := by
    rw [closure_Ioo (show (0 : unitInterval) ≠ 1 from zero_ne_one)]
    exact ⟨bot_le, le_top⟩
  have honeClosure : (1 : unitInterval) ∈ closure (Set.Ioo 0 1) := by
    rw [closure_Ioo (show (0 : unitInterval) ≠ 1 from zero_ne_one)]
    exact ⟨bot_le, le_top⟩
  -- Continuity transports the two one-sided limit statements to the arc.
  rw [hinteriorRange]
  exact ⟨mem_closure_image ha.continuous.continuousAt hzeroClosure,
    mem_closure_image ha.continuous.continuousAt honeClosure⟩

/-- Helper for Example 50.6: two embedded interval ranges with a common point
have a closed connected union in a Hausdorff ambient space. -/
private lemma embeddedArcPairUnionIsClosedAndConnected
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (a b : unitInterval → X) (ha : Topology.IsEmbedding a)
    (hb : Topology.IsEmbedding b)
    (hinter : (Set.range a ∩ Set.range b).Nonempty) :
    IsClosed (Set.range a ∪ Set.range b) ∧
      IsConnected (Set.range a ∪ Set.range b) := by
  have haGeometry := embeddedArcRangeIsClosedAndConnected a ha
  have hbGeometry := embeddedArcRangeIsClosedAndConnected b hb
  constructor
  · -- A finite union of the two compact ranges remains closed.
    exact haGeometry.1.union hbGeometry.1
  · -- Their common point joins the two connected ranges.
    exact IsConnected.union hinter haGeometry.2 hbGeometry.2

/-- Helper for Example 50.6: the endpoint subset of the range of an embedded
interval is the image of the two parameter endpoints. -/
private lemma embeddedArc_endpointImage_eq_pair
    {X : Type u} [TopologicalSpace X]
    (a : unitInterval → X) (ha : Topology.IsEmbedding a) :
    letI : Topology.IsArc (Set.range a) :=
      ⟨⟨ha.toHomeomorph.symm⟩⟩
    Subtype.val '' {x : Set.range a | Topology.IsArc.IsEndpoint x} =
      {a 0, a 1} := by
  letI : Topology.IsArc (Set.range a) :=
    ⟨⟨ha.toHomeomorph.symm⟩⟩
  let e : Set.range a ≃ₜ unitInterval := ha.toHomeomorph.symm
  -- Arc coordinates identify the abstract endpoints with parameters `0` and `1`.
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change Topology.IsArc.IsEndpoint x at hx
    rw [Topology.IsArc.isEndpoint_iff e x] at hx
    rcases hx with hx | hx
    · left
      simpa [e] using congrArg Subtype.val hx
    · right
      simpa [e] using congrArg Subtype.val hx
  · intro hy
    rcases hy with rfl | hy
    · refine ⟨⟨a 0, Set.mem_range_self 0⟩, ?_, rfl⟩
      change Topology.IsArc.IsEndpoint
        (⟨a 0, Set.mem_range_self 0⟩ : Set.range a)
      rw [Topology.IsArc.isEndpoint_iff e]
      left
      apply Subtype.ext
      simp [e]
    · rw [Set.mem_singleton_iff] at hy
      subst y
      refine ⟨⟨a 1, Set.mem_range_self 1⟩, ?_, rfl⟩
      change Topology.IsArc.IsEndpoint
        (⟨a 1, Set.mem_range_self 1⟩ : Set.range a)
      rw [Topology.IsArc.isEndpoint_iff e]
      right
      apply Subtype.ext
      simp [e]

/-- Helper for Example 50.6: two embedded spherical arcs meeting exactly at
their two distinct common endpoints separate the sphere into two components. -/
private lemma embeddedArcPairUnion_separatesInto_two
    (a b : unitInterval → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (p q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (hpq : p ≠ q)
    (hinter : Set.range a ∩ Set.range b = {p, q}) :
    (Set.range a ∪ Set.range b).SeparatesInto 2 := by
  letI : Topology.IsArc (Set.range a) := ⟨⟨ha.toHomeomorph.symm⟩⟩
  letI : Topology.IsArc (Set.range b) := ⟨⟨hb.toHomeomorph.symm⟩⟩
  have haGeometry := embeddedArcRangeIsClosedAndConnected a ha
  have hbGeometry := embeddedArcRangeIsClosedAndConnected b hb
  -- Theorem 63.5 applies because each individual arc is nonseparating.
  exact union_separatesInto_two_of_inter_pair (Set.range a) (Set.range b)
    haGeometry.1 hbGeometry.1 haGeometry.2 hbGeometry.2
    ⟨p, q, hpq, hinter⟩ (arc_not_separates _) (arc_not_separates _)

/-- Helper for Example 50.6: two embedded arcs with the same distinct endpoints
and no other intersection form a simple closed curve. -/
private lemma isSimpleClosedCurve_pairArcRanges
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (a b : unitInterval → X) (ha : Topology.IsEmbedding a)
    (hb : Topology.IsEmbedding b) (hzero : a 0 = b 0)
    (hone : a 1 = b 1)
    (hinter : Set.range a ∩ Set.range b = {a 0, a 1}) :
    Topology.IsSimpleClosedCurve ↑(Set.range a ∪ Set.range b) := by
  classical
  let upper : Set Circle := Set.range (Circle.path 1 (-1))
  let lower : Set Circle := Set.range (Circle.path (-1) 1)
  let upperParam : Circle → unitInterval := Function.invFun (Circle.path 1 (-1))
  let lowerParam : Circle → unitInterval := Function.invFun (Circle.path (-1) 1)
  let upperMap : Circle → X := fun z ↦ a (upperParam z)
  let lowerMap : Circle → X := fun z ↦ b (unitInterval.symm (lowerParam z))
  let pasted : Circle → X := upper.piecewise upperMap lowerMap
  have hpathUpper : Function.Injective (Circle.path 1 (-1)) :=
    Circle.path_injective_of_ne (Circle.neg_ne_self 1).symm
  have hpathLower : Function.Injective (Circle.path (-1) 1) :=
    Circle.path_injective_of_ne (Circle.neg_ne_self 1)
  have hcover : upper ∪ lower = Set.univ := by
    exact Circle.range_path_union_range_path (Circle.neg_ne_self 1).symm
  have hpathsInter : upper ∩ lower = {(1 : Circle), -1} := by
    exact Circle.range_path_inter_range_path (Circle.neg_ne_self 1).symm
  have hupperClosed : IsClosed upper :=
    (isCompact_range (Circle.path 1 (-1)).continuous).isClosed
  have hlowerClosed : IsClosed lower :=
    (isCompact_range (Circle.path (-1) 1).continuous).isClosed
  -- The inverse parameter functions are continuous on their respective path ranges.
  have hupperMapContinuous : ContinuousOn upperMap upper := by
    rw [continuousOn_iff_continuous_restrict]
    let e :=
      (Circle.path 1 (-1)).continuous.isClosedEmbedding hpathUpper |>.isEmbedding
        |>.toHomeomorph
    have hformula : upper.restrict upperMap = a ∘ e.symm := by
      funext z
      apply congrArg a
      apply hpathUpper
      exact (Function.invFun_eq z.property).trans
        (congrArg Subtype.val (e.apply_symm_apply z)).symm
    rw [hformula]
    exact ha.continuous.comp e.symm.continuous
  have hlowerMapContinuous : ContinuousOn lowerMap lower := by
    rw [continuousOn_iff_continuous_restrict]
    let e :=
      (Circle.path (-1) 1).continuous.isClosedEmbedding hpathLower |>.isEmbedding
        |>.toHomeomorph
    have hformula : lower.restrict lowerMap =
        b ∘ unitInterval.symm ∘ e.symm := by
      funext z
      apply congrArg b
      apply congrArg unitInterval.symm
      apply hpathLower
      exact (Function.invFun_eq z.property).trans
        (congrArg Subtype.val (e.apply_symm_apply z)).symm
    rw [hformula]
    exact hb.continuous.comp (unitInterval.continuous_symm.comp e.symm.continuous)
  have hupperZero : upperParam 1 = 0 := by
    simpa only [upperParam, Path.source] using
      Function.leftInverse_invFun hpathUpper (0 : unitInterval)
  have hupperOne : upperParam (-1) = 1 := by
    simpa only [upperParam, Path.target] using
      Function.leftInverse_invFun hpathUpper (1 : unitInterval)
  have hlowerZero : lowerParam (-1) = 0 := by
    simpa only [lowerParam, Path.source] using
      Function.leftInverse_invFun hpathLower (0 : unitInterval)
  have hlowerOne : lowerParam 1 = 1 := by
    simpa only [lowerParam, Path.target] using
      Function.leftInverse_invFun hpathLower (1 : unitInterval)
  -- Reversing the second parameter makes the two formulas agree at both endpoints.
  have hmapsAgree : Set.EqOn upperMap lowerMap (upper ∩ lower) := by
    intro z hz
    rw [hpathsInter] at hz
    rcases hz with rfl | hz
    · simpa only [upperMap, lowerMap, hupperZero, hlowerOne,
        unitInterval.symm_one] using hzero
    · rw [Set.mem_singleton_iff] at hz
      subst z
      simpa only [upperMap, lowerMap, hupperOne, hlowerZero,
        unitInterval.symm_zero] using hone
  have hpastedUpper : ContinuousOn pasted upper := by
    refine hupperMapContinuous.congr fun z hz ↦ ?_
    exact upper.piecewise_eq_of_mem upperMap lowerMap hz
  have hpastedLower : ContinuousOn pasted lower := by
    refine hlowerMapContinuous.congr fun z hz ↦ ?_
    by_cases hzu : z ∈ upper
    · simp only [pasted, upper.piecewise_eq_of_mem upperMap lowerMap hzu]
      exact hmapsAgree ⟨hzu, hz⟩
    · exact upper.piecewise_eq_of_notMem upperMap lowerMap hzu
  have hpastedContinuous : Continuous pasted := by
    rw [← continuousOn_univ, ← hcover]
    exact hpastedUpper.union_of_isClosed hpastedLower hupperClosed hlowerClosed
  -- On each closed half, the pasted map recovers the corresponding arc range.
  have hpastedRange : Set.range pasted = Set.range a ∪ Set.range b := by
    apply Set.Subset.antisymm
    · rintro y ⟨z, rfl⟩
      by_cases hzu : z ∈ upper
      · left
        refine ⟨upperParam z, ?_⟩
        exact (upper.piecewise_eq_of_mem upperMap lowerMap hzu).symm
      · right
        refine ⟨unitInterval.symm (lowerParam z), ?_⟩
        exact (upper.piecewise_eq_of_notMem upperMap lowerMap hzu).symm
    · rintro y (hy | hy)
      · obtain ⟨t, rfl⟩ := hy
        refine ⟨Circle.path 1 (-1) t, ?_⟩
        have hmem : Circle.path 1 (-1) t ∈ upper := Set.mem_range_self t
        simp only [pasted, upper.piecewise_eq_of_mem upperMap lowerMap hmem]
        exact congrArg a (Function.leftInverse_invFun hpathUpper t)
      · obtain ⟨t, rfl⟩ := hy
        let z : Circle := Circle.path (-1) 1 (unitInterval.symm t)
        have hzl : z ∈ lower := Set.mem_range_self (unitInterval.symm t)
        have hlowerValue : lowerMap z = b t := by
          simp only [lowerMap, lowerParam, z,
            Function.leftInverse_invFun hpathLower (unitInterval.symm t),
            unitInterval.symm_symm]
        refine ⟨z, ?_⟩
        by_cases hzu : z ∈ upper
        · simp only [pasted, upper.piecewise_eq_of_mem upperMap lowerMap hzu,
            hmapsAgree ⟨hzu, hzl⟩, hlowerValue]
        · simp only [pasted, upper.piecewise_eq_of_notMem upperMap lowerMap hzu,
            hlowerValue]
  -- Equality across opposite circle halves can only occur at their common endpoints.
  have hcross (z w : Circle) (hzu : z ∈ upper) (hwl : w ∈ lower)
      (hwu : w ∉ upper) (hzw : pasted z = pasted w) : z = w := by
    have hmapEq : upperMap z = lowerMap w := by
      simp only [pasted, upper.piecewise_eq_of_mem upperMap lowerMap hzu,
        upper.piecewise_eq_of_notMem upperMap lowerMap hwu] at hzw
      exact hzw
    have hcommon : upperMap z ∈ Set.range a ∩ Set.range b := by
      exact ⟨⟨upperParam z, rfl⟩,
        ⟨unitInterval.symm (lowerParam w), hmapEq.symm⟩⟩
    rw [hinter] at hcommon
    rcases hcommon with hcommon | hcommon
    · have hzParam : upperParam z = 0 := ha.injective hcommon
      have hwParamSymm : unitInterval.symm (lowerParam w) = 0 := by
        apply hb.injective
        rw [← hzero]
        exact hmapEq.symm.trans hcommon
      have hwParam : lowerParam w = 1 := unitInterval.symm_eq_zero.mp hwParamSymm
      calc
        z = Circle.path 1 (-1) (upperParam z) := (Function.invFun_eq hzu).symm
        _ = Circle.path 1 (-1) 0 := congrArg _ hzParam
        _ = 1 := Path.source _
        _ = Circle.path (-1) 1 1 := (Path.target _).symm
        _ = Circle.path (-1) 1 (lowerParam w) := congrArg _ hwParam.symm
        _ = w := Function.invFun_eq hwl
    · rw [Set.mem_singleton_iff] at hcommon
      have hzParam : upperParam z = 1 := ha.injective hcommon
      have hwParamSymm : unitInterval.symm (lowerParam w) = 1 := by
        apply hb.injective
        rw [← hone]
        exact hmapEq.symm.trans hcommon
      have hwParam : lowerParam w = 0 := unitInterval.symm_eq_one.mp hwParamSymm
      calc
        z = Circle.path 1 (-1) (upperParam z) := (Function.invFun_eq hzu).symm
        _ = Circle.path 1 (-1) 1 := congrArg _ hzParam
        _ = -1 := Path.target _
        _ = Circle.path (-1) 1 0 := (Path.source _).symm
        _ = Circle.path (-1) 1 (lowerParam w) := congrArg _ hwParam.symm
        _ = w := Function.invFun_eq hwl
  have hpastedInjective : Function.Injective pasted := by
    intro z w hzw
    by_cases hzu : z ∈ upper
    · by_cases hwu : w ∈ upper
      · have hparam : upperParam z = upperParam w := by
          apply ha.injective
          simp only [pasted, upper.piecewise_eq_of_mem upperMap lowerMap hzu,
            upper.piecewise_eq_of_mem upperMap lowerMap hwu] at hzw
          exact hzw
        calc
          z = Circle.path 1 (-1) (upperParam z) := (Function.invFun_eq hzu).symm
          _ = Circle.path 1 (-1) (upperParam w) := congrArg _ hparam
          _ = w := Function.invFun_eq hwu
      · have hwl : w ∈ lower := by
          have : w ∈ upper ∪ lower := hcover.symm ▸ Set.mem_univ w
          exact this.resolve_left hwu
        exact hcross z w hzu hwl hwu hzw
    · have hzl : z ∈ lower := by
        have : z ∈ upper ∪ lower := hcover.symm ▸ Set.mem_univ z
        exact this.resolve_left hzu
      by_cases hwu : w ∈ upper
      · exact (hcross w z hwu hzl hzu hzw.symm).symm
      · have hwl : w ∈ lower := by
          have : w ∈ upper ∪ lower := hcover.symm ▸ Set.mem_univ w
          exact this.resolve_left hwu
        have hparamSymm : unitInterval.symm (lowerParam z) =
            unitInterval.symm (lowerParam w) := by
          apply hb.injective
          simp only [pasted, upper.piecewise_eq_of_notMem upperMap lowerMap hzu,
            upper.piecewise_eq_of_notMem upperMap lowerMap hwu] at hzw
          exact hzw
        have hparam : lowerParam z = lowerParam w :=
          unitInterval.symm_bijective.injective hparamSymm
        calc
          z = Circle.path (-1) 1 (lowerParam z) := (Function.invFun_eq hzl).symm
          _ = Circle.path (-1) 1 (lowerParam w) := congrArg _ hparam
          _ = w := Function.invFun_eq hwl
  -- The compact-domain embedding is a homeomorphism onto exactly the two arc ranges.
  rw [Topology.IsSimpleClosedCurve.iff_nonempty_homeomorph_circle]
  let hpastedEmbedding : Topology.IsEmbedding pasted :=
    hpastedContinuous.isClosedEmbedding hpastedInjective |>.isEmbedding
  exact ⟨(hpastedEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr hpastedRange)).symm⟩

/-- Helper for Example 50.6: in a set with exactly two components, the component
of a chosen point and the other component are disjoint and cover the set. -/
private lemma existsOtherComponentPartition
    {X : Type u} [TopologicalSpace X] (F : Set X)
    (hF : Cardinal.mk (ConnectedComponents F) = 2) (x : F) :
    ∃ y : F, Disjoint (connectedComponentIn F x) (connectedComponentIn F y) ∧
      connectedComponentIn F x ∪ connectedComponentIn F y = F := by
  classical
  -- Exact cardinality two selects the unique quotient component different from `x`.
  obtain ⟨q, hqx, hqunique⟩ :=
    (Cardinal.mk_eq_two_iff' (ConnectedComponents.mk x)).mp hF
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe q
  have hxy : (x : ConnectedComponents F) ≠ y := hqx.symm
  have hcomponentDisjoint : Disjoint (connectedComponent x) (connectedComponent y) :=
    connectedComponent_disjoint (ConnectedComponents.coe_ne_coe.mp hxy)
  refine ⟨y, ?_, ?_⟩
  · -- Subtype inclusion transports disjointness to ambient components.
    rw [connectedComponentIn_eq_image x.2, connectedComponentIn_eq_image y.2]
    exact Set.disjoint_image_of_injective Subtype.val_injective hcomponentDisjoint
  · -- Every quotient class is either the class of `x` or the selected other class.
    apply Set.Subset.antisymm
    · exact Set.union_subset (connectedComponentIn_subset F x)
        (connectedComponentIn_subset F y)
    · intro z hzF
      let zF : F := ⟨z, hzF⟩
      by_cases hzx : (zF : ConnectedComponents F) = x
      · left
        rw [connectedComponentIn_eq_image x.2]
        exact ⟨zF, ConnectedComponents.coe_eq_coe'.mp hzx, rfl⟩
      · right
        have hzy : (zF : ConnectedComponents F) = y := hqunique _ hzx
        rw [connectedComponentIn_eq_image y.2]
        exact ⟨zF, ConnectedComponents.coe_eq_coe'.mp hzy, rfl⟩

/-- Helper for Example 50.6: a component is unchanged when the smaller ambient
set contains that whole component and is itself contained in the original set. -/
private lemma connectedComponentIn_eq_of_component_subset
    {X : Type u} [TopologicalSpace X] {F R : Set X} {x : X}
    (hx : x ∈ F) (hcomponent : connectedComponentIn F x ⊆ R)
    (hRF : R ⊆ F) :
    connectedComponentIn R x = connectedComponentIn F x := by
  -- The original component contains its base point, so the sandwich also puts
  -- the base point in the smaller ambient set.
  have hxR : x ∈ R := hcomponent (mem_connectedComponentIn hx)
  apply Set.Subset.antisymm
  · -- Maximality in `F` absorbs the component constructed inside `R`.
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hxR)
      ((connectedComponentIn_subset R x).trans hRF)
  · -- Conversely, the assumed component containment lets maximality in `R`
    -- absorb the whole original component.
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hx) hcomponent

/-- Helper for Example 50.6: in a set with exactly two components, two known
distinct components exhaust all possible components. -/
private lemma connectedComponentIn_eq_or_eq_of_mk_eq_two
    {X : Type u} [TopologicalSpace X] (F : Set X)
    (hcard : Cardinal.mk (ConnectedComponents F) = 2)
    {x x₀ x₁ : X} (hx : x ∈ F) (hx₀ : x₀ ∈ F) (hx₁ : x₁ ∈ F)
    (hne : connectedComponentIn F x₀ ≠ connectedComponentIn F x₁) :
    connectedComponentIn F x = connectedComponentIn F x₀ ∨
      connectedComponentIn F x = connectedComponentIn F x₁ := by
  classical
  let xF : F := ⟨x, hx⟩
  let x₀F : F := ⟨x₀, hx₀⟩
  let x₁F : F := ⟨x₁, hx₁⟩
  have hclass₁ne : (x₁F : ConnectedComponents F) ≠ x₀F := by
    intro hclass
    apply hne
    rw [connectedComponentIn_eq_image hx₀, connectedComponentIn_eq_image hx₁]
    exact congrArg (Set.image Subtype.val)
      (ConnectedComponents.coe_eq_coe.mp hclass).symm
  obtain ⟨other, hother, hunique⟩ :=
    (Cardinal.mk_eq_two_iff' (ConnectedComponents.mk x₀F)).mp hcard
  have hclass₁ : (x₁F : ConnectedComponents F) = other :=
    hunique x₁F hclass₁ne
  have componentEq {a b : X} (ha : a ∈ F) (hb : b ∈ F)
      (hab : ((⟨a, ha⟩ : F) : ConnectedComponents F) =
        ((⟨b, hb⟩ : F) : ConnectedComponents F)) :
      connectedComponentIn F a = connectedComponentIn F b := by
    -- Quotient-class equality is equality of subtype components; taking the
    -- ambient image recovers `connectedComponentIn`.
    rw [connectedComponentIn_eq_image ha, connectedComponentIn_eq_image hb]
    exact congrArg (Set.image Subtype.val) (ConnectedComponents.coe_eq_coe.mp hab)
  by_cases hclass : (xF : ConnectedComponents F) = x₀F
  · exact Or.inl (componentEq hx hx₀ hclass)
  · right
    have hxOther : (xF : ConnectedComponents F) = other :=
      hunique xF hclass
    exact componentEq hx hx₁ (hxOther.trans hclass₁.symm)

/-- Helper for Example 50.6: adjoining a crosscut to the closure of the
opposite side of a Jordan curve leaves exactly the other two theta regions. -/
private lemma oppositeJordanComponent_remainder
    (C A : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
    [Topology.IsSimpleClosedCurve C]
    (x : (Cᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)))
    (hAclosed : IsClosed A) (hAconnected : IsConnected A)
    (hAnonseparating : ¬ A.Separates)
    (p q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (hpq : p ≠ q)
    (hinter : C ∩ A = {p, q})
    (hdisjoint : Disjoint (connectedComponentIn Cᶜ x) A) :
    (closure (connectedComponentIn Cᶜ x) ∪ A).SeparatesInto 2 ∧
      (closure (connectedComponentIn Cᶜ x) ∪ A)ᶜ =
        (C ∪ A)ᶜ \ connectedComponentIn Cᶜ x := by
  classical
  let V : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    connectedComponentIn Cᶜ x
  -- Jordan's frontier theorem gives the stable normal form for the selected
  -- closed side.
  have hclosureV : closure V = V ∪ C := by
    rw [closure_eq_self_union_frontier, jordanCurveSphere_frontier_component C x]
  have hcomponents : Cardinal.mk (ConnectedComponents (Cᶜ : Set _)) = 2 :=
    Set.separatesInto_iff.mp (jordanCurveSphere_separatesInto C)
  obtain ⟨y, hVyDisjoint, hVyCover⟩ :=
    existsOtherComponentPartition Cᶜ hcomponents x
  let W : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    connectedComponentIn Cᶜ y
  have hclosureVCompl : (closure V)ᶜ = W := by
    -- The complement of `V ∪ C` is precisely the other Jordan component.
    ext z
    constructor
    · intro hz
      have hzV : z ∉ V := fun hzV ↦ hz (hclosureV.symm ▸ Or.inl hzV)
      have hzC : z ∈ Cᶜ := fun hzC ↦ hz (hclosureV.symm ▸ Or.inr hzC)
      rcases hVyCover.symm ▸ hzC with hzV' | hzW
      · exact (hzV hzV').elim
      · exact hzW
    · intro hzW hzClosure
      rw [hclosureV] at hzClosure
      rcases hzClosure with hzV | hzC
      · exact Set.disjoint_left.mp hVyDisjoint hzV hzW
      · exact (connectedComponentIn_subset Cᶜ y hzW) hzC
  have hVconnected : IsConnected (closure V) := by
    -- A connected component remains connected after taking its closure.
    exact (isConnected_connectedComponentIn_iff.mpr x.property).closure
  have hVnonseparating : ¬ (closure V).Separates := by
    -- Its complement is the other connected Jordan component.
    intro hseparates
    apply (Set.separates_iff.mp hseparates)
    rw [hclosureVCompl]
    exact Subtype.preconnectedSpace
      (isConnected_connectedComponentIn_iff.mpr y.property).isPreconnected
  have hclosureInter : closure V ∩ A = {p, q} := by
    -- The selected open side avoids the crosscut, leaving only the two points
    -- where the crosscut meets the Jordan curve.
    ext z
    constructor
    · rintro ⟨hzClosure, hzA⟩
      rw [hclosureV] at hzClosure
      rcases hzClosure with hzV | hzC
      · exact (Set.disjoint_left.mp hdisjoint hzV hzA).elim
      · exact hinter ▸ ⟨hzC, hzA⟩
    · intro hzPair
      have hzInter : z ∈ C ∩ A := hinter.symm ▸ hzPair
      exact ⟨hclosureV.symm ▸ Or.inr hzInter.1, hzInter.2⟩
  constructor
  · -- Theorem 63.5 now counts the two components of the local remainder.
    exact union_separatesInto_two_of_inter_pair (closure V) A isClosed_closure
      hAclosed hVconnected hAconnected ⟨p, q, hpq, hclosureInter⟩
      hVnonseparating hAnonseparating
  · -- Expanding the closed Jordan side identifies that remainder with the
    -- theta complement after deleting the opposite component.
    rw [hclosureV]
    ext z
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_sdiff]
    tauto

/-- Helper for Example 50.6: for any two theta arms, there is a component on
the side opposite the third arm, and its frontier is exactly those two arms. -/
private lemma existsThetaComponentWithPairFrontier
    (arc : Fin 3 → unitInterval → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (harc : ∀ i, Topology.IsEmbedding (arc i))
    (p q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hzero : ∀ i, arc i 0 = p) (hone : ∀ i, arc i 1 = q)
    (hinter : ∀ {i j}, i ≠ j →
      Set.range (arc i) ∩ Set.range (arc j) = {p, q})
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ x, x ∈ (⋃ l, Set.range (arc l))ᶜ ∧
      connectedComponentIn (⋃ l, Set.range (arc l))ᶜ x =
        connectedComponentIn (Set.range (arc i) ∪ Set.range (arc j))ᶜ x ∧
      frontier (connectedComponentIn (⋃ l, Set.range (arc l))ᶜ x) =
        Set.range (arc i) ∪ Set.range (arc j) := by
  classical
  let C : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Set.range (arc i) ∪ Set.range (arc j)
  let theta : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    ⋃ l, Set.range (arc l)
  have hzeroPair : arc i 0 = arc j 0 := (hzero i).trans (hzero j).symm
  have honePair : arc i 1 = arc j 1 := (hone i).trans (hone j).symm
  have hinterPair : Set.range (arc i) ∩ Set.range (arc j) =
      {arc i 0, arc i 1} := by
    rw [hinter hij, hzero i, hone i]
  letI : Topology.IsSimpleClosedCurve ↑C :=
    isSimpleClosedCurve_pairArcRanges (arc i) (arc j) (harc i) (harc j)
      hzeroPair honePair hinterPair
  have hcomponents : Cardinal.mk (ConnectedComponents (Cᶜ : Set _)) = 2 :=
    Set.separatesInto_iff.mp (jordanCurveSphere_separatesInto C)
  let t : unitInterval := ⟨1 / 2, by norm_num⟩
  let y := arc k t
  let interiorArm : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Set.range (arc k) \ {p, q}
  have htZero : t ≠ 0 := by
    intro ht
    have := congrArg Subtype.val ht
    norm_num [t] at this
  have htOne : t ≠ 1 := by
    intro ht
    have := congrArg Subtype.val ht
    norm_num [t] at this
  have hyInterior : y ∈ interiorArm := by
    refine ⟨Set.mem_range_self t, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro hyp
      exact htZero ((harc k).injective (hyp.trans (hzero k).symm))
    · intro hyq
      exact htOne ((harc k).injective (hyq.trans (hone k).symm))
  have hinteriorConnected : IsConnected interiorArm := by
    simpa only [interiorArm, hzero k, hone k] using
      embeddedArc_range_diff_endpoints_isConnected (arc k) (harc k)
  have hinteriorCcompl : interiorArm ⊆ Cᶜ := by
    rintro z ⟨hzk, hzEndpoints⟩
    rw [Set.mem_compl_iff]
    rintro (hzi | hzj)
    · have hzInter : z ∈ Set.range (arc k) ∩ Set.range (arc i) := ⟨hzk, hzi⟩
      rw [hinter hik.symm] at hzInter
      exact hzEndpoints hzInter
    · have hzInter : z ∈ Set.range (arc k) ∩ Set.range (arc j) := ⟨hzk, hzj⟩
      rw [hinter hjk.symm] at hzInter
      exact hzEndpoints hzInter
  let yC : (Cᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
    ⟨y, hinteriorCcompl hyInterior⟩
  obtain ⟨x, hdisjoint, hpartition⟩ :=
    existsOtherComponentPartition Cᶜ hcomponents yC
  let U : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    connectedComponentIn Cᶜ yC
  let V : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    connectedComponentIn Cᶜ x
  have hinteriorU : interiorArm ⊆ U := by
    exact hinteriorConnected.2.subset_connectedComponentIn hyInterior hinteriorCcompl
  have hVavoidsThird : V ∩ Set.range (arc k) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨hzV, hzk⟩
    by_cases hzEndpoints : z ∈ ({p, q} : Set _)
    · have hzC : z ∈ C := by
        rcases hzEndpoints with rfl | hzq
        · left
          exact ⟨0, hzero i⟩
        · rw [Set.mem_singleton_iff] at hzq
          subst z
          left
          exact ⟨1, hone i⟩
      exact (connectedComponentIn_subset Cᶜ x hzV) hzC
    · exact Set.disjoint_left.mp hdisjoint (hinteriorU ⟨hzk, hzEndpoints⟩) hzV
  have hindices (l : Fin 3) : l = i ∨ l = j ∨ l = k := by
    omega
  have hVtheta : V ⊆ thetaᶜ := by
    intro z hzV hzTheta
    obtain ⟨l, hzl⟩ := Set.mem_iUnion.mp hzTheta
    rcases hindices l with rfl | rfl | rfl
    · exact (connectedComponentIn_subset Cᶜ x hzV) (Or.inl hzl)
    · exact (connectedComponentIn_subset Cᶜ x hzV) (Or.inr hzl)
    · exact (Set.eq_empty_iff_forall_notMem.mp hVavoidsThird z) ⟨hzV, hzl⟩
  have hthetaC : thetaᶜ ⊆ Cᶜ := by
    intro z hzTheta hzC
    rcases hzC with hzi | hzj
    · exact hzTheta (Set.mem_iUnion.mpr ⟨i, hzi⟩)
    · exact hzTheta (Set.mem_iUnion.mpr ⟨j, hzj⟩)
  have hxV : (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∈ V :=
    mem_connectedComponentIn x.property
  have hxTheta : (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∈ thetaᶜ :=
    hVtheta hxV
  have hcomponentEq : connectedComponentIn thetaᶜ x = V := by
    apply Set.Subset.antisymm
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hxTheta)
        ((connectedComponentIn_subset thetaᶜ x).trans hthetaC)
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
        hxV hVtheta
  refine ⟨x, hxTheta, hcomponentEq, ?_⟩
  -- The opposite theta component is unchanged from the chosen Jordan side.
  rw [hcomponentEq]
  exact jordanCurveSphere_frontier_component C x

/-- Helper for Example 50.6: every complementary component of three embedded
arcs is the component cut out by a pair of arms, and its frontier is that pair. -/
private lemma threeEmbeddedArcs_componentPairClassification
    (arc : Fin 3 → unitInterval → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (harc : ∀ i, Topology.IsEmbedding (arc i))
    (p q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (hpq : p ≠ q)
    (hzero : ∀ i, arc i 0 = p) (hone : ∀ i, arc i 1 = q)
    (hinter : ∀ {i j}, i ≠ j →
      Set.range (arc i) ∩ Set.range (arc j) = {p, q}) :
    ∀ x, x ∈ (⋃ i, Set.range (arc i))ᶜ →
      ∃ i,
        connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x =
          connectedComponentIn
            (⋃ (j : Fin 3) (_ : j ≠ i), Set.range (arc j))ᶜ x ∧
        frontier (connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x) =
          ⋃ (j : Fin 3) (_ : j ≠ i), Set.range (arc j) := by
  letI : LocallyConnectedSpace
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    ChartedSpace.locallyConnectedSpace
      (EuclideanSpace ℝ (Fin 2)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  intro x hx
  -- Construct the three opposite-arm components; their frontiers are the three
  -- possible unions of two theta arms.
  obtain ⟨x₀, hx₀, hcomponentPair₀, hfrontier₀⟩ :=
    existsThetaComponentWithPairFrontier arc harc p q hzero hone hinter
      (i := 1) (j := 2) (k := 0) (by decide) (by decide) (by decide)
  obtain ⟨x₁, hx₁, hcomponentPair₁, hfrontier₁⟩ :=
    existsThetaComponentWithPairFrontier arc harc p q hzero hone hinter
      (i := 0) (j := 2) (k := 1) (by decide) (by decide) (by decide)
  obtain ⟨x₂, hx₂, hcomponentPair₂, hfrontier₂⟩ :=
    existsThetaComponentWithPairFrontier arc harc p q hzero hone hinter
      (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)
  have hotherRanges₀ :
      (⋃ (j : Fin 3) (_ : j ≠ 0), Set.range (arc j)) =
        Set.range (arc 1) ∪ Set.range (arc 2) := by
    ext z
    constructor
    · intro hz
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
      obtain ⟨hj0, hzj⟩ := Set.mem_iUnion.mp hj
      fin_cases j
      · exact (hj0 rfl).elim
      · exact Or.inl hzj
      · exact Or.inr hzj
    · rintro (hz | hz)
      · exact Set.mem_iUnion.mpr ⟨1,
          Set.mem_iUnion.mpr ⟨by decide, hz⟩⟩
      · exact Set.mem_iUnion.mpr ⟨2,
          Set.mem_iUnion.mpr ⟨by decide, hz⟩⟩
  have hotherRanges₁ :
      (⋃ (j : Fin 3) (_ : j ≠ 1), Set.range (arc j)) =
        Set.range (arc 0) ∪ Set.range (arc 2) := by
    ext z
    constructor
    · intro hz
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
      obtain ⟨hj1, hzj⟩ := Set.mem_iUnion.mp hj
      fin_cases j
      · exact Or.inl hzj
      · exact (hj1 rfl).elim
      · exact Or.inr hzj
    · rintro (hz | hz)
      · exact Set.mem_iUnion.mpr ⟨0,
          Set.mem_iUnion.mpr ⟨by decide, hz⟩⟩
      · exact Set.mem_iUnion.mpr ⟨2,
          Set.mem_iUnion.mpr ⟨by decide, hz⟩⟩
  have hotherRanges₂ :
      (⋃ (j : Fin 3) (_ : j ≠ 2), Set.range (arc j)) =
        Set.range (arc 0) ∪ Set.range (arc 1) := by
    ext z
    constructor
    · intro hz
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
      obtain ⟨hj2, hzj⟩ := Set.mem_iUnion.mp hj
      fin_cases j
      · exact Or.inl hzj
      · exact Or.inr hzj
      · exact (hj2 rfl).elim
    · rintro (hz | hz)
      · exact Set.mem_iUnion.mpr ⟨0,
          Set.mem_iUnion.mpr ⟨by decide, hz⟩⟩
      · exact Set.mem_iUnion.mpr ⟨1,
          Set.mem_iUnion.mpr ⟨by decide, hz⟩⟩
  by_cases hcomponent₀ : connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x =
      connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₀
  · have hxPair : x ∈ connectedComponentIn
        (Set.range (arc 1) ∪ Set.range (arc 2))ᶜ x₀ := by
      rw [← hcomponentPair₀, ← hcomponent₀]
      exact mem_connectedComponentIn hx
    refine ⟨0, ?_, ?_⟩
    · rw [hotherRanges₀]
      exact hcomponent₀.trans (hcomponentPair₀.trans
        (connectedComponentIn_eq hxPair))
    · rw [hcomponent₀, hfrontier₀, hotherRanges₀]
  by_cases hcomponent₁ : connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x =
      connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₁
  · have hxPair : x ∈ connectedComponentIn
        (Set.range (arc 0) ∪ Set.range (arc 2))ᶜ x₁ := by
      rw [← hcomponentPair₁, ← hcomponent₁]
      exact mem_connectedComponentIn hx
    refine ⟨1, ?_, ?_⟩
    · rw [hotherRanges₁]
      exact hcomponent₁.trans (hcomponentPair₁.trans
        (connectedComponentIn_eq hxPair))
    · rw [hcomponent₁, hfrontier₁, hotherRanges₁]
  by_cases hcomponent₂ : connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x =
      connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₂
  · have hxPair : x ∈ connectedComponentIn
        (Set.range (arc 0) ∪ Set.range (arc 1))ᶜ x₂ := by
      rw [← hcomponentPair₂, ← hcomponent₂]
      exact mem_connectedComponentIn hx
    refine ⟨2, ?_, ?_⟩
    · rw [hotherRanges₂]
      exact hcomponent₂.trans (hcomponentPair₂.trans
        (connectedComponentIn_eq hxPair))
    · rw [hcomponent₂, hfrontier₂, hotherRanges₂]
  -- Route correction: counting the whole theta complement directly leaves the
  -- ambient set implicit.  Instead, remove the side opposite arm `2`; Theorem
  -- 63.5 counts the resulting remainder, and the component sandwich transports
  -- that count back to the theta complement.
  let C : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Set.range (arc 0) ∪ Set.range (arc 1)
  let A : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Set.range (arc 2)
  have hthetaEq : C ∪ A = ⋃ i, Set.range (arc i) := by
    ext z
    constructor
    · rintro ((hz | hz) | hz)
      · exact Set.mem_iUnion.mpr ⟨0, hz⟩
      · exact Set.mem_iUnion.mpr ⟨1, hz⟩
      · exact Set.mem_iUnion.mpr ⟨2, hz⟩
    · intro hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      fin_cases i
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
  have hthetaC : (⋃ i, Set.range (arc i))ᶜ ⊆ Cᶜ := by
    intro z hzTheta hzC
    exact hzTheta (hthetaEq ▸ Or.inl hzC)
  let x₂C : (Cᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
    ⟨x₂, hthetaC hx₂⟩
  have hcomponentPair₂C :
      connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₂ =
        connectedComponentIn Cᶜ x₂C := by
    simpa only [C, x₂C] using hcomponentPair₂
  have hCzero : arc 0 0 = arc 1 0 := (hzero 0).trans (hzero 1).symm
  have hCone : arc 0 1 = arc 1 1 := (hone 0).trans (hone 1).symm
  have hCinter : Set.range (arc 0) ∩ Set.range (arc 1) =
      {arc 0 0, arc 0 1} := by
    rw [hinter (by decide), hzero 0, hone 0]
  letI : Topology.IsSimpleClosedCurve C :=
    isSimpleClosedCurve_pairArcRanges (arc 0) (arc 1) (harc 0) (harc 1)
      hCzero hCone hCinter
  letI : Topology.IsArc A := ⟨⟨(harc 2).toHomeomorph.symm⟩⟩
  have hAgeometry : IsClosed A ∧ IsConnected A := by
    simpa only [A] using embeddedArcRangeIsClosedAndConnected (arc 2) (harc 2)
  have hCAinter : C ∩ A = {p, q} := by
    ext z
    constructor
    · rintro ⟨hzC, hzA⟩
      rcases hzC with hz₀ | hz₁
      · have hzPair : z ∈ Set.range (arc 0) ∩ Set.range (arc 2) := ⟨hz₀, hzA⟩
        rw [hinter (by decide)] at hzPair
        exact hzPair
      · have hzPair : z ∈ Set.range (arc 1) ∩ Set.range (arc 2) := ⟨hz₁, hzA⟩
        rw [hinter (by decide)] at hzPair
        exact hzPair
    · intro hzPair
      rcases hzPair with rfl | hzq
      · exact ⟨Or.inl ⟨0, hzero 0⟩, ⟨0, hzero 2⟩⟩
      · rw [Set.mem_singleton_iff] at hzq
        subst z
        exact ⟨Or.inl ⟨1, hone 0⟩, ⟨1, hone 2⟩⟩
  have hV₂A : Disjoint (connectedComponentIn Cᶜ x₂C) A := by
    apply Set.disjoint_left.mpr
    intro z hzV hzA
    rw [← hcomponentPair₂C] at hzV
    exact (connectedComponentIn_subset (⋃ i, Set.range (arc i))ᶜ x₂ hzV)
      (Set.mem_iUnion.mpr ⟨2, hzA⟩)
  obtain ⟨hRtwo, hRident⟩ := oppositeJordanComponent_remainder C A x₂C
    hAgeometry.1 hAgeometry.2 (arc_not_separates A) p q hpq hCAinter hV₂A
  let Remainder : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    (closure (connectedComponentIn Cᶜ x₂C) ∪ A)ᶜ
  have hRidentTheta : Remainder =
      (⋃ i, Set.range (arc i))ᶜ \
        connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₂ := by
    calc
      Remainder = (C ∪ A)ᶜ \ connectedComponentIn Cᶜ x₂C := hRident
      _ = (⋃ i, Set.range (arc i))ᶜ \
          connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₂ := by
        rw [hthetaEq, hcomponentPair₂C]
  have hRcard : Cardinal.mk (ConnectedComponents Remainder) = 2 := by
    have hcard := Set.separatesInto_iff.mp hRtwo
    change Cardinal.mk (ConnectedComponents
      ((closure (connectedComponentIn Cᶜ x₂C) ∪ A)ᶜ : Set _)) = 2
    norm_num at hcard ⊢
    exact hcard
  let t : unitInterval := ⟨1 / 2, by norm_num⟩
  have htZero : t ≠ 0 := by
    intro ht
    have := congrArg Subtype.val ht
    norm_num [t] at this
  have htOne : t ≠ 1 := by
    intro ht
    have := congrArg Subtype.val ht
    norm_num [t] at this
  have hmidpointNotOther {i j : Fin 3} (hij : i ≠ j) :
      arc i t ∉ Set.range (arc j) := by
    intro hmem
    have hcommon : arc i t ∈ Set.range (arc i) ∩ Set.range (arc j) :=
      ⟨Set.mem_range_self t, hmem⟩
    rw [hinter hij] at hcommon
    rcases hcommon with hcommon | hcommon
    · exact htZero ((harc i).injective (hcommon.trans (hzero i).symm))
    · rw [Set.mem_singleton_iff] at hcommon
      exact htOne ((harc i).injective (hcommon.trans (hone i).symm))
  have hcomponent₀₁ :
      connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₀ ≠
        connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₁ := by
    intro heq
    have hfrontierEq := congrArg frontier heq
    rw [hfrontier₀, hfrontier₁] at hfrontierEq
    have hmid : arc 1 t ∈ Set.range (arc 1) ∪ Set.range (arc 2) :=
      Or.inl (Set.mem_range_self t)
    rw [hfrontierEq] at hmid
    exact hmid.elim (hmidpointNotOther (by decide))
      (hmidpointNotOther (by decide))
  have hcomponent₀₂ :
      connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₀ ≠
        connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₂ := by
    intro heq
    have hfrontierEq := congrArg frontier heq
    rw [hfrontier₀, hfrontier₂] at hfrontierEq
    have hmid : arc 2 t ∈ Set.range (arc 1) ∪ Set.range (arc 2) :=
      Or.inr (Set.mem_range_self t)
    rw [hfrontierEq] at hmid
    exact hmid.elim (hmidpointNotOther (by decide))
      (hmidpointNotOther (by decide))
  have hcomponent₁₂ :
      connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₁ ≠
        connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₂ := by
    intro heq
    have hfrontierEq := congrArg frontier heq
    rw [hfrontier₁, hfrontier₂] at hfrontierEq
    have hmid : arc 2 t ∈ Set.range (arc 0) ∪ Set.range (arc 2) :=
      Or.inr (Set.mem_range_self t)
    rw [hfrontierEq] at hmid
    exact hmid.elim (hmidpointNotOther (by decide))
      (hmidpointNotOther (by decide))
  have mem_remainder_of_component_ne {z}
      (hz : z ∈ (⋃ i, Set.range (arc i))ᶜ)
      (hne : connectedComponentIn (⋃ i, Set.range (arc i))ᶜ z ≠
        connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₂) :
      z ∈ Remainder := by
    rw [hRidentTheta]
    refine ⟨hz, ?_⟩
    intro hzV
    exact hne (connectedComponentIn_eq hzV).symm
  have component_subset_remainder {z}
      (hne : connectedComponentIn (⋃ i, Set.range (arc i))ᶜ z ≠
        connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₂) :
      connectedComponentIn (⋃ i, Set.range (arc i))ᶜ z ⊆ Remainder := by
    rw [hRidentTheta]
    intro w hw
    refine ⟨connectedComponentIn_subset _ z hw, ?_⟩
    intro hw₂
    exact hne ((connectedComponentIn_eq hw).trans
      (connectedComponentIn_eq hw₂).symm)
  have hRsubsetTheta : Remainder ⊆ (⋃ i, Set.range (arc i))ᶜ := by
    rw [hRidentTheta]
    exact Set.sdiff_subset
  have component_remainder_eq {z}
      (hz : z ∈ (⋃ i, Set.range (arc i))ᶜ)
      (hne : connectedComponentIn (⋃ i, Set.range (arc i))ᶜ z ≠
        connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₂) :
      connectedComponentIn Remainder z =
        connectedComponentIn (⋃ i, Set.range (arc i))ᶜ z := by
    exact connectedComponentIn_eq_of_component_subset hz
      (component_subset_remainder hne) hRsubsetTheta
  have hxR := mem_remainder_of_component_ne hx hcomponent₂
  have hx₀R := mem_remainder_of_component_ne hx₀ hcomponent₀₂
  have hx₁R := mem_remainder_of_component_ne hx₁ hcomponent₁₂
  have hRcomponent₀₁ : connectedComponentIn Remainder x₀ ≠
      connectedComponentIn Remainder x₁ := by
    rw [component_remainder_eq hx₀ hcomponent₀₂,
      component_remainder_eq hx₁ hcomponent₁₂]
    exact hcomponent₀₁
  rcases connectedComponentIn_eq_or_eq_of_mk_eq_two Remainder hRcard
      hxR hx₀R hx₁R hRcomponent₀₁ with hxEq | hxEq
  · rw [component_remainder_eq hx hcomponent₂,
      component_remainder_eq hx₀ hcomponent₀₂] at hxEq
    exact (hcomponent₀ hxEq).elim
  · rw [component_remainder_eq hx hcomponent₂,
      component_remainder_eq hx₁ hcomponent₁₂] at hxEq
    exact (hcomponent₁ hxEq).elim

/-- Helper for Example 50.6: the frontier of a complementary component of three
embedded arcs is contained in the union of two of the arc ranges. -/
private lemma threeEmbeddedArcs_frontier_subset_otherRanges
    (arc : Fin 3 → unitInterval → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (harc : ∀ i, Topology.IsEmbedding (arc i))
    (p q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (hpq : p ≠ q)
    (hzero : ∀ i, arc i 0 = p) (hone : ∀ i, arc i 1 = q)
    (hinter : ∀ {i j}, i ≠ j →
      Set.range (arc i) ∩ Set.range (arc j) = {p, q}) :
    ∀ x, x ∈ (⋃ i, Set.range (arc i))ᶜ →
      ∃ i, frontier (connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x) ⊆
        ⋃ (j : Fin 3) (_ : j ≠ i), Set.range (arc j) := by
  intro x hx
  -- Forget only the component identity from the exact pair classification.
  obtain ⟨i, _, hfrontier⟩ := threeEmbeddedArcs_componentPairClassification
    arc harc p q hpq hzero hone hinter x hx
  exact ⟨i, hfrontier.le⟩

/-- Helper for Example 50.6: two compatible theta presentations of a complete
four-vertex graph force every complementary-component closure to omit a vertex. -/
private lemma twoThetaCrosscut_componentClosure_omitsVertex
    (first dual : Fin 3 → unitInterval →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hfirst : ∀ i, Topology.IsEmbedding (first i))
    (hdual : ∀ i, Topology.IsEmbedding (dual i))
    (p q r s : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hpq : p ≠ q) (hrs : r ≠ s)
    (hfirstZero : ∀ i, first i 0 = p)
    (hfirstOne : ∀ i, first i 1 = q)
    (hdualZero : ∀ i, dual i 0 = r)
    (hdualOne : ∀ i, dual i 1 = s)
    (hfirstInter : ∀ {i j}, i ≠ j →
      Set.range (first i) ∩ Set.range (first j) = {p, q})
    (hdualInter : ∀ {i j}, i ≠ j →
      Set.range (dual i) ∩ Set.range (dual j) = {r, s})
    (houter : Set.range (first 0) ∪ Set.range (first 2) =
      Set.range (dual 0) ∪ Set.range (dual 2))
    (hcarrier : (⋃ i, Set.range (first i)) ∪ Set.range (dual 1) =
      (⋃ i, Set.range (dual i)) ∪ Set.range (first 1))
    (hdualInteriorFirst : Set.range (dual 1) \ {r, s} ⊆
      (⋃ i, Set.range (first i))ᶜ)
    (hfirstDirectOuter : Set.range (first 1) \ {p, q} ⊆
      (Set.range (first 0) ∪ Set.range (first 2))ᶜ)
    (hrFirst : r ∈ Set.range (first 0))
    (hrFirstOther : ∀ j, j ≠ 0 → r ∉ Set.range (first j))
    (hsFirst : s ∈ Set.range (first 2))
    (hsFirstOther : ∀ j, j ≠ 2 → s ∉ Set.range (first j))
    (hpDual : p ∈ Set.range (dual 0))
    (hpDualOther : ∀ j, j ≠ 0 → p ∉ Set.range (dual j))
    (hqDual : q ∈ Set.range (dual 2))
    (hqDualOther : ∀ j, j ≠ 2 → q ∉ Set.range (dual j)) :
    ∀ x, x ∈ ((⋃ i, Set.range (first i)) ∪ Set.range (dual 1))ᶜ →
      p ∉ closure (connectedComponentIn
          ((⋃ i, Set.range (first i)) ∪ Set.range (dual 1))ᶜ x) ∨
      q ∉ closure (connectedComponentIn
          ((⋃ i, Set.range (first i)) ∪ Set.range (dual 1))ᶜ x) ∨
      r ∉ closure (connectedComponentIn
          ((⋃ i, Set.range (first i)) ∪ Set.range (dual 1))ᶜ x) ∨
      s ∉ closure (connectedComponentIn
          ((⋃ i, Set.range (first i)) ∪ Set.range (dual 1))ᶜ x) := by
  classical
  let firstTheta := ⋃ i, Set.range (first i)
  let dualTheta := ⋃ i, Set.range (dual i)
  let Y := firstTheta ∪ Set.range (dual 1)
  let C := Set.range (first 0) ∪ Set.range (first 2)
  intro x hx
  have hYFirst : Yᶜ ⊆ firstThetaᶜ := by
    intro z hzY hzFirst
    exact hzY (Or.inl hzFirst)
  have hYDual : Yᶜ ⊆ dualThetaᶜ := by
    intro z hzY hzDual
    apply hzY
    change z ∈ (⋃ i, Set.range (first i)) ∪ Set.range (dual 1)
    change z ∈ ⋃ i, Set.range (dual i) at hzDual
    rw [hcarrier]
    exact Or.inl hzDual
  have hxFirst : x ∈ firstThetaᶜ := hYFirst hx
  have hxDual : x ∈ dualThetaᶜ := hYDual hx
  have hcomponentFirst : connectedComponentIn Yᶜ x ⊆
      connectedComponentIn firstThetaᶜ x := by
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hx)
      ((connectedComponentIn_subset Yᶜ x).trans hYFirst)
  have hcomponentDual : connectedComponentIn Yᶜ x ⊆
      connectedComponentIn dualThetaᶜ x := by
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hx)
      ((connectedComponentIn_subset Yᶜ x).trans hYDual)
  obtain ⟨i, hxFirstPair, hxFirstFrontier⟩ :=
    threeEmbeddedArcs_componentPairClassification first hfirst p q hpq
      hfirstZero hfirstOne hfirstInter x hxFirst
  fin_cases i
  · -- The first composite arm is omitted, so its internal vertex `r` is omitted.
    have hrOther : r ∉ ⋃ (j : Fin 3) (_ : j ≠ 0), Set.range (first j) := by
      intro hr
      obtain ⟨j, hr⟩ := Set.mem_iUnion.mp hr
      obtain ⟨hj, hrj⟩ := Set.mem_iUnion.mp hr
      exact hrFirstOther j hj hrj
    have hrTheta : r ∉ closure (connectedComponentIn firstThetaᶜ x) :=
      not_mem_closure_connectedComponentIn_of_frontier_subset
        (Set.mem_iUnion.mpr ⟨0, hrFirst⟩) hrOther hxFirstFrontier.le
    exact Or.inr (Or.inr (Or.inl (fun hrY ↦
      hrTheta (closure_mono hcomponentFirst hrY))))
  · -- Only the direct-arm case can reach the crosscut region; classify the
    -- same full-graph component through the dual theta presentation.
    obtain ⟨j, hxDualPair, hxDualFrontier⟩ :=
      threeEmbeddedArcs_componentPairClassification dual hdual r s hrs
        hdualZero hdualOne hdualInter x hxDual
    fin_cases j
    · have hpOther : p ∉ ⋃ (k : Fin 3) (_ : k ≠ 0),
          Set.range (dual k) := by
        intro hp
        obtain ⟨k, hp⟩ := Set.mem_iUnion.mp hp
        obtain ⟨hk, hpk⟩ := Set.mem_iUnion.mp hp
        exact hpDualOther k hk hpk
      have hpTheta : p ∉ closure (connectedComponentIn dualThetaᶜ x) :=
        not_mem_closure_connectedComponentIn_of_frontier_subset
          (Set.mem_iUnion.mpr ⟨0, hpDual⟩) hpOther hxDualFrontier.le
      exact Or.inl (fun hpY ↦ hpTheta (closure_mono hcomponentDual hpY))
    · -- If both classifiers chose their direct arms, the crosscut interior
      -- would lie simultaneously on both sides of the common Jordan curve.
      have hfirstOtherOne :
          (⋃ (k : Fin 3) (_ : k ≠ 1), Set.range (first k)) = C := by
        ext z
        constructor
        · intro hz
          obtain ⟨k, hz⟩ := Set.mem_iUnion.mp hz
          obtain ⟨hk, hzk⟩ := Set.mem_iUnion.mp hz
          fin_cases k
          · exact Or.inl hzk
          · exact (hk rfl).elim
          · exact Or.inr hzk
        · rintro (hz | hz)
          · exact Set.mem_iUnion.mpr ⟨0,
              Set.mem_iUnion.mpr ⟨by decide, hz⟩⟩
          · exact Set.mem_iUnion.mpr ⟨2,
              Set.mem_iUnion.mpr ⟨by decide, hz⟩⟩
      have hdualOtherOne :
          (⋃ (k : Fin 3) (_ : k ≠ 1), Set.range (dual k)) = C := by
        calc
          (⋃ (k : Fin 3) (_ : k ≠ 1), Set.range (dual k)) =
              Set.range (dual 0) ∪ Set.range (dual 2) := by
            ext z
            constructor
            · intro hz
              obtain ⟨k, hz⟩ := Set.mem_iUnion.mp hz
              obtain ⟨hk, hzk⟩ := Set.mem_iUnion.mp hz
              fin_cases k
              · exact Or.inl hzk
              · exact (hk rfl).elim
              · exact Or.inr hzk
            · rintro (hz | hz)
              · exact Set.mem_iUnion.mpr ⟨0,
                  Set.mem_iUnion.mpr ⟨by decide, hz⟩⟩
              · exact Set.mem_iUnion.mpr ⟨2,
                  Set.mem_iUnion.mpr ⟨by decide, hz⟩⟩
          _ = C := houter.symm
      have hxFirstDirect : connectedComponentIn firstThetaᶜ x =
          connectedComponentIn Cᶜ x := by
        change connectedComponentIn (⋃ i, Set.range (first i))ᶜ x =
          connectedComponentIn Cᶜ x
        rw [← hfirstOtherOne]
        exact hxFirstPair
      have hxDualDirect : connectedComponentIn dualThetaᶜ x =
          connectedComponentIn Cᶜ x := by
        change connectedComponentIn (⋃ i, Set.range (dual i))ᶜ x =
          connectedComponentIn Cᶜ x
        rw [← hdualOtherOne]
        exact hxDualPair
      have hCzero : first 0 0 = first 2 0 :=
        (hfirstZero 0).trans (hfirstZero 2).symm
      have hCone : first 0 1 = first 2 1 :=
        (hfirstOne 0).trans (hfirstOne 2).symm
      have hCinter : Set.range (first 0) ∩ Set.range (first 2) =
          {first 0 0, first 0 1} := by
        rw [hfirstInter (by decide), hfirstZero 0, hfirstOne 0]
      letI : Topology.IsSimpleClosedCurve C :=
        isSimpleClosedCurve_pairArcRanges (first 0) (first 2)
          (hfirst 0) (hfirst 2) hCzero hCone hCinter
      have hCcard : Cardinal.mk (ConnectedComponents (Cᶜ : Set _)) = 2 :=
        Set.separatesInto_iff.mp (jordanCurveSphere_separatesInto C)
      let t : unitInterval := ⟨1 / 2, by norm_num⟩
      have htZero : t ≠ 0 := by
        intro ht
        have := congrArg Subtype.val ht
        norm_num [t] at this
      have htOne : t ≠ 1 := by
        intro ht
        have := congrArg Subtype.val ht
        norm_num [t] at this
      let b := first 1 t
      let d := dual 1 t
      have hbInterior : b ∈ Set.range (first 1) \ {p, q} := by
        refine ⟨Set.mem_range_self t, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun h ↦ htZero ((hfirst 1).injective
          (h.trans (hfirstZero 1).symm)),
          fun h ↦ htOne ((hfirst 1).injective
            (h.trans (hfirstOne 1).symm))⟩
      have hdInterior : d ∈ Set.range (dual 1) \ {r, s} := by
        refine ⟨Set.mem_range_self t, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun h ↦ htZero ((hdual 1).injective
          (h.trans (hdualZero 1).symm)),
          fun h ↦ htOne ((hdual 1).injective
            (h.trans (hdualOne 1).symm))⟩
      have hbC : b ∈ Cᶜ := hfirstDirectOuter hbInterior
      have hdFirst : d ∈ firstThetaᶜ := hdualInteriorFirst hdInterior
      have hdC : d ∈ Cᶜ := by
        intro hdC
        rcases hdC with hd0 | hd2
        · exact hdFirst (Set.mem_iUnion.mpr ⟨0, hd0⟩)
        · exact hdFirst (Set.mem_iUnion.mpr ⟨2, hd2⟩)
      have hxC : x ∈ Cᶜ := by
        intro hxC'
        rcases hxC' with hx0 | hx2
        · exact hxFirst (Set.mem_iUnion.mpr ⟨0, hx0⟩)
        · exact hxFirst (Set.mem_iUnion.mpr ⟨2, hx2⟩)
      have hdualInteriorConnected :
          IsConnected (Set.range (dual 1) \ {r, s}) := by
        simpa only [hdualZero 1, hdualOne 1] using
          embeddedArc_range_diff_endpoints_isConnected (dual 1) (hdual 1)
      have hdualInteriorComponent : Set.range (dual 1) \ {r, s} ⊆
          connectedComponentIn firstThetaᶜ d := by
        exact hdualInteriorConnected.2.subset_connectedComponentIn hdInterior
          hdualInteriorFirst
      have hdualEnds := embeddedArc_endpoints_mem_closure_interiorRange
        (dual 1) (hdual 1)
      rw [hdualZero 1, hdualOne 1] at hdualEnds
      have hrClosure : r ∈ closure
          (connectedComponentIn firstThetaᶜ d) :=
        closure_mono hdualInteriorComponent hdualEnds.1
      have hsClosure : s ∈ closure
          (connectedComponentIn firstThetaᶜ d) :=
        closure_mono hdualInteriorComponent hdualEnds.2
      obtain ⟨k, hdPair, hdFrontier⟩ :=
        threeEmbeddedArcs_componentPairClassification first hfirst p q hpq
          hfirstZero hfirstOne hfirstInter d hdFirst
      have hdDirect : connectedComponentIn firstThetaᶜ d =
          connectedComponentIn Cᶜ d := by
        fin_cases k
        · have hrOther : r ∉ ⋃ (l : Fin 3) (_ : l ≠ 0),
              Set.range (first l) := by
            intro hr'
            obtain ⟨l, hr'⟩ := Set.mem_iUnion.mp hr'
            obtain ⟨hl, hrl⟩ := Set.mem_iUnion.mp hr'
            exact hrFirstOther l hl hrl
          exact (not_mem_closure_connectedComponentIn_of_frontier_subset
            (Set.mem_iUnion.mpr ⟨0, hrFirst⟩) hrOther hdFrontier.le
            hrClosure).elim
        · change connectedComponentIn (⋃ i, Set.range (first i))ᶜ d =
              connectedComponentIn Cᶜ d
          rw [← hfirstOtherOne]
          exact hdPair
        · have hsOther : s ∉ ⋃ (l : Fin 3) (_ : l ≠ 2),
              Set.range (first l) := by
            intro hs'
            obtain ⟨l, hs'⟩ := Set.mem_iUnion.mp hs'
            obtain ⟨hl, hsl⟩ := Set.mem_iUnion.mp hs'
            exact hsFirstOther l hl hsl
          exact (not_mem_closure_connectedComponentIn_of_frontier_subset
            (Set.mem_iUnion.mpr ⟨2, hsFirst⟩) hsOther hdFrontier.le
            hsClosure).elim
      have hxCNeB : connectedComponentIn Cᶜ x ≠
          connectedComponentIn Cᶜ b := by
        intro heq
        have hbCx : b ∈ connectedComponentIn Cᶜ x := by
          rw [heq]
          exact mem_connectedComponentIn hbC
        have hbFirstComp : b ∈ connectedComponentIn firstThetaᶜ x :=
          hxFirstDirect.symm ▸ hbCx
        exact (connectedComponentIn_subset firstThetaᶜ x hbFirstComp)
          (Set.mem_iUnion.mpr ⟨1, Set.mem_range_self t⟩)
      have hdCNeB : connectedComponentIn Cᶜ d ≠
          connectedComponentIn Cᶜ b := by
        intro heq
        have hbCd : b ∈ connectedComponentIn Cᶜ d := by
          rw [heq]
          exact mem_connectedComponentIn hbC
        have hbFirstComp : b ∈ connectedComponentIn firstThetaᶜ d :=
          hdDirect.symm ▸ hbCd
        exact (connectedComponentIn_subset firstThetaᶜ d hbFirstComp)
          (Set.mem_iUnion.mpr ⟨1, Set.mem_range_self t⟩)
      have hxCd : connectedComponentIn Cᶜ x =
          connectedComponentIn Cᶜ d := by
        rcases connectedComponentIn_eq_or_eq_of_mk_eq_two Cᶜ hCcard
            hxC hbC hdC hdCNeB.symm with hxb | hxd
        · exact (hxCNeB hxb).elim
        · exact hxd
      have hdCx : d ∈ connectedComponentIn Cᶜ x := by
        rw [hxCd]
        exact mem_connectedComponentIn hdC
      have hdDualComp : d ∈ connectedComponentIn dualThetaᶜ x :=
        hxDualDirect.symm ▸ hdCx
      exact ((connectedComponentIn_subset dualThetaᶜ x hdDualComp)
        (Set.mem_iUnion.mpr ⟨1, Set.mem_range_self t⟩)).elim
    · have hqOther : q ∉ ⋃ (k : Fin 3) (_ : k ≠ 2),
          Set.range (dual k) := by
        intro hq
        obtain ⟨k, hq⟩ := Set.mem_iUnion.mp hq
        obtain ⟨hk, hqk⟩ := Set.mem_iUnion.mp hq
        exact hqDualOther k hk hqk
      have hqTheta : q ∉ closure (connectedComponentIn dualThetaᶜ x) :=
        not_mem_closure_connectedComponentIn_of_frontier_subset
          (Set.mem_iUnion.mpr ⟨2, hqDual⟩) hqOther hxDualFrontier.le
      exact Or.inr (Or.inl (fun hqY ↦
        hqTheta (closure_mono hcomponentDual hqY)))
  · -- The third composite arm is omitted, so its internal vertex `s` is omitted.
    have hsOther : s ∉ ⋃ (j : Fin 3) (_ : j ≠ 2), Set.range (first j) := by
      intro hs'
      obtain ⟨j, hs'⟩ := Set.mem_iUnion.mp hs'
      obtain ⟨hj, hsj⟩ := Set.mem_iUnion.mp hs'
      exact hsFirstOther j hj hsj
    have hsTheta : s ∉ closure (connectedComponentIn firstThetaᶜ x) :=
      not_mem_closure_connectedComponentIn_of_frontier_subset
        (Set.mem_iUnion.mpr ⟨2, hsFirst⟩) hsOther hxFirstFrontier.le
    exact Or.inr (Or.inr (Or.inr (fun hsY ↦
      hsTheta (closure_mono hcomponentFirst hsY))))

/-- Helper for Example 50.6: a realized edge from vertex `4` to a selected
`Fin 4` vertex meets any selected `K₄` edge only at that selected vertex. -/
private lemma embeddedSpoke_inter_selectedEdge_subset_endpoint
    (R : (SimpleGraph.completeGraph (Fin 5)).LinearRealization)
    (F : R.Carrier → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hF : Function.Injective F) (i a b : Fin 4) (hab : a ≠ b)
    (spokeEdge selectedEdge : (SimpleGraph.completeGraph (Fin 5)).edgeSet)
    (hspoke : spokeEdge.1 = s(4, Fin.castAdd 1 i))
    (hselected : selectedEdge.1 = s(Fin.castAdd 1 a, Fin.castAdd 1 b)) :
    F '' R.finiteLinearGraph.edgeSet (R.edgeEquiv spokeEdge) ∩
        F '' R.finiteLinearGraph.edgeSet (R.edgeEquiv selectedEdge) ⊆
      {F (R.vertex (Fin.castAdd 1 i))} := by
  have h4i : (4 : Fin 5) ≠ Fin.castAdd 1 i := by
    intro h
    have := congrArg Fin.val h
    simp at this
    have hiLt := i.isLt
    omega
  have hab' : Fin.castAdd 1 a ≠ Fin.castAdd 1 b := by
    intro h
    apply hab
    apply Fin.ext
    exact congrArg (fun x : Fin 5 ↦ x.val) h
  have hedgeNe : spokeEdge ≠ selectedEdge := by
    intro h
    have hval := congrArg Subtype.val h
    rw [hspoke, hselected, Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · have := congrArg Fin.val hval.1
      simp at this
      have haLt := a.isLt
      omega
    · have := congrArg Fin.val hval.1
      simp at this
      have hbLt := b.isLt
      omega
  have hinterEndpoints :=
    R.finiteLinearGraph.inter_subset_endpoints (R.edgeEquiv.injective.ne hedgeNe)
  have hspokeEndpoints := realizedEdge_endpointPair R h4i spokeEdge hspoke
  have hselectedEndpoints :=
    realizedEdge_endpointPair R hab' selectedEdge hselected
  rintro y ⟨⟨x, hxSpoke, rfl⟩, ⟨z, hzSelected, hxz⟩⟩
  have hzx : z = x := hF hxz
  have hxEndpoints := hinterEndpoints ⟨hxSpoke, hzx ▸ hzSelected⟩
  rw [hspokeEndpoints, hselectedEndpoints] at hxEndpoints
  rcases hxEndpoints with ⟨hx4 | hxi, hxa | hxb⟩
  · have hvertex := R.vertex_injective (hx4.symm.trans hxa)
    have := congrArg Fin.val hvertex
    simp at this
    have haLt := a.isLt
    exfalso
    omega
  · have hvertex := R.vertex_injective (hx4.symm.trans hxb)
    have := congrArg Fin.val hvertex
    simp at this
    have hbLt := b.isLt
    exfalso
    omega
  · exact Set.mem_singleton_iff.mpr (congrArg F hxi)
  · exact Set.mem_singleton_iff.mpr (congrArg F hxi)

-- Route correction: the unavailable §64 frontier classifications are stronger than
-- needed; the endgame uses only omission from complementary-component closures.
/-- Helper for Example 50.6: if every complementary-component closure omits a
marked vertex, connected tendrils from one center to all marked vertices are impossible. -/
private lemma componentClosureOmission_obstructsStar
    {X : Type u} {iota : Type v} [TopologicalSpace X]
    (Y : Set X) (c : X) (vertex : iota → X) (tendril : iota → Set X)
    (hc : c ∈ Yᶜ)
    (homit : ∀ x, x ∈ Yᶜ →
      ∃ i, vertex i ∉ closure (connectedComponentIn Yᶜ x))
    (htendril : ∀ i, IsConnected (tendril i) ∧ c ∈ tendril i ∧
      tendril i ⊆ Yᶜ ∧ vertex i ∈ closure (tendril i)) :
    False := by
  obtain ⟨i, hi⟩ := homit c hc
  -- The selected tendril lies in the component of its common center, so its
  -- marked limiting vertex lies in that component's closure.
  have htendrilComponent : tendril i ⊆ connectedComponentIn Yᶜ c :=
    (htendril i).1.isPreconnected.subset_connectedComponentIn
      (htendril i).2.1 (htendril i).2.2.1
  exact hi (closure_mono htendrilComponent (htendril i).2.2.2)

/-- Helper for Example 50.6: three embedded sphere arcs with common endpoints
force each complementary-component closure to omit a marker from one arm. -/
private lemma threeEmbeddedArcs_componentClosure_omitsMarkedPoint
    (arc : Fin 3 → unitInterval → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (harc : ∀ i, Topology.IsEmbedding (arc i))
    (p q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (hpq : p ≠ q)
    (hzero : ∀ i, arc i 0 = p) (hone : ∀ i, arc i 1 = q)
    (hinter : ∀ {i j}, i ≠ j →
      Set.range (arc i) ∩ Set.range (arc j) = {p, q})
    (marker : Fin 3 → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hmarkerOwn : ∀ i, marker i ∈ Set.range (arc i))
    (hmarkerOther : ∀ {i j}, i ≠ j → marker i ∉ Set.range (arc j)) :
    ∀ x, x ∈ (⋃ i, Set.range (arc i))ᶜ →
      ∃ i, marker i ∉
        closure (connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x) := by
  intro x hx
  -- The separation interface selects the arm omitted by this component's
  -- frontier; the marker on that arm avoids every range in the frontier bound.
  obtain ⟨i, hfrontier⟩ := threeEmbeddedArcs_frontier_subset_otherRanges
    arc harc p q hpq hzero hone hinter x hx
  refine ⟨i, not_mem_closure_connectedComponentIn_of_frontier_subset ?_ ?_ hfrontier⟩
  · exact Set.mem_iUnion.mpr ⟨i, hmarkerOwn i⟩
  · intro hi
    obtain ⟨j, hi⟩ := Set.mem_iUnion.mp hi
    obtain ⟨hji, hij⟩ := Set.mem_iUnion.mp hi
    exact hmarkerOther hji.symm hij

/-- Helper for Example 50.6: a family of connected tendrils from one complementary
component cannot accumulate at vertices omitted by their correspondingly indexed
frontiers. -/
private lemma frontierOmission_obstructsStar
    {X : Type u} {ι : Type v} [TopologicalSpace X]
    (Y : Set X) (B : ι → Set X) (c : X) (vertex : ι → X) (tendril : ι → Set X)
    (hvertex : ∀ i, vertex i ∈ Y) (homit : ∀ i, vertex i ∉ B i)
    (hfrontier : ∃ j, frontier (connectedComponentIn Yᶜ c) = B j)
    (htendril : ∀ i, IsConnected (tendril i) ∧ c ∈ tendril i ∧
      tendril i ⊆ Yᶜ ∧ vertex i ∈ closure (tendril i)) :
    False := by
  obtain ⟨j, hboundary⟩ := hfrontier
  -- Connectedness places the tendril indexed by the chosen boundary in the
  -- complementary component containing its common center.
  have htendril_component : tendril j ⊆ connectedComponentIn Yᶜ c :=
    (htendril j).1.isPreconnected.subset_connectedComponentIn
      (htendril j).2.1 (htendril j).2.2.1
  have hvertex_closure : vertex j ∈ closure (connectedComponentIn Yᶜ c) :=
    closure_mono htendril_component (htendril j).2.2.2
  -- The limiting vertex lies in `Y`, so it cannot lie in the complementary
  -- component itself and must instead lie in the classified frontier.
  rw [closure_eq_self_union_frontier] at hvertex_closure
  rcases hvertex_closure with hcomponent | hcomponentFrontier
  · exact (connectedComponentIn_subset Yᶜ c hcomponent) (hvertex j)
  · rw [hboundary] at hcomponentFrontier
    exact homit j hcomponentFrontier

/-- Helper for Example 50.6: the first theta together with its crosscut has
the six-range normal form used by the selected complete-four carrier. -/
private lemma thetaCrosscutCarrier_eq_sixRanges
    (first : Fin 3 → unitInterval →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (cross a01 a12 a02 a03 a32 a13 : unitInterval →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (htheta : (⋃ i, Set.range (first i)) =
      Set.range (first 0) ∪ Set.range (first 1) ∪ Set.range (first 2))
    (hzero : Set.range (first 0) = Set.range a01 ∪ Set.range a12)
    (hone : Set.range (first 1) = Set.range a02)
    (htwo : Set.range (first 2) = Set.range a03 ∪ Set.range a32)
    (hcross : Set.range cross = Set.range a13) :
    (⋃ i, Set.range (first i)) ∪ Set.range cross =
      ((((Set.range a01 ∪ Set.range a12) ∪ Set.range a02) ∪
        Set.range a03) ∪ Set.range a32) ∪ Set.range a13 := by
  -- Normalize the finite theta union, then reassociate the six primitive ranges.
  rw [htheta, hzero, hone, htwo, hcross]
  ext y
  simp only [Set.mem_union]
  tauto

/-- Helper for Example 50.6: component omission for the selected `K₄` carrier
extends to the four half-open edges from vertex `4`. -/
private lemma existsCompleteFourSpokesOfComponentOmission
    (R : (SimpleGraph.completeGraph (Fin 5)).LinearRealization)
    (F : R.Carrier → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hF : Topology.IsEmbedding F)
    (Y : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
    (e01 e12 e02 e03 e32 e13 : (SimpleGraph.completeGraph (Fin 5)).edgeSet)
    (he01 : e01.1 = s(0, 1)) (he12 : e12.1 = s(1, 2))
    (he02 : e02.1 = s(0, 2)) (he03 : e03.1 = s(0, 3))
    (he32 : e32.1 = s(3, 2)) (he13 : e13.1 = s(1, 3))
    (hY : Y =
      ((((F '' R.finiteLinearGraph.edgeSet (R.edgeEquiv e01) ∪
        F '' R.finiteLinearGraph.edgeSet (R.edgeEquiv e12)) ∪
        F '' R.finiteLinearGraph.edgeSet (R.edgeEquiv e02)) ∪
        F '' R.finiteLinearGraph.edgeSet (R.edgeEquiv e03)) ∪
        F '' R.finiteLinearGraph.edgeSet (R.edgeEquiv e32)) ∪
        F '' R.finiteLinearGraph.edgeSet (R.edgeEquiv e13))
    (homit : ∀ x, x ∈ Yᶜ → ∃ i : Fin 4,
      F (R.vertex (Fin.castAdd 1 i)) ∉
        closure (connectedComponentIn Yᶜ x)) :
    ∃ (c : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (vertex : Fin 4 → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (tendril : Fin 4 → Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)),
      c ∈ Yᶜ ∧
        (∀ x, x ∈ Yᶜ →
          ∃ i, vertex i ∉ closure (connectedComponentIn Yᶜ x)) ∧
        ∀ i, IsConnected (tendril i) ∧ c ∈ tendril i ∧
          tendril i ⊆ Yᶜ ∧ vertex i ∈ closure (tendril i) := by
  classical
  let vertex : Fin 4 → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    fun i ↦ F (R.vertex (Fin.castAdd 1 i))
  have hspokeAdj (i : Fin 4) :
      (SimpleGraph.completeGraph (Fin 5)).Adj 4 (Fin.castAdd 1 i) := by
    intro h
    have hval := congrArg Fin.val h
    simp at hval
    have hiLt := i.isLt
    omega
  let spokeEdge : Fin 4 → (SimpleGraph.completeGraph (Fin 5)).edgeSet :=
    fun i ↦ ⟨s(4, Fin.castAdd 1 i), hspokeAdj i⟩
  have hspokeData : ∀ i, ∃ gamma : unitInterval →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      Topology.IsEmbedding gamma ∧
        gamma 0 = F (R.vertex 4) ∧ gamma 1 = vertex i ∧
        Set.range gamma =
          F '' R.finiteLinearGraph.edgeSet (R.edgeEquiv (spokeEdge i)) := by
    intro i
    have hne : (4 : Fin 5) ≠ Fin.castAdd 1 i := by
      intro h
      have hval := congrArg Fin.val h
      simp at hval
      have hiLt := i.isLt
      omega
    exact existsOrientedEmbeddedRealizedEdge R F hF hne (spokeEdge i) rfl
  choose spoke hspokeEmbedding hspokeZero hspokeOne hspokeRange using hspokeData
  let tendril : Fin 4 → Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    fun i ↦ spoke i '' Set.Ico 0 1
  have htendril (i : Fin 4) : IsConnected (tendril i) ∧
      F (R.vertex 4) ∈ tendril i ∧ tendril i ⊆ Yᶜ ∧
        vertex i ∈ closure (tendril i) := by
    constructor
    · exact (isConnected_Ico zero_lt_one).image (spoke i)
        (hspokeEmbedding i).continuous.continuousOn
    constructor
    · have hzeroMem : (0 : unitInterval) ∈ Set.Ico 0 1 := by simp
      exact ⟨0, ⟨hzeroMem, hspokeZero i⟩⟩
    constructor
    · rintro y ⟨t, ht, rfl⟩
      rw [Set.mem_compl_iff]
      intro hyY
      rw [hY] at hyY
      have htOne : t ≠ 1 := ne_of_lt ht.2
      have hnotSelectedEdge (a b : Fin 4) (hab : a ≠ b)
          (edge : (SimpleGraph.completeGraph (Fin 5)).edgeSet)
          (hedge : edge.1 = s(Fin.castAdd 1 a, Fin.castAdd 1 b)) :
          spoke i t ∉ F '' R.finiteLinearGraph.edgeSet (R.edgeEquiv edge) := by
        intro hyEdge
        have hySpoke : spoke i t ∈
            F '' R.finiteLinearGraph.edgeSet (R.edgeEquiv (spokeEdge i)) := by
          rw [← hspokeRange i]
          exact Set.mem_range_self t
        have hyCommon : spoke i t ∈
            F '' R.finiteLinearGraph.edgeSet (R.edgeEquiv (spokeEdge i)) ∩
              F '' R.finiteLinearGraph.edgeSet (R.edgeEquiv edge) :=
          ⟨hySpoke, hyEdge⟩
        have hyEndpoint := embeddedSpoke_inter_selectedEdge_subset_endpoint
          R F hF.injective i a b hab (spokeEdge i) edge rfl hedge hyCommon
        have hyValue := Set.mem_singleton_iff.mp hyEndpoint
        exact htOne ((hspokeEmbedding i).injective
          (hyValue.trans (hspokeOne i).symm))
      rcases hyY with ((((hy01 | hy12) | hy02) | hy03) | hy32) | hy13
      · exact hnotSelectedEdge 0 1 (by decide) e01 he01 hy01
      · exact hnotSelectedEdge 1 2 (by decide) e12 he12 hy12
      · exact hnotSelectedEdge 0 2 (by decide) e02 he02 hy02
      · exact hnotSelectedEdge 0 3 (by decide) e03 he03 hy03
      · exact hnotSelectedEdge 3 2 (by decide) e32 he32 hy32
      · exact hnotSelectedEdge 1 3 (by decide) e13 he13 hy13
    · have honeClosure : (1 : unitInterval) ∈ closure (Set.Ico 0 1) := by
        rw [closure_Ico zero_ne_one]
        exact ⟨bot_le, le_top⟩
      change vertex i ∈ closure (spoke i '' Set.Ico 0 1)
      rw [← hspokeOne i]
      exact mem_closure_image (hspokeEmbedding i).continuous.continuousAt
        honeClosure
  refine ⟨F (R.vertex 4), vertex, tendril, ?_, homit, htendril⟩
  -- Every half-open spoke contains the common center and lies outside `Y`.
  exact (htendril 0).2.2.1 (htendril 0).2.1

/-- Helper for Example 50.6: an embedded selected `K₄` inside `K₅` supplies
the component-omission data and the four deleted spokes needed by the abstract endgame. -/
private lemma existsSelectedCompleteFourComponentOmissionData
    (R : (SimpleGraph.completeGraph (Fin 5)).LinearRealization)
    (F : R.Carrier → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hF : Topology.IsEmbedding F) :
    ∃ (Y : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
      (c : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (vertex : Fin 4 → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (tendril : Fin 4 → Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)),
      c ∈ Yᶜ ∧
        (∀ x, x ∈ Yᶜ →
          ∃ i, vertex i ∉ closure (connectedComponentIn Yᶜ x)) ∧
        ∀ i, IsConnected (tendril i) ∧ c ∈ tendril i ∧
          tendril i ⊆ Yᶜ ∧ vertex i ∈ closure (tendril i) := by
  classical
  -- Select the six edges on vertices `0,1,2,3`; vertex `4` will supply the spokes.
  have h01Adj : (SimpleGraph.completeGraph (Fin 5)).Adj 0 1 := by simp
  have h12Adj : (SimpleGraph.completeGraph (Fin 5)).Adj 1 2 := by simp
  have h02Adj : (SimpleGraph.completeGraph (Fin 5)).Adj 0 2 := by simp
  have h03Adj : (SimpleGraph.completeGraph (Fin 5)).Adj 0 3 := by simp
  have h32Adj : (SimpleGraph.completeGraph (Fin 5)).Adj 3 2 := by simp
  have h13Adj : (SimpleGraph.completeGraph (Fin 5)).Adj 1 3 := by simp
  let e01 : (SimpleGraph.completeGraph (Fin 5)).edgeSet :=
    ⟨s(0, 1), h01Adj⟩
  let e12 : (SimpleGraph.completeGraph (Fin 5)).edgeSet :=
    ⟨s(1, 2), h12Adj⟩
  let e02 : (SimpleGraph.completeGraph (Fin 5)).edgeSet :=
    ⟨s(0, 2), h02Adj⟩
  let e03 : (SimpleGraph.completeGraph (Fin 5)).edgeSet :=
    ⟨s(0, 3), h03Adj⟩
  let e32 : (SimpleGraph.completeGraph (Fin 5)).edgeSet :=
    ⟨s(3, 2), h32Adj⟩
  let e13 : (SimpleGraph.completeGraph (Fin 5)).edgeSet :=
    ⟨s(1, 3), h13Adj⟩
  obtain ⟨a01, ha01Embedding, ha01Zero, ha01One, ha01Range⟩ :=
    existsOrientedEmbeddedRealizedEdge R F hF (by decide) e01 rfl
  obtain ⟨a12, ha12Embedding, ha12Zero, ha12One, ha12Range⟩ :=
    existsOrientedEmbeddedRealizedEdge R F hF (by decide) e12 rfl
  obtain ⟨a02, ha02Embedding, ha02Zero, ha02One, ha02Range⟩ :=
    existsOrientedEmbeddedRealizedEdge R F hF (by decide) e02 rfl
  obtain ⟨a03, ha03Embedding, ha03Zero, ha03One, ha03Range⟩ :=
    existsOrientedEmbeddedRealizedEdge R F hF (by decide) e03 rfl
  obtain ⟨a32, ha32Embedding, ha32Zero, ha32One, ha32Range⟩ :=
    existsOrientedEmbeddedRealizedEdge R F hF (by decide) e32 rfl
  obtain ⟨a13, ha13Embedding, ha13Zero, ha13One, ha13Range⟩ :=
    existsOrientedEmbeddedRealizedEdge R F hF (by decide) e13 rfl
  obtain ⟨a10, ha10Embedding, ha10Zero, ha10One, ha10Range⟩ :=
    existsOrientedEmbeddedRealizedEdge R F hF
      (a := (1 : Fin 5)) (b := 0) (by decide) e01 (by
        change s((0 : Fin 5), 1) = s(1, 0)
        rw [Sym2.eq_iff]
        exact Or.inr ⟨rfl, rfl⟩)
  obtain ⟨a23, ha23Embedding, ha23Zero, ha23One, ha23Range⟩ :=
    existsOrientedEmbeddedRealizedEdge R F hF
      (a := (2 : Fin 5)) (b := 3) (by decide) e32 (by
        change s((3 : Fin 5), 2) = s(2, 3)
        rw [Sym2.eq_iff]
        exact Or.inr ⟨rfl, rfl⟩)
  -- Record the primitive edge intersections once; all theta incidence follows
  -- by distributing intersections over the concatenated ranges.
  have h01_12 : Set.range a01 ∩ Set.range a12 =
      {F (R.vertex (1 : Fin 5))} := by
    rw [ha01Range, ha12Range]
    apply embeddedRealizedEdge_inter_eq_singleton R F hF.injective
    · intro h
      have hval := congrArg Subtype.val h
      simp [e01, e12] at hval
    · simp [e01]
    · simp [e12]
  have h03_32 : Set.range a03 ∩ Set.range a32 =
      {F (R.vertex (3 : Fin 5))} := by
    rw [ha03Range, ha32Range]
    apply embeddedRealizedEdge_inter_eq_singleton R F hF.injective
    · intro h
      have hval := congrArg Subtype.val h
      simp [e03, e32] at hval
    · simp [e03]
    · simp [e32]
  have h10_03 : Set.range a10 ∩ Set.range a03 =
      {F (R.vertex (0 : Fin 5))} := by
    rw [ha10Range, ha03Range]
    apply embeddedRealizedEdge_inter_eq_singleton R F hF.injective
    · intro h
      have hval := congrArg Subtype.val h
      simp [e01, e03] at hval
    · simp [e01]
    · simp [e03]
  have h12_23 : Set.range a12 ∩ Set.range a23 =
      {F (R.vertex (2 : Fin 5))} := by
    rw [ha12Range, ha23Range]
    apply embeddedRealizedEdge_inter_eq_singleton R F hF.injective
    · intro h
      have hval := congrArg Subtype.val h
      simp [e12, e32] at hval
    · simp [e12]
    · simp [e32]
  have h01_03 : Set.range a01 ∩ Set.range a03 =
      {F (R.vertex (0 : Fin 5))} := by
    rw [ha01Range, ha03Range]
    apply embeddedRealizedEdge_inter_eq_singleton R F hF.injective
    · intro h
      have hval := congrArg Subtype.val h
      simp [e01, e03] at hval
    · simp [e01]
    · simp [e03]
  have h12_32 : Set.range a12 ∩ Set.range a32 =
      {F (R.vertex (2 : Fin 5))} := by
    rw [ha12Range, ha32Range]
    apply embeddedRealizedEdge_inter_eq_singleton R F hF.injective
    · intro h
      have hval := congrArg Subtype.val h
      simp [e12, e32] at hval
    · simp [e12]
    · simp [e32]
  have h01_32 : Set.range a01 ∩ Set.range a32 = ∅ := by
    rw [ha01Range, ha32Range]
    apply embeddedRealizedEdge_inter_eq_empty R F hF.injective
      (a := (0 : Fin 5)) (b := 1) (c := 3) (d := 2)
      (by decide) (by decide) e01 e32 rfl rfl
    · intro h
      have hval := congrArg Subtype.val h
      simp [e01, e32] at hval
    · apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, hx'⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hx'
      omega
  have h12_03 : Set.range a12 ∩ Set.range a03 = ∅ := by
    rw [ha12Range, ha03Range]
    apply embeddedRealizedEdge_inter_eq_empty R F hF.injective
      (a := (1 : Fin 5)) (b := 2) (c := 0) (d := 3)
      (by decide) (by decide) e12 e03 rfl rfl
    · intro h
      have hval := congrArg Subtype.val h
      simp [e12, e03] at hval
    · apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, hx'⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hx'
      omega
  have h02_01 : Set.range a02 ∩ Set.range a01 =
      {F (R.vertex (0 : Fin 5))} := by
    rw [ha02Range, ha01Range]
    apply embeddedRealizedEdge_inter_eq_singleton R F hF.injective
    · intro h
      have hval := congrArg Subtype.val h
      simp [e02, e01] at hval
    · simp [e02]
    · simp [e01]
  have h02_12 : Set.range a02 ∩ Set.range a12 =
      {F (R.vertex (2 : Fin 5))} := by
    rw [ha02Range, ha12Range]
    apply embeddedRealizedEdge_inter_eq_singleton R F hF.injective
    · intro h
      have hval := congrArg Subtype.val h
      simp [e02, e12] at hval
    · simp [e02]
    · simp [e12]
  have h02_03 : Set.range a02 ∩ Set.range a03 =
      {F (R.vertex (0 : Fin 5))} := by
    rw [ha02Range, ha03Range]
    apply embeddedRealizedEdge_inter_eq_singleton R F hF.injective
    · intro h
      have hval := congrArg Subtype.val h
      simp [e02, e03] at hval
    · simp [e02]
    · simp [e03]
  have h02_32 : Set.range a02 ∩ Set.range a32 =
      {F (R.vertex (2 : Fin 5))} := by
    rw [ha02Range, ha32Range]
    apply embeddedRealizedEdge_inter_eq_singleton R F hF.injective
    · intro h
      have hval := congrArg Subtype.val h
      simp [e02, e32] at hval
    · simp [e02]
    · simp [e32]
  have h13_01 : Set.range a13 ∩ Set.range a01 =
      {F (R.vertex (1 : Fin 5))} := by
    rw [ha13Range, ha01Range]
    apply embeddedRealizedEdge_inter_eq_singleton R F hF.injective
    · intro h
      have hval := congrArg Subtype.val h
      simp [e13, e01] at hval
    · simp [e13]
    · simp [e01]
  have h13_12 : Set.range a13 ∩ Set.range a12 =
      {F (R.vertex (1 : Fin 5))} := by
    rw [ha13Range, ha12Range]
    apply embeddedRealizedEdge_inter_eq_singleton R F hF.injective
    · intro h
      have hval := congrArg Subtype.val h
      simp [e13, e12] at hval
    · simp [e13]
    · simp [e12]
  have h13_03 : Set.range a13 ∩ Set.range a03 =
      {F (R.vertex (3 : Fin 5))} := by
    rw [ha13Range, ha03Range]
    apply embeddedRealizedEdge_inter_eq_singleton R F hF.injective
    · intro h
      have hval := congrArg Subtype.val h
      simp [e13, e03] at hval
    · simp [e13]
    · simp [e03]
  have h13_32 : Set.range a13 ∩ Set.range a32 =
      {F (R.vertex (3 : Fin 5))} := by
    rw [ha13Range, ha32Range]
    apply embeddedRealizedEdge_inter_eq_singleton R F hF.injective
    · intro h
      have hval := congrArg Subtype.val h
      simp [e13, e32] at hval
    · simp [e13]
    · simp [e32]
  have h02_13 : Set.range a02 ∩ Set.range a13 = ∅ := by
    rw [ha02Range, ha13Range]
    apply embeddedRealizedEdge_inter_eq_empty R F hF.injective
      (a := (0 : Fin 5)) (b := 2) (c := 1) (d := 3)
      (by decide) (by decide) e02 e13 rfl rfl
    · intro h
      have hval := congrArg Subtype.val h
      simp [e02, e13] at hval
    · apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, hx'⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hx'
      omega
  -- Concatenate adjacent primitive edges to obtain the two compatible theta families.
  obtain ⟨arm012, harm012Embedding, harm012Zero, harm012One, harm012Range⟩ :=
    existsEmbeddedArc_union_of_endpoint_inter_singleton a01 a12
      ha01Embedding ha12Embedding (ha01One.trans ha12Zero.symm) (by
        rw [ha01One]
        exact h01_12)
  obtain ⟨arm032, harm032Embedding, harm032Zero, harm032One, harm032Range⟩ :=
    existsEmbeddedArc_union_of_endpoint_inter_singleton a03 a32
      ha03Embedding ha32Embedding (ha03One.trans ha32Zero.symm) (by
        rw [ha03One]
        exact h03_32)
  obtain ⟨arm103, harm103Embedding, harm103Zero, harm103One, harm103Range⟩ :=
    existsEmbeddedArc_union_of_endpoint_inter_singleton a10 a03
      ha10Embedding ha03Embedding (ha10One.trans ha03Zero.symm) (by
        rw [ha10One]
        exact h10_03)
  obtain ⟨arm123, harm123Embedding, harm123Zero, harm123One, harm123Range⟩ :=
    existsEmbeddedArc_union_of_endpoint_inter_singleton a12 a23
      ha12Embedding ha23Embedding (ha12One.trans ha23Zero.symm) (by
        rw [ha12One]
        exact h12_23)
  let first : Fin 3 → unitInterval →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    ![arm012, a02, arm032]
  let dual : Fin 3 → unitInterval →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    ![arm103, a13, arm123]
  let p := F (R.vertex (0 : Fin 5))
  let q := F (R.vertex (2 : Fin 5))
  let r := F (R.vertex (1 : Fin 5))
  let s := F (R.vertex (3 : Fin 5))
  have hfirstEmbedding (i : Fin 3) : Topology.IsEmbedding (first i) := by
    fin_cases i
    · exact harm012Embedding
    · exact ha02Embedding
    · exact harm032Embedding
  have hdualEmbedding (i : Fin 3) : Topology.IsEmbedding (dual i) := by
    fin_cases i
    · exact harm103Embedding
    · exact ha13Embedding
    · exact harm123Embedding
  have hfirstZero (i : Fin 3) : first i 0 = p := by
    fin_cases i
    · exact harm012Zero.trans ha01Zero
    · exact ha02Zero
    · exact harm032Zero.trans ha03Zero
  have hfirstOne (i : Fin 3) : first i 1 = q := by
    fin_cases i
    · exact harm012One.trans ha12One
    · exact ha02One
    · exact harm032One.trans ha32One
  have hdualZero (i : Fin 3) : dual i 0 = r := by
    fin_cases i
    · exact harm103Zero.trans ha10Zero
    · exact ha13Zero
    · exact harm123Zero.trans ha12Zero
  have hdualOne (i : Fin 3) : dual i 1 = s := by
    fin_cases i
    · exact harm103One.trans ha03One
    · exact ha13One
    · exact harm123One.trans ha23One
  have hfirstRange0 : Set.range (first 0) =
      Set.range a01 ∪ Set.range a12 := by
    exact harm012Range
  have hfirstRange1 : Set.range (first 1) = Set.range a02 := rfl
  have hfirstRange2 : Set.range (first 2) =
      Set.range a03 ∪ Set.range a32 := by
    exact harm032Range
  have hdualRange0 : Set.range (dual 0) =
      Set.range a10 ∪ Set.range a03 := by
    exact harm103Range
  have hdualRange1 : Set.range (dual 1) = Set.range a13 := rfl
  have hdualRange2 : Set.range (dual 2) =
      Set.range a12 ∪ Set.range a23 := by
    exact harm123Range
  have h10_12 : Set.range a10 ∩ Set.range a12 = {r} := by
    rw [ha10Range, ← ha01Range]
    exact h01_12
  have h10_23 : Set.range a10 ∩ Set.range a23 = ∅ := by
    rw [ha10Range, ← ha01Range, ha23Range, ← ha32Range]
    exact h01_32
  have h03_23 : Set.range a03 ∩ Set.range a23 = {s} := by
    rw [ha23Range, ← ha32Range]
    exact h03_32
  have h13_10 : Set.range a13 ∩ Set.range a10 = {r} := by
    rw [ha10Range, ← ha01Range]
    exact h13_01
  have h13_23 : Set.range a13 ∩ Set.range a23 = {s} := by
    rw [ha23Range, ← ha32Range]
    exact h13_32
  have hfirst01 : Set.range (first 0) ∩ Set.range (first 1) = {p, q} := by
    rw [hfirstRange0, hfirstRange1]
    ext y
    constructor
    · rintro ⟨hy01 | hy12, hy02⟩
      · have hy : y ∈ Set.range a02 ∩ Set.range a01 := ⟨hy02, hy01⟩
        rw [h02_01] at hy
        exact Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hy))
      · have hy : y ∈ Set.range a02 ∩ Set.range a12 := ⟨hy02, hy12⟩
        rw [h02_12] at hy
        exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mp hy))
    · intro hy
      rcases Set.mem_insert_iff.mp hy with rfl | hyq
      · exact ⟨Or.inl ⟨0, ha01Zero⟩, ⟨0, ha02Zero⟩⟩
      · rw [Set.mem_singleton_iff] at hyq
        subst y
        exact ⟨Or.inr ⟨1, ha12One⟩, ⟨1, ha02One⟩⟩
  have hfirst12 : Set.range (first 1) ∩ Set.range (first 2) = {p, q} := by
    rw [hfirstRange1, hfirstRange2]
    ext y
    constructor
    · rintro ⟨hy02, hy03 | hy32⟩
      · have hy : y ∈ Set.range a02 ∩ Set.range a03 := ⟨hy02, hy03⟩
        rw [h02_03] at hy
        exact Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hy))
      · have hy : y ∈ Set.range a02 ∩ Set.range a32 := ⟨hy02, hy32⟩
        rw [h02_32] at hy
        exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mp hy))
    · intro hy
      rcases Set.mem_insert_iff.mp hy with rfl | hyq
      · exact ⟨⟨0, ha02Zero⟩, Or.inl ⟨0, ha03Zero⟩⟩
      · rw [Set.mem_singleton_iff] at hyq
        subst y
        exact ⟨⟨1, ha02One⟩, Or.inr ⟨1, ha32One⟩⟩
  have hfirst02 : Set.range (first 0) ∩ Set.range (first 2) = {p, q} := by
    rw [hfirstRange0, hfirstRange2]
    ext y
    constructor
    · rintro ⟨hy01 | hy12, hy03 | hy32⟩
      · have hy : y ∈ Set.range a01 ∩ Set.range a03 := ⟨hy01, hy03⟩
        rw [h01_03] at hy
        exact Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hy))
      · have hy : y ∈ Set.range a01 ∩ Set.range a32 := ⟨hy01, hy32⟩
        rw [h01_32] at hy
        exact hy.elim
      · have hy : y ∈ Set.range a12 ∩ Set.range a03 := ⟨hy12, hy03⟩
        rw [h12_03] at hy
        exact hy.elim
      · have hy : y ∈ Set.range a12 ∩ Set.range a32 := ⟨hy12, hy32⟩
        rw [h12_32] at hy
        exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mp hy))
    · intro hy
      rcases Set.mem_insert_iff.mp hy with rfl | hyq
      · exact ⟨Or.inl ⟨0, ha01Zero⟩, Or.inl ⟨0, ha03Zero⟩⟩
      · rw [Set.mem_singleton_iff] at hyq
        subst y
        exact ⟨Or.inr ⟨1, ha12One⟩, Or.inr ⟨1, ha32One⟩⟩
  have hdual01 : Set.range (dual 0) ∩ Set.range (dual 1) = {r, s} := by
    rw [hdualRange0, hdualRange1]
    ext y
    constructor
    · rintro ⟨hy10 | hy03, hy13⟩
      · have hy : y ∈ Set.range a13 ∩ Set.range a10 := ⟨hy13, hy10⟩
        rw [h13_10] at hy
        exact Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hy))
      · have hy : y ∈ Set.range a13 ∩ Set.range a03 := ⟨hy13, hy03⟩
        rw [h13_03] at hy
        exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mp hy))
    · intro hy
      rcases Set.mem_insert_iff.mp hy with rfl | hys
      · exact ⟨Or.inl ⟨0, ha10Zero⟩, ⟨0, ha13Zero⟩⟩
      · rw [Set.mem_singleton_iff] at hys
        subst y
        exact ⟨Or.inr ⟨1, ha03One⟩, ⟨1, ha13One⟩⟩
  have hdual12 : Set.range (dual 1) ∩ Set.range (dual 2) = {r, s} := by
    rw [hdualRange1, hdualRange2]
    ext y
    constructor
    · rintro ⟨hy13, hy12 | hy23⟩
      · have hy : y ∈ Set.range a13 ∩ Set.range a12 := ⟨hy13, hy12⟩
        rw [h13_12] at hy
        exact Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hy))
      · have hy : y ∈ Set.range a13 ∩ Set.range a23 := ⟨hy13, hy23⟩
        rw [h13_23] at hy
        exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mp hy))
    · intro hy
      rcases Set.mem_insert_iff.mp hy with rfl | hys
      · exact ⟨⟨0, ha13Zero⟩, Or.inl ⟨0, ha12Zero⟩⟩
      · rw [Set.mem_singleton_iff] at hys
        subst y
        exact ⟨⟨1, ha13One⟩, Or.inr ⟨1, ha23One⟩⟩
  have hdual02 : Set.range (dual 0) ∩ Set.range (dual 2) = {r, s} := by
    rw [hdualRange0, hdualRange2]
    ext y
    constructor
    · rintro ⟨hy10 | hy03, hy12 | hy23⟩
      · have hy : y ∈ Set.range a10 ∩ Set.range a12 := ⟨hy10, hy12⟩
        rw [h10_12] at hy
        exact Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hy))
      · have hy : y ∈ Set.range a10 ∩ Set.range a23 := ⟨hy10, hy23⟩
        rw [h10_23] at hy
        exact hy.elim
      · have hy : y ∈ Set.range a12 ∩ Set.range a03 := ⟨hy12, hy03⟩
        rw [h12_03] at hy
        exact hy.elim
      · have hy : y ∈ Set.range a03 ∩ Set.range a23 := ⟨hy03, hy23⟩
        rw [h03_23] at hy
        exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mp hy))
    · intro hy
      rcases Set.mem_insert_iff.mp hy with rfl | hys
      · exact ⟨Or.inl ⟨0, ha10Zero⟩, Or.inl ⟨0, ha12Zero⟩⟩
      · rw [Set.mem_singleton_iff] at hys
        subst y
        exact ⟨Or.inr ⟨1, ha03One⟩, Or.inr ⟨1, ha23One⟩⟩
  have hfirstInter {i j : Fin 3} (hij : i ≠ j) :
      Set.range (first i) ∩ Set.range (first j) = {p, q} := by
    fin_cases i
    · fin_cases j
      · exact (hij rfl).elim
      · exact hfirst01
      · exact hfirst02
    · fin_cases j
      · rw [Set.inter_comm]
        exact hfirst01
      · exact (hij rfl).elim
      · exact hfirst12
    · fin_cases j
      · rw [Set.inter_comm]
        exact hfirst02
      · rw [Set.inter_comm]
        exact hfirst12
      · exact (hij rfl).elim
  have hdualInter {i j : Fin 3} (hij : i ≠ j) :
      Set.range (dual i) ∩ Set.range (dual j) = {r, s} := by
    fin_cases i
    · fin_cases j
      · exact (hij rfl).elim
      · exact hdual01
      · exact hdual02
    · fin_cases j
      · rw [Set.inter_comm]
        exact hdual01
      · exact (hij rfl).elim
      · exact hdual12
    · fin_cases j
      · rw [Set.inter_comm]
        exact hdual02
      · rw [Set.inter_comm]
        exact hdual12
      · exact (hij rfl).elim
  have hfirstTheta : (⋃ i, Set.range (first i)) =
      Set.range (first 0) ∪ Set.range (first 1) ∪ Set.range (first 2) := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hy
      fin_cases i
      · exact Or.inl (Or.inl hyi)
      · exact Or.inl (Or.inr hyi)
      · exact Or.inr hyi
    · rintro ((hy | hy) | hy)
      · exact Set.mem_iUnion.mpr ⟨0, hy⟩
      · exact Set.mem_iUnion.mpr ⟨1, hy⟩
      · exact Set.mem_iUnion.mpr ⟨2, hy⟩
  have hdualTheta : (⋃ i, Set.range (dual i)) =
      Set.range (dual 0) ∪ Set.range (dual 1) ∪ Set.range (dual 2) := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hy
      fin_cases i
      · exact Or.inl (Or.inl hyi)
      · exact Or.inl (Or.inr hyi)
      · exact Or.inr hyi
    · rintro ((hy | hy) | hy)
      · exact Set.mem_iUnion.mpr ⟨0, hy⟩
      · exact Set.mem_iUnion.mpr ⟨1, hy⟩
      · exact Set.mem_iUnion.mpr ⟨2, hy⟩
  have houter : Set.range (first 0) ∪ Set.range (first 2) =
      Set.range (dual 0) ∪ Set.range (dual 2) := by
    rw [hfirstRange0, hfirstRange2, hdualRange0, hdualRange2]
    rw [ha10Range, ← ha01Range, ha23Range, ← ha32Range]
    ext y
    simp only [Set.mem_union]
    tauto
  have hcarrier : (⋃ i, Set.range (first i)) ∪ Set.range (dual 1) =
      (⋃ i, Set.range (dual i)) ∪ Set.range (first 1) := by
    rw [hfirstTheta, hdualTheta, hfirstRange0, hfirstRange1,
      hfirstRange2, hdualRange0, hdualRange1, hdualRange2]
    rw [ha10Range, ← ha01Range, ha23Range, ← ha32Range]
    ext y
    simp only [Set.mem_union]
    tauto
  have hdualInteriorFirst : Set.range (dual 1) \ {r, s} ⊆
      (⋃ i, Set.range (first i))ᶜ := by
    rintro y ⟨hy13, hyEnds⟩ hyFirst
    obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hyFirst
    fin_cases i
    · have hyi' : y ∈ Set.range arm012 := by
        simpa [first] using hyi
      rw [harm012Range] at hyi'
      rcases hyi' with hy01 | hy12
      · have hy : y ∈ Set.range a13 ∩ Set.range a01 := ⟨hy13, hy01⟩
        rw [h13_01] at hy
        exact hyEnds (Set.mem_insert_iff.mpr
          (Or.inl (Set.mem_singleton_iff.mp hy)))
      · have hy : y ∈ Set.range a13 ∩ Set.range a12 := ⟨hy13, hy12⟩
        rw [h13_12] at hy
        exact hyEnds (Set.mem_insert_iff.mpr
          (Or.inl (Set.mem_singleton_iff.mp hy)))
    · have hyi' : y ∈ Set.range a02 := by
        simpa [first] using hyi
      have hy : y ∈ Set.range a02 ∩ Set.range a13 := ⟨hyi', hy13⟩
      rw [h02_13, Set.mem_empty_iff_false] at hy
      exact hy.elim
    · have hyi' : y ∈ Set.range arm032 := by
        simpa [first] using hyi
      rw [harm032Range] at hyi'
      rcases hyi' with hy03 | hy32
      · have hy : y ∈ Set.range a13 ∩ Set.range a03 := ⟨hy13, hy03⟩
        rw [h13_03] at hy
        exact hyEnds (Set.mem_insert_iff.mpr
          (Or.inr (Set.mem_singleton_iff.mp hy)))
      · have hy : y ∈ Set.range a13 ∩ Set.range a32 := ⟨hy13, hy32⟩
        rw [h13_32] at hy
        exact hyEnds (Set.mem_insert_iff.mpr
          (Or.inr (Set.mem_singleton_iff.mp hy)))
  have hfirstDirectOuter : Set.range (first 1) \ {p, q} ⊆
      (Set.range (first 0) ∪ Set.range (first 2))ᶜ := by
    rintro y ⟨hy, hyEnds⟩ (hy0 | hy2)
    · have hinter : y ∈ Set.range (first 1) ∩ Set.range (first 0) :=
        ⟨hy, hy0⟩
      rw [hfirstInter (by decide)] at hinter
      exact hyEnds hinter
    · have hinter : y ∈ Set.range (first 1) ∩ Set.range (first 2) :=
        ⟨hy, hy2⟩
      rw [hfirstInter (by decide)] at hinter
      exact hyEnds hinter
  have hrFirst : r ∈ Set.range (first 0) := by
    rw [hfirstRange0]
    exact Or.inl ⟨1, ha01One⟩
  have hsFirst : s ∈ Set.range (first 2) := by
    rw [hfirstRange2]
    exact Or.inl ⟨1, ha03One⟩
  have hpDual : p ∈ Set.range (dual 0) := by
    rw [hdualRange0]
    exact Or.inl ⟨1, ha10One⟩
  have hqDual : q ∈ Set.range (dual 2) := by
    rw [hdualRange2]
    exact Or.inl ⟨1, ha12One⟩
  have hrFirstOther (j : Fin 3) (hj : j ≠ 0) : r ∉ Set.range (first j) := by
    intro hrj
    have hrPair : r ∈ Set.range (first 0) ∩ Set.range (first j) :=
      ⟨hrFirst, hrj⟩
    rw [hfirstInter hj.symm] at hrPair
    rcases hrPair with hrp | hrq
    · have hvertex := hF.injective hrp
      exact (by decide : (1 : Fin 5) ≠ 0) (R.vertex_injective hvertex)
    · have hvertex := hF.injective (Set.mem_singleton_iff.mp hrq)
      exact (by decide : (1 : Fin 5) ≠ 2) (R.vertex_injective hvertex)
  have hsFirstOther (j : Fin 3) (hj : j ≠ 2) : s ∉ Set.range (first j) := by
    intro hsj
    have hsPair : s ∈ Set.range (first 2) ∩ Set.range (first j) :=
      ⟨hsFirst, hsj⟩
    rw [hfirstInter hj.symm] at hsPair
    rcases hsPair with hsp | hsq
    · have hvertex := hF.injective hsp
      exact (by decide : (3 : Fin 5) ≠ 0) (R.vertex_injective hvertex)
    · have hvertex := hF.injective (Set.mem_singleton_iff.mp hsq)
      exact (by decide : (3 : Fin 5) ≠ 2) (R.vertex_injective hvertex)
  have hpDualOther (j : Fin 3) (hj : j ≠ 0) : p ∉ Set.range (dual j) := by
    intro hpj
    have hpPair : p ∈ Set.range (dual 0) ∩ Set.range (dual j) :=
      ⟨hpDual, hpj⟩
    rw [hdualInter hj.symm] at hpPair
    rcases hpPair with hpr | hps
    · have hvertex := hF.injective hpr
      exact (by decide : (0 : Fin 5) ≠ 1) (R.vertex_injective hvertex)
    · have hvertex := hF.injective (Set.mem_singleton_iff.mp hps)
      exact (by decide : (0 : Fin 5) ≠ 3) (R.vertex_injective hvertex)
  have hqDualOther (j : Fin 3) (hj : j ≠ 2) : q ∉ Set.range (dual j) := by
    intro hqj
    have hqPair : q ∈ Set.range (dual 2) ∩ Set.range (dual j) :=
      ⟨hqDual, hqj⟩
    rw [hdualInter hj.symm] at hqPair
    rcases hqPair with hqr | hqs
    · have hvertex := hF.injective hqr
      exact (by decide : (2 : Fin 5) ≠ 1) (R.vertex_injective hvertex)
    · have hvertex := hF.injective (Set.mem_singleton_iff.mp hqs)
      exact (by decide : (2 : Fin 5) ≠ 3) (R.vertex_injective hvertex)
  have hpq : p ≠ q := hF.injective.ne (R.vertex_injective.ne (by decide))
  have hrs : r ≠ s := hF.injective.ne (R.vertex_injective.ne (by decide))
  let Y := (⋃ i, Set.range (first i)) ∪ Set.range (dual 1)
  let vertex : Fin 4 → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    fun i ↦ F (R.vertex (Fin.castAdd 1 i))
  have homit : ∀ x, x ∈ Yᶜ →
      ∃ i, vertex i ∉ closure (connectedComponentIn Yᶜ x) := by
    intro x hx
    rcases twoThetaCrosscut_componentClosure_omitsVertex first dual
        hfirstEmbedding hdualEmbedding p q r s hpq hrs hfirstZero hfirstOne
        hdualZero hdualOne hfirstInter hdualInter houter hcarrier
        hdualInteriorFirst hfirstDirectOuter hrFirst hrFirstOther hsFirst
        hsFirstOther hpDual hpDualOther hqDual hqDualOther x hx with
      hp | hq | hr | hs
    · exact ⟨0, hp⟩
    · exact ⟨2, hq⟩
    · exact ⟨1, hr⟩
    · exact ⟨3, hs⟩
  have hYRanges : Y =
      ((((Set.range a01 ∪ Set.range a12) ∪ Set.range a02) ∪
        Set.range a03) ∪ Set.range a32) ∪ Set.range a13 := by
    exact thetaCrosscutCarrier_eq_sixRanges first (dual 1)
      a01 a12 a02 a03 a32 a13 hfirstTheta hfirstRange0 hfirstRange1
      hfirstRange2 hdualRange1
  have hYEdges : Y =
      ((((F '' R.finiteLinearGraph.edgeSet (R.edgeEquiv e01) ∪
        F '' R.finiteLinearGraph.edgeSet (R.edgeEquiv e12)) ∪
        F '' R.finiteLinearGraph.edgeSet (R.edgeEquiv e02)) ∪
        F '' R.finiteLinearGraph.edgeSet (R.edgeEquiv e03)) ∪
        F '' R.finiteLinearGraph.edgeSet (R.edgeEquiv e32)) ∪
        F '' R.finiteLinearGraph.edgeSet (R.edgeEquiv e13) := by
    rw [hYRanges, ha01Range, ha12Range, ha02Range, ha03Range,
      ha32Range, ha13Range]
  obtain ⟨c, vertex', tendril, hc, homit', htendril⟩ :=
    existsCompleteFourSpokesOfComponentOmission R F hF Y
      e01 e12 e02 e03 e32 e13 rfl rfl rfl rfl rfl rfl hYEdges homit
  exact ⟨Y, c, vertex', tendril, hc, homit', htendril⟩

/-- Helper for Example 50.6: an embedded utilities graph supplies a theta union,
three marked houses, and the three deleted utility spokes needed by the abstract endgame. -/
private lemma existsUtilitiesComponentOmissionData
    (R : (completeBipartiteGraph (Fin 3) (Fin 3)).LinearRealization)
    (F : R.Carrier → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hF : Topology.IsEmbedding F) :
    ∃ (Y : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
      (c : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (vertex : Fin 3 → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (tendril : Fin 3 → Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)),
      c ∈ Yᶜ ∧
        (∀ x, x ∈ Yᶜ →
          ∃ i, vertex i ∉ closure (connectedComponentIn Yᶜ x)) ∧
        ∀ i, IsConnected (tendril i) ∧ c ∈ tendril i ∧
          tendril i ⊆ Yᶜ ∧ vertex i ∈ closure (tendril i) := by
  classical
  -- Use utilities `1` and `2` as the theta endpoints, with one arm through
  -- each house; utility `0` supplies the three deleted spokes.
  have hleftAdj (i : Fin 3) :
      (completeBipartiteGraph (Fin 3) (Fin 3)).Adj (.inl 1) (.inr i) :=
    Or.inl ⟨rfl, rfl⟩
  have hrightAdj (i : Fin 3) :
      (completeBipartiteGraph (Fin 3) (Fin 3)).Adj (.inr i) (.inl 2) :=
    Or.inr ⟨rfl, rfl⟩
  have hspokeAdj (i : Fin 3) :
      (completeBipartiteGraph (Fin 3) (Fin 3)).Adj (.inl 0) (.inr i) :=
    Or.inl ⟨rfl, rfl⟩
  let leftEdge : Fin 3 → (completeBipartiteGraph (Fin 3) (Fin 3)).edgeSet :=
    fun i ↦ ⟨s(.inl 1, .inr i), hleftAdj i⟩
  let rightEdge : Fin 3 → (completeBipartiteGraph (Fin 3) (Fin 3)).edgeSet :=
    fun i ↦ ⟨s(.inr i, .inl 2), hrightAdj i⟩
  let spokeEdge : Fin 3 → (completeBipartiteGraph (Fin 3) (Fin 3)).edgeSet :=
    fun i ↦ ⟨s(.inl 0, .inr i), hspokeAdj i⟩
  have hleftData : ∀ i, ∃ gamma : unitInterval →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      Topology.IsEmbedding gamma ∧
        gamma 0 = F (R.vertex (.inl 1)) ∧
        gamma 1 = F (R.vertex (.inr i)) ∧
        Set.range gamma =
          F '' R.finiteLinearGraph.edgeSet (R.edgeEquiv (leftEdge i)) := by
    intro i
    have hne : (Sum.inl (1 : Fin 3) : Fin 3 ⊕ Fin 3) ≠ .inr i := by simp
    exact existsOrientedEmbeddedRealizedEdge R F hF hne (leftEdge i) rfl
  choose left hleftEmbedding hleftZero hleftOne hleftRange using hleftData
  have hrightData : ∀ i, ∃ gamma : unitInterval →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      Topology.IsEmbedding gamma ∧
        gamma 0 = F (R.vertex (.inr i)) ∧
        gamma 1 = F (R.vertex (.inl 2)) ∧
        Set.range gamma =
          F '' R.finiteLinearGraph.edgeSet (R.edgeEquiv (rightEdge i)) := by
    intro i
    have hne : (Sum.inr i : Fin 3 ⊕ Fin 3) ≠ .inl 2 := by simp
    exact existsOrientedEmbeddedRealizedEdge R F hF hne (rightEdge i) rfl
  choose right hrightEmbedding hrightZero hrightOne hrightRange using hrightData
  have hspokeData : ∀ i, ∃ gamma : unitInterval →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      Topology.IsEmbedding gamma ∧
        gamma 0 = F (R.vertex (.inl 0)) ∧
        gamma 1 = F (R.vertex (.inr i)) ∧
        Set.range gamma =
          F '' R.finiteLinearGraph.edgeSet (R.edgeEquiv (spokeEdge i)) := by
    intro i
    have hne : (Sum.inl (0 : Fin 3) : Fin 3 ⊕ Fin 3) ≠ .inr i := by simp
    exact existsOrientedEmbeddedRealizedEdge R F hF hne (spokeEdge i) rfl
  choose spoke hspokeEmbedding hspokeZero hspokeOne hspokeRange using hspokeData
  have hleftRightInter (i : Fin 3) :
      Set.range (left i) ∩ Set.range (right i) = {F (R.vertex (.inr i))} := by
    rw [hleftRange i, hrightRange i]
    apply embeddedRealizedEdge_inter_eq_singleton R F hF.injective
    · intro h
      have hval := congrArg Subtype.val h
      simp [leftEdge, rightEdge] at hval
    · simp [leftEdge]
    · simp [rightEdge]
  have harmData : ∀ i, ∃ gamma : unitInterval →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      Topology.IsEmbedding gamma ∧
        gamma 0 = F (R.vertex (.inl 1)) ∧
        gamma 1 = F (R.vertex (.inl 2)) ∧
        Set.range gamma = Set.range (left i) ∪ Set.range (right i) := by
    intro i
    have hinter : Set.range (left i) ∩ Set.range (right i) = {left i 1} := by
      rw [hleftOne i]
      exact hleftRightInter i
    obtain ⟨gamma, hgamma, hzero, hone, hrange⟩ :=
      existsEmbeddedArc_union_of_endpoint_inter_singleton
      (left i) (right i) (hleftEmbedding i) (hrightEmbedding i)
      ((hleftOne i).trans (hrightZero i).symm) hinter
    exact ⟨gamma, hgamma, hzero.trans (hleftZero i),
      hone.trans (hrightOne i), hrange⟩
  choose arm harmEmbedding harmZero harmOne harmRange using harmData
  have hendpointNe :
      F (R.vertex (.inl (1 : Fin 3))) ≠ F (R.vertex (.inl (2 : Fin 3))) := by
    have hne : (Sum.inl (1 : Fin 3) : Fin 3 ⊕ Fin 3) ≠ .inl 2 := by simp
    exact hF.injective.ne (R.vertex_injective.ne hne)
  have hleftInter {i j : Fin 3} (hij : i ≠ j) :
      Set.range (left i) ∩ Set.range (left j) = {F (R.vertex (.inl 1))} := by
    rw [hleftRange i, hleftRange j]
    apply embeddedRealizedEdge_inter_eq_singleton R F hF.injective
    · intro h
      have hval := congrArg Subtype.val h
      rw [show (leftEdge i).1 = s(.inl 1, .inr i) from rfl,
        show (leftEdge j).1 = s(.inl 1, .inr j) from rfl, Sym2.eq_iff] at hval
      have hij' : i = j := by simpa using hval
      exact hij hij'
    · simp [leftEdge]
    · simp [leftEdge]
  have hrightInter {i j : Fin 3} (hij : i ≠ j) :
      Set.range (right i) ∩ Set.range (right j) = {F (R.vertex (.inl 2))} := by
    rw [hrightRange i, hrightRange j]
    apply embeddedRealizedEdge_inter_eq_singleton R F hF.injective
    · intro h
      have hval := congrArg Subtype.val h
      rw [show (rightEdge i).1 = s(.inr i, .inl 2) from rfl,
        show (rightEdge j).1 = s(.inr j, .inl 2) from rfl, Sym2.eq_iff] at hval
      have hij' : i = j := by simpa using hval
      exact hij hij'
    · simp [rightEdge]
    · simp [rightEdge]
  have hleftRightDisjoint {i j : Fin 3} (hij : i ≠ j) :
      Set.range (left i) ∩ Set.range (right j) = ∅ := by
    rw [hleftRange i, hrightRange j]
    have hab : (Sum.inl (1 : Fin 3) : Fin 3 ⊕ Fin 3) ≠ .inr i := by simp
    have hcd : (Sum.inr j : Fin 3 ⊕ Fin 3) ≠ .inl 2 := by simp
    apply embeddedRealizedEdge_inter_eq_empty R F hF.injective
        hab hcd (leftEdge i) (rightEdge j) rfl rfl
    · intro h
      have hval := congrArg Subtype.val h
      simp [leftEdge, rightEdge, hij] at hval
    · apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, hy⟩
      rcases hx with rfl | rfl
      · simp at hy
      · simp [hij] at hy
  have hrightLeftDisjoint {i j : Fin 3} (hij : i ≠ j) :
      Set.range (right i) ∩ Set.range (left j) = ∅ := by
    rw [hrightRange i, hleftRange j]
    have hab : (Sum.inr i : Fin 3 ⊕ Fin 3) ≠ .inl 2 := by simp
    have hcd : (Sum.inl (1 : Fin 3) : Fin 3 ⊕ Fin 3) ≠ .inr j := by simp
    apply embeddedRealizedEdge_inter_eq_empty R F hF.injective
        hab hcd (rightEdge i) (leftEdge j) rfl rfl
    · intro h
      have hval := congrArg Subtype.val h
      simp [leftEdge, rightEdge, hij] at hval
    · apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, hy⟩
      rcases hx with rfl | rfl
      · simp [hij] at hy
      · simp at hy
  have harmInter {i j : Fin 3} (hij : i ≠ j) :
      Set.range (arm i) ∩ Set.range (arm j) =
        {F (R.vertex (.inl 1)), F (R.vertex (.inl 2))} := by
    rw [harmRange i, harmRange j]
    ext y
    constructor
    · rintro ⟨hleft | hright, hleft' | hright'⟩
      · have hy : y ∈ Set.range (left i) ∩ Set.range (left j) :=
          ⟨hleft, hleft'⟩
        rw [hleftInter hij] at hy
        exact Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hy))
      · have hy : y ∈ Set.range (left i) ∩ Set.range (right j) :=
          ⟨hleft, hright'⟩
        rw [hleftRightDisjoint hij] at hy
        exact hy.elim
      · have hy : y ∈ Set.range (right i) ∩ Set.range (left j) :=
          ⟨hright, hleft'⟩
        rw [hrightLeftDisjoint hij] at hy
        exact hy.elim
      · have hy : y ∈ Set.range (right i) ∩ Set.range (right j) :=
          ⟨hright, hright'⟩
        rw [hrightInter hij] at hy
        exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mp hy))
    · intro hy
      rcases Set.mem_insert_iff.mp hy with rfl | hy
      · exact ⟨Or.inl ⟨0, hleftZero i⟩, Or.inl ⟨0, hleftZero j⟩⟩
      · rw [Set.mem_singleton_iff] at hy
        subst y
        exact ⟨Or.inr ⟨1, hrightOne i⟩, Or.inr ⟨1, hrightOne j⟩⟩
  let marker : Fin 3 → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    fun i ↦ F (R.vertex (.inr i))
  have hmarkerOwn (i : Fin 3) : marker i ∈ Set.range (arm i) := by
    rw [harmRange i]
    exact Or.inl ⟨1, hleftOne i⟩
  have hmarkerOther {i j : Fin 3} (hij : i ≠ j) :
      marker i ∉ Set.range (arm j) := by
    intro hmarkerJ
    have hcommon : marker i ∈ Set.range (arm i) ∩ Set.range (arm j) :=
      ⟨hmarkerOwn i, hmarkerJ⟩
    rw [harmInter hij] at hcommon
    rcases hcommon with hmarkerP | hmarkerQ
    · have hvertex := hF.injective hmarkerP
      have := R.vertex_injective hvertex
      simp at this
    · have hvertex := hF.injective (Set.mem_singleton_iff.mp hmarkerQ)
      have := R.vertex_injective hvertex
      simp at this
  have hspokeLeftSame (i : Fin 3) :
      Set.range (spoke i) ∩ Set.range (left i) = {marker i} := by
    rw [hspokeRange i, hleftRange i]
    apply embeddedRealizedEdge_inter_eq_singleton R F hF.injective
    · intro h
      have hval := congrArg Subtype.val h
      simp [spokeEdge, leftEdge] at hval
    · simp [spokeEdge]
    · simp [leftEdge]
  have hspokeRightSame (i : Fin 3) :
      Set.range (spoke i) ∩ Set.range (right i) = {marker i} := by
    rw [hspokeRange i, hrightRange i]
    apply embeddedRealizedEdge_inter_eq_singleton R F hF.injective
    · intro h
      have hval := congrArg Subtype.val h
      simp [spokeEdge, rightEdge] at hval
    · simp [spokeEdge]
    · simp [rightEdge]
  have hspokeLeftDisjoint {i j : Fin 3} (hij : i ≠ j) :
      Set.range (spoke i) ∩ Set.range (left j) = ∅ := by
    rw [hspokeRange i, hleftRange j]
    have hab : (Sum.inl (0 : Fin 3) : Fin 3 ⊕ Fin 3) ≠ .inr i := by simp
    have hcd : (Sum.inl (1 : Fin 3) : Fin 3 ⊕ Fin 3) ≠ .inr j := by simp
    apply embeddedRealizedEdge_inter_eq_empty R F hF.injective
        hab hcd (spokeEdge i) (leftEdge j) rfl rfl
    · intro h
      have hval := congrArg Subtype.val h
      simp [spokeEdge, leftEdge, hij] at hval
    · apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, hy⟩
      rcases hx with rfl | rfl
      · simp at hy
      · simp [hij] at hy
  have hspokeRightDisjoint {i j : Fin 3} (hij : i ≠ j) :
      Set.range (spoke i) ∩ Set.range (right j) = ∅ := by
    rw [hspokeRange i, hrightRange j]
    have hab : (Sum.inl (0 : Fin 3) : Fin 3 ⊕ Fin 3) ≠ .inr i := by simp
    have hcd : (Sum.inr j : Fin 3 ⊕ Fin 3) ≠ .inl 2 := by simp
    apply embeddedRealizedEdge_inter_eq_empty R F hF.injective
        hab hcd (spokeEdge i) (rightEdge j) rfl rfl
    · intro h
      have hval := congrArg Subtype.val h
      simp [spokeEdge, rightEdge, hij] at hval
    · apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, hy⟩
      rcases hx with rfl | rfl
      · simp at hy
      · simp [hij] at hy
  let Y := ⋃ i, Set.range (arm i)
  have homit : ∀ x, x ∈ Yᶜ →
      ∃ i, marker i ∉ closure (connectedComponentIn Yᶜ x) := by
    intro x hx
    exact threeEmbeddedArcs_componentClosure_omitsMarkedPoint arm harmEmbedding
      (F (R.vertex (.inl 1))) (F (R.vertex (.inl 2))) hendpointNe
      harmZero harmOne harmInter marker hmarkerOwn hmarkerOther x hx
  -- The remaining edge to each house is used without its house endpoint; this
  -- half-open image is connected and accumulates at the omitted marker.
  let tendril : Fin 3 → Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    fun i ↦ spoke i '' Set.Ico 0 1
  have htendril (i : Fin 3) : IsConnected (tendril i) ∧
      F (R.vertex (.inl 0)) ∈ tendril i ∧ tendril i ⊆ Yᶜ ∧
        marker i ∈ closure (tendril i) := by
    constructor
    · exact (isConnected_Ico zero_lt_one).image (spoke i)
        (hspokeEmbedding i).continuous.continuousOn
    constructor
    · have hzeroMem : (0 : unitInterval) ∈ Set.Ico 0 1 := by simp
      exact ⟨0, ⟨hzeroMem, hspokeZero i⟩⟩
    constructor
    · rintro y ⟨t, ht, rfl⟩
      rw [Set.mem_compl_iff]
      intro hyY
      rcases Set.mem_iUnion.mp hyY with ⟨j, hyArm⟩
      rw [harmRange j] at hyArm
      have htOne : t ≠ 1 := ne_of_lt ht.2
      rcases hyArm with hyLeft | hyRight
      · by_cases hij : i = j
        · subst j
          have hcommon : spoke i t ∈ Set.range (spoke i) ∩ Set.range (left i) :=
            ⟨Set.mem_range_self t, hyLeft⟩
          rw [hspokeLeftSame i] at hcommon
          have hvalue := Set.mem_singleton_iff.mp hcommon
          exact htOne ((hspokeEmbedding i).injective (hvalue.trans (hspokeOne i).symm))
        · have hcommon : spoke i t ∈ Set.range (spoke i) ∩ Set.range (left j) :=
            ⟨Set.mem_range_self t, hyLeft⟩
          rw [hspokeLeftDisjoint hij] at hcommon
          exact hcommon
      · by_cases hij : i = j
        · subst j
          have hcommon : spoke i t ∈ Set.range (spoke i) ∩ Set.range (right i) :=
            ⟨Set.mem_range_self t, hyRight⟩
          rw [hspokeRightSame i] at hcommon
          have hvalue := Set.mem_singleton_iff.mp hcommon
          exact htOne ((hspokeEmbedding i).injective (hvalue.trans (hspokeOne i).symm))
        · have hcommon : spoke i t ∈ Set.range (spoke i) ∩ Set.range (right j) :=
            ⟨Set.mem_range_self t, hyRight⟩
          rw [hspokeRightDisjoint hij] at hcommon
          exact hcommon
    · have honeClosure : (1 : unitInterval) ∈ closure (Set.Ico 0 1) := by
        rw [closure_Ico zero_ne_one]
        exact ⟨bot_le, le_top⟩
      change F (R.vertex (.inr i)) ∈ closure (spoke i '' Set.Ico 0 1)
      rw [← hspokeOne i]
      exact mem_closure_image (hspokeEmbedding i).continuous.continuousAt honeClosure
  refine ⟨Y, F (R.vertex (.inl 0)), marker, tendril, ?_, homit, htendril⟩
  -- The common spoke center belongs to every tendril and hence lies outside the theta union.
  exact (htendril 0).2.2.1 (htendril 0).2.1

/-- Example 50.6 (4). No topological linear-graph realization of the complete graph on
five vertices embeds in the plane. The proof is deferred to §64. -/
theorem completeGraphFive_not_isEmbedding
    (R : (SimpleGraph.completeGraph (Fin 5)).LinearRealization) :
    ¬ ∃ f : R.Carrier → ℝ × ℝ, Topology.IsEmbedding f := by
  rintro ⟨f, hf⟩
  -- Transport the hypothetical plane embedding to the standard sphere, where
  -- the complementary-component closure obstruction is naturally formulated.
  obtain ⟨F, hF⟩ := existsSphereEmbeddingOfPlaneEmbedding f hf
  have hSphereObstruction : ¬ Topology.IsEmbedding F := by
    intro hF'
    -- Extract the selected `K₄`, its omitted closure marker, and all four
    -- spokes, then close the contradiction at the common deleted vertex.
    obtain ⟨Y, c, vertex, tendril, hc, homit, htendril⟩ :=
      existsSelectedCompleteFourComponentOmissionData R F hF'
    exact componentClosureOmission_obstructsStar Y c vertex tendril hc homit htendril
  exact hSphereObstruction hF

/- The complete graph on five vertices has this canonical combinatorial owner. -/
#check SimpleGraph.completeGraph (Fin 5)

/-- The gas-water-electricity assertion of Example 50.6 (5): no topological
linear-graph realization of this graph embeds in the plane. The proof is deferred
to §64. -/
theorem utilitiesGraph_not_isEmbedding
    (R : (completeBipartiteGraph (Fin 3) (Fin 3)).LinearRealization) :
    ¬ ∃ f : R.Carrier → ℝ × ℝ, Topology.IsEmbedding f := by
  rintro ⟨f, hf⟩
  -- Transport the hypothetical plane embedding to the standard sphere, where
  -- the complementary-component closure obstruction is naturally formulated.
  obtain ⟨F, hF⟩ := existsSphereEmbeddingOfPlaneEmbedding f hf
  have hSphereObstruction : ¬ Topology.IsEmbedding F := by
    intro hF'
    -- Extract the theta union, one omitted house marker, and the three spokes
    -- from the remaining utility, then apply the shared closure endgame.
    obtain ⟨Y, c, vertex, tendril, hc, homit, htendril⟩ :=
      existsUtilitiesComponentOmissionData R F hF'
    exact componentClosureOmission_obstructsStar Y c vertex tendril hc homit htendril
  exact hSphereObstruction hF

/- The utilities graph has this canonical combinatorial owner. -/
#check completeBipartiteGraph (Fin 3) (Fin 3)
