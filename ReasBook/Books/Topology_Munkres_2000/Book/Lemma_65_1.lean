module

public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Topology_Munkres_2000.Book.Definition_61_3.SimpleClosedCurve
public import Topology_Munkres_2000.Book.Lemma_55_1.Inclusions
public import Topology_Munkres_2000.Book.Lemma_64_3
public import Topology_Munkres_2000.Book.Theorem_63_1
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Topology.Connected.Basic

public section

open Set
open scoped Sym2

namespace CompleteGraphFour

/-- The edge of a realized complete graph on four vertices joining distinct vertices
`i` and `j`, viewed as a subset of the standard two-sphere. -/
def edge
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) (i j : Fin 4) (hij : i ≠ j) : Set (StandardSphere 2) :=
  R.ambientEdge X e ⟨s(i, j), hij⟩

/-- The point at parameter `t` on the edge joining distinct vertices `i` and `j` in a
realized complete graph on four vertices. -/
def edgePoint
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) (i j : Fin 4) (hij : i ≠ j) (t : unitInterval) :
    StandardSphere 2 :=
  e (R.finiteLinearGraph.edge (R.edgeEquiv ⟨s(i, j), hij⟩) t)

/-- Helper for Lemma 65.1: every parameter point belongs to its ambient
realized edge. -/
private lemma edgePoint_mem_edge
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) {i j : Fin 4} (hij : i ≠ j)
    (t : unitInterval) : edgePoint X R e i j hij t ∈ edge X R e i j hij := by
  -- The intrinsic parameter point witnesses membership in the ambient image.
  rw [edge, SimpleGraph.LinearRealization.ambientEdge_eq_image_edgeSet]
  refine ⟨e (R.finiteLinearGraph.edge (R.edgeEquiv ⟨s(i, j), hij⟩) t), ?_, rfl⟩
  exact ⟨R.finiteLinearGraph.edge (R.edgeEquiv ⟨s(i, j), hij⟩) t,
    R.finiteLinearGraph.edgeSet_def (R.edgeEquiv ⟨s(i, j), hij⟩) ▸
      Set.mem_range_self t, rfl⟩

/-- Helper for Lemma 65.1: a nonendpoint parameter point of a realized edge
does not lie on a distinct realized edge. -/
private lemma edgePoint_not_mem_edge_of_pair_ne
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) {i j k l : Fin 4} (hij : i ≠ j) (hkl : k ≠ l)
    (hpairs : s(i, j) ≠ s(k, l)) (t : unitInterval)
    (ht_zero : t ≠ 0) (ht_one : t ≠ 1) :
    edgePoint X R e i j hij t ∉ edge X R e k l hkl := by
  -- Pull a hypothetical ambient intersection back through the realization.
  intro htEdge
  let diagonal : (SimpleGraph.completeGraph (Fin 4)).edgeSet := ⟨s(i, j), hij⟩
  let other : (SimpleGraph.completeGraph (Fin 4)).edgeSet := ⟨s(k, l), hkl⟩
  have hdiagonal_ne_other : diagonal ≠ other := by
    intro h
    exact hpairs (congrArg Subtype.val h)
  have hedge_ne : R.edgeEquiv diagonal ≠ R.edgeEquiv other :=
    R.edgeEquiv.injective.ne hdiagonal_ne_other
  have htDiagonal :
      R.finiteLinearGraph.edge (R.edgeEquiv diagonal) t ∈
        R.finiteLinearGraph.edgeSet (R.edgeEquiv diagonal) := by
    rw [R.finiteLinearGraph.edgeSet_def]
    exact Set.mem_range_self t
  rw [edge, SimpleGraph.LinearRealization.ambientEdge_eq_image_edgeSet] at htEdge
  rcases htEdge with ⟨y, ⟨x, hxOther, rfl⟩, hy⟩
  have hySubtype :
      e x = e (R.finiteLinearGraph.edge (R.edgeEquiv diagonal) t) := by
    apply Subtype.ext
    exact hy
  have hx : x = R.finiteLinearGraph.edge (R.edgeEquiv diagonal) t :=
    e.injective hySubtype
  have htEndpoints := R.finiteLinearGraph.inter_subset_endpoints hedge_ne
    ⟨htDiagonal, hx ▸ hxOther⟩
  -- The intrinsic edge embedding then forces the parameter to be an endpoint.
  rcases htEndpoints.1 with htStart | htEnd
  · apply ht_zero
    exact (R.finiteLinearGraph.edgeEmbedding (R.edgeEquiv diagonal)).injective htStart
  · apply ht_one
    exact (R.finiteLinearGraph.edgeEmbedding (R.edgeEquiv diagonal)).injective
      (Set.mem_singleton_iff.mp htEnd)

/-- Helper for Lemma 65.1: a realized vertex incident to an abstract edge lies
in the corresponding intrinsic realized edge. -/
private lemma realizedVertex_mem_edgeSet
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    {a b : Fin 4} (_hab : a ≠ b)
    (graphEdge : (SimpleGraph.completeGraph (Fin 4)).edgeSet)
    (hedge : graphEdge.1 = s(a, b)) :
    R.vertex a ∈ R.finiteLinearGraph.edgeSet (R.edgeEquiv graphEdge) := by
  -- Incidence identifies the vertex with one of the two edge parameters.
  rw [R.finiteLinearGraph.edgeSet_def]
  have ha : a ∈ graphEdge.1 := hedge ▸ Sym2.mem_mk_left a b
  rcases (R.incident_iff_endpoint graphEdge a).mp ha with haZero | haOne
  · exact ⟨0, haZero.symm⟩
  · exact ⟨1, haOne.symm⟩

/-- Helper for Lemma 65.1: the parameter endpoints of a realized edge are
exactly its two realized combinatorial vertices. -/
private lemma realizedEdge_endpointPair
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    {a b : Fin 4} (hab : a ≠ b)
    (graphEdge : (SimpleGraph.completeGraph (Fin 4)).edgeSet)
    (hedge : graphEdge.1 = s(a, b)) :
    ({R.finiteLinearGraph.edge (R.edgeEquiv graphEdge) 0,
        R.finiteLinearGraph.edge (R.edgeEquiv graphEdge) 1} : Set R.Carrier) =
      {R.vertex a, R.vertex b} := by
  -- The two distinct incident vertices must occupy opposite interval endpoints.
  have ha : a ∈ graphEdge.1 := hedge ▸ Sym2.mem_mk_left a b
  have hb : b ∈ graphEdge.1 := hedge ▸ Sym2.mem_mk_right a b
  have haEndpoint := (R.incident_iff_endpoint graphEdge a).mp ha
  have hbEndpoint := (R.incident_iff_endpoint graphEdge b).mp hb
  have hvertexNe : R.vertex a ≠ R.vertex b := R.vertex_injective.ne hab
  rcases haEndpoint with haZero | haOne
  · rcases hbEndpoint with hbZero | hbOne
    · exact (hvertexNe (haZero.trans hbZero.symm)).elim
    · rw [haZero, hbOne]
  · rcases hbEndpoint with hbZero | hbOne
    · rw [haOne, hbZero, Set.pair_comm]
    · exact (hvertexNe (haOne.trans hbOne.symm)).elim

/-- Helper for Lemma 65.1: a realized edge can be parameterized in either
chosen direction between its two ambient vertices. -/
private lemma existsOrientedEdge
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) {a b : Fin 4} (hab : a ≠ b) :
    ∃ gamma : unitInterval → StandardSphere 2,
      Topology.IsEmbedding gamma ∧
      gamma 0 = e (R.vertex a) ∧ gamma 1 = e (R.vertex b) ∧
      Set.range gamma = edge X R e a b hab := by
  let graphEdge : (SimpleGraph.completeGraph (Fin 4)).edgeSet := ⟨s(a, b), hab⟩
  let raw := R.finiteLinearGraph.edge (R.edgeEquiv graphEdge)
  let ambientRaw : unitInterval → StandardSphere 2 := fun t ↦ e (raw t)
  have hrawEmbedding : Topology.IsEmbedding raw :=
    R.finiteLinearGraph.edgeEmbedding (R.edgeEquiv graphEdge)
  have hambientEmbedding : Topology.IsEmbedding ambientRaw :=
    Topology.IsEmbedding.subtypeVal.comp (e.isEmbedding.comp hrawEmbedding)
  have ha : a ∈ graphEdge.1 := Sym2.mem_mk_left a b
  have hb : b ∈ graphEdge.1 := Sym2.mem_mk_right a b
  have haEndpoint := (R.incident_iff_endpoint graphEdge a).mp ha
  have hbEndpoint := (R.incident_iff_endpoint graphEdge b).mp hb
  have hvertexNe : R.vertex a ≠ R.vertex b := R.vertex_injective.ne hab
  have hrange : Set.range ambientRaw = edge X R e a b hab := by
    rw [edge, SimpleGraph.LinearRealization.ambientEdge_eq_image_edgeSet]
    unfold ambientRaw raw
    rw [R.finiteLinearGraph.edgeSet_def]
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨e (R.finiteLinearGraph.edge (R.edgeEquiv graphEdge) t),
        ⟨R.finiteLinearGraph.edge (R.edgeEquiv graphEdge) t,
          Set.mem_range_self t, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨_, ⟨t, rfl⟩, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
  -- Reverse the stored parameterization exactly when its endpoints have the
  -- opposite orientation from the requested vertices.
  rcases haEndpoint with haZero | haOne
  · rcases hbEndpoint with hbZero | hbOne
    · exact (hvertexNe (haZero.trans hbZero.symm)).elim
    · refine ⟨ambientRaw, hambientEmbedding, ?_, ?_, hrange⟩
      · exact congrArg (fun x : R.Carrier ↦ (e x : StandardSphere 2)) haZero.symm
      · exact congrArg (fun x : R.Carrier ↦ (e x : StandardSphere 2)) hbOne.symm
  · rcases hbEndpoint with hbZero | hbOne
    · let gamma : unitInterval → StandardSphere 2 :=
        fun t ↦ ambientRaw (unitInterval.symm t)
      refine ⟨gamma,
        hambientEmbedding.comp unitInterval.symmHomeomorph.isEmbedding, ?_, ?_, ?_⟩
      · simpa [gamma, ambientRaw, raw] using
          congrArg (fun x : R.Carrier ↦ (e x : StandardSphere 2)) haOne.symm
      · simpa [gamma, ambientRaw, raw] using
          congrArg (fun x : R.Carrier ↦ (e x : StandardSphere 2)) hbZero.symm
      · rw [← hrange]
        apply Set.Subset.antisymm
        · rintro _ ⟨t, rfl⟩
          exact Set.mem_range_self (unitInterval.symm t)
        · rintro _ ⟨t, rfl⟩
          exact ⟨unitInterval.symm t, by simp [gamma]⟩
    · exact (hvertexNe (haOne.trans hbOne.symm)).elim

/-- Helper for Lemma 65.1: both transported combinatorial endpoints belong to
their ambient realized edge. -/
private lemma ambientVertices_mem_edge
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) {a b : Fin 4} (hab : a ≠ b) :
    (e (R.vertex a) : StandardSphere 2) ∈ edge X R e a b hab ∧
      (e (R.vertex b) : StandardSphere 2) ∈ edge X R e a b hab := by
  obtain ⟨gamma, -, hzero, hone, hrange⟩ := existsOrientedEdge X R e hab
  -- The two interval endpoints witness membership in the parameterized range.
  rw [← hrange]
  exact ⟨⟨0, hzero⟩, ⟨1, hone⟩⟩

/-- Helper for Lemma 65.1: two distinct realized edges intersect exactly in
the intersection of their transported endpoint pairs. -/
private lemma edge_inter_edge_eq_endpointPairs
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) {a b c d : Fin 4} (hab : a ≠ b) (hcd : c ≠ d)
    (hpairs : s(a, b) ≠ s(c, d)) :
    edge X R e a b hab ∩ edge X R e c d hcd =
      ({(e (R.vertex a) : StandardSphere 2),
          (e (R.vertex b) : StandardSphere 2)} ∩
        {(e (R.vertex c) : StandardSphere 2),
          (e (R.vertex d) : StandardSphere 2)} : Set (StandardSphere 2)) := by
  let first : (SimpleGraph.completeGraph (Fin 4)).edgeSet := ⟨s(a, b), hab⟩
  let second : (SimpleGraph.completeGraph (Fin 4)).edgeSet := ⟨s(c, d), hcd⟩
  have hfirst_ne_second : first ≠ second := by
    intro h
    exact hpairs (congrArg Subtype.val h)
  have hedgeNe : R.edgeEquiv first ≠ R.edgeEquiv second :=
    R.edgeEquiv.injective.ne hfirst_ne_second
  have hinterEndpoints := R.finiteLinearGraph.inter_subset_endpoints hedgeNe
  have hfirstEndpoints := realizedEdge_endpointPair R hab first rfl
  have hsecondEndpoints := realizedEdge_endpointPair R hcd second rfl
  have hinjective : Function.Injective
      (fun x : R.Carrier ↦ (e x : StandardSphere 2)) :=
    Subtype.val_injective.comp e.injective
  rw [edge, edge, SimpleGraph.LinearRealization.ambientEdge_eq_image_edgeSet,
    SimpleGraph.LinearRealization.ambientEdge_eq_image_edgeSet]
  apply Set.Subset.antisymm
  · -- Pull a common ambient point back to the intrinsic edge intersection.
    rintro y ⟨⟨_, ⟨x, hxFirst, rfl⟩, rfl⟩, ⟨_, ⟨z, hzSecond, rfl⟩, hxz⟩⟩
    have hzx : z = x := hinjective hxz
    have hxEndpoints := hinterEndpoints ⟨hxFirst, hzx ▸ hzSecond⟩
    rw [hfirstEndpoints, hsecondEndpoints] at hxEndpoints
    rcases hxEndpoints with ⟨hxab, hxcd⟩
    constructor
    · rcases hxab with hxa | hxb
      · exact Or.inl (congrArg (fun w : R.Carrier ↦
          (e w : StandardSphere 2)) hxa)
      · exact Or.inr (Set.mem_singleton_iff.mpr
          (congrArg (fun w : R.Carrier ↦ (e w : StandardSphere 2)) hxb))
    · rcases hxcd with hxc | hxd
      · exact Or.inl (congrArg (fun w : R.Carrier ↦
          (e w : StandardSphere 2)) hxc)
      · exact Or.inr (Set.mem_singleton_iff.mpr
          (congrArg (fun w : R.Carrier ↦ (e w : StandardSphere 2)) hxd))
  · -- Conversely, each common transported endpoint lies on both edges.
    rintro y ⟨hyab, hycd⟩
    rcases hyab with hya | hyb
    · rcases hycd with hyc | hyd
      · exact ⟨⟨e (R.vertex a),
          ⟨R.vertex a, realizedVertex_mem_edgeSet R hab first rfl, rfl⟩,
            hya.symm⟩,
          ⟨e (R.vertex c),
            ⟨R.vertex c, realizedVertex_mem_edgeSet R hcd second rfl, rfl⟩,
              hyc.symm⟩⟩
      · have hyd' : y = (e (R.vertex d) : StandardSphere 2) :=
          Set.mem_singleton_iff.mp hyd
        have hsecondSymm : second.1 = s(d, c) := by
          rw [Sym2.eq_iff]
          exact Or.inr ⟨rfl, rfl⟩
        exact ⟨⟨e (R.vertex a),
          ⟨R.vertex a, realizedVertex_mem_edgeSet R hab first rfl, rfl⟩,
            hya.symm⟩,
          ⟨e (R.vertex d),
            ⟨R.vertex d,
              realizedVertex_mem_edgeSet R hcd.symm second hsecondSymm, rfl⟩,
              hyd'.symm⟩⟩
    · rcases hycd with hyc | hyd
      · have hyb' : y = (e (R.vertex b) : StandardSphere 2) :=
          Set.mem_singleton_iff.mp hyb
        have hfirstSymm : first.1 = s(b, a) := by
          rw [Sym2.eq_iff]
          exact Or.inr ⟨rfl, rfl⟩
        exact ⟨⟨e (R.vertex b),
          ⟨R.vertex b,
            realizedVertex_mem_edgeSet R hab.symm first hfirstSymm, rfl⟩,
            hyb'.symm⟩,
          ⟨e (R.vertex c),
            ⟨R.vertex c, realizedVertex_mem_edgeSet R hcd second rfl, rfl⟩,
              hyc.symm⟩⟩
      · have hyb' : y = (e (R.vertex b) : StandardSphere 2) :=
          Set.mem_singleton_iff.mp hyb
        have hyd' : y = (e (R.vertex d) : StandardSphere 2) :=
          Set.mem_singleton_iff.mp hyd
        have hfirstSymm : first.1 = s(b, a) := by
          rw [Sym2.eq_iff]
          exact Or.inr ⟨rfl, rfl⟩
        have hsecondSymm : second.1 = s(d, c) := by
          rw [Sym2.eq_iff]
          exact Or.inr ⟨rfl, rfl⟩
        exact ⟨⟨e (R.vertex b),
          ⟨R.vertex b,
            realizedVertex_mem_edgeSet R hab.symm first hfirstSymm, rfl⟩,
            hyb'.symm⟩,
          ⟨e (R.vertex d),
            ⟨R.vertex d,
              realizedVertex_mem_edgeSet R hcd.symm second hsecondSymm, rfl⟩,
              hyd'.symm⟩⟩

/-- Helper for Lemma 65.1: concatenating injective paths whose ranges meet
only at their common endpoint preserves injectivity. -/
private lemma pathTrans_injective_of_range_inter_eq_singleton
    {Z : Type*} [TopologicalSpace Z] {a b c : Z}
    (gamma : Path a b) (delta : Path b c)
    (hgamma : Function.Injective gamma) (hdelta : Function.Injective delta)
    (hinter : Set.range gamma ∩ Set.range delta = {b}) :
    Function.Injective (gamma.trans delta) := by
  -- Equal values in the same half reduce to injectivity of the corresponding path.
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
        exact ⟨by linarith [s.2.1], by linarith⟩
      have htv : 2 * (t : ℝ) - 1 ∈ Set.Icc (0 : ℝ) 1 := by
        exact ⟨by linarith, by linarith [t.2.2]⟩
      let su : unitInterval := ⟨2 * (s : ℝ), hsu⟩
      let tv : unitInterval := ⟨2 * (t : ℝ) - 1, htv⟩
      have hst' : gamma su = delta tv := hst
      have hmem : gamma su ∈ Set.range gamma ∩ Set.range delta :=
        ⟨Set.mem_range_self su, tv, hst'.symm⟩
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
        exact ⟨by linarith, by linarith [s.2.2]⟩
      have htv : 2 * (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
        exact ⟨by linarith [t.2.1], by linarith⟩
      let su : unitInterval := ⟨2 * (s : ℝ) - 1, hsu⟩
      let tv : unitInterval := ⟨2 * (t : ℝ), htv⟩
      have hst' : delta su = gamma tv := hst
      have hmem : gamma tv ∈ Set.range gamma ∩ Set.range delta :=
        ⟨Set.mem_range_self tv, su, hst'⟩
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

/-- Helper for Lemma 65.1: two embedded arcs meeting only at their joining
endpoint concatenate to an embedded arc whose range is their union. -/
private lemma existsEmbeddedArcWithRangeUnion
    {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    (a b : unitInterval → Z) (ha : Topology.IsEmbedding a)
    (hb : Topology.IsEmbedding b) (hend : a 1 = b 0)
    (hinter : Set.range a ∩ Set.range b = {a 1}) :
    ∃ gamma : unitInterval → Z, Topology.IsEmbedding gamma ∧
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
  have halphaCoe : (alpha : unitInterval → Z) = a := rfl
  have hbetaCoe : (beta : unitInterval → Z) = b := by
    exact Path.cast_coe rawBeta hend rfl
  have hbetaEmbedding : Topology.IsEmbedding beta := by
    rw [hbetaCoe]
    exact hb
  have hinter' : Set.range alpha ∩ Set.range beta = {a 1} := by
    rw [halphaCoe, hbetaCoe]
    exact hinter
  have hgammaInjective : Function.Injective gamma :=
    pathTrans_injective_of_range_inter_eq_singleton alpha beta
      (halphaCoe.symm ▸ ha.injective) hbetaEmbedding.injective hinter'
  refine ⟨gamma, gamma.continuous.isClosedEmbedding hgammaInjective |>.isEmbedding,
    gamma.source, gamma.target, ?_⟩
  -- Path concatenation has exactly the union of the two input ranges.
  rw [Path.trans_range, halphaCoe, hbetaCoe]

/-- Helper for Lemma 65.1: two embedded arcs with the same endpoints and no
other intersection form a simple closed curve. -/
private lemma isSimpleClosedCurve_pairArcRanges
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (a b : unitInterval → Y) (ha : Topology.IsEmbedding a)
    (hb : Topology.IsEmbedding b) (hzero : a 0 = b 0)
    (hone : a 1 = b 1)
    (hinter : Set.range a ∩ Set.range b = {a 0, a 1}) :
    Topology.IsSimpleClosedCurve ↑(Set.range a ∪ Set.range b) := by
  classical
  let upper : Set Circle := Set.range (Circle.path 1 (-1))
  let lower : Set Circle := Set.range (Circle.path (-1) 1)
  let upperParam : Circle → unitInterval := Function.invFun (Circle.path 1 (-1))
  let lowerParam : Circle → unitInterval := Function.invFun (Circle.path (-1) 1)
  let upperMap : Circle → Y := fun z ↦ a (upperParam z)
  let lowerMap : Circle → Y := fun z ↦ b (unitInterval.symm (lowerParam z))
  let pasted : Circle → Y := upper.piecewise upperMap lowerMap
  have hpathUpper : Function.Injective (Circle.path 1 (-1)) :=
    Circle.path_injective_of_ne (Circle.neg_ne_self 1).symm
  have hpathLower : Function.Injective (Circle.path (-1) 1) :=
    Circle.path_injective_of_ne (Circle.neg_ne_self 1)
  have hcover : upper ∪ lower = Set.univ :=
    Circle.range_path_union_range_path (Circle.neg_ne_self 1).symm
  have hpathsInter : upper ∩ lower = {(1 : Circle), -1} :=
    Circle.range_path_inter_range_path (Circle.neg_ne_self 1).symm
  have hupperClosed : IsClosed upper :=
    (isCompact_range (Circle.path 1 (-1)).continuous).isClosed
  have hlowerClosed : IsClosed lower :=
    (isCompact_range (Circle.path (-1) 1).continuous).isClosed
  -- The inverse path parameters are continuous on their respective semicircles.
  have hupperMapContinuous : ContinuousOn upperMap upper := by
    rw [continuousOn_iff_continuous_restrict]
    let upperEquiv :=
      (Circle.path 1 (-1)).continuous.isClosedEmbedding hpathUpper |>.isEmbedding
        |>.toHomeomorph
    have hformula : upper.restrict upperMap = a ∘ upperEquiv.symm := by
      funext z
      apply congrArg a
      apply hpathUpper
      exact (Function.invFun_eq z.property).trans
        (congrArg Subtype.val (upperEquiv.apply_symm_apply z)).symm
    rw [hformula]
    exact ha.continuous.comp upperEquiv.symm.continuous
  have hlowerMapContinuous : ContinuousOn lowerMap lower := by
    rw [continuousOn_iff_continuous_restrict]
    let lowerEquiv :=
      (Circle.path (-1) 1).continuous.isClosedEmbedding hpathLower |>.isEmbedding
        |>.toHomeomorph
    have hformula : lower.restrict lowerMap =
        b ∘ unitInterval.symm ∘ lowerEquiv.symm := by
      funext z
      apply congrArg b
      apply congrArg unitInterval.symm
      apply hpathLower
      exact (Function.invFun_eq z.property).trans
        (congrArg Subtype.val (lowerEquiv.apply_symm_apply z)).symm
    rw [hformula]
    exact hb.continuous.comp
      (unitInterval.continuous_symm.comp lowerEquiv.symm.continuous)
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
  -- Reversing the lower parameter makes the maps agree at both endpoints.
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
  -- The two circle halves map onto exactly the two arc ranges.
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
  -- A collision between different semicircles can only be their shared endpoint.
  have hcross (z w : Circle) (hzu : z ∈ upper) (hwl : w ∈ lower)
      (hwu : w ∉ upper) (hzw : pasted z = pasted w) : z = w := by
    have hmapEq : upperMap z = lowerMap w := by
      simp only [pasted, upper.piecewise_eq_of_mem upperMap lowerMap hzu,
        upper.piecewise_eq_of_notMem upperMap lowerMap hwu] at hzw
      exact hzw
    have hcommon : upperMap z ∈ Set.range a ∩ Set.range b :=
      ⟨⟨upperParam z, rfl⟩,
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
          have hw : w ∈ upper ∪ lower := hcover.symm ▸ Set.mem_univ w
          exact hw.resolve_left hwu
        exact hcross z w hzu hwl hwu hzw
    · have hzl : z ∈ lower := by
        have hz : z ∈ upper ∪ lower := hcover.symm ▸ Set.mem_univ z
        exact hz.resolve_left hzu
      by_cases hwu : w ∈ upper
      · exact (hcross w z hwu hzl hzu hzw.symm).symm
      · have hwl : w ∈ lower := by
          have hw : w ∈ upper ∪ lower := hcover.symm ▸ Set.mem_univ w
          exact hw.resolve_left hwu
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
  -- The compact-domain embedding identifies the pasted range with a circle.
  rw [Topology.IsSimpleClosedCurve.iff_nonempty_homeomorph_circle]
  let hpastedEmbedding : Topology.IsEmbedding pasted :=
    hpastedContinuous.isClosedEmbedding hpastedInjective |>.isEmbedding
  exact ⟨(hpastedEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr hpastedRange)).symm⟩

/-- Helper for Lemma 65.1: reversing the two combinatorial endpoints does not
change the ambient realized edge. -/
private lemma edge_comm
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) {i j : Fin 4} (hij : i ≠ j) :
    edge X R e i j hij = edge X R e j i hij.symm := by
  -- The two edge subtypes have the same unordered endpoint pair.
  unfold edge
  congr 1
  apply Subtype.ext
  rw [Sym2.eq_iff]
  exact Or.inr ⟨rfl, rfl⟩

/-- Helper for Lemma 65.1: three ambient embedded arcs with theta incidence
give a theta presentation of their specified union. -/
private lemma existsThetaPresentationOnCarrier
    {Z : Type*} [TopologicalSpace Z] (Y : Set Z)
    (arc : Fin 3 → unitInterval → Z)
    (harc : ∀ i, Topology.IsEmbedding (arc i))
    (p q : Z) (hzero : ∀ i, arc i 0 = p) (hone : ∀ i, arc i 1 = q)
    (hcover : ⋃ i, Set.range (arc i) = Y)
    (hinter : ∀ i j, i ≠ j →
      Set.range (arc i) ∩ Set.range (arc j) = {p, q}) :
    ∃ P : Topology.ThetaPresentation Y,
      ∀ i, P.ambientEdge i = Set.range (arc i) := by
  have harcMem (i : Fin 3) (t : unitInterval) : arc i t ∈ Y := by
    rw [← hcover]
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_range_self t⟩
  have hpMem : p ∈ Y := by
    rw [← hcover]
    exact Set.mem_iUnion.mpr ⟨0, ⟨0, hzero 0⟩⟩
  have hqMem : q ∈ Y := by
    rw [← hcover]
    exact Set.mem_iUnion.mpr ⟨0, ⟨1, hone 0⟩⟩
  let p' : Y := ⟨p, hpMem⟩
  let q' : Y := ⟨q, hqMem⟩
  have hliftedContinuous (i : Fin 3) :
      Continuous (fun t ↦ (⟨arc i t, harcMem i t⟩ : Y)) :=
    (harc i).continuous.subtype_mk (harcMem i)
  let lifted : Fin 3 → C(unitInterval, Y) := fun i ↦
    ⟨fun t ↦ ⟨arc i t, harcMem i t⟩, hliftedContinuous i⟩
  have hliftedEmbedding (i : Fin 3) :
      Topology.IsEmbedding (lifted i) := by
    apply (Topology.IsEmbedding.of_comp_iff
      Topology.IsEmbedding.subtypeVal).mp
    exact harc i
  have hliftedZero (i : Fin 3) : lifted i 0 = p' := by
    apply Subtype.ext
    exact hzero i
  have hliftedOne (i : Fin 3) : lifted i 1 = q' := by
    apply Subtype.ext
    exact hone i
  have hliftedCover : ⋃ i, Set.range (lifted i) = Set.univ := by
    ext x
    constructor
    · intro _
      exact Set.mem_univ x
    · intro _
      have hx : (x : Z) ∈ ⋃ i, Set.range (arc i) := hcover.symm ▸ x.property
      obtain ⟨i, t, ht⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨i, ⟨t, Subtype.ext ht⟩⟩
  have hliftedInter (i j : Fin 3) (hij : i ≠ j) :
      Set.range (lifted i) ∩ Set.range (lifted j) = {p', q'} := by
    ext x
    constructor
    · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
      have hxAmbient : (x : Z) ∈
          Set.range (arc i) ∩ Set.range (arc j) :=
        ⟨⟨s, congrArg Subtype.val hs⟩,
          ⟨t, congrArg Subtype.val ht⟩⟩
      rw [hinter i j hij] at hxAmbient
      rcases hxAmbient with hp | hq
      · exact Or.inl (Subtype.ext hp)
      · exact Or.inr (Set.mem_singleton_iff.mpr (Subtype.ext hq))
    · intro hx
      rcases hx with rfl | hx
      · exact ⟨⟨0, hliftedZero i⟩, ⟨0, hliftedZero j⟩⟩
      · rw [Set.mem_singleton_iff] at hx
        subst x
        exact ⟨⟨1, hliftedOne i⟩, ⟨1, hliftedOne j⟩⟩
  let P : Topology.ThetaPresentation Y :=
    { initial := p'
      terminal := q'
      arc := lifted
      isEmbedding := hliftedEmbedding
      map_zero := hliftedZero
      map_one := hliftedOne
      iUnion_range := hliftedCover
      range_inter_range := hliftedInter }
  refine ⟨P, ?_⟩
  intro i
  -- Forgetting the subtype proof recovers the original ambient arc.
  rw [P.ambientEdge_eq_range]
  rfl

/-- Helper for Lemma 65.1: equality of complementary-component classes gives
equality of their ambient connected components. -/
private lemma connectedComponentIn_eq_of_componentClass_eq
    {Z : Type*} [TopologicalSpace Z] {F : Set Z} (a b : F)
    (h : (a : ConnectedComponents F) = b) :
    connectedComponentIn F a = connectedComponentIn F b := by
  -- Move the quotient equality through the subtype inclusion.
  rw [connectedComponentIn_eq_image a.property,
    connectedComponentIn_eq_image b.property]
  exact congrArg (Set.image Subtype.val) (ConnectedComponents.coe_eq_coe.mp h)

/-- Helper for Lemma 65.1: equality of ambient components gives equality of
the corresponding connected-component quotient classes. -/
private lemma connectedComponents_coe_eq_of_connectedComponentIn_eq
    {Z : Type*} [TopologicalSpace Z] {F : Set Z} (a b : F)
    (h : connectedComponentIn F a = connectedComponentIn F b) :
    (a : ConnectedComponents F) = b := by
  -- Membership of `a` in `b`'s component lifts to the subtype component.
  have ha : (a : Z) ∈ connectedComponentIn F b :=
    h ▸ mem_connectedComponentIn a.property
  rw [connectedComponentIn_eq_image b.property] at ha
  obtain ⟨z, hz, hza⟩ := ha
  exact ConnectedComponents.coe_eq_coe'.mpr (Subtype.ext hza ▸ hz)

/-- Helper for Lemma 65.1: both endpoints of an embedded interval arc are
limits of points in its endpoint-deleted range. -/
private lemma embeddedArc_endpoints_mem_closure_interiorRange
    {Z : Type*} [TopologicalSpace Z]
    (a : unitInterval → Z) (ha : Topology.IsEmbedding a) :
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
  -- Continuity carries the two one-sided limits to the arc range.
  rw [hinteriorRange]
  exact ⟨mem_closure_image ha.continuous.continuousAt hzeroClosure,
    mem_closure_image ha.continuous.continuousAt honeClosure⟩

/-- Helper for Lemma 65.1: a theta presentation has three indexed complementary
regions with the expected pair-of-edge frontiers. -/
private lemma existsIndexedThetaRegions
    (Y : Set (StandardSphere 2)) (P : Topology.ThetaPresentation Y) :
    ∃ representative : Fin 3 → (Yᶜ : Set (StandardSphere 2)),
      Function.Bijective (fun i ↦
        (representative i : ConnectedComponents
          (Yᶜ : Set (StandardSphere 2)))) ∧
      frontier (connectedComponentIn Yᶜ (representative 0)) =
        P.ambientEdge 1 ∪ P.ambientEdge 2 ∧
      frontier (connectedComponentIn Yᶜ (representative 1)) =
        P.ambientEdge 0 ∪ P.ambientEdge 2 ∧
      frontier (connectedComponentIn Yᶜ (representative 2)) =
        P.ambientEdge 0 ∪ P.ambientEdge 1 ∧
      connectedComponentIn Yᶜ (representative 2) =
        connectedComponentIn (P.ambientEdge 0 ∪ P.ambientEdge 1)ᶜ
          (representative 2) := by
  classical
  have hfrontierRange := Topology.ThetaPresentation.frontier_range Y P
  have hfrontierZeroMem : P.ambientEdge 1 ∪ P.ambientEdge 2 ∈
      Set.range (fun x : (Yᶜ : Set (StandardSphere 2)) ↦
        frontier (connectedComponentIn Yᶜ x)) := by
    rw [hfrontierRange]
    exact Or.inr (Or.inl rfl)
  have hfrontierOneMem : P.ambientEdge 0 ∪ P.ambientEdge 2 ∈
      Set.range (fun x : (Yᶜ : Set (StandardSphere 2)) ↦
        frontier (connectedComponentIn Yᶜ x)) := by
    rw [hfrontierRange]
    exact Or.inr (Or.inr rfl)
  obtain ⟨xZero, hfrontierZero⟩ := hfrontierZeroMem
  obtain ⟨xOne, hfrontierOne⟩ := hfrontierOneMem
  change frontier (connectedComponentIn Yᶜ xZero) =
    P.ambientEdge 1 ∪ P.ambientEdge 2 at hfrontierZero
  change frontier (connectedComponentIn Yᶜ xOne) =
    P.ambientEdge 0 ∪ P.ambientEdge 2 at hfrontierOne
  obtain ⟨xTwo, xTwoPair, hfrontierTwo, hcomponentPairTwo⟩ :=
    Topology.ThetaPresentation.pairEdge_component Y P
  have htMem : (1 / 2 : ℝ) ∈ Set.Icc 0 1 := by norm_num
  let t : unitInterval := ⟨1 / 2, htMem⟩
  have htZero : t ≠ 0 := by
    intro ht
    have htValue := congrArg Subtype.val ht
    norm_num [t] at htValue
  have htOne : t ≠ 1 := by
    intro ht
    have htValue := congrArg Subtype.val ht
    norm_num [t] at htValue
  have hmidpointNotOther {i j : Fin 3} (hij : i ≠ j) :
      (P.arc i t : StandardSphere 2) ∉ P.ambientEdge j := by
    intro hmem
    have hown : (P.arc i t : StandardSphere 2) ∈ P.ambientEdge i := by
      rw [P.ambientEdge_eq_range]
      exact Set.mem_range_self t
    have hcommon : (P.arc i t : StandardSphere 2) ∈
        P.ambientEdge i ∩ P.ambientEdge j := ⟨hown, hmem⟩
    rw [P.ambientEdge_inter_ambientEdge i j hij] at hcommon
    rcases hcommon with hcommon | hcommon
    · have hparameter : t = 0 := (P.isEmbedding i).injective
          ((Subtype.ext hcommon).trans (P.map_zero i).symm)
      exact htZero hparameter
    · rw [Set.mem_singleton_iff] at hcommon
      have hparameter : t = 1 := (P.isEmbedding i).injective
          ((Subtype.ext hcommon).trans (P.map_one i).symm)
      exact htOne hparameter
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have hcomponentZeroOne : connectedComponentIn Yᶜ xZero ≠
      connectedComponentIn Yᶜ xOne := by
    intro heq
    have hfrontierEq := congrArg frontier heq
    rw [hfrontierZero, hfrontierOne] at hfrontierEq
    have hmid : (P.arc 1 t : StandardSphere 2) ∈
        P.ambientEdge 1 ∪ P.ambientEdge 2 := by
      left
      rw [P.ambientEdge_eq_range]
      exact Set.mem_range_self t
    rw [hfrontierEq] at hmid
    exact hmid.elim (hmidpointNotOther h10) (hmidpointNotOther h12)
  have hcomponentZeroTwo : connectedComponentIn Yᶜ xZero ≠
      connectedComponentIn Yᶜ xTwo := by
    intro heq
    have hfrontierEq := congrArg frontier heq
    rw [hfrontierZero, hfrontierTwo] at hfrontierEq
    have hmid : (P.arc 2 t : StandardSphere 2) ∈
        P.ambientEdge 1 ∪ P.ambientEdge 2 := by
      right
      rw [P.ambientEdge_eq_range]
      exact Set.mem_range_self t
    rw [hfrontierEq] at hmid
    exact hmid.elim (hmidpointNotOther h20) (hmidpointNotOther h21)
  have hcomponentOneTwo : connectedComponentIn Yᶜ xOne ≠
      connectedComponentIn Yᶜ xTwo := by
    intro heq
    have hfrontierEq := congrArg frontier heq
    rw [hfrontierOne, hfrontierTwo] at hfrontierEq
    have hmid : (P.arc 2 t : StandardSphere 2) ∈
        P.ambientEdge 0 ∪ P.ambientEdge 2 := by
      right
      rw [P.ambientEdge_eq_range]
      exact Set.mem_range_self t
    rw [hfrontierEq] at hmid
    exact hmid.elim (hmidpointNotOther h20) (hmidpointNotOther h21)
  have hclassZeroOne : (xZero : ConnectedComponents
      (Yᶜ : Set (StandardSphere 2))) ≠ xOne := by
    intro h
    exact hcomponentZeroOne
      (connectedComponentIn_eq_of_componentClass_eq xZero xOne h)
  have hclassZeroTwo : (xZero : ConnectedComponents
      (Yᶜ : Set (StandardSphere 2))) ≠ xTwo := by
    intro h
    exact hcomponentZeroTwo
      (connectedComponentIn_eq_of_componentClass_eq xZero xTwo h)
  have hclassOneTwo : (xOne : ConnectedComponents
      (Yᶜ : Set (StandardSphere 2))) ≠ xTwo := by
    intro h
    exact hcomponentOneTwo
      (connectedComponentIn_eq_of_componentClass_eq xOne xTwo h)
  let representative : Fin 3 → (Yᶜ : Set (StandardSphere 2)) :=
    ![xZero, xOne, xTwo]
  let regionClass : Fin 3 →
      ConnectedComponents (Yᶜ : Set (StandardSphere 2)) :=
    fun i ↦ representative i
  have hregionInjective : Function.Injective regionClass := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hclassZeroOne (by simpa [regionClass, representative] using hij)).elim
    · exact (hclassZeroTwo (by simpa [regionClass, representative] using hij)).elim
    · exact (hclassZeroOne (by simpa [regionClass, representative] using hij.symm)).elim
    · rfl
    · exact (hclassOneTwo (by simpa [regionClass, representative] using hij)).elim
    · exact (hclassZeroTwo (by simpa [regionClass, representative] using hij.symm)).elim
    · exact (hclassOneTwo (by simpa [regionClass, representative] using hij.symm)).elim
    · rfl
  have hcard : Cardinal.mk (ConnectedComponents
      (Yᶜ : Set (StandardSphere 2))) = 3 :=
    Set.separatesInto_iff.mp
      (Topology.ThetaPresentation.separatesInto Y P)
  obtain ⟨classEquiv⟩ := Cardinal.mk_eq_nat_iff.mp hcard
  have hregionSurjective : Function.Surjective regionClass :=
    hregionInjective.surjective_of_finite classEquiv.symm
  have hxTwoPair : (xTwo : StandardSphere 2) ∈
      (P.ambientEdge 0 ∪ P.ambientEdge 1)ᶜ := by
    intro hx
    exact hx.elim (fun hxZero ↦ xTwo.property (P.ambientEdge_subset 0 hxZero))
      (fun hxOne ↦ xTwo.property (P.ambientEdge_subset 1 hxOne))
  have hxTwoInPairComponent : (xTwo : StandardSphere 2) ∈
      connectedComponentIn (P.ambientEdge 0 ∪ P.ambientEdge 1)ᶜ xTwoPair := by
    rw [← hcomponentPairTwo]
    exact mem_connectedComponentIn xTwo.property
  have hcomponentPairTwoSelf : connectedComponentIn Yᶜ xTwo =
      connectedComponentIn (P.ambientEdge 0 ∪ P.ambientEdge 1)ᶜ xTwo :=
    hcomponentPairTwo.trans (connectedComponentIn_eq hxTwoInPairComponent)
  refine ⟨representative, ⟨hregionInjective, hregionSurjective⟩, ?_, ?_, ?_, ?_⟩
  · simpa [representative] using hfrontierZero
  · simpa [representative] using hfrontierOne
  · simpa [representative] using hfrontierTwo
  · simpa [representative] using hcomponentPairTwoSelf

/-- The realized four-edge cycle `0-1-2-3-0` in a complete graph on four vertices. -/
def cycle
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) : Set (StandardSphere 2) :=
  edge X R e 0 1 (of_decide_eq_true rfl) ∪
    edge X R e 1 2 (of_decide_eq_true rfl) ∪
    edge X R e 2 3 (of_decide_eq_true rfl) ∪
    edge X R e 3 0 (of_decide_eq_true rfl)

/-- Helper for Lemma 65.1: the theta subspace obtained by adjoining the
`0-2` diagonal to the four-edge cycle. -/
private def cycleThetaCarrier
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) : Set (StandardSphere 2) :=
  cycle X R e ∪ edge X R e 0 2 (of_decide_eq_true rfl)

/-- Helper for Lemma 65.1: the four cycle edges form two embedded arcs from
vertex `0` to vertex `2`, meeting only at those endpoints. -/
private lemma existsCyclePairArcs
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) :
    ∃ first second : unitInterval → StandardSphere 2,
      Topology.IsEmbedding first ∧ Topology.IsEmbedding second ∧
      first 0 = e (R.vertex 0) ∧ first 1 = e (R.vertex 2) ∧
      second 0 = e (R.vertex 0) ∧ second 1 = e (R.vertex 2) ∧
      Set.range first =
        edge X R e 0 1 (of_decide_eq_true rfl) ∪
          edge X R e 1 2 (of_decide_eq_true rfl) ∧
      Set.range second =
        edge X R e 2 3 (of_decide_eq_true rfl) ∪
          edge X R e 3 0 (of_decide_eq_true rfl) ∧
      Set.range first ∩ Set.range second =
        {(e (R.vertex 0) : StandardSphere 2),
          (e (R.vertex 2) : StandardSphere 2)} := by
  -- Orient the four cycle edges into two paths from vertex `0` to vertex `2`.
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h32 : (3 : Fin 4) ≠ 2 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have h30 : (3 : Fin 4) ≠ 0 := by decide
  obtain ⟨a01, ha01Embedding, ha01Zero, ha01One, ha01Range⟩ :=
    existsOrientedEdge X R e h01
  obtain ⟨a12, ha12Embedding, ha12Zero, ha12One, ha12Range⟩ :=
    existsOrientedEdge X R e h12
  obtain ⟨a03, ha03Embedding, ha03Zero, ha03One, ha03Range⟩ :=
    existsOrientedEdge X R e h03
  obtain ⟨a32, ha32Embedding, ha32Zero, ha32One, ha32Range⟩ :=
    existsOrientedEdge X R e h32
  have hambientVertexInjective : Function.Injective
      (fun i : Fin 4 ↦ (e (R.vertex i) : StandardSphere 2)) :=
    Subtype.val_injective.comp (e.injective.comp R.vertex_injective)
  have hfin01 : (0 : Fin 4) ≠ 1 := by decide
  have hfin02 : (0 : Fin 4) ≠ 2 := by decide
  have hfin03 : (0 : Fin 4) ≠ 3 := by decide
  have hfin12 : (1 : Fin 4) ≠ 2 := by decide
  have hfin13 : (1 : Fin 4) ≠ 3 := by decide
  have hfin23 : (2 : Fin 4) ≠ 3 := by decide
  have hv01 := hambientVertexInjective.ne hfin01
  have hv02 := hambientVertexInjective.ne hfin02
  have hv03 := hambientVertexInjective.ne hfin03
  have hv12 := hambientVertexInjective.ne hfin12
  have hv13 := hambientVertexInjective.ne hfin13
  have hv23 := hambientVertexInjective.ne hfin23
  have hp01_12 : s((0 : Fin 4), 1) ≠ s(1, 2) := by decide
  have hp03_32 : s((0 : Fin 4), 3) ≠ s(3, 2) := by decide
  have hp01_03 : s((0 : Fin 4), 1) ≠ s(0, 3) := by decide
  have hp01_32 : s((0 : Fin 4), 1) ≠ s(3, 2) := by decide
  have hp12_03 : s((1 : Fin 4), 2) ≠ s(0, 3) := by decide
  have hp12_32 : s((1 : Fin 4), 2) ≠ s(3, 2) := by decide
  have hinter01_12 : Set.range a01 ∩ Set.range a12 =
      {(e (R.vertex 1) : StandardSphere 2)} := by
    rw [ha01Range, ha12Range,
      edge_inter_edge_eq_endpointPairs X R e h01 h12 hp01_12]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  have hinter03_32 : Set.range a03 ∩ Set.range a32 =
      {(e (R.vertex 3) : StandardSphere 2)} := by
    rw [ha03Range, ha32Range,
      edge_inter_edge_eq_endpointPairs X R e h03 h32 hp03_32]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  have hinter01_12_join : Set.range a01 ∩ Set.range a12 = {a01 1} := by
    rw [ha01One]
    exact hinter01_12
  have hinter03_32_join : Set.range a03 ∩ Set.range a32 = {a03 1} := by
    rw [ha03One]
    exact hinter03_32
  obtain ⟨first, hfirstEmbedding, hfirstZero, hfirstOne, hfirstRange⟩ :=
    existsEmbeddedArcWithRangeUnion a01 a12 ha01Embedding ha12Embedding
      (ha01One.trans ha12Zero.symm) hinter01_12_join
  obtain ⟨second, hsecondEmbedding, hsecondZero, hsecondOne, hsecondRange⟩ :=
    existsEmbeddedArcWithRangeUnion a03 a32 ha03Embedding ha32Embedding
      (ha03One.trans ha32Zero.symm) hinter03_32_join
  -- The four constituent edge intersections leave only vertices `0` and `2`.
  have hinter01_03 : Set.range a01 ∩ Set.range a03 =
      {(e (R.vertex 0) : StandardSphere 2)} := by
    rw [ha01Range, ha03Range,
      edge_inter_edge_eq_endpointPairs X R e h01 h03 hp01_03]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  have hinter01_32 : Set.range a01 ∩ Set.range a32 = ∅ := by
    rw [ha01Range, ha32Range,
      edge_inter_edge_eq_endpointPairs X R e h01 h32 hp01_32]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false]
    aesop
  have hinter12_03 : Set.range a12 ∩ Set.range a03 = ∅ := by
    rw [ha12Range, ha03Range,
      edge_inter_edge_eq_endpointPairs X R e h12 h03 hp12_03]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false]
    aesop
  have hinter12_32 : Set.range a12 ∩ Set.range a32 =
      {(e (R.vertex 2) : StandardSphere 2)} := by
    rw [ha12Range, ha32Range,
      edge_inter_edge_eq_endpointPairs X R e h12 h32 hp12_32]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  have hfirstSecondInter : Set.range first ∩ Set.range second =
      {(e (R.vertex 0) : StandardSphere 2),
        (e (R.vertex 2) : StandardSphere 2)} := by
    rw [hfirstRange, hsecondRange]
    ext z
    constructor
    · rintro ⟨hz01 | hz12, hz03 | hz32⟩
      · have hz : z ∈ Set.range a01 ∩ Set.range a03 := ⟨hz01, hz03⟩
        rw [hinter01_03] at hz
        exact Or.inl (Set.mem_singleton_iff.mp hz)
      · have hz : z ∈ Set.range a01 ∩ Set.range a32 := ⟨hz01, hz32⟩
        rw [hinter01_32] at hz
        exact hz.elim
      · have hz : z ∈ Set.range a12 ∩ Set.range a03 := ⟨hz12, hz03⟩
        rw [hinter12_03] at hz
        exact hz.elim
      · have hz : z ∈ Set.range a12 ∩ Set.range a32 := ⟨hz12, hz32⟩
        rw [hinter12_32] at hz
        exact Or.inr (Set.mem_singleton_iff.mp hz)
    · intro hz
      rcases hz with rfl | hz
      · exact ⟨Or.inl ⟨0, ha01Zero⟩, Or.inl ⟨0, ha03Zero⟩⟩
      · rw [Set.mem_singleton_iff] at hz
        subst z
        exact ⟨Or.inr ⟨1, ha12One⟩, Or.inr ⟨1, ha32One⟩⟩
  have h03_30 : edge X R e 0 3 h03 = edge X R e 3 0 h30 := by
    rw [← show h03.symm = h30 from Subsingleton.elim _ _]
    exact edge_comm X R e h03
  have h32_23 : edge X R e 3 2 h32 = edge X R e 2 3 h23 := by
    rw [← show h32.symm = h23 from Subsingleton.elim _ _]
    exact edge_comm X R e h32
  have hsecondCanonical : Set.range second =
      edge X R e 2 3 h23 ∪ edge X R e 3 0 h30 := by
    rw [hsecondRange, ha03Range, ha32Range, h03_30, h32_23, Set.union_comm]
  -- Package only the endpoint, range, and intersection data needed downstream.
  exact ⟨first, second, hfirstEmbedding, hsecondEmbedding,
    hfirstZero.trans ha01Zero, hfirstOne.trans ha12One,
    hsecondZero.trans ha03Zero, hsecondOne.trans ha32One,
    hfirstRange.trans (congrArg₂ (· ∪ ·) ha01Range ha12Range),
    hsecondCanonical,
    hfirstSecondInter⟩

/-- Helper for Lemma 65.1: adjoining the `0-2` diagonal gives a theta
presentation whose pair-edge boundary is the original four-cycle. -/
private lemma existsCycleThetaPresentation
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) :
    ∃ P : Topology.ThetaPresentation (cycleThetaCarrier X R e),
      P.ambientEdge 0 ∪ P.ambientEdge 1 = cycle X R e ∧
      P.ambientEdge 2 = edge X R e 0 2 (of_decide_eq_true rfl) ∧
      (e (R.vertex 1) : StandardSphere 2) ∈ P.ambientEdge 0 ∧
      (e (R.vertex 1) : StandardSphere 2) ∉
        P.ambientEdge 1 ∪ P.ambientEdge 2 ∧
      (e (R.vertex 3) : StandardSphere 2) ∈ P.ambientEdge 1 ∧
      (e (R.vertex 3) : StandardSphere 2) ∉
        P.ambientEdge 0 ∪ P.ambientEdge 2 := by
  obtain ⟨first, second, hfirstEmbedding, hsecondEmbedding,
      hfirstZero, hfirstOne, hsecondZero, hsecondOne,
      hfirstRange, hsecondRange, hfirstSecondInter⟩ :=
    existsCyclePairArcs X R e
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  obtain ⟨diagonal, hdiagonalEmbedding, hdiagonalZero, hdiagonalOne,
      hdiagonalRange⟩ := existsOrientedEdge X R e h02
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have h30 : (3 : Fin 4) ≠ 0 := by decide
  have hp01_02 : s((0 : Fin 4), 1) ≠ s(0, 2) := by decide
  have hp12_02 : s((1 : Fin 4), 2) ≠ s(0, 2) := by decide
  have hp23_02 : s((2 : Fin 4), 3) ≠ s(0, 2) := by decide
  have hp30_02 : s((3 : Fin 4), 0) ≠ s(0, 2) := by decide
  have hambientVertexInjective : Function.Injective
      (fun i : Fin 4 ↦ (e (R.vertex i) : StandardSphere 2)) :=
    Subtype.val_injective.comp (e.injective.comp R.vertex_injective)
  have hv01 := hambientVertexInjective.ne (by decide : (0 : Fin 4) ≠ 1)
  have hv02 := hambientVertexInjective.ne (by decide : (0 : Fin 4) ≠ 2)
  have hv03 := hambientVertexInjective.ne (by decide : (0 : Fin 4) ≠ 3)
  have hv12 := hambientVertexInjective.ne (by decide : (1 : Fin 4) ≠ 2)
  have hv13 := hambientVertexInjective.ne (by decide : (1 : Fin 4) ≠ 3)
  have hv23 := hambientVertexInjective.ne (by decide : (2 : Fin 4) ≠ 3)
  have hinter01_02 :
      edge X R e 0 1 h01 ∩ edge X R e 0 2 h02 =
        {(e (R.vertex 0) : StandardSphere 2)} := by
    rw [edge_inter_edge_eq_endpointPairs X R e h01 h02 hp01_02]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  have hinter12_02 :
      edge X R e 1 2 h12 ∩ edge X R e 0 2 h02 =
        {(e (R.vertex 2) : StandardSphere 2)} := by
    rw [edge_inter_edge_eq_endpointPairs X R e h12 h02 hp12_02]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  have hinter23_02 :
      edge X R e 2 3 h23 ∩ edge X R e 0 2 h02 =
        {(e (R.vertex 2) : StandardSphere 2)} := by
    rw [edge_inter_edge_eq_endpointPairs X R e h23 h02 hp23_02]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  have hinter30_02 :
      edge X R e 3 0 h30 ∩ edge X R e 0 2 h02 =
        {(e (R.vertex 0) : StandardSphere 2)} := by
    rw [edge_inter_edge_eq_endpointPairs X R e h30 h02 hp30_02]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  have hfirstDiagonalInter : Set.range first ∩ Set.range diagonal =
      {(e (R.vertex 0) : StandardSphere 2),
        (e (R.vertex 2) : StandardSphere 2)} := by
    rw [hfirstRange, hdiagonalRange]
    ext z
    constructor
    · rintro ⟨hzFirst, hzDiagonal⟩
      rcases hzFirst with hz01 | hz12
      · have hz : z ∈ edge X R e 0 1 h01 ∩ edge X R e 0 2 h02 :=
          ⟨hz01, hzDiagonal⟩
        rw [hinter01_02] at hz
        exact Or.inl (Set.mem_singleton_iff.mp hz)
      · have hz : z ∈ edge X R e 1 2 h12 ∩ edge X R e 0 2 h02 :=
          ⟨hz12, hzDiagonal⟩
        rw [hinter12_02] at hz
        exact Or.inr (Set.mem_singleton_iff.mp hz)
    · intro hz
      rcases hz with rfl | hz
      · exact ⟨Or.inl (ambientVertices_mem_edge X R e h01).1,
          (ambientVertices_mem_edge X R e h02).1⟩
      · rw [Set.mem_singleton_iff] at hz
        subst z
        exact ⟨Or.inr (ambientVertices_mem_edge X R e h12).2,
          (ambientVertices_mem_edge X R e h02).2⟩
  have hsecondDiagonalInter : Set.range second ∩ Set.range diagonal =
      {(e (R.vertex 0) : StandardSphere 2),
        (e (R.vertex 2) : StandardSphere 2)} := by
    rw [hsecondRange, hdiagonalRange]
    ext z
    constructor
    · rintro ⟨hzSecond, hzDiagonal⟩
      rcases hzSecond with hz23 | hz30
      · have hz : z ∈ edge X R e 2 3 h23 ∩ edge X R e 0 2 h02 :=
          ⟨hz23, hzDiagonal⟩
        rw [hinter23_02] at hz
        exact Or.inr (Set.mem_singleton_iff.mp hz)
      · have hz : z ∈ edge X R e 3 0 h30 ∩ edge X R e 0 2 h02 :=
          ⟨hz30, hzDiagonal⟩
        rw [hinter30_02] at hz
        exact Or.inl (Set.mem_singleton_iff.mp hz)
    · intro hz
      rcases hz with rfl | hz
      · exact ⟨Or.inr (ambientVertices_mem_edge X R e h30).2,
          (ambientVertices_mem_edge X R e h02).1⟩
      · rw [Set.mem_singleton_iff] at hz
        subst z
        exact ⟨Or.inl (ambientVertices_mem_edge X R e h23).1,
          (ambientVertices_mem_edge X R e h02).2⟩
  let arc : Fin 3 → unitInterval → StandardSphere 2 :=
    ![first, second, diagonal]
  have harcEmbedding (i : Fin 3) : Topology.IsEmbedding (arc i) := by
    fin_cases i
    · exact hfirstEmbedding
    · exact hsecondEmbedding
    · exact hdiagonalEmbedding
  have harcZero (i : Fin 3) : arc i 0 = e (R.vertex 0) := by
    fin_cases i
    · exact hfirstZero
    · exact hsecondZero
    · exact hdiagonalZero
  have harcOne (i : Fin 3) : arc i 1 = e (R.vertex 2) := by
    fin_cases i
    · exact hfirstOne
    · exact hsecondOne
    · exact hdiagonalOne
  have harcInter (i j : Fin 3) (hij : i ≠ j) :
      Set.range (arc i) ∩ Set.range (arc j) =
        {(e (R.vertex 0) : StandardSphere 2),
          (e (R.vertex 2) : StandardSphere 2)} := by
    fin_cases i
    · fin_cases j
      · exact (hij rfl).elim
      · exact hfirstSecondInter
      · exact hfirstDiagonalInter
    · fin_cases j
      · rw [Set.inter_comm]
        exact hfirstSecondInter
      · exact (hij rfl).elim
      · exact hsecondDiagonalInter
    · fin_cases j
      · rw [Set.inter_comm]
        exact hfirstDiagonalInter
      · rw [Set.inter_comm]
        exact hsecondDiagonalInter
      · exact (hij rfl).elim
  have hcycleRanges : Set.range first ∪ Set.range second = cycle X R e := by
    rw [hfirstRange, hsecondRange]
    unfold cycle
    ext z
    simp only [Set.mem_union]
    tauto
  have harcCover : ⋃ i, Set.range (arc i) = cycleThetaCarrier X R e := by
    have hfinite : ⋃ i, Set.range (arc i) =
        Set.range first ∪ Set.range second ∪ Set.range diagonal := by
      ext z
      constructor
      · intro hz
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
        fin_cases i
        · exact Or.inl (Or.inl hi)
        · exact Or.inl (Or.inr hi)
        · exact Or.inr hi
      · rintro ((hz | hz) | hz)
        · exact Set.mem_iUnion.mpr ⟨0, hz⟩
        · exact Set.mem_iUnion.mpr ⟨1, hz⟩
        · exact Set.mem_iUnion.mpr ⟨2, hz⟩
    rw [hfinite, hcycleRanges, hdiagonalRange]
    rfl
  obtain ⟨P, hPedge⟩ := existsThetaPresentationOnCarrier
    (cycleThetaCarrier X R e) arc harcEmbedding
    (e (R.vertex 0)) (e (R.vertex 2)) harcZero harcOne harcCover harcInter
  have hpairCycle : P.ambientEdge 0 ∪ P.ambientEdge 1 = cycle X R e := by
    rw [hPedge 0, hPedge 1]
    exact hcycleRanges
  have hthirdDiagonal : P.ambientEdge 2 = edge X R e 0 2 h02 := by
    rw [hPedge 2]
    exact hdiagonalRange
  have hv1First : (e (R.vertex 1) : StandardSphere 2) ∈ Set.range first := by
    rw [hfirstRange]
    exact Or.inl (ambientVertices_mem_edge X R e h01).2
  have hv3Second : (e (R.vertex 3) : StandardSphere 2) ∈ Set.range second := by
    rw [hsecondRange]
    exact Or.inl (ambientVertices_mem_edge X R e h23).2
  have hv1NotSecond : (e (R.vertex 1) : StandardSphere 2) ∉ Set.range second := by
    intro hmem
    have hends : (e (R.vertex 1) : StandardSphere 2) ∈
        ({(e (R.vertex 0) : StandardSphere 2),
          (e (R.vertex 2) : StandardSphere 2)} : Set (StandardSphere 2)) := by
      rw [← hfirstSecondInter]
      exact ⟨hv1First, hmem⟩
    exact hends.elim (fun h ↦ hv01 h.symm)
      (fun h ↦ hv12 (Set.mem_singleton_iff.mp h))
  have hv1NotDiagonal :
      (e (R.vertex 1) : StandardSphere 2) ∉ Set.range diagonal := by
    intro hmem
    have hends : (e (R.vertex 1) : StandardSphere 2) ∈
        ({(e (R.vertex 0) : StandardSphere 2),
          (e (R.vertex 2) : StandardSphere 2)} : Set (StandardSphere 2)) := by
      rw [← hfirstDiagonalInter]
      exact ⟨hv1First, hmem⟩
    exact hends.elim (fun h ↦ hv01 h.symm)
      (fun h ↦ hv12 (Set.mem_singleton_iff.mp h))
  have hv3NotFirst : (e (R.vertex 3) : StandardSphere 2) ∉ Set.range first := by
    intro hmem
    have hends : (e (R.vertex 3) : StandardSphere 2) ∈
        ({(e (R.vertex 0) : StandardSphere 2),
          (e (R.vertex 2) : StandardSphere 2)} : Set (StandardSphere 2)) := by
      rw [← hfirstSecondInter]
      exact ⟨hmem, hv3Second⟩
    exact hends.elim (fun h ↦ hv03 h.symm)
      (fun h ↦ hv23 (Set.mem_singleton_iff.mp h).symm)
  have hv3NotDiagonal :
      (e (R.vertex 3) : StandardSphere 2) ∉ Set.range diagonal := by
    intro hmem
    have hends : (e (R.vertex 3) : StandardSphere 2) ∈
        ({(e (R.vertex 0) : StandardSphere 2),
          (e (R.vertex 2) : StandardSphere 2)} : Set (StandardSphere 2)) := by
      rw [← hsecondDiagonalInter]
      exact ⟨hv3Second, hmem⟩
    exact hends.elim (fun h ↦ hv03 h.symm)
      (fun h ↦ hv23 (Set.mem_singleton_iff.mp h).symm)
  -- Rewrite the vertex-incidence facts through the presentation edge interface.
  refine ⟨P, hpairCycle, hthirdDiagonal, ?_, ?_, ?_, ?_⟩
  · rw [hPedge 0]
    exact hv1First
  · rw [hPedge 1, hPedge 2]
    exact fun h ↦ h.elim hv1NotSecond hv1NotDiagonal
  · rw [hPedge 1]
    exact hv3Second
  · rw [hPedge 0, hPedge 2]
    exact fun h ↦ h.elim hv3NotFirst hv3NotDiagonal

/-- The four-edge cycle in a realized complete graph on four vertices is a simple closed curve. -/
instance instIsSimpleClosedCurveCycle
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) : Topology.IsSimpleClosedCurve (cycle X R e) := by
  obtain ⟨first, second, hfirstEmbedding, hsecondEmbedding,
      hfirstZero, hfirstOne, hsecondZero, hsecondOne,
      hfirstRange, hsecondRange, hfirstSecondInter⟩ :=
    existsCyclePairArcs X R e
  -- Paste the two arcs after rewriting their common endpoints.
  have hcycleCurve : Topology.IsSimpleClosedCurve
      ↑(Set.range first ∪ Set.range second) := by
    have hzero : first 0 = second 0 := hfirstZero.trans hsecondZero.symm
    have hone : first 1 = second 1 := hfirstOne.trans hsecondOne.symm
    have hinter : Set.range first ∩ Set.range second = {first 0, first 1} := by
      rw [hfirstZero, hfirstOne]
      exact hfirstSecondInter
    exact isSimpleClosedCurve_pairArcRanges first second hfirstEmbedding
      hsecondEmbedding hzero hone hinter
  -- Normalize the two arc ranges to the declaration's cycle ordering.
  have hcycleCarrier : Set.range first ∪ Set.range second = cycle X R e := by
    rw [hfirstRange, hsecondRange]
    unfold cycle
    ext z
    simp only [Set.mem_union]
    tauto
  rw [hcycleCarrier] at hcycleCurve
  exact hcycleCurve

/-- The four-edge cycle avoids nonendpoint points on the two diagonal edges. -/
lemma cycle_subset_pairComplement
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) (t₁₃ t₂₄ : unitInterval)
    (ht₁₃_zero : t₁₃ ≠ 0) (ht₁₃_one : t₁₃ ≠ 1)
    (ht₂₄_zero : t₂₄ ≠ 0) (ht₂₄_one : t₂₄ ≠ 1) :
    cycle X R e ⊆
      ({edgePoint X R e 0 2 (of_decide_eq_true rfl) t₁₃,
        edgePoint X R e 1 3 (of_decide_eq_true rfl) t₂₄}ᶜ :
        Set (StandardSphere 2)) := by
  -- Each puncture is interior to a diagonal, hence avoids all four cycle edges.
  have h02_01 : s((0 : Fin 4), 2) ≠ s(0, 1) := by decide
  have h02_12 : s((0 : Fin 4), 2) ≠ s(1, 2) := by decide
  have h02_23 : s((0 : Fin 4), 2) ≠ s(2, 3) := by decide
  have h02_30 : s((0 : Fin 4), 2) ≠ s(3, 0) := by decide
  have h13_01 : s((1 : Fin 4), 3) ≠ s(0, 1) := by decide
  have h13_12 : s((1 : Fin 4), 3) ≠ s(1, 2) := by decide
  have h13_23 : s((1 : Fin 4), 3) ≠ s(2, 3) := by decide
  have h13_30 : s((1 : Fin 4), 3) ≠ s(3, 0) := by decide
  intro z hzCycle hzPuncture
  rcases hzCycle with ((hz01 | hz12) | hz23) | hz30
  · rcases hzPuncture with rfl | hz13
    · exact edgePoint_not_mem_edge_of_pair_ne X R e
        (of_decide_eq_true rfl) (of_decide_eq_true rfl) h02_01 t₁₃
        ht₁₃_zero ht₁₃_one hz01
    · rw [Set.mem_singleton_iff] at hz13
      subst z
      exact edgePoint_not_mem_edge_of_pair_ne X R e
        (of_decide_eq_true rfl) (of_decide_eq_true rfl) h13_01 t₂₄
        ht₂₄_zero ht₂₄_one hz01
  · rcases hzPuncture with rfl | hz13
    · exact edgePoint_not_mem_edge_of_pair_ne X R e
        (of_decide_eq_true rfl) (of_decide_eq_true rfl) h02_12 t₁₃
        ht₁₃_zero ht₁₃_one hz12
    · rw [Set.mem_singleton_iff] at hz13
      subst z
      exact edgePoint_not_mem_edge_of_pair_ne X R e
        (of_decide_eq_true rfl) (of_decide_eq_true rfl) h13_12 t₂₄
        ht₂₄_zero ht₂₄_one hz12
  · rcases hzPuncture with rfl | hz13
    · exact edgePoint_not_mem_edge_of_pair_ne X R e
        (of_decide_eq_true rfl) (of_decide_eq_true rfl) h02_23 t₁₃
        ht₁₃_zero ht₁₃_one hz23
    · rw [Set.mem_singleton_iff] at hz13
      subst z
      exact edgePoint_not_mem_edge_of_pair_ne X R e
        (of_decide_eq_true rfl) (of_decide_eq_true rfl) h13_23 t₂₄
        ht₂₄_zero ht₂₄_one hz23
  · rcases hzPuncture with rfl | hz13
    · exact edgePoint_not_mem_edge_of_pair_ne X R e
        (of_decide_eq_true rfl) (of_decide_eq_true rfl) h02_30 t₁₃
        ht₁₃_zero ht₁₃_one hz30
    · rw [Set.mem_singleton_iff] at hz13
      subst z
      exact edgePoint_not_mem_edge_of_pair_ne X R e
        (of_decide_eq_true rfl) (of_decide_eq_true rfl) h13_30 t₂₄
        ht₂₄_zero ht₂₄_one hz30

/-- Helper for Lemma 65.1: deleting its endpoints from the `1-3` diagonal
places the entire connected interior in the complement of the cycle theta. -/
private lemma edgeThirteenInterior_subset_cycleThetaComplement
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) :
    edge X R e 1 3 (of_decide_eq_true rfl) \
        {(e (R.vertex 1) : StandardSphere 2),
          (e (R.vertex 3) : StandardSphere 2)} ⊆
      (cycleThetaCarrier X R e)ᶜ := by
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have h30 : (3 : Fin 4) ≠ 0 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have hp13_01 : s((1 : Fin 4), 3) ≠ s(0, 1) := by decide
  have hp13_12 : s((1 : Fin 4), 3) ≠ s(1, 2) := by decide
  have hp13_23 : s((1 : Fin 4), 3) ≠ s(2, 3) := by decide
  have hp13_30 : s((1 : Fin 4), 3) ≠ s(3, 0) := by decide
  have hp13_02 : s((1 : Fin 4), 3) ≠ s(0, 2) := by decide
  have hambientVertexInjective : Function.Injective
      (fun i : Fin 4 ↦ (e (R.vertex i) : StandardSphere 2)) :=
    Subtype.val_injective.comp (e.injective.comp R.vertex_injective)
  have hv01 := hambientVertexInjective.ne (by decide : (0 : Fin 4) ≠ 1)
  have hv02 := hambientVertexInjective.ne (by decide : (0 : Fin 4) ≠ 2)
  have hv03 := hambientVertexInjective.ne (by decide : (0 : Fin 4) ≠ 3)
  have hv12 := hambientVertexInjective.ne (by decide : (1 : Fin 4) ≠ 2)
  have hv13 := hambientVertexInjective.ne (by decide : (1 : Fin 4) ≠ 3)
  have hv23 := hambientVertexInjective.ne (by decide : (2 : Fin 4) ≠ 3)
  have hinter13_01 : edge X R e 1 3 h13 ∩ edge X R e 0 1 h01 =
      {(e (R.vertex 1) : StandardSphere 2)} := by
    rw [edge_inter_edge_eq_endpointPairs X R e h13 h01 hp13_01]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  have hinter13_12 : edge X R e 1 3 h13 ∩ edge X R e 1 2 h12 =
      {(e (R.vertex 1) : StandardSphere 2)} := by
    rw [edge_inter_edge_eq_endpointPairs X R e h13 h12 hp13_12]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  have hinter13_23 : edge X R e 1 3 h13 ∩ edge X R e 2 3 h23 =
      {(e (R.vertex 3) : StandardSphere 2)} := by
    rw [edge_inter_edge_eq_endpointPairs X R e h13 h23 hp13_23]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  have hinter13_30 : edge X R e 1 3 h13 ∩ edge X R e 3 0 h30 =
      {(e (R.vertex 3) : StandardSphere 2)} := by
    rw [edge_inter_edge_eq_endpointPairs X R e h13 h30 hp13_30]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  have hinter13_02 : edge X R e 1 3 h13 ∩ edge X R e 0 2 h02 = ∅ := by
    rw [edge_inter_edge_eq_endpointPairs X R e h13 h02 hp13_02]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false]
    aesop
  -- Every possible intersection with the theta lies at a deleted endpoint.
  rintro z ⟨hz13, hzEnds⟩ hzTheta
  rcases hzTheta with hzCycle | hz02
  · rcases hzCycle with ((hz01 | hz12) | hz23) | hz30
    · have hz : z ∈ edge X R e 1 3 h13 ∩ edge X R e 0 1 h01 :=
        ⟨hz13, hz01⟩
      rw [hinter13_01] at hz
      exact hzEnds (Or.inl (Set.mem_singleton_iff.mp hz))
    · have hz : z ∈ edge X R e 1 3 h13 ∩ edge X R e 1 2 h12 :=
        ⟨hz13, hz12⟩
      rw [hinter13_12] at hz
      exact hzEnds (Or.inl (Set.mem_singleton_iff.mp hz))
    · have hz : z ∈ edge X R e 1 3 h13 ∩ edge X R e 2 3 h23 :=
        ⟨hz13, hz23⟩
      rw [hinter13_23] at hz
      exact hzEnds (Or.inr (Set.mem_singleton_iff.mpr
        (Set.mem_singleton_iff.mp hz)))
    · have hz : z ∈ edge X R e 1 3 h13 ∩ edge X R e 3 0 h30 :=
        ⟨hz13, hz30⟩
      rw [hinter13_30] at hz
      exact hzEnds (Or.inr (Set.mem_singleton_iff.mpr
        (Set.mem_singleton_iff.mp hz)))
  · have hz : z ∈ edge X R e 1 3 h13 ∩ edge X R e 0 2 h02 :=
      ⟨hz13, hz02⟩
    rw [hinter13_02] at hz
    exact hz.elim

/-- Part (1) of Lemma 65.1: interior points of the two diagonal edges of an embedded complete
graph on four vertices lie in different components of the complement of its
four-edge cycle. -/
theorem diagonalPoints_differentComponents
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) (t₁₃ t₂₄ : unitInterval)
    (ht₁₃_zero : t₁₃ ≠ 0) (ht₁₃_one : t₁₃ ≠ 1)
    (ht₂₄_zero : t₂₄ ≠ 0) (ht₂₄_one : t₂₄ ≠ 1) :
    connectedComponentIn (cycle X R e)ᶜ
        (edgePoint X R e 0 2 (of_decide_eq_true rfl) t₁₃) ≠
      connectedComponentIn (cycle X R e)ᶜ
        (edgePoint X R e 1 3 (of_decide_eq_true rfl) t₂₄) := by
  let p := edgePoint X R e 0 2 (of_decide_eq_true rfl) t₁₃
  let q := edgePoint X R e 1 3 (of_decide_eq_true rfl) t₂₄
  let theta := cycleThetaCarrier X R e
  obtain ⟨P, hpairCycle, hthirdDiagonal, hv1First, hv1Other,
      hv3Second, hv3Other⟩ := existsCycleThetaPresentation X R e
  obtain ⟨representative, hrepresentative, hfrontierZero,
      hfrontierOne, hfrontierTwo, hpairComponent⟩ :=
    existsIndexedThetaRegions theta P
  change P.ambientEdge 0 ∪ P.ambientEdge 1 = cycle X R e at hpairCycle
  rw [hpairCycle] at hpairComponent
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  obtain ⟨diagonal, hdiagonalEmbedding, hdiagonalZero, hdiagonalOne,
      hdiagonalRange⟩ := existsOrientedEdge X R e h13
  let interior : Set (StandardSphere 2) :=
    Set.range diagonal \
      {(e (R.vertex 1) : StandardSphere 2),
        (e (R.vertex 3) : StandardSphere 2)}
  have hinteriorTheta : interior ⊆ thetaᶜ := by
    intro z hz
    apply edgeThirteenInterior_subset_cycleThetaComplement X R e
    rw [← hdiagonalRange]
    exact hz
  have hqEdge : q ∈ edge X R e 1 3 h13 := by
    exact edgePoint_mem_edge X R e h13 t₂₄
  have hqNeVertexOne : q ≠ (e (R.vertex 1) : StandardSphere 2) := by
    intro hq
    have h01 : (0 : Fin 4) ≠ 1 := by decide
    have hpairs : s((1 : Fin 4), 3) ≠ s(0, 1) := by decide
    have hv1Edge : (e (R.vertex 1) : StandardSphere 2) ∈
        edge X R e 0 1 h01 :=
      (ambientVertices_mem_edge X R e h01).2
    have hnot := edgePoint_not_mem_edge_of_pair_ne X R e h13
      h01 hpairs t₂₄ ht₂₄_zero ht₂₄_one
    have hq' : edgePoint X R e 1 3 h13 t₂₄ =
        (e (R.vertex 1) : StandardSphere 2) := by simpa [q] using hq
    exact hnot (hq' ▸ hv1Edge)
  have hqNeVertexThree : q ≠ (e (R.vertex 3) : StandardSphere 2) := by
    intro hq
    have h23 : (2 : Fin 4) ≠ 3 := by decide
    have hpairs : s((1 : Fin 4), 3) ≠ s(2, 3) := by decide
    have hv3Edge : (e (R.vertex 3) : StandardSphere 2) ∈
        edge X R e 2 3 h23 :=
      (ambientVertices_mem_edge X R e h23).2
    have hnot := edgePoint_not_mem_edge_of_pair_ne X R e h13
      h23 hpairs t₂₄ ht₂₄_zero ht₂₄_one
    have hq' : edgePoint X R e 1 3 h13 t₂₄ =
        (e (R.vertex 3) : StandardSphere 2) := by simpa [q] using hq
    exact hnot (hq' ▸ hv3Edge)
  have hqInterior : q ∈ interior := by
    refine ⟨hdiagonalRange ▸ hqEdge, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hqNeVertexOne, hqNeVertexThree⟩
  have hqTheta : q ∈ thetaᶜ := hinteriorTheta hqInterior
  have hinteriorConnected : IsConnected interior := by
    simpa only [interior, hdiagonalZero, hdiagonalOne] using
      embeddedArc_range_diff_endpoints_isConnected diagonal hdiagonalEmbedding
  have hinteriorComponent : interior ⊆ connectedComponentIn thetaᶜ q :=
    hinteriorConnected.2.subset_connectedComponentIn hqInterior hinteriorTheta
  have hdiagonalEnds := embeddedArc_endpoints_mem_closure_interiorRange
    diagonal hdiagonalEmbedding
  rw [hdiagonalZero, hdiagonalOne] at hdiagonalEnds
  have hv1Closure : (e (R.vertex 1) : StandardSphere 2) ∈
      closure (connectedComponentIn thetaᶜ q) :=
    closure_mono hinteriorComponent hdiagonalEnds.1
  have hv3Closure : (e (R.vertex 3) : StandardSphere 2) ∈
      closure (connectedComponentIn thetaᶜ q) :=
    closure_mono hinteriorComponent hdiagonalEnds.2
  let qTheta : (thetaᶜ : Set (StandardSphere 2)) := ⟨q, hqTheta⟩
  obtain ⟨regionIndex, hregionIndex⟩ := hrepresentative.2
    (qTheta : ConnectedComponents (thetaᶜ : Set (StandardSphere 2)))
  have hqThetaComponent : connectedComponentIn thetaᶜ q =
      connectedComponentIn thetaᶜ (representative 2) := by
    have hcomponent := (connectedComponentIn_eq_of_componentClass_eq
      (representative regionIndex) qTheta hregionIndex).symm
    fin_cases regionIndex
    · have hv1Theta : (e (R.vertex 1) : StandardSphere 2) ∈ theta :=
        P.ambientEdge_subset 0 hv1First
      have hv1NotClosure :=
        not_mem_closure_connectedComponentIn_of_frontier_subset
          hv1Theta hv1Other hfrontierZero.le
      exact (hv1NotClosure (hcomponent ▸ hv1Closure)).elim
    · have hv3Theta : (e (R.vertex 3) : StandardSphere 2) ∈ theta :=
        P.ambientEdge_subset 1 hv3Second
      have hv3NotClosure :=
        not_mem_closure_connectedComponentIn_of_frontier_subset
          hv3Theta hv3Other hfrontierOne.le
      exact (hv3NotClosure (hcomponent ▸ hv3Closure)).elim
    · exact hcomponent
  have hqCycle : q ∈ (cycle X R e)ᶜ := by
    intro hqCycle
    have havoid := cycle_subset_pairComplement X R e t₁₃ t₂₄
      ht₁₃_zero ht₁₃_one ht₂₄_zero ht₂₄_one hqCycle
    exact havoid (Or.inr rfl)
  have hqInPairRegion : q ∈ connectedComponentIn (cycle X R e)ᶜ
      (representative 2) := by
    have hmem : q ∈ connectedComponentIn thetaᶜ q :=
      mem_connectedComponentIn hqTheta
    rw [hqThetaComponent, hpairComponent] at hmem
    exact hmem
  have hqCycleComponent : connectedComponentIn (cycle X R e)ᶜ q =
      connectedComponentIn (cycle X R e)ᶜ (representative 2) :=
    (connectedComponentIn_eq hqInPairRegion).symm
  have hpCycle : p ∈ (cycle X R e)ᶜ := by
    intro hpCycle
    have havoid := cycle_subset_pairComplement X R e t₁₃ t₂₄
      ht₁₃_zero ht₁₃_one ht₂₄_zero ht₂₄_one hpCycle
    exact havoid (Or.inl rfl)
  have hpTheta : p ∈ theta := by
    right
    exact edgePoint_mem_edge X R e (by decide) t₁₃
  -- Equality of the two cycle components would put the first diagonal point
  -- into a theta-complementary region, contradicting its membership in the theta.
  intro heq
  have hpInPairRegion : p ∈ connectedComponentIn (cycle X R e)ᶜ
      (representative 2) := by
    rw [← hqCycleComponent, ← heq]
    exact mem_connectedComponentIn hpCycle
  have hpInThetaComplement : p ∈ connectedComponentIn thetaᶜ
      (representative 2) := by
    rw [hpairComponent]
    exact hpInPairRegion
  exact (connectedComponentIn_subset thetaᶜ _ hpInThetaComplement) hpTheta

/-- Helper for Lemma 65.1: the two chosen nonendpoint diagonal points are distinct. -/
private lemma diagonalEdgePoints_ne
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) (t₁₃ t₂₄ : unitInterval)
    (ht₂₄_zero : t₂₄ ≠ 0) (ht₂₄_one : t₂₄ ≠ 1) :
    edgePoint X R e 0 2 (of_decide_eq_true rfl) t₁₃ ≠
      edgePoint X R e 1 3 (of_decide_eq_true rfl) t₂₄ := by
  have hpairs : s((1 : Fin 4), 3) ≠ s(0, 2) := by decide
  have hfirstMem := edgePoint_mem_edge X R e
    (by decide : (0 : Fin 4) ≠ 2) t₁₃
  have hsecondNotMem := edgePoint_not_mem_edge_of_pair_ne X R e
    (by decide : (1 : Fin 4) ≠ 3) (by decide : (0 : Fin 4) ≠ 2)
    hpairs t₂₄ ht₂₄_zero ht₂₄_one
  -- Equality would place the second diagonal point on the disjoint first diagonal.
  intro heq
  exact hsecondNotMem (heq ▸ hfirstMem)

/-- Helper for Lemma 65.1: forgetting the second puncture gives a nested point
of the once-punctured sphere. -/
private def pairComplementToNestedPuncture (p q : StandardSphere 2) :
    ({p, q}ᶜ : Set (StandardSphere 2)) →
      {x : ({p}ᶜ : Set (StandardSphere 2)) // x.1 ≠ q} :=
  fun x ↦ ⟨⟨x.1, fun hp ↦ x.2 (Or.inl hp)⟩, fun hq ↦ x.2 (Or.inr hq)⟩

/-- Helper for Lemma 65.1: flattening a nested puncture gives a point outside
the corresponding two-point set. -/
private def nestedPunctureToPairComplement (p q : StandardSphere 2) :
    {x : ({p}ᶜ : Set (StandardSphere 2)) // x.1 ≠ q} →
      ({p, q}ᶜ : Set (StandardSphere 2)) :=
  fun x ↦ ⟨x.1.1, fun h ↦ h.elim x.1.2 x.2⟩

/-- Helper for Lemma 65.1: nesting a point outside two punctures is continuous. -/
private lemma continuous_pairComplementToNestedPuncture (p q : StandardSphere 2) :
    Continuous (pairComplementToNestedPuncture p q) := by
  -- Build the two subtype layers separately to keep transports out of later uses.
  have hinner : Continuous (fun x : ({p, q}ᶜ : Set (StandardSphere 2)) ↦
      (⟨x.1, fun hp ↦ x.2 (Or.inl hp)⟩ : ({p}ᶜ : Set (StandardSphere 2)))) :=
    continuous_subtype_val.subtype_mk
      (fun (x : ({p, q}ᶜ : Set (StandardSphere 2))) hp ↦ x.2 (Or.inl hp))
  exact hinner.subtype_mk (fun x hq ↦ x.2 (Or.inr hq))

/-- Helper for Lemma 65.1: flattening a nested puncture is continuous. -/
private lemma continuous_nestedPunctureToPairComplement (p q : StandardSphere 2) :
    Continuous (nestedPunctureToPairComplement p q) := by
  -- The underlying map is the composite of the two subtype projections.
  exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
    (fun x h ↦ h.elim x.1.2 x.2)

/-- Helper for Lemma 65.1: flattening after nesting fixes a pair-complement point. -/
private lemma nestedPunctureToPairComplement_leftInverse (p q : StandardSphere 2) :
    Function.LeftInverse (nestedPunctureToPairComplement p q)
      (pairComplementToNestedPuncture p q) := by
  -- Both sides have the same ambient sphere value.
  intro x
  apply Subtype.ext
  exact Eq.refl x.1

/-- Helper for Lemma 65.1: nesting after flattening fixes a nested puncture point. -/
private lemma nestedPunctureToPairComplement_rightInverse (p q : StandardSphere 2) :
    Function.RightInverse (nestedPunctureToPairComplement p q)
      (pairComplementToNestedPuncture p q) := by
  -- Compare first the outer and then the inner subtype values.
  intro x
  apply Subtype.ext
  apply Subtype.ext
  exact Eq.refl x.1.1

/-- Helper for Lemma 65.1: the two-point complement is the complement of the
second point inside the sphere punctured at the first. -/
private def pairComplementHomeomorphNestedPuncture (p q : StandardSphere 2) :
    ({p, q}ᶜ : Set (StandardSphere 2)) ≃ₜ
      {x : ({p}ᶜ : Set (StandardSphere 2)) // x.1 ≠ q} :=
  { toFun := pairComplementToNestedPuncture p q
    invFun := nestedPunctureToPairComplement p q
    left_inv := nestedPunctureToPairComplement_leftInverse p q
    right_inv := nestedPunctureToPairComplement_rightInverse p q
    continuous_toFun := continuous_pairComplementToNestedPuncture p q
    continuous_invFun := continuous_nestedPunctureToPairComplement p q }

/-- Helper for Lemma 65.1: distinct sphere points put the second point in the
complement of the first. -/
private lemma secondPoint_mem_firstPointComplement
    (p q : StandardSphere 2) (hpq : p ≠ q) : q ∈ ({p}ᶜ : Set (StandardSphere 2)) := by
  -- Complement membership is the reversed distinctness hypothesis.
  simpa using hpq.symm

/-- Helper for Lemma 65.1: stereographic and complex coordinates identify a
once-punctured sphere with `ℂ`. -/
private noncomputable def puncturedSphereHomeomorphComplex (p : StandardSphere 2) :
    ({p}ᶜ : Set (StandardSphere 2)) ≃ₜ ℂ :=
  (StandardSphere.puncturedHomeomorphPlane p).trans
    Complex.orthonormalBasisOneI.repr.symm.toHomeomorph

/-- Helper for Lemma 65.1: translating stereographic coordinates sends the
second puncture to zero. -/
private noncomputable def translatedPuncturedSphereChart
    (p q : StandardSphere 2) (hpq : p ≠ q) :
    ({p}ᶜ : Set (StandardSphere 2)) ≃ₜ ℂ :=
  (puncturedSphereHomeomorphComplex p).trans
    (Homeomorph.subRight
      (puncturedSphereHomeomorphComplex p
        ⟨q, secondPoint_mem_firstPointComplement p q hpq⟩))

/-- Helper for Lemma 65.1: the translated chart is nonzero exactly away from
the second puncture. -/
private lemma translatedPuncturedSphereChart_ne_zero_iff
    (p q : StandardSphere 2) (hpq : p ≠ q)
    (x : ({p}ᶜ : Set (StandardSphere 2))) :
    x.1 ≠ q ↔ translatedPuncturedSphereChart p q hpq x ≠ 0 := by
  -- Translation reduces nonvanishing to injectivity of the original chart.
  simp only [translatedPuncturedSphereChart, Homeomorph.trans_apply,
    Homeomorph.subRight_apply, sub_ne_zero]
  rw [(puncturedSphereHomeomorphComplex p).injective.ne_iff]
  simpa using (Subtype.coe_ne_coe (a := x)
    (b := (⟨q, secondPoint_mem_firstPointComplement p q hpq⟩ :
      ({p}ᶜ : Set (StandardSphere 2)))))

/-- Helper for Lemma 65.1: distinct punctures identify the twice-punctured
sphere with the punctured complex plane. -/
private noncomputable def pairComplementHomeomorphPuncturedComplex
    (p q : StandardSphere 2) (hpq : p ≠ q) :
    ({p, q}ᶜ : Set (StandardSphere 2)) ≃ₜ {z : ℂ // z ≠ 0} :=
  (pairComplementHomeomorphNestedPuncture p q).trans
    ((translatedPuncturedSphereChart p q hpq).subtype
      (translatedPuncturedSphereChart_ne_zero_iff p q hpq))

/-- Helper for Lemma 65.1: polar and logarithmic coordinates identify the
punctured complex plane with the infinite cylinder. -/
private noncomputable def puncturedComplexHomeomorphInfiniteCylinder :
    {z : ℂ // z ≠ 0} ≃ₜ Circle × ℝ :=
  Complex.polarHomeomorph.symm.trans
    ((Homeomorph.refl Circle).prodCongr Real.expOrderIso.toHomeomorph.symm)

/-- Helper for Lemma 65.1: the punctured complex plane has infinite-cyclic
fundamental group at every basepoint. -/
private lemma puncturedComplex_fundamentalGroupEquivInt
    (z : {z : ℂ // z ≠ 0}) :
    Nonempty (FundamentalGroup {z : ℂ // z ≠ 0} z ≃* Multiplicative ℤ) := by
  -- Transfer the cylinder calculation through polar coordinates.
  let cylinderEquiv := puncturedComplexHomeomorphInfiniteCylinder
  exact ⟨(cylinderEquiv.fundamentalGroupMulEquiv z).trans
    (fundamentalGroup_infiniteCylinder (cylinderEquiv z)).some⟩

/-- Helper for Lemma 65.1: a twice-punctured two-sphere has infinite-cyclic
fundamental group at every basepoint. -/
private lemma pairComplementFundamentalGroupEquivInt
    (p q : StandardSphere 2) (hpq : p ≠ q)
    (x : ({p, q}ᶜ : Set (StandardSphere 2))) :
    Nonempty (FundamentalGroup ({p, q}ᶜ : Set (StandardSphere 2)) x ≃*
      Multiplicative ℤ) := by
  -- Pass to the punctured complex plane and then to its cylinder model.
  let puncturedEquiv := pairComplementHomeomorphPuncturedComplex p q hpq
  exact ⟨(puncturedEquiv.fundamentalGroupMulEquiv x).trans
    (puncturedComplex_fundamentalGroupEquivInt (puncturedEquiv x)).some⟩

/-- Helper for Lemma 65.1: the fundamental group of the realized four-cycle
has canonical infinite-cyclic coordinates at every basepoint. -/
private lemma cycleFundamentalGroupEquivInt
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) (c : cycle X R e) :
    Nonempty (FundamentalGroup (cycle X R e) c ≃* Multiplicative ℤ) := by
  obtain ⟨curveEquiv⟩ :=
    Topology.IsSimpleClosedCurve.homeomorphic_circle (X := cycle X R e)
  -- Move the image basepoint on the circle before applying its standard computation.
  exact ⟨(curveEquiv.fundamentalGroupMulEquiv c).trans
    ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
      (curveEquiv c) 1).trans Circle.fundamentalGroupEquivInt)⟩

/-- Helper for Lemma 65.1: a nontrivial homomorphism between groups with
infinite-cyclic coordinates is injective. -/
private lemma monoidHom_injective_of_equivInt_of_ne_one
    {G H : Type*} [Group G] [Group H] (f : G →* H)
    (sourceCoordinates : G ≃* Multiplicative ℤ)
    (targetCoordinates : H ≃* Multiplicative ℤ) (hf : f ≠ 1) :
    Function.Injective f := by
  let coordinateMap : Multiplicative ℤ →* Multiplicative ℤ :=
    targetCoordinates.toMonoidHom.comp
      (f.comp sourceCoordinates.symm.toMonoidHom)
  have coordinateMap_ne_one : coordinateMap ≠ 1 := by
    intro hcoordinate
    apply hf
    ext x
    apply targetCoordinates.injective
    calc
      targetCoordinates (f x) = coordinateMap (sourceCoordinates x) := by
        simp only [coordinateMap, MonoidHom.comp_apply,
          MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      _ = 1 := by rw [hcoordinate]; rfl
      _ = targetCoordinates 1 := targetCoordinates.map_one.symm
  let additiveCoordinateMap : ℤ →+ ℤ := coordinateMap.toAdditive
  have additiveCoordinateMap_ne_zero : additiveCoordinateMap ≠ 0 := by
    intro hadditive
    apply coordinateMap_ne_one
    apply MonoidHom.toAdditive.injective
    exact hadditive
  have generator_image_ne_zero : additiveCoordinateMap 1 ≠ 0 := by
    intro hgenerator
    apply additiveCoordinateMap_ne_zero
    apply AddMonoidHom.ext_int
    simpa using hgenerator
  have additiveCoordinateMap_injective : Function.Injective additiveCoordinateMap := by
    intro m n hmn
    have hm : additiveCoordinateMap m = m * additiveCoordinateMap 1 := by
      simpa only [zsmul_eq_mul, Int.cast_id, mul_one] using
        additiveCoordinateMap.map_zsmul m (1 : ℤ)
    have hn : additiveCoordinateMap n = n * additiveCoordinateMap 1 := by
      simpa only [zsmul_eq_mul, Int.cast_id, mul_one] using
        additiveCoordinateMap.map_zsmul n (1 : ℤ)
    rw [hm, hn] at hmn
    exact mul_right_cancel₀ generator_image_ne_zero hmn
  have coordinateMap_injective : Function.Injective coordinateMap := by
    intro m n hmn
    apply Multiplicative.toAdd.injective
    exact additiveCoordinateMap_injective hmn
  -- Transport injectivity back through the two coordinate equivalences.
  intro x y hxy
  apply sourceCoordinates.injective
  apply coordinateMap_injective
  simpa only [coordinateMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply] using congrArg targetCoordinates hxy

/-- Helper for Lemma 65.1: a surjective homomorphism to a group with integer
coordinates cannot be the trivial homomorphism. -/
private lemma monoidHom_ne_one_of_surjective_of_equivInt
    {G H : Type*} [Group G] [Group H] (f : G →* H)
    (targetCoordinates : H ≃* Multiplicative ℤ)
    (hf : Function.Surjective f) : f ≠ 1 := by
  let generator : H := targetCoordinates.symm (Multiplicative.ofAdd (1 : ℤ))
  have generator_ne_one : generator ≠ 1 := by
    intro hgenerator
    have hcoordinates := congrArg targetCoordinates hgenerator
    simp only [generator, MulEquiv.apply_symm_apply, map_one] at hcoordinates
    norm_num at hcoordinates
  obtain ⟨preimage, hpreimage⟩ := hf generator
  -- A trivial map cannot hit the chosen nonidentity integer generator.
  intro htrivial
  apply generator_ne_one
  rw [← hpreimage, htrivial]
  rfl

/-- Helper for Lemma 65.1: relabeling the vertices of a complete-graph
realization preserves the endpoint incidence law. -/
private lemma relabelRealization_incident
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (σ : Equiv.Perm (Fin 4))
    (graphEdge : (SimpleGraph.completeGraph (Fin 4)).edgeSet) (x : Fin 4) :
    x ∈ graphEdge.1 ↔
      R.vertex (σ x) = R.finiteLinearGraph.edge
          (R.edgeEquiv
            ((SimpleGraph.Iso.completeGraph σ).mapEdgeSet graphEdge)) 0 ∨
        R.vertex (σ x) = R.finiteLinearGraph.edge
          (R.edgeEquiv
            ((SimpleGraph.Iso.completeGraph σ).mapEdgeSet graphEdge)) 1 := by
  rw [← R.incident_iff_endpoint]
  change x ∈ graphEdge.1 ↔ σ x ∈ Sym2.map σ graphEdge.1
  constructor
  · intro hx
    exact Sym2.mem_map.mpr ⟨x, hx, rfl⟩
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Sym2.mem_map.mp hx
    exact σ.injective hyx ▸ hy

/-- Helper for Lemma 65.1: a permutation of the four vertices induces the
corresponding relabeled linear realization. -/
private def relabelRealization
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (σ : Equiv.Perm (Fin 4)) :
    (SimpleGraph.completeGraph (Fin 4)).LinearRealization :=
  { Carrier := R.Carrier
    linearGraph := R.linearGraph
    vertex := fun i ↦ R.vertex (σ i)
    vertex_injective := R.vertex_injective.comp σ.injective
    edgeEquiv := (SimpleGraph.Iso.completeGraph σ).mapEdgeSet.trans R.edgeEquiv
    vertex_eq_endpoint_iff := relabelRealization_incident R σ }

/-- Helper for Lemma 65.1: a relabeled realized edge is the original edge
between the corresponding permuted vertices. -/
private lemma edge_relabelRealization
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) (σ : Equiv.Perm (Fin 4))
    {i j : Fin 4} (hij : i ≠ j) :
    edge X (relabelRealization R σ) e i j hij =
      edge X R e (σ i) (σ j) (σ.injective.ne hij) := by
  -- Both sides select the same intrinsic edge after mapping the unordered pair.
  unfold edge relabelRealization
  rw [SimpleGraph.LinearRealization.ambientEdge_eq_image_edgeSet,
    SimpleGraph.LinearRealization.ambientEdge_eq_image_edgeSet]
  rfl

/-- Helper for Lemma 65.1: a parameter point on a relabeled edge is the same
parameter point on the corresponding original edge. -/
private lemma edgePoint_relabelRealization
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) (σ : Equiv.Perm (Fin 4))
    {i j : Fin 4} (hij : i ≠ j) (t : unitInterval) :
    edgePoint X (relabelRealization R σ) e i j hij t =
      edgePoint X R e (σ i) (σ j) (σ.injective.ne hij) t := by
  -- Relabeling changes only the combinatorial name of the stored edge.
  unfold edgePoint relabelRealization SimpleGraph.LinearRealization.finiteLinearGraph
  rfl

/-- Helper for Lemma 65.1: the alternative four-cycle follows the vertex order
`0-2-1-3-0`. -/
private def alternativeCycle
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) : Set (StandardSphere 2) :=
  edge X R e 0 2 (of_decide_eq_true rfl) ∪
    edge X R e 2 1 (of_decide_eq_true rfl) ∪
    edge X R e 1 3 (of_decide_eq_true rfl) ∪
    edge X R e 3 0 (of_decide_eq_true rfl)

/-- Helper for Lemma 65.1: swapping vertices `1` and `2` turns the canonical
cycle into the alternative cycle. -/
private lemma cycle_relabelSwap_eq_alternativeCycle
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) :
    cycle X (relabelRealization R (Equiv.swap 1 2)) e =
      alternativeCycle X R e := by
  -- Normalize each of the four relabeled edges separately.
  unfold cycle alternativeCycle
  rw [edge_relabelRealization, edge_relabelRealization,
    edge_relabelRealization, edge_relabelRealization]
  have hswapZero : Equiv.swap (1 : Fin 4) 2 0 = 0 := by decide
  have hswapOne : Equiv.swap (1 : Fin 4) 2 1 = 2 := by decide
  have hswapTwo : Equiv.swap (1 : Fin 4) 2 2 = 1 := by decide
  have hswapThree : Equiv.swap (1 : Fin 4) 2 3 = 3 := by decide
  have hfirst : edge X R e (Equiv.swap 1 2 0) (Equiv.swap 1 2 1)
      ((Equiv.swap 1 2).injective.ne (by decide)) =
      edge X R e 0 2 (of_decide_eq_true rfl) := by
    unfold edge
    congr 1
  have hsecond : edge X R e (Equiv.swap 1 2 1) (Equiv.swap 1 2 2)
      ((Equiv.swap 1 2).injective.ne (by decide)) =
      edge X R e 2 1 (of_decide_eq_true rfl) := by
    unfold edge
    congr 1
  have hthird : edge X R e (Equiv.swap 1 2 2) (Equiv.swap 1 2 3)
      ((Equiv.swap 1 2).injective.ne (by decide)) =
      edge X R e 1 3 (of_decide_eq_true rfl) := by
    unfold edge
    congr 1
  have hfourth : edge X R e (Equiv.swap 1 2 3) (Equiv.swap 1 2 0)
      ((Equiv.swap 1 2).injective.ne (by decide)) =
      edge X R e 3 0 (of_decide_eq_true rfl) := by
    unfold edge
    congr 1
  rw [hfirst, hsecond, hthird, hfourth]

/-- Helper for Lemma 65.1: interior points of edges `0-1` and `2-3` lie in
different components of the alternative-cycle complement. -/
private lemma alternativeDiagonalPoints_differentComponents
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) (t₀₁ t₂₃ : unitInterval)
    (ht₀₁_zero : t₀₁ ≠ 0) (ht₀₁_one : t₀₁ ≠ 1)
    (ht₂₃_zero : t₂₃ ≠ 0) (ht₂₃_one : t₂₃ ≠ 1) :
    connectedComponentIn (alternativeCycle X R e)ᶜ
        (edgePoint X R e 0 1 (of_decide_eq_true rfl) t₀₁) ≠
      connectedComponentIn (alternativeCycle X R e)ᶜ
        (edgePoint X R e 2 3 (of_decide_eq_true rfl) t₂₃) := by
  let σ : Equiv.Perm (Fin 4) := Equiv.swap 1 2
  have hdifferent := diagonalPoints_differentComponents X
    (relabelRealization R σ) e t₀₁ t₂₃
    ht₀₁_zero ht₀₁_one ht₂₃_zero ht₂₃_one
  -- Rewrite the relabeled cycle and its two diagonals to their original names.
  simpa [σ, cycle_relabelSwap_eq_alternativeCycle,
    edgePoint_relabelRealization, Equiv.swap_apply_def] using hdifferent

/-- Helper for Lemma 65.1: induced fundamental-group maps commute with
basepoint change along a path. -/
private lemma fundamentalGroupMap_basepointChange_naturality
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) {y₀ y₁ : Y} (gamma : Path y₀ y₁) :
    (FundamentalGroup.fundamentalGroupMulEquivOfPath
        (gamma.map f.continuous)).toMonoidHom.comp
        (FundamentalGroup.map f y₀) =
      (FundamentalGroup.map f y₁).comp
        (FundamentalGroup.fundamentalGroupMulEquivOfPath gamma).toMonoidHom := by
  -- Functoriality carries conjugation by `gamma` to conjugation by its image.
  ext loop
  let F := FundamentalGroupoid.map f
  let sourceIso : FundamentalGroupoid.mk y₀ ≅ FundamentalGroupoid.mk y₁ :=
    (CategoryTheory.Groupoid.isoEquivHom _ _).symm ⟦gamma⟧
  let targetIso : FundamentalGroupoid.mk (f y₀) ≅ FundamentalGroupoid.mk (f y₁) :=
    (CategoryTheory.Groupoid.isoEquivHom _ _).symm ⟦gamma.map f.continuous⟧
  have mapIso_eq : F.mapIso sourceIso = targetIso := by
    apply CategoryTheory.Iso.ext
    rfl
  change targetIso.conj (F.map loop) = F.map (sourceIso.conj loop)
  rw [← mapIso_eq]
  simp only [CategoryTheory.Iso.conj_apply, CategoryTheory.Functor.mapIso_hom,
    CategoryTheory.Functor.mapIso_inv, CategoryTheory.Functor.map_comp]
  rfl

/-- Helper for Lemma 65.1: surjectivity of an induced fundamental-group map
passes forward along a path in its source. -/
private lemma fundamentalGroupMap_surjective_of_path
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) {y₀ y₁ : Y} (gamma : Path y₀ y₁) :
    Function.Surjective (FundamentalGroup.map f y₀) →
      Function.Surjective (FundamentalGroup.map f y₁) := by
  intro hsurjective targetLoop
  let sourceChange := FundamentalGroup.fundamentalGroupMulEquivOfPath gamma
  let targetChange := FundamentalGroup.fundamentalGroupMulEquivOfPath
    (gamma.map f.continuous)
  obtain ⟨oldTarget, holdTarget⟩ := targetChange.surjective targetLoop
  obtain ⟨oldSource, holdSource⟩ := hsurjective oldTarget
  refine ⟨sourceChange oldSource, ?_⟩
  have naturality := DFunLike.congr_fun
    (fundamentalGroupMap_basepointChange_naturality f gamma) oldSource
  -- Traverse the naturality square and then apply both chosen preimage equations.
  calc
    FundamentalGroup.map f y₁ (sourceChange oldSource) =
        targetChange (FundamentalGroup.map f y₀ oldSource) := naturality.symm
    _ = targetChange oldTarget := congrArg targetChange holdSource
    _ = targetLoop := holdTarget

/-- Helper for Lemma 65.1: mapping a concatenated source loop maps each of its
two constituent paths. -/
private lemma fundamentalGroupMap_fromPath_trans
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) {a b : Y} (alpha : Path a b) (beta : Path b a) :
    FundamentalGroup.map f a
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (alpha.trans beta))) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          ((alpha.map f.continuous).trans (beta.map f.continuous))) := by
  -- Expose quotient mapping and use functoriality of path concatenation.
  rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map, Path.map_trans]

/-- Helper for Lemma 65.1: a nonendpoint parameter point of a realized edge
differs from both realized endpoints. -/
private lemma edgePoint_ne_endpoints
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) {i j : Fin 4} (hij : i ≠ j) (t : unitInterval)
    (ht_zero : t ≠ 0) (ht_one : t ≠ 1) :
    edgePoint X R e i j hij t ≠ e (R.vertex i) ∧
      edgePoint X R e i j hij t ≠ e (R.vertex j) := by
  let graphEdge : (SimpleGraph.completeGraph (Fin 4)).edgeSet :=
    ⟨s(i, j), hij⟩
  have hendpoints := realizedEdge_endpointPair R hij graphEdge rfl
  have hiEndpoint : R.vertex i ∈
      ({R.finiteLinearGraph.edge (R.edgeEquiv graphEdge) 0,
        R.finiteLinearGraph.edge (R.edgeEquiv graphEdge) 1} : Set R.Carrier) := by
    rw [hendpoints]
    exact Or.inl rfl
  have hjEndpoint : R.vertex j ∈
      ({R.finiteLinearGraph.edge (R.edgeEquiv graphEdge) 0,
        R.finiteLinearGraph.edge (R.edgeEquiv graphEdge) 1} : Set R.Carrier) := by
    rw [hendpoints]
    exact Or.inr (Set.mem_singleton_iff.mpr rfl)
  -- Injectivity of the stored edge parameterization detects either endpoint.
  constructor
  · intro hpoint
    have hintrinsic :
        R.finiteLinearGraph.edge (R.edgeEquiv graphEdge) t = R.vertex i := by
      apply e.injective
      apply Subtype.ext
      exact hpoint
    rcases hiEndpoint with hiZero | hiOne
    · apply ht_zero
      exact (R.finiteLinearGraph.edgeEmbedding (R.edgeEquiv graphEdge)).injective
        (hintrinsic.trans hiZero)
    · apply ht_one
      exact (R.finiteLinearGraph.edgeEmbedding (R.edgeEquiv graphEdge)).injective
        (hintrinsic.trans (Set.mem_singleton_iff.mp hiOne))
  · intro hpoint
    have hintrinsic :
        R.finiteLinearGraph.edge (R.edgeEquiv graphEdge) t = R.vertex j := by
      apply e.injective
      apply Subtype.ext
      exact hpoint
    rcases hjEndpoint with hjZero | hjOne
    · apply ht_zero
      exact (R.finiteLinearGraph.edgeEmbedding (R.edgeEquiv graphEdge)).injective
        (hintrinsic.trans hjZero)
    · apply ht_one
      exact (R.finiteLinearGraph.edgeEmbedding (R.edgeEquiv graphEdge)).injective
        (hintrinsic.trans (Set.mem_singleton_iff.mp hjOne))

/-- Helper for Lemma 65.1: a nondegenerate subpath of an injective path is
injective. -/
private lemma Path.subpath_injective_of_ne
    {Z : Type*} [TopologicalSpace Z] {x y : Z}
    (gamma : Path x y) (hgamma : Function.Injective gamma)
    (s t : unitInterval) (hst : s ≠ t) :
    Function.Injective (gamma.subpath s t) := by
  -- The affine reparameterization is injective when its endpoints differ.
  intro u v huv
  change gamma (Set.Icc.convexComb s t u) =
    gamma (Set.Icc.convexComb s t v) at huv
  have hparameters := congrArg Subtype.val (hgamma huv)
  have hvalues : (s : ℝ) ≠ (t : ℝ) := Subtype.coe_ne_coe.mpr hst
  apply Subtype.ext
  simp only [Set.Icc.coe_convexComb] at hparameters
  rcases lt_or_gt_of_ne hvalues with hlt | hgt
  · nlinarith
  · nlinarith

/-- Helper for Lemma 65.1: an oriented realized edge splits at an interior
point into two subpaths with controlled ranges and endpoint omissions. -/
private lemma existsOrientedEdgeSplitAtPoint
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) {a b : Fin 4} (hab : a ≠ b)
    {p : StandardSphere 2} (hp : p ∈ edge X R e a b hab)
    (hpA : p ≠ e (R.vertex a)) (hpB : p ≠ e (R.vertex b)) :
    ∃ (left : Path (e (R.vertex a) : StandardSphere 2) p)
        (right : Path p (e (R.vertex b) : StandardSphere 2)),
      Set.range left ∪ Set.range right = edge X R e a b hab ∧
      Set.range left ∩ Set.range right = {p} ∧
      Set.range left ⊆ edge X R e a b hab ∧
      Set.range right ⊆ edge X R e a b hab ∧
      (e (R.vertex b) : StandardSphere 2) ∉ Set.range left ∧
      (e (R.vertex a) : StandardSphere 2) ∉ Set.range right := by
  obtain ⟨gamma, hgamma, hzero, hone, hrange⟩ :=
    existsOrientedEdge X R e hab
  let gammaMap : C(unitInterval, StandardSphere 2) :=
    ⟨gamma, hgamma.continuous⟩
  let gammaPath : Path (e (R.vertex a) : StandardSphere 2)
      (e (R.vertex b) : StandardSphere 2) :=
    ⟨gammaMap, hzero, hone⟩
  have hpRange : p ∈ Set.range gamma := by
    rw [hrange]
    exact hp
  obtain ⟨t, ht⟩ := hpRange
  have htZero : t ≠ 0 := by
    intro htValue
    apply hpA
    subst t
    exact ht.symm.trans hzero
  have htOne : t ≠ 1 := by
    intro htValue
    apply hpB
    subst t
    exact ht.symm.trans hone
  let leftRaw := gammaPath.subpath 0 t
  let rightRaw := gammaPath.subpath t 1
  let left : Path (e (R.vertex a) : StandardSphere 2) p :=
    leftRaw.cast gammaPath.source.symm ht.symm
  let right : Path p (e (R.vertex b) : StandardSphere 2) :=
    rightRaw.cast ht.symm gammaPath.target.symm
  have leftCoe : (left : unitInterval → StandardSphere 2) = leftRaw :=
    Path.cast_coe leftRaw gammaPath.source.symm ht.symm
  have rightCoe : (right : unitInterval → StandardSphere 2) = rightRaw :=
    Path.cast_coe rightRaw ht.symm gammaPath.target.symm
  have hcover : Set.range left ∪ Set.range right = edge X R e a b hab := by
    -- The two parameter intervals cover the full oriented edge.
    rw [leftCoe, rightCoe, Path.range_subpath_of_le gammaPath 0 t bot_le,
      Path.range_subpath_of_le gammaPath t 1 le_top, ← hrange]
    ext z
    constructor
    · intro hz
      rcases hz with ⟨u, -, huz⟩ | ⟨u, -, huz⟩
      · change gamma u = z at huz
        exact ⟨u, huz⟩
      · change gamma u = z at huz
        exact ⟨u, huz⟩
    · rintro ⟨u, huz⟩
      by_cases hut : u ≤ t
      · exact Or.inl ⟨u, ⟨bot_le, hut⟩, huz⟩
      · exact Or.inr ⟨u, ⟨le_of_not_ge hut, le_top⟩, huz⟩
  have hinter : Set.range left ∩ Set.range right = {p} := by
    -- Injectivity forces the two parameter intervals to meet only at `t`.
    rw [leftCoe, rightCoe, Path.range_subpath_of_le gammaPath 0 t bot_le,
      Path.range_subpath_of_le gammaPath t 1 le_top]
    ext z
    constructor
    · rintro ⟨⟨u, hu, huz⟩, ⟨v, hv, hvz⟩⟩
      change gamma u = z at huz
      change gamma v = z at hvz
      have huv : u = v := hgamma.injective (huz.trans hvz.symm)
      have htu : t ≤ u := by simpa [huv] using hv.1
      have hut : u = t := le_antisymm hu.2 htu
      rw [Set.mem_singleton_iff]
      exact huz.symm.trans ((congrArg gamma hut).trans ht)
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact ⟨⟨t, ⟨bot_le, le_rfl⟩, ht⟩,
        ⟨t, ⟨le_rfl, le_top⟩, ht⟩⟩
  have hleftSubset : Set.range left ⊆ edge X R e a b hab := by
    intro z hz
    rw [← hcover]
    exact Or.inl hz
  have hrightSubset : Set.range right ⊆ edge X R e a b hab := by
    intro z hz
    rw [← hcover]
    exact Or.inr hz
  have hbNotLeft : (e (R.vertex b) : StandardSphere 2) ∉ Set.range left := by
    rw [leftCoe, Path.range_subpath_of_le gammaPath 0 t bot_le]
    rintro ⟨u, hu, hub⟩
    change gamma u = (e (R.vertex b) : StandardSphere 2) at hub
    have huOne : u = 1 := hgamma.injective (hub.trans hone.symm)
    apply htOne
    exact le_antisymm le_top (huOne ▸ hu.2)
  have haNotRight : (e (R.vertex a) : StandardSphere 2) ∉ Set.range right := by
    rw [rightCoe, Path.range_subpath_of_le gammaPath t 1 le_top]
    rintro ⟨u, hu, hua⟩
    change gamma u = (e (R.vertex a) : StandardSphere 2) at hua
    have huZero : u = 0 := hgamma.injective (hua.trans hzero.symm)
    apply htZero
    exact le_antisymm (huZero ▸ hu.1) bot_le
  -- The split-path interface hides all orientation and subpath bookkeeping.
  exact ⟨left, right, hcover, hinter, hleftSubset, hrightSubset,
    hbNotLeft, haNotRight⟩

/-- Helper for Lemma 65.1: endpoint restrictions detect disjointness of
subsets of two distinct realized edges. -/
private lemma edgeSubsets_disjoint_of_endpointRestrictions
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) {a b c d : Fin 4}
    (hab : a ≠ b) (hcd : c ≠ d) (hpairs : s(a, b) ≠ s(c, d))
    {A B : Set (StandardSphere 2)}
    (hA : A ⊆ edge X R e a b hab) (hB : B ⊆ edge X R e c d hcd)
    (hendpoints : Disjoint
      (A ∩ {(e (R.vertex a) : StandardSphere 2),
        (e (R.vertex b) : StandardSphere 2)})
      (B ∩ {(e (R.vertex c) : StandardSphere 2),
        (e (R.vertex d) : StandardSphere 2)})) :
    Disjoint A B := by
  rw [Set.disjoint_left] at hendpoints ⊢
  intro z hzA hzB
  have hzEdges : z ∈ edge X R e a b hab ∩ edge X R e c d hcd :=
    ⟨hA hzA, hB hzB⟩
  rw [edge_inter_edge_eq_endpointPairs X R e hab hcd hpairs] at hzEdges
  -- A common point would belong to both endpoint-restricted subsets.
  exact hendpoints ⟨hzA, hzEdges.1⟩ ⟨hzB, hzEdges.2⟩

/-- Helper for Lemma 65.1: the intersection of two distinct realized edges
is the image of the intersection of their combinatorial endpoint pairs. -/
private lemma edge_inter_edge_eq_endpointIndexImage
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) {a b c d : Fin 4}
    (hab : a ≠ b) (hcd : c ≠ d) (hpairs : s(a, b) ≠ s(c, d)) :
    edge X R e a b hab ∩ edge X R e c d hcd =
      (fun i : Fin 4 ↦ (e (R.vertex i) : StandardSphere 2)) ''
        (({a, b} : Set (Fin 4)) ∩ {c, d}) := by
  let vertexImage := fun i : Fin 4 ↦ (e (R.vertex i) : StandardSphere 2)
  have hvertexImage : Function.Injective vertexImage :=
    Subtype.val_injective.comp (e.injective.comp R.vertex_injective)
  calc
    edge X R e a b hab ∩ edge X R e c d hcd =
        ({vertexImage a, vertexImage b} ∩
          {vertexImage c, vertexImage d} : Set (StandardSphere 2)) :=
      edge_inter_edge_eq_endpointPairs X R e hab hcd hpairs
    _ = vertexImage '' ({a, b} : Set (Fin 4)) ∩
        vertexImage '' ({c, d} : Set (Fin 4)) := by
      simp only [Set.image_insert_eq, Set.image_singleton]
    _ = vertexImage '' (({a, b} : Set (Fin 4)) ∩ {c, d}) :=
      (Set.image_inter hvertexImage).symm

/-- Helper for Lemma 65.1: subsets of ambient sets with empty intersection
are disjoint. -/
private lemma disjoint_of_subsets_of_inter_eq_empty
    {Z : Type*} {A B E F : Set Z} (hA : A ⊆ E) (hB : B ⊆ F)
    (hinter : E ∩ F = ∅) : Disjoint A B := by
  rw [Set.disjoint_left]
  intro z hzA hzB
  have hz : z ∈ E ∩ F := ⟨hA hzA, hB hzB⟩
  rw [hinter] at hz
  exact hz

/-- Helper for Lemma 65.1: subsets of ambient sets meeting at one point are
disjoint when one subset omits that point. -/
private lemma disjoint_of_subsets_of_inter_eq_singleton
    {Z : Type*} {A B E F : Set Z} {p : Z}
    (hA : A ⊆ E) (hB : B ⊆ F) (hinter : E ∩ F = {p})
    (hp : p ∉ A ∨ p ∉ B) : Disjoint A B := by
  rw [Set.disjoint_left]
  intro z hzA hzB
  have hz : z ∈ E ∩ F := ⟨hA hzA, hB hzB⟩
  rw [hinter, Set.mem_singleton_iff] at hz
  rcases hp with hpA | hpB
  · exact hpA (hz ▸ hzA)
  · exact hpB (hz ▸ hzB)

/-- Helper for Lemma 65.1: an oriented realized edge has a path
parameterization with the prescribed endpoints and full edge range. -/
private lemma existsOrientedEdgePath
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) {a b : Fin 4} (hab : a ≠ b) :
    ∃ gamma : Path (e (R.vertex a) : StandardSphere 2)
        (e (R.vertex b) : StandardSphere 2),
      Topology.IsEmbedding gamma ∧
        Set.range gamma = edge X R e a b hab := by
  obtain ⟨gamma, hgamma, hzero, hone, hrange⟩ :=
    existsOrientedEdge X R e hab
  let gammaMap : C(unitInterval, StandardSphere 2) :=
    ⟨gamma, hgamma.continuous⟩
  let gammaPath : Path (e (R.vertex a) : StandardSphere 2)
      (e (R.vertex b) : StandardSphere 2) :=
    ⟨gammaMap, hzero, hone⟩
  have gammaCoe : (gammaPath : unitInterval → StandardSphere 2) = gamma := rfl
  -- Package the existing oriented embedding as a path without changing its range.
  refine ⟨gammaPath, ?_, ?_⟩
  · rw [gammaCoe]
    exact hgamma
  · rw [gammaCoe]
    exact hrange

/-- Helper for Lemma 65.1: the four textbook broken-line paths decompose the
alternative cycle into two closed puncture-to-puncture obstacles. -/
private lemma existsAlternativeCycleCrossingDecomposition
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X)
    (p q x y : StandardSphere 2)
    (hp : p ∈ edge X R e 0 2 (of_decide_eq_true rfl))
    (hq : q ∈ edge X R e 1 3 (of_decide_eq_true rfl))
    (hx : x ∈ edge X R e 0 1 (of_decide_eq_true rfl))
    (hy : y ∈ edge X R e 2 3 (of_decide_eq_true rfl))
    (hpEnds : p ≠ e (R.vertex 0) ∧ p ≠ e (R.vertex 2))
    (hqEnds : q ≠ e (R.vertex 1) ∧ q ≠ e (R.vertex 3))
    (hxEnds : x ≠ e (R.vertex 0) ∧ x ≠ e (R.vertex 1))
    (hyEnds : y ≠ e (R.vertex 2) ∧ y ≠ e (R.vertex 3)) :
    ∃ (alpha : Path x y) (beta : Path y x)
        (D₁ D₂ : Set (StandardSphere 2)),
      IsClosed D₁ ∧ IsClosed D₂ ∧ D₁ ∩ D₂ = {p, q} ∧
      D₁ ∪ D₂ = alternativeCycle X R e ∧
      Set.range alpha ⊆ cycle X R e ∧
      Set.range beta ⊆ cycle X R e ∧
      Disjoint (Set.range alpha) D₁ ∧
      Disjoint (Set.range beta) D₂ := by
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h21 : (2 : Fin 4) ≠ 1 := by decide
  have h30 : (3 : Fin 4) ≠ 0 := by decide
  obtain ⟨pLeft, pRight, hpCover, hpInter, hpLeftSubset, hpRightSubset,
      hv2NotPLeft, hv0NotPRight⟩ :=
    existsOrientedEdgeSplitAtPoint X R e h02 hp hpEnds.1 hpEnds.2
  obtain ⟨qLeft, qRight, hqCover, hqInter, hqLeftSubset, hqRightSubset,
      hv3NotQLeft, hv1NotQRight⟩ :=
    existsOrientedEdgeSplitAtPoint X R e h13 hq hqEnds.1 hqEnds.2
  obtain ⟨xLeft, xRight, hxCover, hxInter, hxLeftSubset, hxRightSubset,
      hv1NotXLeft, hv0NotXRight⟩ :=
    existsOrientedEdgeSplitAtPoint X R e h01 hx hxEnds.1 hxEnds.2
  obtain ⟨yLeft, yRight, hyCover, hyInter, hyLeftSubset, hyRightSubset,
      hv3NotYLeft, hv2NotYRight⟩ :=
    existsOrientedEdgeSplitAtPoint X R e h23 hy hyEnds.1 hyEnds.2
  obtain ⟨edge03, -, hedge03Range⟩ := existsOrientedEdgePath X R e h03
  obtain ⟨edge21, -, hedge21Range⟩ := existsOrientedEdgePath X R e h21
  obtain ⟨edge30, -, hedge30Range⟩ := existsOrientedEdgePath X R e h30
  let alpha : Path x y := xLeft.symm.trans (edge03.trans yRight.symm)
  let beta : Path y x := yLeft.symm.trans (edge21.trans xRight.symm)
  let d₁ : Path p q := pRight.trans (edge21.trans qLeft)
  let d₂ : Path q p := qRight.trans (edge30.trans pLeft)
  let D₁ : Set (StandardSphere 2) := Set.range d₁
  let D₂ : Set (StandardSphere 2) := Set.range d₂
  have hedge03Subset : Set.range edge03 ⊆ edge X R e 0 3 h03 := by
    rw [hedge03Range]
  have hedge21Subset : Set.range edge21 ⊆ edge X R e 2 1 h21 := by
    rw [hedge21Range]
  have hedge30Subset : Set.range edge30 ⊆ edge X R e 3 0 h30 := by
    rw [hedge30Range]
  -- Compute once the realized-edge intersections used by all range arguments.
  have hinter02_13 : edge X R e 0 2 h02 ∩ edge X R e 1 3 h13 = ∅ := by
    have hindices : ({0, 2} : Set (Fin 4)) ∩ {1, 3} = ∅ := by
      ext i
      fin_cases i <;> simp
    rw [edge_inter_edge_eq_endpointIndexImage X R e h02 h13 (by decide),
      hindices, Set.image_empty]
  have hinter02_30 : edge X R e 0 2 h02 ∩ edge X R e 3 0 h30 =
      {(e (R.vertex 0) : StandardSphere 2)} := by
    have hindices : ({0, 2} : Set (Fin 4)) ∩ {3, 0} = {0} := by
      ext i
      fin_cases i <;> simp
    rw [edge_inter_edge_eq_endpointIndexImage X R e h02 h30 (by decide),
      hindices, Set.image_singleton]
  have hinter21_13 : edge X R e 2 1 h21 ∩ edge X R e 1 3 h13 =
      {(e (R.vertex 1) : StandardSphere 2)} := by
    have hindices : ({2, 1} : Set (Fin 4)) ∩ {1, 3} = {1} := by
      ext i
      fin_cases i <;> simp
    rw [edge_inter_edge_eq_endpointIndexImage X R e h21 h13 (by decide),
      hindices, Set.image_singleton]
  have hinter21_30 : edge X R e 2 1 h21 ∩ edge X R e 3 0 h30 = ∅ := by
    have hindices : ({2, 1} : Set (Fin 4)) ∩ {3, 0} = ∅ := by
      ext i
      fin_cases i <;> simp
    rw [edge_inter_edge_eq_endpointIndexImage X R e h21 h30 (by decide),
      hindices, Set.image_empty]
  have hinter21_02 : edge X R e 2 1 h21 ∩ edge X R e 0 2 h02 =
      {(e (R.vertex 2) : StandardSphere 2)} := by
    have hindices : ({2, 1} : Set (Fin 4)) ∩ {0, 2} = {2} := by
      ext i
      fin_cases i <;> simp
    rw [edge_inter_edge_eq_endpointIndexImage X R e h21 h02 (by decide),
      hindices, Set.image_singleton]
  have hinter13_30 : edge X R e 1 3 h13 ∩ edge X R e 3 0 h30 =
      {(e (R.vertex 3) : StandardSphere 2)} := by
    have hindices : ({1, 3} : Set (Fin 4)) ∩ {3, 0} = {3} := by
      ext i
      fin_cases i <;> simp
    rw [edge_inter_edge_eq_endpointIndexImage X R e h13 h30 (by decide),
      hindices, Set.image_singleton]
  have hinter13_02 : edge X R e 1 3 h13 ∩ edge X R e 0 2 h02 = ∅ := by
    rw [Set.inter_comm, hinter02_13]
  have hinter01_02 : edge X R e 0 1 h01 ∩ edge X R e 0 2 h02 =
      {(e (R.vertex 0) : StandardSphere 2)} := by
    have hindices : ({0, 1} : Set (Fin 4)) ∩ {0, 2} = {0} := by
      ext i
      fin_cases i <;> simp
    rw [edge_inter_edge_eq_endpointIndexImage X R e h01 h02 (by decide),
      hindices, Set.image_singleton]
  have hinter01_21 : edge X R e 0 1 h01 ∩ edge X R e 2 1 h21 =
      {(e (R.vertex 1) : StandardSphere 2)} := by
    have hindices : ({0, 1} : Set (Fin 4)) ∩ {2, 1} = {1} := by
      ext i
      fin_cases i <;> simp
    rw [edge_inter_edge_eq_endpointIndexImage X R e h01 h21 (by decide),
      hindices, Set.image_singleton]
  have hinter01_13 : edge X R e 0 1 h01 ∩ edge X R e 1 3 h13 =
      {(e (R.vertex 1) : StandardSphere 2)} := by
    have hindices : ({0, 1} : Set (Fin 4)) ∩ {1, 3} = {1} := by
      ext i
      fin_cases i <;> simp
    rw [edge_inter_edge_eq_endpointIndexImage X R e h01 h13 (by decide),
      hindices, Set.image_singleton]
  have hinter03_02 : edge X R e 0 3 h03 ∩ edge X R e 0 2 h02 =
      {(e (R.vertex 0) : StandardSphere 2)} := by
    have hindices : ({0, 3} : Set (Fin 4)) ∩ {0, 2} = {0} := by
      ext i
      fin_cases i <;> simp
    rw [edge_inter_edge_eq_endpointIndexImage X R e h03 h02 (by decide),
      hindices, Set.image_singleton]
  have hinter03_21 : edge X R e 0 3 h03 ∩ edge X R e 2 1 h21 = ∅ := by
    have hindices : ({0, 3} : Set (Fin 4)) ∩ {2, 1} = ∅ := by
      ext i
      fin_cases i <;> simp
    rw [edge_inter_edge_eq_endpointIndexImage X R e h03 h21 (by decide),
      hindices, Set.image_empty]
  have hinter03_13 : edge X R e 0 3 h03 ∩ edge X R e 1 3 h13 =
      {(e (R.vertex 3) : StandardSphere 2)} := by
    have hindices : ({0, 3} : Set (Fin 4)) ∩ {1, 3} = {3} := by
      ext i
      fin_cases i <;> simp
    rw [edge_inter_edge_eq_endpointIndexImage X R e h03 h13 (by decide),
      hindices, Set.image_singleton]
  have hinter23_02 : edge X R e 2 3 h23 ∩ edge X R e 0 2 h02 =
      {(e (R.vertex 2) : StandardSphere 2)} := by
    have hindices : ({2, 3} : Set (Fin 4)) ∩ {0, 2} = {2} := by
      ext i
      fin_cases i <;> simp
    rw [edge_inter_edge_eq_endpointIndexImage X R e h23 h02 (by decide),
      hindices, Set.image_singleton]
  have hinter23_21 : edge X R e 2 3 h23 ∩ edge X R e 2 1 h21 =
      {(e (R.vertex 2) : StandardSphere 2)} := by
    have hindices : ({2, 3} : Set (Fin 4)) ∩ {2, 1} = {2} := by
      ext i
      fin_cases i <;> simp
    rw [edge_inter_edge_eq_endpointIndexImage X R e h23 h21 (by decide),
      hindices, Set.image_singleton]
  have hinter23_13 : edge X R e 2 3 h23 ∩ edge X R e 1 3 h13 =
      {(e (R.vertex 3) : StandardSphere 2)} := by
    have hindices : ({2, 3} : Set (Fin 4)) ∩ {1, 3} = {3} := by
      ext i
      fin_cases i <;> simp
    rw [edge_inter_edge_eq_endpointIndexImage X R e h23 h13 (by decide),
      hindices, Set.image_singleton]
  have hinter23_30 : edge X R e 2 3 h23 ∩ edge X R e 3 0 h30 =
      {(e (R.vertex 3) : StandardSphere 2)} := by
    have hindices : ({2, 3} : Set (Fin 4)) ∩ {3, 0} = {3} := by
      ext i
      fin_cases i <;> simp
    rw [edge_inter_edge_eq_endpointIndexImage X R e h23 h30 (by decide),
      hindices, Set.image_singleton]
  have hinter01_30 : edge X R e 0 1 h01 ∩ edge X R e 3 0 h30 =
      {(e (R.vertex 0) : StandardSphere 2)} := by
    have hindices : ({0, 1} : Set (Fin 4)) ∩ {3, 0} = {0} := by
      ext i
      fin_cases i <;> simp
    rw [edge_inter_edge_eq_endpointIndexImage X R e h01 h30 (by decide),
      hindices, Set.image_singleton]
  -- The obstacle pieces are pairwise disjoint except at their designated split points.
  have hPrightQright : Disjoint (Set.range pRight) (Set.range qRight) :=
    disjoint_of_subsets_of_inter_eq_empty hpRightSubset hqRightSubset hinter02_13
  have hPrightEdge30 : Disjoint (Set.range pRight) (Set.range edge30) :=
    disjoint_of_subsets_of_inter_eq_singleton hpRightSubset hedge30Subset
      hinter02_30 (Or.inl hv0NotPRight)
  have hEdge21Qright : Disjoint (Set.range edge21) (Set.range qRight) :=
    disjoint_of_subsets_of_inter_eq_singleton hedge21Subset hqRightSubset
      hinter21_13 (Or.inr hv1NotQRight)
  have hEdge21Edge30 : Disjoint (Set.range edge21) (Set.range edge30) :=
    disjoint_of_subsets_of_inter_eq_empty hedge21Subset hedge30Subset hinter21_30
  have hEdge21Pleft : Disjoint (Set.range edge21) (Set.range pLeft) :=
    disjoint_of_subsets_of_inter_eq_singleton hedge21Subset hpLeftSubset
      hinter21_02 (Or.inr hv2NotPLeft)
  have hQleftEdge30 : Disjoint (Set.range qLeft) (Set.range edge30) :=
    disjoint_of_subsets_of_inter_eq_singleton hqLeftSubset hedge30Subset
      hinter13_30 (Or.inl hv3NotQLeft)
  have hQleftPleft : Disjoint (Set.range qLeft) (Set.range pLeft) :=
    disjoint_of_subsets_of_inter_eq_empty hqLeftSubset hpLeftSubset hinter13_02
  have hD₁Range : D₁ = Set.range pRight ∪
      (Set.range edge21 ∪ Set.range qLeft) := by
    unfold D₁ d₁
    rw [Path.trans_range, Path.trans_range]
  have hD₂Range : D₂ = Set.range qRight ∪
      (Set.range edge30 ∪ Set.range pLeft) := by
    unfold D₂ d₂
    rw [Path.trans_range, Path.trans_range]
  have hDinter : D₁ ∩ D₂ = {p, q} := by
    rw [hD₁Range, hD₂Range]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨hzPright | hzEdge21 | hzQleft,
          hzQright | hzEdge30 | hzPleft⟩
      · exact (Set.disjoint_left.mp hPrightQright hzPright hzQright).elim
      · exact (Set.disjoint_left.mp hPrightEdge30 hzPright hzEdge30).elim
      · have hz : z ∈ Set.range pLeft ∩ Set.range pRight :=
          ⟨hzPleft, hzPright⟩
        rw [hpInter, Set.mem_singleton_iff] at hz
        exact Or.inl hz
      · exact (Set.disjoint_left.mp hEdge21Qright hzEdge21 hzQright).elim
      · exact (Set.disjoint_left.mp hEdge21Edge30 hzEdge21 hzEdge30).elim
      · exact (Set.disjoint_left.mp hEdge21Pleft hzEdge21 hzPleft).elim
      · have hz : z ∈ Set.range qLeft ∩ Set.range qRight :=
          ⟨hzQleft, hzQright⟩
        rw [hqInter, Set.mem_singleton_iff] at hz
        exact Or.inr hz
      · exact (Set.disjoint_left.mp hQleftEdge30 hzQleft hzEdge30).elim
      · exact (Set.disjoint_left.mp hQleftPleft hzQleft hzPleft).elim
    · intro hz
      rcases hz with rfl | rfl
      · exact ⟨Or.inl ⟨0, pRight.source⟩,
          Or.inr (Or.inr ⟨1, pLeft.target⟩)⟩
      · exact ⟨Or.inr (Or.inr ⟨1, qLeft.target⟩),
          Or.inl ⟨0, qRight.source⟩⟩
  have hDunion : D₁ ∪ D₂ = alternativeCycle X R e := by
    rw [hD₁Range, hD₂Range]
    unfold alternativeCycle
    rw [← hpCover, ← hqCover, ← hedge21Range, ← hedge30Range]
    ext z
    simp only [Set.mem_union]
    tauto
  have hAlphaRange : Set.range alpha = Set.range xLeft ∪
      (Set.range edge03 ∪ Set.range yRight) := by
    unfold alpha
    rw [Path.trans_range, Path.trans_range, Path.symm_range, Path.symm_range]
  have hBetaRange : Set.range beta = Set.range yLeft ∪
      (Set.range edge21 ∪ Set.range xRight) := by
    unfold beta
    rw [Path.trans_range, Path.trans_range, Path.symm_range, Path.symm_range]
  have hAlphaCycle : Set.range alpha ⊆ cycle X R e := by
    rw [hAlphaRange]
    intro z hz
    rcases hz with hzX | hz03 | hzY
    · have hz01 := hxLeftSubset hzX
      unfold cycle
      exact Or.inl (Or.inl (Or.inl hz01))
    · have hz30 : z ∈ edge X R e 3 0 h30 := by
        rw [← edge_comm X R e h03]
        exact hedge03Subset hz03
      unfold cycle
      exact Or.inr hz30
    · have hz23 := hyRightSubset hzY
      unfold cycle
      exact Or.inl (Or.inr hz23)
  have hBetaCycle : Set.range beta ⊆ cycle X R e := by
    rw [hBetaRange]
    intro z hz
    rcases hz with hzY | hz21 | hzX
    · have hz23 := hyLeftSubset hzY
      unfold cycle
      exact Or.inl (Or.inr hz23)
    · have hz12 : z ∈ edge X R e 1 2 h21.symm := by
        rw [← edge_comm X R e h21]
        exact hedge21Subset hz21
      unfold cycle
      exact Or.inl (Or.inl (Or.inr hz12))
    · have hz01 := hxRightSubset hzX
      unfold cycle
      exact Or.inl (Or.inl (Or.inl hz01))
  -- Each cycle path avoids the obstacle assigned to the opposite side.
  have hXleftPright : Disjoint (Set.range xLeft) (Set.range pRight) :=
    disjoint_of_subsets_of_inter_eq_singleton hxLeftSubset hpRightSubset
      hinter01_02 (Or.inr hv0NotPRight)
  have hXleftEdge21 : Disjoint (Set.range xLeft) (Set.range edge21) :=
    disjoint_of_subsets_of_inter_eq_singleton hxLeftSubset hedge21Subset
      hinter01_21 (Or.inl hv1NotXLeft)
  have hXleftQleft : Disjoint (Set.range xLeft) (Set.range qLeft) :=
    disjoint_of_subsets_of_inter_eq_singleton hxLeftSubset hqLeftSubset
      hinter01_13 (Or.inl hv1NotXLeft)
  have hEdge03Pright : Disjoint (Set.range edge03) (Set.range pRight) :=
    disjoint_of_subsets_of_inter_eq_singleton hedge03Subset hpRightSubset
      hinter03_02 (Or.inr hv0NotPRight)
  have hEdge03Edge21 : Disjoint (Set.range edge03) (Set.range edge21) :=
    disjoint_of_subsets_of_inter_eq_empty hedge03Subset hedge21Subset hinter03_21
  have hEdge03Qleft : Disjoint (Set.range edge03) (Set.range qLeft) :=
    disjoint_of_subsets_of_inter_eq_singleton hedge03Subset hqLeftSubset
      hinter03_13 (Or.inr hv3NotQLeft)
  have hYrightPright : Disjoint (Set.range yRight) (Set.range pRight) :=
    disjoint_of_subsets_of_inter_eq_singleton hyRightSubset hpRightSubset
      hinter23_02 (Or.inl hv2NotYRight)
  have hYrightEdge21 : Disjoint (Set.range yRight) (Set.range edge21) :=
    disjoint_of_subsets_of_inter_eq_singleton hyRightSubset hedge21Subset
      hinter23_21 (Or.inl hv2NotYRight)
  have hYrightQleft : Disjoint (Set.range yRight) (Set.range qLeft) :=
    disjoint_of_subsets_of_inter_eq_singleton hyRightSubset hqLeftSubset
      hinter23_13 (Or.inr hv3NotQLeft)
  have hAlphaD₁ : Disjoint (Set.range alpha) D₁ := by
    rw [hAlphaRange, hD₁Range, Set.disjoint_left]
    intro z hzAlpha hzD₁
    rcases hzAlpha with hzX | hz03 | hzY
    · rcases hzD₁ with hzP | hz21 | hzQ
      · exact Set.disjoint_left.mp hXleftPright hzX hzP
      · exact Set.disjoint_left.mp hXleftEdge21 hzX hz21
      · exact Set.disjoint_left.mp hXleftQleft hzX hzQ
    · rcases hzD₁ with hzP | hz21 | hzQ
      · exact Set.disjoint_left.mp hEdge03Pright hz03 hzP
      · exact Set.disjoint_left.mp hEdge03Edge21 hz03 hz21
      · exact Set.disjoint_left.mp hEdge03Qleft hz03 hzQ
    · rcases hzD₁ with hzP | hz21 | hzQ
      · exact Set.disjoint_left.mp hYrightPright hzY hzP
      · exact Set.disjoint_left.mp hYrightEdge21 hzY hz21
      · exact Set.disjoint_left.mp hYrightQleft hzY hzQ
  have hYleftQright : Disjoint (Set.range yLeft) (Set.range qRight) :=
    disjoint_of_subsets_of_inter_eq_singleton hyLeftSubset hqRightSubset
      hinter23_13 (Or.inl hv3NotYLeft)
  have hYleftEdge30 : Disjoint (Set.range yLeft) (Set.range edge30) :=
    disjoint_of_subsets_of_inter_eq_singleton hyLeftSubset hedge30Subset
      hinter23_30 (Or.inl hv3NotYLeft)
  have hYleftPleft : Disjoint (Set.range yLeft) (Set.range pLeft) :=
    disjoint_of_subsets_of_inter_eq_singleton hyLeftSubset hpLeftSubset
      hinter23_02 (Or.inr hv2NotPLeft)
  have hEdge21Qright : Disjoint (Set.range edge21) (Set.range qRight) :=
    disjoint_of_subsets_of_inter_eq_singleton hedge21Subset hqRightSubset
      hinter21_13 (Or.inr hv1NotQRight)
  have hEdge21Pleft' : Disjoint (Set.range edge21) (Set.range pLeft) :=
    disjoint_of_subsets_of_inter_eq_singleton hedge21Subset hpLeftSubset
      hinter21_02 (Or.inr hv2NotPLeft)
  have hXrightQright : Disjoint (Set.range xRight) (Set.range qRight) :=
    disjoint_of_subsets_of_inter_eq_singleton hxRightSubset hqRightSubset
      hinter01_13 (Or.inr hv1NotQRight)
  have hXrightEdge30 : Disjoint (Set.range xRight) (Set.range edge30) :=
    disjoint_of_subsets_of_inter_eq_singleton hxRightSubset hedge30Subset
      hinter01_30 (Or.inl hv0NotXRight)
  have hXrightPleft : Disjoint (Set.range xRight) (Set.range pLeft) :=
    disjoint_of_subsets_of_inter_eq_singleton hxRightSubset hpLeftSubset
      hinter01_02 (Or.inl hv0NotXRight)
  have hBetaD₂ : Disjoint (Set.range beta) D₂ := by
    rw [hBetaRange, hD₂Range, Set.disjoint_left]
    intro z hzBeta hzD₂
    rcases hzBeta with hzY | hz21 | hzX
    · rcases hzD₂ with hzQ | hz30 | hzP
      · exact Set.disjoint_left.mp hYleftQright hzY hzQ
      · exact Set.disjoint_left.mp hYleftEdge30 hzY hz30
      · exact Set.disjoint_left.mp hYleftPleft hzY hzP
    · rcases hzD₂ with hzQ | hz30 | hzP
      · exact Set.disjoint_left.mp hEdge21Qright hz21 hzQ
      · exact Set.disjoint_left.mp hEdge21Edge30 hz21 hz30
      · exact Set.disjoint_left.mp hEdge21Pleft' hz21 hzP
    · rcases hzD₂ with hzQ | hz30 | hzP
      · exact Set.disjoint_left.mp hXrightQright hzX hzQ
      · exact Set.disjoint_left.mp hXrightEdge30 hzX hz30
      · exact Set.disjoint_left.mp hXrightPleft hzX hzP
  have hD₁Closed : IsClosed D₁ := (isCompact_range d₁.continuous).isClosed
  have hD₂Closed : IsClosed D₂ := (isCompact_range d₂.continuous).isClosed
  -- Return only the stable range and avoidance interface used by the cover proof.
  exact ⟨alpha, beta, D₁, D₂, hD₁Closed, hD₂Closed, hDinter,
    hDunion, hAlphaCycle, hBetaCycle, hAlphaD₁, hBetaD₂⟩

/-- Helper for Lemma 65.1: two closed obstacles meeting at the punctures
produce the required open crossing cover from their two complementary regions. -/
private lemma existsPuncturedObstacleCrossingCover
    {Z W : Type*} [TopologicalSpace Z] [LocallyConnectedSpace Z]
    [TopologicalSpace W] (p q : Z)
    (f : C(W, ({p, q}ᶜ : Set Z))) {a b : W}
    (alpha : Path a b) (beta : Path b a) (D₁ D₂ : Set Z)
    (hD₁Closed : IsClosed D₁) (hD₂Closed : IsClosed D₂)
    (hinter : D₁ ∩ D₂ = {p, q})
    (ha : (f a : Z) ∈ (D₁ ∪ D₂)ᶜ) (hb : (f b : Z) ∈ (D₁ ∪ D₂)ᶜ)
    (hdifferent : connectedComponentIn (D₁ ∪ D₂)ᶜ (f a : Z) ≠
      connectedComponentIn (D₁ ∪ D₂)ᶜ (f b : Z))
    (hcomponents : Cardinal.mk
      (ConnectedComponents ((D₁ ∪ D₂)ᶜ : Set Z)) = 2)
    (halpha : ∀ t, (f (alpha t) : Z) ∉ D₁)
    (hbeta : ∀ t, (f (beta t) : Z) ∉ D₂) :
    ∃ U V A B : Set ({p, q}ᶜ : Set Z),
      IsOpen U ∧ IsOpen V ∧ IsOpen A ∧ IsOpen B ∧
      U ∪ V = Set.univ ∧ U ∩ V = A ∪ B ∧ Disjoint A B ∧
      f a ∈ A ∧ f b ∈ B ∧
      (∀ t, f (alpha t) ∈ U) ∧ (∀ t, f (beta t) ∈ V) := by
  classical
  let F : Set Z := (D₁ ∪ D₂)ᶜ
  let aF : F := ⟨f a, ha⟩
  let bF : F := ⟨f b, hb⟩
  have endpointClasses_ne :
      (aF : ConnectedComponents F) ≠ bF := by
    -- Equal quotient classes would contradict the prescribed endpoint regions.
    intro hclasses
    apply hdifferent
    exact connectedComponentIn_eq_of_componentClass_eq aF bF hclasses
  have componentCases (z : F) :
      (z : ConnectedComponents F) = aF ∨
        (z : ConnectedComponents F) = bF := by
    -- A two-element component quotient is exhausted by the distinct endpoint classes.
    obtain ⟨other, hother, hotherUnique⟩ :=
      (Cardinal.mk_eq_two_iff'
        (aF : ConnectedComponents F)).mp hcomponents
    have b_eq_other : (bF : ConnectedComponents F) = other :=
      hotherUnique bF endpointClasses_ne.symm
    by_cases hz : (z : ConnectedComponents F) = aF
    · exact Or.inl hz
    · exact Or.inr ((hotherUnique z hz).trans b_eq_other.symm)
  let U : Set ({p, q}ᶜ : Set Z) := Subtype.val ⁻¹' D₁ᶜ
  let V : Set ({p, q}ᶜ : Set Z) := Subtype.val ⁻¹' D₂ᶜ
  let A : Set ({p, q}ᶜ : Set Z) :=
    Subtype.val ⁻¹' connectedComponentIn F (f a : Z)
  let B : Set ({p, q}ᶜ : Set Z) :=
    Subtype.val ⁻¹' connectedComponentIn F (f b : Z)
  have hUopen : IsOpen U :=
    hD₁Closed.isOpen_compl.preimage continuous_subtype_val
  have hVopen : IsOpen V :=
    hD₂Closed.isOpen_compl.preimage continuous_subtype_val
  have hAopen : IsOpen A := by
    -- Ambient components of the open common complement remain open after pullback.
    exact (hD₁Closed.union hD₂Closed).isOpen_compl.connectedComponentIn.preimage
      continuous_subtype_val
  have hBopen : IsOpen B := by
    exact (hD₁Closed.union hD₂Closed).isOpen_compl.connectedComponentIn.preimage
      continuous_subtype_val
  have hcover : U ∪ V = Set.univ := by
    -- A pair-complement point cannot lie on both obstacles.
    ext z
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases hzD₁ : (z : Z) ∈ D₁
    · right
      intro hzD₂
      have hinterMembership :=
        congrArg (fun S : Set Z ↦ (z : Z) ∈ S) hinter
      have hzPair : (z : Z) ∈ ({p, q} : Set Z) :=
        hinterMembership.mp ⟨hzD₁, hzD₂⟩
      exact z.property hzPair
    · exact Or.inl hzD₁
  have hoverlap : U ∩ V = A ∪ B := by
    ext z
    constructor
    · intro hz
      have hzF : (z : Z) ∈ F := by
        intro hzUnion
        exact hzUnion.elim hz.1 hz.2
      let zF : F := ⟨z, hzF⟩
      rcases componentCases zF with hzA | hzB
      · left
        change (z : Z) ∈ connectedComponentIn F (f a : Z)
        have heq := connectedComponentIn_eq_of_componentClass_eq zF aF hzA
        exact heq ▸ mem_connectedComponentIn hzF
      · right
        change (z : Z) ∈ connectedComponentIn F (f b : Z)
        have heq := connectedComponentIn_eq_of_componentClass_eq zF bF hzB
        exact heq ▸ mem_connectedComponentIn hzF
    · intro hz
      rcases hz with hzA | hzB
      · have hzF : (z : Z) ∈ F :=
          connectedComponentIn_subset F (f a : Z) hzA
        exact ⟨fun hzD₁ ↦ hzF (Or.inl hzD₁),
          fun hzD₂ ↦ hzF (Or.inr hzD₂)⟩
      · have hzF : (z : Z) ∈ F :=
          connectedComponentIn_subset F (f b : Z) hzB
        exact ⟨fun hzD₁ ↦ hzF (Or.inl hzD₁),
          fun hzD₂ ↦ hzF (Or.inr hzD₂)⟩
  have hdisjoint : Disjoint A B := by
    -- Two ambient connected components with a common point would coincide.
    rw [Set.disjoint_left]
    intro z hzA hzB
    apply hdifferent
    exact (connectedComponentIn_eq hzA).trans (connectedComponentIn_eq hzB).symm
  have haA : f a ∈ A := mem_connectedComponentIn ha
  have hbB : f b ∈ B := mem_connectedComponentIn hb
  have halphaU : ∀ t, f (alpha t) ∈ U := halpha
  have hbetaV : ∀ t, f (beta t) ∈ V := hbeta
  -- Package the two obstacle complements and their ambient component partition.
  exact ⟨U, V, A, B, hUopen, hVopen, hAopen, hBopen, hcover, hoverlap,
    hdisjoint, haA, hbB, halphaU, hbetaV⟩

/-- Helper for Lemma 65.1: the split diagonal arcs and the two complementary
cycle paths supply the source proof's crossing-cover certificate. -/
private lemma existsCycleCrossingCover
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) (t₁₃ t₂₄ : unitInterval)
    (ht₁₃_zero : t₁₃ ≠ 0) (ht₁₃_one : t₁₃ ≠ 1)
    (ht₂₄_zero : t₂₄ ≠ 0) (ht₂₄_one : t₂₄ ≠ 1) :
    let pairComplement : Set (StandardSphere 2) :=
      {edgePoint X R e 0 2 (of_decide_eq_true rfl) t₁₃,
        edgePoint X R e 1 3 (of_decide_eq_true rfl) t₂₄}ᶜ
    let inclusion : C(cycle X R e, pairComplement) :=
      ContinuousMap.inclusion
        (cycle_subset_pairComplement X R e t₁₃ t₂₄ ht₁₃_zero ht₁₃_one
          ht₂₄_zero ht₂₄_one)
    ∃ (a b : cycle X R e) (alpha : Path a b) (beta : Path b a)
        (U V A B : Set pairComplement),
      IsOpen U ∧ IsOpen V ∧ IsOpen A ∧ IsOpen B ∧
      U ∪ V = Set.univ ∧ U ∩ V = A ∪ B ∧ Disjoint A B ∧
      inclusion a ∈ A ∧ inclusion b ∈ B ∧
      (∀ t, inclusion (alpha t) ∈ U) ∧
      (∀ t, inclusion (beta t) ∈ V) := by
  dsimp only
  let p := edgePoint X R e 0 2 (of_decide_eq_true rfl) t₁₃
  let q := edgePoint X R e 1 3 (of_decide_eq_true rfl) t₂₄
  let pairComplement : Set (StandardSphere 2) := {p, q}ᶜ
  let inclusion : C(cycle X R e, pairComplement) :=
    ContinuousMap.inclusion
      (cycle_subset_pairComplement X R e t₁₃ t₂₄ ht₁₃_zero ht₁₃_one
        ht₂₄_zero ht₂₄_one)
  have hmidpointMem : (1 / 2 : ℝ) ∈ Set.Icc 0 1 := by norm_num
  let midpoint : unitInterval := ⟨1 / 2, hmidpointMem⟩
  have hmidpointZero : midpoint ≠ 0 := by
    intro h
    have hvalue := congrArg Subtype.val h
    norm_num [midpoint] at hvalue
  have hmidpointOne : midpoint ≠ 1 := by
    intro h
    have hvalue := congrArg Subtype.val h
    norm_num [midpoint] at hvalue
  let x := edgePoint X R e 0 1 (of_decide_eq_true rfl) midpoint
  let y := edgePoint X R e 2 3 (of_decide_eq_true rfl) midpoint
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have hp : p ∈ edge X R e 0 2 (of_decide_eq_true rfl) := by
    exact edgePoint_mem_edge X R e h02 t₁₃
  have hq : q ∈ edge X R e 1 3 (of_decide_eq_true rfl) := by
    exact edgePoint_mem_edge X R e h13 t₂₄
  have hx : x ∈ edge X R e 0 1 (of_decide_eq_true rfl) := by
    exact edgePoint_mem_edge X R e h01 midpoint
  have hy : y ∈ edge X R e 2 3 (of_decide_eq_true rfl) := by
    exact edgePoint_mem_edge X R e h23 midpoint
  have hpEnds : p ≠ e (R.vertex 0) ∧ p ≠ e (R.vertex 2) := by
    exact edgePoint_ne_endpoints X R e h02 t₁₃ ht₁₃_zero ht₁₃_one
  have hqEnds : q ≠ e (R.vertex 1) ∧ q ≠ e (R.vertex 3) := by
    exact edgePoint_ne_endpoints X R e h13 t₂₄ ht₂₄_zero ht₂₄_one
  have hxEnds : x ≠ e (R.vertex 0) ∧ x ≠ e (R.vertex 1) := by
    exact edgePoint_ne_endpoints X R e h01 midpoint
      hmidpointZero hmidpointOne
  have hyEnds : y ≠ e (R.vertex 2) ∧ y ≠ e (R.vertex 3) := by
    exact edgePoint_ne_endpoints X R e h23 midpoint
      hmidpointZero hmidpointOne
  obtain ⟨alphaAmbient, betaAmbient, D₁, D₂, hD₁Closed, hD₂Closed,
      hDinter, hDunion, hAlphaCycle, hBetaCycle, hAlphaD₁, hBetaD₂⟩ :=
    existsAlternativeCycleCrossingDecomposition X R e p q x y hp hq hx hy
      hpEnds hqEnds hxEnds hyEnds
  have hxCycle : x ∈ cycle X R e := by
    unfold cycle
    exact Or.inl (Or.inl (Or.inl hx))
  have hyCycle : y ∈ cycle X R e := by
    unfold cycle
    exact Or.inl (Or.inr hy)
  let a : cycle X R e := ⟨x, hxCycle⟩
  let b : cycle X R e := ⟨y, hyCycle⟩
  have hAlphaMem (t : unitInterval) : alphaAmbient t ∈ cycle X R e :=
    hAlphaCycle (Set.mem_range_self t)
  have hBetaMem (t : unitInterval) : betaAmbient t ∈ cycle X R e :=
    hBetaCycle (Set.mem_range_self t)
  have hAlphaContinuous : Continuous
      (fun t ↦ (⟨alphaAmbient t, hAlphaMem t⟩ : cycle X R e)) :=
    alphaAmbient.continuous.subtype_mk hAlphaMem
  have hBetaContinuous : Continuous
      (fun t ↦ (⟨betaAmbient t, hBetaMem t⟩ : cycle X R e)) :=
    betaAmbient.continuous.subtype_mk hBetaMem
  have hAlphaSource :
      (⟨alphaAmbient 0, hAlphaMem 0⟩ : cycle X R e) = a := by
    apply Subtype.ext
    exact alphaAmbient.source
  have hAlphaTarget :
      (⟨alphaAmbient 1, hAlphaMem 1⟩ : cycle X R e) = b := by
    apply Subtype.ext
    exact alphaAmbient.target
  have hBetaSource :
      (⟨betaAmbient 0, hBetaMem 0⟩ : cycle X R e) = b := by
    apply Subtype.ext
    exact betaAmbient.source
  have hBetaTarget :
      (⟨betaAmbient 1, hBetaMem 1⟩ : cycle X R e) = a := by
    apply Subtype.ext
    exact betaAmbient.target
  let alpha : Path a b :=
    { toContinuousMap :=
        ⟨fun t ↦ ⟨alphaAmbient t, hAlphaMem t⟩, hAlphaContinuous⟩
      source' := hAlphaSource
      target' := hAlphaTarget }
  let beta : Path b a :=
    { toContinuousMap :=
        ⟨fun t ↦ ⟨betaAmbient t, hBetaMem t⟩, hBetaContinuous⟩
      source' := hBetaSource
      target' := hBetaTarget }
  have halphaAvoid (t : unitInterval) :
      (inclusion (alpha t) : StandardSphere 2) ∉ D₁ := by
    exact Set.disjoint_left.mp hAlphaD₁ (Set.mem_range_self t)
  have hbetaAvoid (t : unitInterval) :
      (inclusion (beta t) : StandardSphere 2) ∉ D₂ := by
    exact Set.disjoint_left.mp hBetaD₂ (Set.mem_range_self t)
  have haNotD₁ : (inclusion a : StandardSphere 2) ∉ D₁ := by
    simpa only [alpha.source] using halphaAvoid 0
  have haNotD₂ : (inclusion a : StandardSphere 2) ∉ D₂ := by
    simpa only [beta.target] using hbetaAvoid 1
  have hbNotD₁ : (inclusion b : StandardSphere 2) ∉ D₁ := by
    simpa only [alpha.target] using halphaAvoid 1
  have hbNotD₂ : (inclusion b : StandardSphere 2) ∉ D₂ := by
    simpa only [beta.source] using hbetaAvoid 0
  have haComplement :
      (inclusion a : StandardSphere 2) ∈ (D₁ ∪ D₂)ᶜ :=
    fun h ↦ h.elim haNotD₁ haNotD₂
  have hbComplement :
      (inclusion b : StandardSphere 2) ∈ (D₁ ∪ D₂)ᶜ :=
    fun h ↦ h.elim hbNotD₁ hbNotD₂
  have hAlternativeCurve :
      Topology.IsSimpleClosedCurve (alternativeCycle X R e) := by
    rw [← cycle_relabelSwap_eq_alternativeCycle X R e]
    infer_instance
  have hcomponents : Cardinal.mk
      (ConnectedComponents ((D₁ ∪ D₂)ᶜ : Set (StandardSphere 2))) = 2 := by
    rw [hDunion]
    exact Set.separatesInto_iff.mp
      (@jordanCurveSphere_separatesInto (alternativeCycle X R e)
        hAlternativeCurve)
  have hdifferent :
      connectedComponentIn (D₁ ∪ D₂)ᶜ
          (inclusion a : StandardSphere 2) ≠
        connectedComponentIn (D₁ ∪ D₂)ᶜ
          (inclusion b : StandardSphere 2) := by
    rw [hDunion]
    exact alternativeDiagonalPoints_differentComponents X R e midpoint midpoint
      hmidpointZero hmidpointOne hmidpointZero hmidpointOne
  -- Local instance justification (regularity): the charted-sphere API supplies
  -- the local connectedness used to make complementary components open.
  letI : LocallyConnectedSpace (StandardSphere 2) :=
    ChartedSpace.locallyConnectedSpace
      (EuclideanSpace ℝ (Fin 2)) (StandardSphere 2)
  obtain ⟨U, V, A, B, hUopen, hVopen, hAopen, hBopen, hcover,
      hoverlap, hdisjoint, haA, hbB, halphaU, hbetaV⟩ :=
    existsPuncturedObstacleCrossingCover p q inclusion alpha beta D₁ D₂
      hD₁Closed hD₂Closed hDinter haComplement hbComplement hdifferent
      hcomponents halphaAvoid hbetaAvoid
  -- The lifted cycle paths and obstacle regions are exactly the requested certificate.
  exact ⟨a, b, alpha, beta, U, V, A, B, hUopen, hVopen, hAopen, hBopen,
    hcover, hoverlap, hdisjoint, haA, hbB, halphaU, hbetaV⟩

/-- Helper for Lemma 65.1: the source crossing-loop construction makes the
cycle inclusion surjective on fundamental groups at every cycle basepoint. -/
private lemma cycleInclusionMap_surjective
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) (t₁₃ t₂₄ : unitInterval)
    (ht₁₃_zero : t₁₃ ≠ 0) (ht₁₃_one : t₁₃ ≠ 1)
    (ht₂₄_zero : t₂₄ ≠ 0) (ht₂₄_one : t₂₄ ≠ 1)
    (c : cycle X R e) :
    Function.Surjective
      (FundamentalGroup.mapOfSubset
        (cycle_subset_pairComplement X R e t₁₃ t₂₄ ht₁₃_zero ht₁₃_one
          ht₂₄_zero ht₂₄_one) c) := by
  let pairComplement : Set (StandardSphere 2) :=
    {edgePoint X R e 0 2 (of_decide_eq_true rfl) t₁₃,
      edgePoint X R e 1 3 (of_decide_eq_true rfl) t₂₄}ᶜ
  let inclusion : C(cycle X R e, pairComplement) :=
    ContinuousMap.inclusion
      (cycle_subset_pairComplement X R e t₁₃ t₂₄ ht₁₃_zero ht₁₃_one
        ht₂₄_zero ht₂₄_one)
  obtain ⟨a, b, alpha, beta, U, V, A, B, hU, hV, hA, hB,
      hcover, hoverlap, hdisjoint, ha, hb, halpha, hbeta⟩ :=
    existsCycleCrossingCover X R e t₁₃ t₂₄ ht₁₃_zero ht₁₃_one
      ht₂₄_zero ht₂₄_one
  have hpq : edgePoint X R e 0 2 (of_decide_eq_true rfl) t₁₃ ≠
      edgePoint X R e 1 3 (of_decide_eq_true rfl) t₂₄ :=
    diagonalEdgePoints_ne X R e t₁₃ t₂₄ ht₂₄_zero ht₂₄_one
  obtain ⟨coordinates⟩ := pairComplementFundamentalGroupEquivInt
    (edgePoint X R e 0 2 (of_decide_eq_true rfl) t₁₃)
    (edgePoint X R e 1 3 (of_decide_eq_true rfl) t₂₄) hpq (inclusion a)
  -- Local instance justification (canonical structure): Theorem 63.1 needs the
  -- infinite structure transported by the proved integer-coordinate equivalence.
  letI : Infinite (FundamentalGroup pairComplement (inclusion a)) :=
    coordinates.toEquiv.infinite_iff.mpr inferInstance
  -- Local instance justification (canonical structure): Theorem 63.1 needs the
  -- cyclic structure transported by the same integer-coordinate equivalence.
  letI : IsCyclic (FundamentalGroup pairComplement (inclusion a)) :=
    coordinates.isCyclic.mpr inferInstance
  have mappedLoopGenerates :
      Subgroup.zpowers
          (FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk
              ((alpha.map inclusion.continuous).trans
                (beta.map inclusion.continuous)))) = ⊤ := by
    exact crossingLoopClass_zpowers_eq_top U V A B
      (alpha.map inclusion.continuous) (beta.map inclusion.continuous)
      hU hV hA hB hcover hoverlap hdisjoint ha hb halpha hbeta
  let sourceGenerator :=
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (alpha.trans beta))
  have sourceGeneratorImage : FundamentalGroup.map inclusion a sourceGenerator =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          ((alpha.map inclusion.continuous).trans
            (beta.map inclusion.continuous))) := by
    exact fundamentalGroupMap_fromPath_trans inclusion alpha beta
  have surjectiveAtA : Function.Surjective (FundamentalGroup.map inclusion a) := by
    intro targetLoop
    have targetMem : targetLoop ∈ Subgroup.zpowers
        (FundamentalGroup.map inclusion a sourceGenerator) := by
      rw [sourceGeneratorImage, mappedLoopGenerates]
      exact Subgroup.mem_top targetLoop
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp targetMem
    refine ⟨sourceGenerator ^ n, ?_⟩
    rw [map_zpow, hn]
  obtain ⟨curveEquiv⟩ :=
    Topology.IsSimpleClosedCurve.homeomorphic_circle (X := cycle X R e)
  letI : PathConnectedSpace (cycle X R e) :=
    curveEquiv.symm.surjective.pathConnectedSpace curveEquiv.symm.continuous
  let basepointPath : Path a c := PathConnectedSpace.somePath a c
  -- Transport the generator certificate from the chosen crossing point to `c`.
  rw [FundamentalGroup.mapOfSubset_eq_map_inclusion]
  exact fundamentalGroupMap_surjective_of_path inclusion basepointPath surjectiveAtA

/-- Lemma 65.1 (2): Inclusion of the four-edge cycle into the sphere punctured at
interior points of the two diagonal edges induces a bijection on fundamental groups. -/
theorem cycleInclusionMap_bijective
    (X : Set (StandardSphere 2))
    (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)
    (e : R.Carrier ≃ₜ X) (t₁₃ t₂₄ : unitInterval)
    (ht₁₃_zero : t₁₃ ≠ 0) (ht₁₃_one : t₁₃ ≠ 1)
    (ht₂₄_zero : t₂₄ ≠ 0) (ht₂₄_one : t₂₄ ≠ 1)
    (c : cycle X R e) :
    Function.Bijective
      (FundamentalGroup.mapOfSubset
        (cycle_subset_pairComplement X R e t₁₃ t₂₄ ht₁₃_zero ht₁₃_one
          ht₂₄_zero ht₂₄_one) c) := by
  let p := edgePoint X R e 0 2 (of_decide_eq_true rfl) t₁₃
  let q := edgePoint X R e 1 3 (of_decide_eq_true rfl) t₂₄
  let inclusion := FundamentalGroup.mapOfSubset
    (cycle_subset_pairComplement X R e t₁₃ t₂₄ ht₁₃_zero ht₁₃_one
      ht₂₄_zero ht₂₄_one) c
  have hpq : p ≠ q := by
    exact diagonalEdgePoints_ne X R e t₁₃ t₂₄ ht₂₄_zero ht₂₄_one
  obtain ⟨sourceCoordinates⟩ := cycleFundamentalGroupEquivInt X R e c
  obtain ⟨targetCoordinates⟩ := pairComplementFundamentalGroupEquivInt
    p q hpq ((ContinuousMap.inclusion
      (cycle_subset_pairComplement X R e t₁₃ t₂₄ ht₁₃_zero ht₁₃_one
        ht₂₄_zero ht₂₄_one)) c)
  have hsurjective : Function.Surjective inclusion := by
    exact cycleInclusionMap_surjective X R e t₁₃ t₂₄ ht₁₃_zero ht₁₃_one
      ht₂₄_zero ht₂₄_one c
  -- Surjectivity supplies nontriviality; integer coordinates then force injectivity.
  refine ⟨?_, hsurjective⟩
  apply monoidHom_injective_of_equivInt_of_ne_one inclusion
    sourceCoordinates targetCoordinates
  exact monoidHom_ne_one_of_surjective_of_equivInt inclusion
    targetCoordinates hsurjective


end CompleteGraphFour
