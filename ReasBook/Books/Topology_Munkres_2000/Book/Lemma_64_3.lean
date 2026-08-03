module

public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Topology_Munkres_2000.Book.Definition_61_1.Separation
public import Topology_Munkres_2000.Book.Lemma_64_1
public import Topology_Munkres_2000.Book.Lemma_64_3.RealizedEdge

public section

open Set
open scoped Sym2

namespace SimpleGraph.LinearRealization

variable (R : (SimpleGraph.completeGraph (Fin 4)).LinearRealization)

/-- The triangle in a realized complete graph on four vertices opposite the vertex `i`,
viewed as a subset of the standard two-sphere. -/
def oppositeBoundary (X : Set (StandardSphere 2)) (e : R.Carrier ≃ₜ X)
    (i : Fin 4) : Set (StandardSphere 2) :=
  ⋃ (edge : (SimpleGraph.completeGraph (Fin 4)).edgeSet) (_ : i ∉ edge.1),
    R.ambientEdge X e edge

/-- Every triangle opposite a vertex lies in the realized complete graph. -/
theorem oppositeBoundary_subset (X : Set (StandardSphere 2)) (e : R.Carrier ≃ₜ X)
    (i : Fin 4) : R.oppositeBoundary X e i ⊆ X := by
  rintro x hx
  rcases Set.mem_iUnion.mp hx with ⟨edge, hx⟩
  rcases Set.mem_iUnion.mp hx with ⟨_, hx⟩
  exact R.ambientEdge_subset X e edge hx

/-- Helper for Lemma 64.3: concatenating two injective paths whose ranges meet
only at their common endpoint preserves injectivity. -/
private lemma pathTrans_injective_of_range_inter_eq_singleton
    {Z : Type*} [TopologicalSpace Z] {a b c : Z}
    (gamma : Path a b) (delta : Path b c)
    (hgamma : Function.Injective gamma) (hdelta : Function.Injective delta)
    (hinter : Set.range gamma ∩ Set.range delta = {b}) :
    Function.Injective (gamma.trans delta) := by
  -- Equal values in the same half are handled by the corresponding arc.
  intro s t hst
  by_cases hs : (s : ℝ) ≤ 1 / 2
  · by_cases ht : (t : ℝ) ≤ 1 / 2
    · rw [Path.trans_apply, dif_pos hs, Path.trans_apply, dif_pos ht] at hst
      have huv := hgamma hst
      apply Subtype.ext
      have huvVal := congrArg Subtype.val huv
      norm_num at huvVal
      linarith
    · -- In opposite halves, the singleton intersection forces the right
      -- parameter to be the initial endpoint, contradicting its half.
      rw [Path.trans_apply, dif_pos hs, Path.trans_apply, dif_neg ht] at hst
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
    · -- The symmetric opposite-half case forces the left parameter to the
      -- midpoint, again contradicting its chosen half.
      rw [Path.trans_apply, dif_neg hs, Path.trans_apply, dif_pos ht] at hst
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

/-- Helper for Lemma 64.3: two embedded arcs meeting only at the terminal
endpoint of the first concatenate to an embedded arc with union range. -/
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

/-- Helper for Lemma 64.3: an incident realized vertex lies on its realized edge. -/
private lemma realizedVertex_mem_edgeSet {a b : Fin 4} (_hab : a ≠ b)
    (edge : (SimpleGraph.completeGraph (Fin 4)).edgeSet)
    (hedge : edge.1 = s(a, b)) :
    R.vertex a ∈ R.finiteLinearGraph.edgeSet (R.edgeEquiv edge) := by
  rw [R.finiteLinearGraph.edgeSet_def]
  have ha : a ∈ edge.1 := hedge ▸ Sym2.mem_mk_left a b
  rcases (R.incident_iff_endpoint edge a).mp ha with haZero | haOne
  · exact ⟨0, haZero.symm⟩
  · exact ⟨1, haOne.symm⟩

/-- Helper for Lemma 64.3: the parameter endpoints of a realized edge are the
realized vertices specified by its combinatorial endpoint pair. -/
private lemma realizedEdge_endpointPair {a b : Fin 4} (hab : a ≠ b)
    (edge : (SimpleGraph.completeGraph (Fin 4)).edgeSet)
    (hedge : edge.1 = s(a, b)) :
    ({R.finiteLinearGraph.edge (R.edgeEquiv edge) 0,
        R.finiteLinearGraph.edge (R.edgeEquiv edge) 1} : Set R.Carrier) =
      {R.vertex a, R.vertex b} := by
  have ha : a ∈ edge.1 := hedge ▸ Sym2.mem_mk_left a b
  have hb : b ∈ edge.1 := hedge ▸ Sym2.mem_mk_right a b
  have haEndpoint := (R.incident_iff_endpoint edge a).mp ha
  have hbEndpoint := (R.incident_iff_endpoint edge b).mp hb
  have hvertexNe : R.vertex a ≠ R.vertex b := R.vertex_injective.ne hab
  -- Distinctness forces the two vertices onto opposite parameter endpoints.
  rcases haEndpoint with haZero | haOne
  · rcases hbEndpoint with hbZero | hbOne
    · exact (hvertexNe (haZero.trans hbZero.symm)).elim
    · rw [haZero, hbOne]
  · rcases hbEndpoint with hbZero | hbOne
    · rw [haOne, hbZero, Set.pair_comm]
    · exact (hvertexNe (haOne.trans hbOne.symm)).elim

/-- Helper for Lemma 64.3: a realized edge admits either chosen orientation
after transporting it into the ambient two-sphere. -/
private lemma existsOrientedAmbientEdge (X : Set (StandardSphere 2))
    (e : R.Carrier ≃ₜ X) {a b : Fin 4} (hab : a ≠ b)
    (edge : (SimpleGraph.completeGraph (Fin 4)).edgeSet)
    (hedge : edge.1 = s(a, b)) :
    ∃ gamma : unitInterval → StandardSphere 2, Topology.IsEmbedding gamma ∧
      gamma 0 = e (R.vertex a) ∧ gamma 1 = e (R.vertex b) ∧
        Set.range gamma = R.ambientEdge X e edge := by
  let raw := R.finiteLinearGraph.edge (R.edgeEquiv edge)
  let ambientRaw : unitInterval → StandardSphere 2 := fun t ↦ e (raw t)
  have hrawEmbedding : Topology.IsEmbedding raw :=
    R.finiteLinearGraph.edgeEmbedding (R.edgeEquiv edge)
  have hambientEmbedding : Topology.IsEmbedding ambientRaw :=
    Topology.IsEmbedding.subtypeVal.comp (e.isEmbedding.comp hrawEmbedding)
  have ha : a ∈ edge.1 := hedge ▸ Sym2.mem_mk_left a b
  have hb : b ∈ edge.1 := hedge ▸ Sym2.mem_mk_right a b
  have haEndpoint := (R.incident_iff_endpoint edge a).mp ha
  have hbEndpoint := (R.incident_iff_endpoint edge b).mp hb
  have hvertexNe : R.vertex a ≠ R.vertex b := R.vertex_injective.ne hab
  have hrange : Set.range ambientRaw = R.ambientEdge X e edge := by
    rw [ambientEdge_eq_image_edgeSet R X e edge]
    unfold ambientRaw raw
    rw [R.finiteLinearGraph.edgeSet_def]
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨e (R.finiteLinearGraph.edge (R.edgeEquiv edge) t),
        ⟨R.finiteLinearGraph.edge (R.edgeEquiv edge) t,
          Set.mem_range_self t, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨_, ⟨t, rfl⟩, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
  -- The endpoint incidence alternatives determine whether to use the stored
  -- parameterization or reverse it by interval symmetry.
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

/-- Helper for Lemma 64.3: distinct ambient realized edges intersect exactly
in the intersection of their two transported endpoint pairs. -/
private lemma ambientEdge_inter_eq_endpointPairs
    (X : Set (StandardSphere 2)) (e : R.Carrier ≃ₜ X)
    {a b c d : Fin 4} (hab : a ≠ b) (hcd : c ≠ d)
    (edge₁ edge₂ : (SimpleGraph.completeGraph (Fin 4)).edgeSet)
    (hedge₁ : edge₁.1 = s(a, b)) (hedge₂ : edge₂.1 = s(c, d))
    (hne : edge₁ ≠ edge₂) :
    R.ambientEdge X e edge₁ ∩ R.ambientEdge X e edge₂ =
      ({(e (R.vertex a) : StandardSphere 2),
          (e (R.vertex b) : StandardSphere 2)} ∩
        {(e (R.vertex c) : StandardSphere 2),
          (e (R.vertex d) : StandardSphere 2)} :
          Set (StandardSphere 2)) := by
  have hedgeNe : R.edgeEquiv edge₁ ≠ R.edgeEquiv edge₂ :=
    R.edgeEquiv.injective.ne hne
  have hinterEndpoints :=
    R.finiteLinearGraph.inter_subset_endpoints hedgeNe
  have hfirstEndpoints := realizedEdge_endpointPair R hab edge₁ hedge₁
  have hsecondEndpoints := realizedEdge_endpointPair R hcd edge₂ hedge₂
  have hinjective : Function.Injective
      (fun x : R.Carrier ↦ (e x : StandardSphere 2)) :=
    Subtype.val_injective.comp e.injective
  rw [ambientEdge_eq_image_edgeSet R X e edge₁,
    ambientEdge_eq_image_edgeSet R X e edge₂]
  apply Set.Subset.antisymm
  · -- Pull a common ambient point back to a common point of the two intrinsic
    -- edges, then use the endpoint-intersection axiom.
    rintro y ⟨⟨_, ⟨x, hx₁, rfl⟩, rfl⟩, ⟨_, ⟨z, hz₂, rfl⟩, hxz⟩⟩
    have hzx : z = x := hinjective hxz
    have hxEndpoints := hinterEndpoints ⟨hx₁, hzx ▸ hz₂⟩
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
  · -- A point common to the endpoint pairs comes from one realized vertex on
    -- each edge, hence belongs to both ambient edge images.
    rintro y ⟨hyab, hycd⟩
    rcases hyab with hya | hyb
    · rcases hycd with hyc | hyd
      · exact ⟨⟨e (R.vertex a),
          ⟨R.vertex a, realizedVertex_mem_edgeSet R hab edge₁ hedge₁, rfl⟩,
            hya.symm⟩,
          ⟨e (R.vertex c),
            ⟨R.vertex c, realizedVertex_mem_edgeSet R hcd edge₂ hedge₂, rfl⟩,
              hyc.symm⟩⟩
      · have hyd' : y = (e (R.vertex d) : StandardSphere 2) :=
          Set.mem_singleton_iff.mp hyd
        have hdEdge₂ : R.vertex d ∈
            R.finiteLinearGraph.edgeSet (R.edgeEquiv edge₂) := by
          have hedgeSymm : edge₂.1 = s(d, c) := by
            rw [hedge₂, Sym2.eq_iff]
            exact Or.inr ⟨rfl, rfl⟩
          exact realizedVertex_mem_edgeSet R hcd.symm edge₂ hedgeSymm
        exact ⟨⟨e (R.vertex a),
          ⟨R.vertex a, realizedVertex_mem_edgeSet R hab edge₁ hedge₁, rfl⟩,
            hya.symm⟩,
          ⟨e (R.vertex d),
            ⟨R.vertex d, hdEdge₂, rfl⟩,
              hyd'.symm⟩⟩
    · rcases hycd with hyc | hyd
      · have hyb' : y = (e (R.vertex b) : StandardSphere 2) :=
          Set.mem_singleton_iff.mp hyb
        have hbEdge₁ : R.vertex b ∈
            R.finiteLinearGraph.edgeSet (R.edgeEquiv edge₁) := by
          have hedgeSymm : edge₁.1 = s(b, a) := by
            rw [hedge₁, Sym2.eq_iff]
            exact Or.inr ⟨rfl, rfl⟩
          exact realizedVertex_mem_edgeSet R hab.symm edge₁ hedgeSymm
        exact ⟨⟨e (R.vertex b), ⟨R.vertex b, hbEdge₁, rfl⟩, hyb'.symm⟩,
          ⟨e (R.vertex c),
            ⟨R.vertex c, realizedVertex_mem_edgeSet R hcd edge₂ hedge₂, rfl⟩,
              hyc.symm⟩⟩
      · have hyb' : y = (e (R.vertex b) : StandardSphere 2) :=
          Set.mem_singleton_iff.mp hyb
        have hyd' : y = (e (R.vertex d) : StandardSphere 2) :=
          Set.mem_singleton_iff.mp hyd
        have hbEdge₁ : R.vertex b ∈
            R.finiteLinearGraph.edgeSet (R.edgeEquiv edge₁) := by
          have hedgeSymm : edge₁.1 = s(b, a) := by
            rw [hedge₁, Sym2.eq_iff]
            exact Or.inr ⟨rfl, rfl⟩
          exact realizedVertex_mem_edgeSet R hab.symm edge₁ hedgeSymm
        have hdEdge₂ : R.vertex d ∈
            R.finiteLinearGraph.edgeSet (R.edgeEquiv edge₂) := by
          have hedgeSymm : edge₂.1 = s(d, c) := by
            rw [hedge₂, Sym2.eq_iff]
            exact Or.inr ⟨rfl, rfl⟩
          exact realizedVertex_mem_edgeSet R hcd.symm edge₂ hedgeSymm
        exact ⟨⟨e (R.vertex b), ⟨R.vertex b, hbEdge₁, rfl⟩, hyb'.symm⟩,
          ⟨e (R.vertex d), ⟨R.vertex d, hdEdge₂, rfl⟩, hyd'.symm⟩⟩

/-- Helper for Lemma 64.3: a component in a smaller set agrees with the
ambient component when the latter is already contained in the smaller set. -/
private lemma connectedComponentIn_eq_of_subset_component
    {Z : Type*} [TopologicalSpace Z] {E F : Set Z} {x : Z}
    (hEF : E ⊆ F) (hx : x ∈ E)
    (hcomponent : connectedComponentIn F x ⊆ E) :
    connectedComponentIn E x = connectedComponentIn F x := by
  apply Set.Subset.antisymm
  · -- The smaller-set component is connected in `F` and contains `x`.
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hx)
      ((connectedComponentIn_subset E x).trans hEF)
  · -- Conversely, the assumed containment makes the `F`-component connected
    -- inside `E`, so maximality gives the reverse inclusion.
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn (hEF hx)) hcomponent

/-- Helper for Lemma 64.3: equality of complementary-component classes gives
equality of their ambient connected components. -/
private lemma connectedComponentIn_eq_of_componentClass_eq
    {Z : Type*} [TopologicalSpace Z] {F : Set Z} (a b : F)
    (h : (a : ConnectedComponents F) = b) :
    connectedComponentIn F a = connectedComponentIn F b := by
  -- Express both ambient components as images of subtype components, then
  -- transport the quotient-class equality through the subtype inclusion.
  rw [connectedComponentIn_eq_image a.property,
    connectedComponentIn_eq_image b.property]
  exact congrArg (Set.image Subtype.val) (ConnectedComponents.coe_eq_coe.mp h)

/-- Helper for Lemma 64.3: equality of ambient complementary components gives
equality of their connected-component quotient classes. -/
private lemma connectedComponents_coe_eq_of_connectedComponentIn_eq
    {Z : Type*} [TopologicalSpace Z] {F : Set Z} (a b : F)
    (h : connectedComponentIn F a = connectedComponentIn F b) :
    (a : ConnectedComponents F) = b := by
  -- Membership of `a` in `b`'s ambient component lifts back to the subtype.
  have ha : (a : Z) ∈ connectedComponentIn F b :=
    h ▸ mem_connectedComponentIn a.property
  rw [connectedComponentIn_eq_image b.property] at ha
  obtain ⟨z, hz, hza⟩ := ha
  have hza' : z = a := Subtype.ext hza
  exact ConnectedComponents.coe_eq_coe'.mpr (hza' ▸ hz)

/-- Helper for Lemma 64.3: both endpoints of an embedded interval arc are
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
  -- Continuity carries the two one-sided interval limits to the arc range.
  rw [hinteriorRange]
  exact ⟨mem_closure_image ha.continuous.continuousAt hzeroClosure,
    mem_closure_image ha.continuous.continuousAt honeClosure⟩

/-- Helper for Lemma 64.3: two embedded spherical arcs meeting exactly at two
distinct common endpoints have a union with two complementary components. -/
private lemma embeddedArcPair_separatesIntoTwo
    (a b : unitInterval → StandardSphere 2)
    (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (p q : StandardSphere 2) (hpq : p ≠ q)
    (hinter : Set.range a ∩ Set.range b = {p, q}) :
    (Set.range a ∪ Set.range b).SeparatesInto 2 := by
  have haClosed : IsClosed (Set.range a) :=
    (isCompact_range ha.continuous).isClosed
  have hbClosed : IsClosed (Set.range b) :=
    (isCompact_range hb.continuous).isClosed
  have haConnected : IsConnected (Set.range a) :=
    isConnected_range ha.continuous
  have hbConnected : IsConnected (Set.range b) :=
    isConnected_range hb.continuous
  -- Local instance justification (canonical structure): an embedded interval
  -- range carries its canonical arc structure for `arc_not_separates`.
  letI : Topology.IsArc (Set.range a) := ⟨⟨ha.toHomeomorph.symm⟩⟩
  -- Local instance justification (canonical structure): the second embedded
  -- interval range likewise carries its canonical arc structure.
  letI : Topology.IsArc (Set.range b) := ⟨⟨hb.toHomeomorph.symm⟩⟩
  -- Theorem 63.5 supplies the global two-component invariant.
  exact union_separatesInto_two_of_inter_pair (Set.range a) (Set.range b)
    haClosed hbClosed haConnected hbConnected ⟨p, q, hpq, hinter⟩
    (arc_not_separates _) (arc_not_separates _)

/-- Helper for Lemma 64.3: three ambient embedded arcs with the theta incidence
pattern induce a theta presentation on their union. -/
private lemma existsThetaPresentationOnUnion
    {Z : Type*} [TopologicalSpace Z]
    (arc : Fin 3 → unitInterval → Z)
    (harc : ∀ i, Topology.IsEmbedding (arc i))
    (p q : Z) (hzero : ∀ i, arc i 0 = p) (hone : ∀ i, arc i 1 = q)
    (hinter : ∀ i j, i ≠ j →
      Set.range (arc i) ∩ Set.range (arc j) = {p, q}) :
    ∃ P : Topology.ThetaPresentation (⋃ i, Set.range (arc i)),
      ∀ i, P.ambientEdge i = Set.range (arc i) := by
  let carrier : Set Z := ⋃ i, Set.range (arc i)
  have harcMem (i : Fin 3) (t : unitInterval) : arc i t ∈ carrier := by
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_range_self t⟩
  have hpMem : p ∈ carrier := by
    exact Set.mem_iUnion.mpr ⟨0, ⟨0, hzero 0⟩⟩
  have hqMem : q ∈ carrier := by
    exact Set.mem_iUnion.mpr ⟨0, ⟨1, hone 0⟩⟩
  let p' : carrier := ⟨p, hpMem⟩
  let q' : carrier := ⟨q, hqMem⟩
  have hliftedContinuous (i : Fin 3) :
      Continuous (fun t ↦ (⟨arc i t, harcMem i t⟩ : carrier)) := by
    exact (harc i).continuous.subtype_mk (harcMem i)
  let lifted : Fin 3 → C(unitInterval, carrier) := fun i ↦
    ⟨fun t ↦ ⟨arc i t, harcMem i t⟩, hliftedContinuous i⟩
  have hliftedEmbedding (i : Fin 3) :
      Topology.IsEmbedding (lifted i) := by
    apply (Topology.IsEmbedding.of_comp_iff
      Topology.IsEmbedding.subtypeVal).mp
    change Topology.IsEmbedding (arc i)
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
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp x.property
      obtain ⟨t, ht⟩ := hi
      exact Set.mem_iUnion.mpr ⟨i, ⟨t, Subtype.ext ht⟩⟩
  have hliftedInter (i j : Fin 3) (hij : i ≠ j) :
      Set.range (lifted i) ∩ Set.range (lifted j) = {p', q'} := by
    ext x
    constructor
    · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
      have hxAmbient : (x : Z) ∈
          Set.range (arc i) ∩ Set.range (arc j) := by
        exact ⟨⟨s, congrArg Subtype.val hs⟩,
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
  let P : Topology.ThetaPresentation carrier :=
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
  -- The ambient edge of the lifted presentation forgets only the subtype proof.
  rw [P.ambientEdge_eq_range]
  rfl

/-- Helper for Lemma 64.3: a theta presentation has three indexed,
component-class-bijective complementary regions with the expected frontiers. -/
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
  have hfrontier₀Mem : P.ambientEdge 1 ∪ P.ambientEdge 2 ∈
      Set.range (fun x : (Yᶜ : Set (StandardSphere 2)) ↦
        frontier (connectedComponentIn Yᶜ x)) := by
    rw [hfrontierRange]
    exact Or.inr (Or.inl rfl)
  have hfrontier₁Mem : P.ambientEdge 0 ∪ P.ambientEdge 2 ∈
      Set.range (fun x : (Yᶜ : Set (StandardSphere 2)) ↦
        frontier (connectedComponentIn Yᶜ x)) := by
    rw [hfrontierRange]
    exact Or.inr (Or.inr rfl)
  obtain ⟨x₀, hfrontier₀⟩ := hfrontier₀Mem
  obtain ⟨x₁, hfrontier₁⟩ := hfrontier₁Mem
  change frontier (connectedComponentIn Yᶜ x₀) =
    P.ambientEdge 1 ∪ P.ambientEdge 2 at hfrontier₀
  change frontier (connectedComponentIn Yᶜ x₁) =
    P.ambientEdge 0 ∪ P.ambientEdge 2 at hfrontier₁
  obtain ⟨x₂, x₂Pair, hfrontier₂, hcomponentPair₂⟩ :=
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
  have hcomponent₀₁ : connectedComponentIn Yᶜ x₀ ≠
      connectedComponentIn Yᶜ x₁ := by
    intro heq
    have hfrontierEq := congrArg frontier heq
    rw [hfrontier₀, hfrontier₁] at hfrontierEq
    have hmid : (P.arc 1 t : StandardSphere 2) ∈
        P.ambientEdge 1 ∪ P.ambientEdge 2 := by
      left
      rw [P.ambientEdge_eq_range]
      exact Set.mem_range_self t
    rw [hfrontierEq] at hmid
    exact hmid.elim (hmidpointNotOther h10)
      (hmidpointNotOther h12)
  have hcomponent₀₂ : connectedComponentIn Yᶜ x₀ ≠
      connectedComponentIn Yᶜ x₂ := by
    intro heq
    have hfrontierEq := congrArg frontier heq
    rw [hfrontier₀, hfrontier₂] at hfrontierEq
    have hmid : (P.arc 2 t : StandardSphere 2) ∈
        P.ambientEdge 1 ∪ P.ambientEdge 2 := by
      right
      rw [P.ambientEdge_eq_range]
      exact Set.mem_range_self t
    rw [hfrontierEq] at hmid
    exact hmid.elim (hmidpointNotOther h20)
      (hmidpointNotOther h21)
  have hcomponent₁₂ : connectedComponentIn Yᶜ x₁ ≠
      connectedComponentIn Yᶜ x₂ := by
    intro heq
    have hfrontierEq := congrArg frontier heq
    rw [hfrontier₁, hfrontier₂] at hfrontierEq
    have hmid : (P.arc 2 t : StandardSphere 2) ∈
        P.ambientEdge 0 ∪ P.ambientEdge 2 := by
      right
      rw [P.ambientEdge_eq_range]
      exact Set.mem_range_self t
    rw [hfrontierEq] at hmid
    exact hmid.elim (hmidpointNotOther h20)
      (hmidpointNotOther h21)
  have hclass₀₁ : (x₀ : ConnectedComponents
      (Yᶜ : Set (StandardSphere 2))) ≠ x₁ := by
    intro h
    exact hcomponent₀₁
      (connectedComponentIn_eq_of_componentClass_eq x₀ x₁ h)
  have hclass₀₂ : (x₀ : ConnectedComponents
      (Yᶜ : Set (StandardSphere 2))) ≠ x₂ := by
    intro h
    exact hcomponent₀₂
      (connectedComponentIn_eq_of_componentClass_eq x₀ x₂ h)
  have hclass₁₂ : (x₁ : ConnectedComponents
      (Yᶜ : Set (StandardSphere 2))) ≠ x₂ := by
    intro h
    exact hcomponent₁₂
      (connectedComponentIn_eq_of_componentClass_eq x₁ x₂ h)
  let representative : Fin 3 → (Yᶜ : Set (StandardSphere 2)) :=
    ![x₀, x₁, x₂]
  let regionClass : Fin 3 →
      ConnectedComponents (Yᶜ : Set (StandardSphere 2)) :=
    fun i ↦ representative i
  have hregionInjective : Function.Injective regionClass := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · have hEq : (x₀ : ConnectedComponents
          (Yᶜ : Set (StandardSphere 2))) = x₁ := by
        simpa [regionClass, representative] using hij
      exact (hclass₀₁ hEq).elim
    · have hEq : (x₀ : ConnectedComponents
          (Yᶜ : Set (StandardSphere 2))) = x₂ := by
        simpa [regionClass, representative] using hij
      exact (hclass₀₂ hEq).elim
    · have hEq : (x₀ : ConnectedComponents
          (Yᶜ : Set (StandardSphere 2))) = x₁ := by
        simpa [regionClass, representative] using hij.symm
      exact (hclass₀₁ hEq).elim
    · rfl
    · have hEq : (x₁ : ConnectedComponents
          (Yᶜ : Set (StandardSphere 2))) = x₂ := by
        simpa [regionClass, representative] using hij
      exact (hclass₁₂ hEq).elim
    · have hEq : (x₀ : ConnectedComponents
          (Yᶜ : Set (StandardSphere 2))) = x₂ := by
        simpa [regionClass, representative] using hij.symm
      exact (hclass₀₂ hEq).elim
    · have hEq : (x₁ : ConnectedComponents
          (Yᶜ : Set (StandardSphere 2))) = x₂ := by
        simpa [regionClass, representative] using hij.symm
      exact (hclass₁₂ hEq).elim
    · rfl
  have hcard : Cardinal.mk (ConnectedComponents
      (Yᶜ : Set (StandardSphere 2))) = 3 :=
    Set.separatesInto_iff.mp
      (Topology.ThetaPresentation.separatesInto Y P)
  obtain ⟨classEquiv⟩ := Cardinal.mk_eq_nat_iff.mp hcard
  have hregionSurjective : Function.Surjective regionClass :=
    hregionInjective.surjective_of_finite classEquiv.symm
  have hx₂Pair : (x₂ : StandardSphere 2) ∈
      (P.ambientEdge 0 ∪ P.ambientEdge 1)ᶜ := by
    intro hx
    rcases hx with hx₀ | hx₁
    · exact x₂.property (P.ambientEdge_subset 0 hx₀)
    · exact x₂.property (P.ambientEdge_subset 1 hx₁)
  have hx₂InPairComponent : (x₂ : StandardSphere 2) ∈
      connectedComponentIn (P.ambientEdge 0 ∪ P.ambientEdge 1)ᶜ x₂Pair := by
    rw [← hcomponentPair₂]
    exact mem_connectedComponentIn x₂.property
  have hcomponentPair₂Self : connectedComponentIn Yᶜ x₂ =
      connectedComponentIn (P.ambientEdge 0 ∪ P.ambientEdge 1)ᶜ x₂ := by
    exact hcomponentPair₂.trans (connectedComponentIn_eq hx₂InPairComponent)
  refine ⟨representative, ⟨hregionInjective, hregionSurjective⟩, ?_, ?_, ?_, ?_⟩
  · simpa [representative] using hfrontier₀
  · simpa [representative] using hfrontier₁
  · simpa [representative] using hfrontier₂
  · simpa [representative] using hcomponentPair₂Self

/-- Helper for Lemma 64.3: in a set with exactly two components, two known
distinct components classify every point of the set. -/
private lemma connectedComponentIn_eq_or_eq_of_mk_eq_two
    {Z : Type*} [TopologicalSpace Z] (F : Set Z)
    (hcard : Cardinal.mk (ConnectedComponents F) = 2)
    {x x₀ x₁ : Z} (hx : x ∈ F) (hx₀ : x₀ ∈ F) (hx₁ : x₁ ∈ F)
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
  obtain ⟨other, -, hunique⟩ :=
    (Cardinal.mk_eq_two_iff' (ConnectedComponents.mk x₀F)).mp hcard
  have hclass₁ : (x₁F : ConnectedComponents F) = other :=
    hunique x₁F hclass₁ne
  have componentEq {a b : Z} (ha : a ∈ F) (hb : b ∈ F)
      (hab : ((⟨a, ha⟩ : F) : ConnectedComponents F) =
        ((⟨b, hb⟩ : F) : ConnectedComponents F)) :
      connectedComponentIn F a = connectedComponentIn F b := by
    rw [connectedComponentIn_eq_image ha, connectedComponentIn_eq_image hb]
    exact congrArg (Set.image Subtype.val)
      (ConnectedComponents.coe_eq_coe.mp hab)
  by_cases hclass : (xF : ConnectedComponents F) = x₀F
  · exact Or.inl (componentEq hx hx₀ hclass)
  · right
    have hxOther : (xF : ConnectedComponents F) = other :=
      hunique xF hclass
    exact componentEq hx hx₁ (hxOther.trans hclass₁.symm)

/-- Helper for Lemma 64.3: an injective map transports the intersection of two
unordered endpoint pairs to the intersection of their images. -/
private lemma imagePair_inter_imagePair
    {A B : Type*} (f : A → B) (hf : Function.Injective f)
    (a b c d : A) :
    ({f a, f b} ∩ {f c, f d} : Set B) =
      f '' ({a, b} ∩ {c, d} : Set A) := by
  -- Injectivity lets image commute with intersection, after expanding pairs.
  rw [← Set.image_pair, ← Set.image_pair, ← Set.image_inter hf]

/-- Helper for Lemma 64.3: a singleton intersection of combinatorial endpoint
pairs gives the corresponding singleton intersection of ambient realized edges. -/
private lemma ambientEdge_inter_eq_singleton_of_endpointPair_inter
    (X : Set (StandardSphere 2)) (e : R.Carrier ≃ₜ X)
    {a b c d v : Fin 4} (hab : a ≠ b) (hcd : c ≠ d)
    (edge₁ edge₂ : (SimpleGraph.completeGraph (Fin 4)).edgeSet)
    (hedge₁ : edge₁.1 = s(a, b)) (hedge₂ : edge₂.1 = s(c, d))
    (hne : edge₁ ≠ edge₂)
    (hpairs : ({a, b} ∩ {c, d} : Set (Fin 4)) = {v}) :
    R.ambientEdge X e edge₁ ∩ R.ambientEdge X e edge₂ =
      {(e (R.vertex v) : StandardSphere 2)} := by
  have hinjective : Function.Injective
      (fun i : Fin 4 ↦ (e (R.vertex i) : StandardSphere 2)) :=
    Subtype.val_injective.comp (e.injective.comp R.vertex_injective)
  -- First expose endpoint pairs, then transport their prescribed intersection.
  rw [ambientEdge_inter_eq_endpointPairs R X e hab hcd edge₁ edge₂
    hedge₁ hedge₂ hne, imagePair_inter_imagePair _ hinjective, hpairs,
    Set.image_singleton]

/-- Helper for Lemma 64.3: disjoint combinatorial endpoint pairs give disjoint
ambient realized edges. -/
private lemma ambientEdge_inter_eq_empty_of_endpointPair_disjoint
    (X : Set (StandardSphere 2)) (e : R.Carrier ≃ₜ X)
    {a b c d : Fin 4} (hab : a ≠ b) (hcd : c ≠ d)
    (edge₁ edge₂ : (SimpleGraph.completeGraph (Fin 4)).edgeSet)
    (hedge₁ : edge₁.1 = s(a, b)) (hedge₂ : edge₂.1 = s(c, d))
    (hne : edge₁ ≠ edge₂)
    (hpairs : ({a, b} ∩ {c, d} : Set (Fin 4)) = ∅) :
    R.ambientEdge X e edge₁ ∩ R.ambientEdge X e edge₂ = ∅ := by
  have hinjective : Function.Injective
      (fun i : Fin 4 ↦ (e (R.vertex i) : StandardSphere 2)) :=
    Subtype.val_injective.comp (e.injective.comp R.vertex_injective)
  -- The same endpoint normal form reduces disjointness to the finite pair fact.
  rw [ambientEdge_inter_eq_endpointPairs R X e hab hcd edge₁ edge₂
    hedge₁ hedge₂ hne, imagePair_inter_imagePair _ hinjective, hpairs,
    Set.image_empty]

/-- Helper for Lemma 64.3: the ambient realized edges cover the ambient copy of
the entire finite linear graph. -/
private lemma iUnion_ambientEdge_eq
    (X : Set (StandardSphere 2)) (e : R.Carrier ≃ₜ X) :
    ⋃ edge, R.ambientEdge X e edge = X := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset (fun edge ↦ R.ambientEdge_subset X e edge)
  · intro y hy
    let x : R.Carrier := e.symm ⟨y, hy⟩
    have hxAll : x ∈ ⋃ edge, R.finiteLinearGraph.edgeSet edge := by
      rw [R.finiteLinearGraph.iUnion_edgeSet]
      exact Set.mem_univ x
    obtain ⟨edgeIndex, hxEdge⟩ := Set.mem_iUnion.mp hxAll
    let edge : (SimpleGraph.completeGraph (Fin 4)).edgeSet :=
      R.edgeEquiv.symm edgeIndex
    have hxChosen : x ∈ R.finiteLinearGraph.edgeSet (R.edgeEquiv edge) := by
      simpa only [edge, Equiv.apply_symm_apply] using hxEdge
    apply Set.mem_iUnion.mpr
    refine ⟨edge, ?_⟩
    rw [ambientEdge_eq_image_edgeSet R X e edge]
    exact ⟨e x, ⟨x, hxChosen, rfl⟩,
      congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)⟩

/-- Helper for Lemma 64.3: the six canonical edges of the complete graph on
four vertices cover its ambient realization. -/
private lemma sixAmbientEdges_eq
    (X : Set (StandardSphere 2)) (e : R.Carrier ≃ₜ X) :
    (((R.ambientEdge X e ⟨s(0, 1), of_decide_eq_true rfl⟩ ∪
        R.ambientEdge X e ⟨s(1, 2), of_decide_eq_true rfl⟩) ∪
      (R.ambientEdge X e ⟨s(0, 3), of_decide_eq_true rfl⟩ ∪
        R.ambientEdge X e ⟨s(3, 2), of_decide_eq_true rfl⟩)) ∪
      R.ambientEdge X e ⟨s(0, 2), of_decide_eq_true rfl⟩) ∪
      R.ambientEdge X e ⟨s(1, 3), of_decide_eq_true rfl⟩ = X := by
  -- Enumerate only the finite edge index; all ambient geometry is handled by
  -- the previously proved full-union equation.
  have hcover := iUnion_ambientEdge_eq R X e
  ext y
  constructor
  · intro hy
    rcases hy with h | hy13
    · rcases h with h | hy02
      · rcases h with h | h
        · rcases h with hy01 | hy12
          · exact R.ambientEdge_subset X e _ hy01
          · exact R.ambientEdge_subset X e _ hy12
        · rcases h with hy03 | hy32
          · exact R.ambientEdge_subset X e _ hy03
          · exact R.ambientEdge_subset X e _ hy32
      · exact R.ambientEdge_subset X e _ hy02
    · exact R.ambientEdge_subset X e _ hy13
  · intro hy
    have hyUnion : y ∈ ⋃ edge, R.ambientEdge X e edge := hcover.symm ▸ hy
    obtain ⟨edge, hedge⟩ := Set.mem_iUnion.mp hyUnion
    fin_cases edge
    · exact Or.inl (Or.inl (Or.inl (Or.inl hedge)))
    · exact Or.inl (Or.inr hedge)
    · exact Or.inl (Or.inl (Or.inr (Or.inl hedge)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr hedge)))
    · exact Or.inr hedge
    · have hedgeIndex :
          (⟨s((2 : Fin 4), 3), of_decide_eq_true rfl⟩ :
            (SimpleGraph.completeGraph (Fin 4)).edgeSet) =
            ⟨s(3, 2), of_decide_eq_true rfl⟩ := by
        apply Subtype.ext
        rw [Sym2.eq_iff]
        exact Or.inr ⟨rfl, rfl⟩
      have hedge' : y ∈
          R.ambientEdge X e ⟨s(3, 2), of_decide_eq_true rfl⟩ := by
        rw [← hedgeIndex]
        exact hedge
      exact Or.inl (Or.inl (Or.inr (Or.inr hedge')))

/-- Helper for Lemma 64.3: the triangle opposite vertex zero consists of the
three edges among vertices one, two, and three. -/
private lemma oppositeBoundary_zero_eq
    (X : Set (StandardSphere 2)) (e : R.Carrier ≃ₜ X) :
    R.oppositeBoundary X e 0 =
      (R.ambientEdge X e ⟨s(1, 2), of_decide_eq_true rfl⟩ ∪
        R.ambientEdge X e ⟨s(2, 3), of_decide_eq_true rfl⟩) ∪
        R.ambientEdge X e ⟨s(1, 3), of_decide_eq_true rfl⟩ := by
  -- Enumerating the six edges leaves exactly the three not incident to zero.
  unfold oppositeBoundary
  ext x
  constructor
  · intro hx
    obtain ⟨edge, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hi, hx⟩ := Set.mem_iUnion.mp hx
    fin_cases edge
    · simp at hi
    · simp at hi
    · simp at hi
    · exact Or.inl (Or.inl hx)
    · exact Or.inr hx
    · exact Or.inl (Or.inr hx)
  · rintro ((hx | hx) | hx)
    · exact Set.mem_iUnion.mpr ⟨⟨s(1, 2), of_decide_eq_true rfl⟩,
        Set.mem_iUnion.mpr ⟨by simp, hx⟩⟩
    · exact Set.mem_iUnion.mpr ⟨⟨s(2, 3), of_decide_eq_true rfl⟩,
        Set.mem_iUnion.mpr ⟨by simp, hx⟩⟩
    · exact Set.mem_iUnion.mpr ⟨⟨s(1, 3), of_decide_eq_true rfl⟩,
        Set.mem_iUnion.mpr ⟨by simp, hx⟩⟩

/-- Helper for Lemma 64.3: the triangle opposite vertex one consists of the
three edges among vertices zero, two, and three. -/
private lemma oppositeBoundary_one_eq
    (X : Set (StandardSphere 2)) (e : R.Carrier ≃ₜ X) :
    R.oppositeBoundary X e 1 =
      (R.ambientEdge X e ⟨s(0, 2), of_decide_eq_true rfl⟩ ∪
        R.ambientEdge X e ⟨s(0, 3), of_decide_eq_true rfl⟩) ∪
        R.ambientEdge X e ⟨s(2, 3), of_decide_eq_true rfl⟩ := by
  -- Enumerating the six edges leaves exactly the three not incident to one.
  unfold oppositeBoundary
  ext x
  constructor
  · intro hx
    obtain ⟨edge, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hi, hx⟩ := Set.mem_iUnion.mp hx
    fin_cases edge
    · simp at hi
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr hx)
    · simp at hi
    · simp at hi
    · exact Or.inr hx
  · rintro ((hx | hx) | hx)
    · exact Set.mem_iUnion.mpr ⟨⟨s(0, 2), of_decide_eq_true rfl⟩,
        Set.mem_iUnion.mpr ⟨by simp, hx⟩⟩
    · exact Set.mem_iUnion.mpr ⟨⟨s(0, 3), of_decide_eq_true rfl⟩,
        Set.mem_iUnion.mpr ⟨by simp, hx⟩⟩
    · exact Set.mem_iUnion.mpr ⟨⟨s(2, 3), of_decide_eq_true rfl⟩,
        Set.mem_iUnion.mpr ⟨by simp, hx⟩⟩

/-- Helper for Lemma 64.3: the triangle opposite vertex two consists of the
three edges among vertices zero, one, and three. -/
private lemma oppositeBoundary_two_eq
    (X : Set (StandardSphere 2)) (e : R.Carrier ≃ₜ X) :
    R.oppositeBoundary X e 2 =
      (R.ambientEdge X e ⟨s(0, 1), of_decide_eq_true rfl⟩ ∪
        R.ambientEdge X e ⟨s(0, 3), of_decide_eq_true rfl⟩) ∪
        R.ambientEdge X e ⟨s(1, 3), of_decide_eq_true rfl⟩ := by
  -- Enumerating the six edges leaves exactly the three not incident to two.
  unfold oppositeBoundary
  ext x
  constructor
  · intro hx
    obtain ⟨edge, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hi, hx⟩ := Set.mem_iUnion.mp hx
    fin_cases edge
    · exact Or.inl (Or.inl hx)
    · simp at hi
    · exact Or.inl (Or.inr hx)
    · simp at hi
    · exact Or.inr hx
    · simp at hi
  · rintro ((hx | hx) | hx)
    · exact Set.mem_iUnion.mpr ⟨⟨s(0, 1), of_decide_eq_true rfl⟩,
        Set.mem_iUnion.mpr ⟨by simp, hx⟩⟩
    · exact Set.mem_iUnion.mpr ⟨⟨s(0, 3), of_decide_eq_true rfl⟩,
        Set.mem_iUnion.mpr ⟨by simp, hx⟩⟩
    · exact Set.mem_iUnion.mpr ⟨⟨s(1, 3), of_decide_eq_true rfl⟩,
        Set.mem_iUnion.mpr ⟨by simp, hx⟩⟩

/-- Helper for Lemma 64.3: the triangle opposite vertex three consists of the
three edges among vertices zero, one, and two. -/
private lemma oppositeBoundary_three_eq
    (X : Set (StandardSphere 2)) (e : R.Carrier ≃ₜ X) :
    R.oppositeBoundary X e 3 =
      (R.ambientEdge X e ⟨s(0, 1), of_decide_eq_true rfl⟩ ∪
        R.ambientEdge X e ⟨s(0, 2), of_decide_eq_true rfl⟩) ∪
        R.ambientEdge X e ⟨s(1, 2), of_decide_eq_true rfl⟩ := by
  -- Enumerating the six edges leaves exactly the three not incident to three.
  unfold oppositeBoundary
  ext x
  constructor
  · intro hx
    obtain ⟨edge, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hi, hx⟩ := Set.mem_iUnion.mp hx
    fin_cases edge
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr hx)
    · simp at hi
    · exact Or.inr hx
    · simp at hi
    · simp at hi
  · rintro ((hx | hx) | hx)
    · exact Set.mem_iUnion.mpr ⟨⟨s(0, 1), of_decide_eq_true rfl⟩,
        Set.mem_iUnion.mpr ⟨by simp, hx⟩⟩
    · exact Set.mem_iUnion.mpr ⟨⟨s(0, 2), of_decide_eq_true rfl⟩,
        Set.mem_iUnion.mpr ⟨by simp, hx⟩⟩
    · exact Set.mem_iUnion.mpr ⟨⟨s(1, 2), of_decide_eq_true rfl⟩,
        Set.mem_iUnion.mpr ⟨by simp, hx⟩⟩

/-- Helper for Lemma 64.3: regrouping four sets can exchange the two middle
terms without changing their union. -/
private lemma union_pairs_exchange {Z : Type*} (A B C D : Set Z) :
    (A ∪ B) ∪ (C ∪ D) = (A ∪ C) ∪ (B ∪ D) := by
  -- Membership on both sides is the same four-way disjunction.
  ext x
  simp only [Set.mem_union]
  tauto

/-- Helper for Lemma 64.3: a three-set union is unchanged by a cyclic
permutation of its terms. -/
private lemma union_three_rotate {Z : Type*} (A B C : Set Z) :
    (A ∪ B) ∪ C = (C ∪ A) ∪ B := by
  -- Both sides express membership in one of the same three sets.
  ext x
  simp only [Set.mem_union]
  tauto

/-- Helper for Lemma 64.3: a three-set union is unchanged by exchanging its
last two terms. -/
private lemma union_three_swap_last {Z : Type*} (A B C : Set Z) :
    (A ∪ B) ∪ C = (A ∪ C) ∪ B := by
  -- Both sides express membership in one of the same three sets.
  ext x
  simp only [Set.mem_union]
  tauto

/-- Helper for Lemma 64.3: four pairwise distinct values define an injective
map from `Fin 4` in their displayed order. -/
private lemma finFourVector_injective {Z : Type*} (a b c d : Z)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective ![a, b, c, d] := by
  -- Finite case analysis reduces injectivity to the six supplied inequalities.
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact (hab hij).elim
  · exact (hac hij).elim
  · exact (had hij).elim
  · exact (hab hij.symm).elim
  · rfl
  · exact (hbc hij).elim
  · exact (hbd hij).elim
  · exact (hac hij.symm).elim
  · exact (hbc hij.symm).elim
  · rfl
  · exact (hcd hij).elim
  · exact (had hij.symm).elim
  · exact (hbd hij.symm).elim
  · exact (hcd hij.symm).elim
  · rfl

/-- Helper for Lemma 64.3: the four complementary regions are represented by
the vertices opposite their frontier triangles. -/
private lemma existsFourComplementaryRegions
    (X : Set (StandardSphere 2)) (e : R.Carrier ≃ₜ X) :
    ∃ representative : Fin 4 → (Xᶜ : Set (StandardSphere 2)),
      Function.Bijective (fun i ↦
        (representative i : ConnectedComponents
          (Xᶜ : Set (StandardSphere 2)))) ∧
      ∀ i, frontier (connectedComponentIn Xᶜ (representative i)) =
        R.oppositeBoundary X e i := by
  classical
  -- Route correction: use the owner computation theorem for `ambientEdge`,
  -- then follow the source's theta and its symmetric dual.
  have h01Adj : (SimpleGraph.completeGraph (Fin 4)).Adj 0 1 := by simp
  have h12Adj : (SimpleGraph.completeGraph (Fin 4)).Adj 1 2 := by simp
  have h02Adj : (SimpleGraph.completeGraph (Fin 4)).Adj 0 2 := by simp
  have h03Adj : (SimpleGraph.completeGraph (Fin 4)).Adj 0 3 := by simp
  have h32Adj : (SimpleGraph.completeGraph (Fin 4)).Adj 3 2 := by simp
  have h13Adj : (SimpleGraph.completeGraph (Fin 4)).Adj 1 3 := by simp
  let e01 : (SimpleGraph.completeGraph (Fin 4)).edgeSet :=
    ⟨s(0, 1), h01Adj⟩
  let e12 : (SimpleGraph.completeGraph (Fin 4)).edgeSet :=
    ⟨s(1, 2), h12Adj⟩
  let e02 : (SimpleGraph.completeGraph (Fin 4)).edgeSet :=
    ⟨s(0, 2), h02Adj⟩
  let e03 : (SimpleGraph.completeGraph (Fin 4)).edgeSet :=
    ⟨s(0, 3), h03Adj⟩
  let e32 : (SimpleGraph.completeGraph (Fin 4)).edgeSet :=
    ⟨s(3, 2), h32Adj⟩
  let e13 : (SimpleGraph.completeGraph (Fin 4)).edgeSet :=
    ⟨s(1, 3), h13Adj⟩
  obtain ⟨a01, ha01Embedding, ha01Zero, ha01One, ha01Range⟩ :=
    existsOrientedAmbientEdge R X e (by decide) e01 rfl
  obtain ⟨a12, ha12Embedding, ha12Zero, ha12One, ha12Range⟩ :=
    existsOrientedAmbientEdge R X e (by decide) e12 rfl
  obtain ⟨a02, ha02Embedding, ha02Zero, ha02One, ha02Range⟩ :=
    existsOrientedAmbientEdge R X e (by decide) e02 rfl
  obtain ⟨a03, ha03Embedding, ha03Zero, ha03One, ha03Range⟩ :=
    existsOrientedAmbientEdge R X e (by decide) e03 rfl
  obtain ⟨a32, ha32Embedding, ha32Zero, ha32One, ha32Range⟩ :=
    existsOrientedAmbientEdge R X e (by decide) e32 rfl
  obtain ⟨a13, ha13Embedding, ha13Zero, ha13One, ha13Range⟩ :=
    existsOrientedAmbientEdge R X e (by decide) e13 rfl
  obtain ⟨a10, ha10Embedding, ha10Zero, ha10One, ha10Range⟩ :=
    existsOrientedAmbientEdge R X e
      (a := (1 : Fin 4)) (b := 0) (by decide) e01 (by
        change s((0 : Fin 4), 1) = s(1, 0)
        rw [Sym2.eq_iff]
        exact Or.inr ⟨rfl, rfl⟩)
  obtain ⟨a23, ha23Embedding, ha23Zero, ha23One, ha23Range⟩ :=
    existsOrientedAmbientEdge R X e
      (a := (2 : Fin 4)) (b := 3) (by decide) e32 (by
        change s((3 : Fin 4), 2) = s(2, 3)
        rw [Sym2.eq_iff]
        exact Or.inr ⟨rfl, rfl⟩)
  -- Primitive incidences control both concatenations.
  have h01_12 : Set.range a01 ∩ Set.range a12 =
      {(e (R.vertex (1 : Fin 4)) : StandardSphere 2)} := by
    rw [ha01Range, ha12Range]
    apply ambientEdge_inter_eq_singleton_of_endpointPair_inter R X e
      (by decide) (by decide) e01 e12 rfl rfl
    · intro h
      have hval := congrArg Subtype.val h
      simp [e01, e12] at hval
    · ext i
      fin_cases i <;> simp
  have h03_32 : Set.range a03 ∩ Set.range a32 =
      {(e (R.vertex (3 : Fin 4)) : StandardSphere 2)} := by
    rw [ha03Range, ha32Range]
    apply ambientEdge_inter_eq_singleton_of_endpointPair_inter R X e
      (by decide) (by decide) e03 e32 rfl rfl
    · intro h
      have hval := congrArg Subtype.val h
      simp [e03, e32] at hval
    · ext i
      fin_cases i <;> simp
  have h10_03 : Set.range a10 ∩ Set.range a03 =
      {(e (R.vertex (0 : Fin 4)) : StandardSphere 2)} := by
    rw [ha10Range, ha03Range]
    apply ambientEdge_inter_eq_singleton_of_endpointPair_inter R X e
      (by decide) (by decide) e01 e03 rfl rfl
    · intro h
      have hval := congrArg Subtype.val h
      simp [e01, e03] at hval
    · ext i
      fin_cases i <;> simp
  have h12_23 : Set.range a12 ∩ Set.range a23 =
      {(e (R.vertex (2 : Fin 4)) : StandardSphere 2)} := by
    rw [ha12Range, ha23Range]
    apply ambientEdge_inter_eq_singleton_of_endpointPair_inter R X e
      (a := (1 : Fin 4)) (b := 2) (c := 2) (d := 3) (v := 2)
      (by decide) (by decide) e12 e32 rfl
      (by
        change s((3 : Fin 4), 2) = s(2, 3)
        rw [Sym2.eq_iff]
        exact Or.inr ⟨rfl, rfl⟩)
    · intro h
      have hval := congrArg Subtype.val h
      simp [e12, e32] at hval
    · ext i
      fin_cases i <;> simp
  have h01_03 : Set.range a01 ∩ Set.range a03 =
      {(e (R.vertex (0 : Fin 4)) : StandardSphere 2)} := by
    rw [ha01Range, ha03Range]
    apply ambientEdge_inter_eq_singleton_of_endpointPair_inter R X e
      (by decide) (by decide) e01 e03 rfl rfl
    · intro h
      have hval := congrArg Subtype.val h
      simp [e01, e03] at hval
    · ext i
      fin_cases i <;> simp
  have h12_32 : Set.range a12 ∩ Set.range a32 =
      {(e (R.vertex (2 : Fin 4)) : StandardSphere 2)} := by
    rw [ha12Range, ha32Range]
    apply ambientEdge_inter_eq_singleton_of_endpointPair_inter R X e
      (by decide) (by decide) e12 e32 rfl rfl
    · intro h
      have hval := congrArg Subtype.val h
      simp [e12, e32] at hval
    · ext i
      fin_cases i <;> simp
  have h01_32 : Set.range a01 ∩ Set.range a32 = ∅ := by
    rw [ha01Range, ha32Range]
    apply ambientEdge_inter_eq_empty_of_endpointPair_disjoint R X e
      (by decide) (by decide) e01 e32 rfl rfl
    · intro h
      have hval := congrArg Subtype.val h
      simp [e01, e32] at hval
    · ext i
      fin_cases i <;> simp
  have h12_03 : Set.range a12 ∩ Set.range a03 = ∅ := by
    rw [ha12Range, ha03Range]
    apply ambientEdge_inter_eq_empty_of_endpointPair_disjoint R X e
      (by decide) (by decide) e12 e03 rfl rfl
    · intro h
      have hval := congrArg Subtype.val h
      simp [e12, e03] at hval
    · ext i
      fin_cases i <;> simp
  have h02_01 : Set.range a02 ∩ Set.range a01 =
      {(e (R.vertex (0 : Fin 4)) : StandardSphere 2)} := by
    rw [ha02Range, ha01Range]
    apply ambientEdge_inter_eq_singleton_of_endpointPair_inter R X e
      (by decide) (by decide) e02 e01 rfl rfl
    · intro h
      have hval := congrArg Subtype.val h
      simp [e02, e01] at hval
    · ext i
      fin_cases i <;> simp
  have h02_12 : Set.range a02 ∩ Set.range a12 =
      {(e (R.vertex (2 : Fin 4)) : StandardSphere 2)} := by
    rw [ha02Range, ha12Range]
    apply ambientEdge_inter_eq_singleton_of_endpointPair_inter R X e
      (by decide) (by decide) e02 e12 rfl rfl
    · intro h
      have hval := congrArg Subtype.val h
      simp [e02, e12] at hval
    · ext i
      fin_cases i <;> simp
  have h02_03 : Set.range a02 ∩ Set.range a03 =
      {(e (R.vertex (0 : Fin 4)) : StandardSphere 2)} := by
    rw [ha02Range, ha03Range]
    apply ambientEdge_inter_eq_singleton_of_endpointPair_inter R X e
      (by decide) (by decide) e02 e03 rfl rfl
    · intro h
      have hval := congrArg Subtype.val h
      simp [e02, e03] at hval
    · ext i
      fin_cases i <;> simp
  have h02_32 : Set.range a02 ∩ Set.range a32 =
      {(e (R.vertex (2 : Fin 4)) : StandardSphere 2)} := by
    rw [ha02Range, ha32Range]
    apply ambientEdge_inter_eq_singleton_of_endpointPair_inter R X e
      (by decide) (by decide) e02 e32 rfl rfl
    · intro h
      have hval := congrArg Subtype.val h
      simp [e02, e32] at hval
    · ext i
      fin_cases i <;> simp
  have h13_01 : Set.range a13 ∩ Set.range a01 =
      {(e (R.vertex (1 : Fin 4)) : StandardSphere 2)} := by
    rw [ha13Range, ha01Range]
    apply ambientEdge_inter_eq_singleton_of_endpointPair_inter R X e
      (by decide) (by decide) e13 e01 rfl rfl
    · intro h
      have hval := congrArg Subtype.val h
      simp [e13, e01] at hval
    · ext i
      fin_cases i <;> simp
  have h13_12 : Set.range a13 ∩ Set.range a12 =
      {(e (R.vertex (1 : Fin 4)) : StandardSphere 2)} := by
    rw [ha13Range, ha12Range]
    apply ambientEdge_inter_eq_singleton_of_endpointPair_inter R X e
      (by decide) (by decide) e13 e12 rfl rfl
    · intro h
      have hval := congrArg Subtype.val h
      simp [e13, e12] at hval
    · ext i
      fin_cases i <;> simp
  have h13_03 : Set.range a13 ∩ Set.range a03 =
      {(e (R.vertex (3 : Fin 4)) : StandardSphere 2)} := by
    rw [ha13Range, ha03Range]
    apply ambientEdge_inter_eq_singleton_of_endpointPair_inter R X e
      (by decide) (by decide) e13 e03 rfl rfl
    · intro h
      have hval := congrArg Subtype.val h
      simp [e13, e03] at hval
    · ext i
      fin_cases i <;> simp
  have h13_32 : Set.range a13 ∩ Set.range a32 =
      {(e (R.vertex (3 : Fin 4)) : StandardSphere 2)} := by
    rw [ha13Range, ha32Range]
    apply ambientEdge_inter_eq_singleton_of_endpointPair_inter R X e
      (by decide) (by decide) e13 e32 rfl rfl
    · intro h
      have hval := congrArg Subtype.val h
      simp [e13, e32] at hval
    · ext i
      fin_cases i <;> simp
  have h02_13 : Set.range a02 ∩ Set.range a13 = ∅ := by
    rw [ha02Range, ha13Range]
    apply ambientEdge_inter_eq_empty_of_endpointPair_disjoint R X e
      (by decide) (by decide) e02 e13 rfl rfl
    · intro h
      have hval := congrArg Subtype.val h
      simp [e02, e13] at hval
    · ext i
      fin_cases i <;> simp
  obtain ⟨arm012, harm012Embedding, harm012Zero, harm012One,
      harm012Range⟩ :=
    existsEmbeddedArcWithRangeUnion a01 a12 ha01Embedding ha12Embedding
      (ha01One.trans ha12Zero.symm) (by rw [ha01One]; exact h01_12)
  obtain ⟨arm032, harm032Embedding, harm032Zero, harm032One,
      harm032Range⟩ :=
    existsEmbeddedArcWithRangeUnion a03 a32 ha03Embedding ha32Embedding
      (ha03One.trans ha32Zero.symm) (by rw [ha03One]; exact h03_32)
  obtain ⟨arm103, harm103Embedding, harm103Zero, harm103One,
      harm103Range⟩ :=
    existsEmbeddedArcWithRangeUnion a10 a03 ha10Embedding ha03Embedding
      (ha10One.trans ha03Zero.symm) (by rw [ha10One]; exact h10_03)
  obtain ⟨arm123, harm123Embedding, harm123Zero, harm123One,
      harm123Range⟩ :=
    existsEmbeddedArcWithRangeUnion a12 a23 ha12Embedding ha23Embedding
      (ha12One.trans ha23Zero.symm) (by rw [ha12One]; exact h12_23)
  let first : Fin 3 → unitInterval → StandardSphere 2 :=
    ![arm012, arm032, a02]
  let dual : Fin 3 → unitInterval → StandardSphere 2 :=
    ![arm103, arm123, a13]
  let p : StandardSphere 2 := e (R.vertex 0)
  let q : StandardSphere 2 := e (R.vertex 2)
  let r : StandardSphere 2 := e (R.vertex 1)
  let s : StandardSphere 2 := e (R.vertex 3)
  have hfirstEmbedding (i : Fin 3) : Topology.IsEmbedding (first i) := by
    fin_cases i
    · exact harm012Embedding
    · exact harm032Embedding
    · exact ha02Embedding
  have hdualEmbedding (i : Fin 3) : Topology.IsEmbedding (dual i) := by
    fin_cases i
    · exact harm103Embedding
    · exact harm123Embedding
    · exact ha13Embedding
  have hfirstZero (i : Fin 3) : first i 0 = p := by
    fin_cases i
    · exact harm012Zero.trans ha01Zero
    · exact harm032Zero.trans ha03Zero
    · exact ha02Zero
  have hfirstOne (i : Fin 3) : first i 1 = q := by
    fin_cases i
    · exact harm012One.trans ha12One
    · exact harm032One.trans ha32One
    · exact ha02One
  have hdualZero (i : Fin 3) : dual i 0 = r := by
    fin_cases i
    · exact harm103Zero.trans ha10Zero
    · exact harm123Zero.trans ha12Zero
    · exact ha13Zero
  have hdualOne (i : Fin 3) : dual i 1 = s := by
    fin_cases i
    · exact harm103One.trans ha03One
    · exact harm123One.trans ha23One
    · exact ha13One
  have hfirstRange0 : Set.range (first 0) =
      Set.range a01 ∪ Set.range a12 := harm012Range
  have hfirstRange1 : Set.range (first 1) =
      Set.range a03 ∪ Set.range a32 := harm032Range
  have hfirstRange2 : Set.range (first 2) = Set.range a02 := rfl
  have hdualRange0 : Set.range (dual 0) =
      Set.range a10 ∪ Set.range a03 := harm103Range
  have hdualRange1 : Set.range (dual 1) =
      Set.range a12 ∪ Set.range a23 := harm123Range
  have hdualRange2 : Set.range (dual 2) = Set.range a13 := rfl
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
  -- Distribute intersections over the composite arms to verify both theta
  -- incidence patterns.
  have hfirst01 : Set.range (first 0) ∩ Set.range (first 1) = {p, q} := by
    rw [hfirstRange0, hfirstRange1]
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
  have hfirst02 : Set.range (first 0) ∩ Set.range (first 2) = {p, q} := by
    rw [hfirstRange0, hfirstRange2]
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
    · rintro ⟨hy03 | hy32, hy02⟩
      · have hy : y ∈ Set.range a02 ∩ Set.range a03 := ⟨hy02, hy03⟩
        rw [h02_03] at hy
        exact Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hy))
      · have hy : y ∈ Set.range a02 ∩ Set.range a32 := ⟨hy02, hy32⟩
        rw [h02_32] at hy
        exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mp hy))
    · intro hy
      rcases Set.mem_insert_iff.mp hy with rfl | hyq
      · exact ⟨Or.inl ⟨0, ha03Zero⟩, ⟨0, ha02Zero⟩⟩
      · rw [Set.mem_singleton_iff] at hyq
        subst y
        exact ⟨Or.inr ⟨1, ha32One⟩, ⟨1, ha02One⟩⟩
  have hdual01 : Set.range (dual 0) ∩ Set.range (dual 1) = {r, s} := by
    rw [hdualRange0, hdualRange1]
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
  have hdual02 : Set.range (dual 0) ∩ Set.range (dual 2) = {r, s} := by
    rw [hdualRange0, hdualRange2]
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
    · rintro ⟨hy12 | hy23, hy13⟩
      · have hy : y ∈ Set.range a13 ∩ Set.range a12 := ⟨hy13, hy12⟩
        rw [h13_12] at hy
        exact Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hy))
      · have hy : y ∈ Set.range a13 ∩ Set.range a23 := ⟨hy13, hy23⟩
        rw [h13_23] at hy
        exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mp hy))
    · intro hy
      rcases Set.mem_insert_iff.mp hy with rfl | hys
      · exact ⟨Or.inl ⟨0, ha12Zero⟩, ⟨0, ha13Zero⟩⟩
      · rw [Set.mem_singleton_iff] at hys
        subst y
        exact ⟨Or.inr ⟨1, ha23One⟩, ⟨1, ha13One⟩⟩
  have hfirstInter (i j : Fin 3) (hij : i ≠ j) :
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
  have hdualInter (i j : Fin 3) (hij : i ≠ j) :
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
  let firstTheta : Set (StandardSphere 2) := ⋃ i, Set.range (first i)
  let dualTheta : Set (StandardSphere 2) := ⋃ i, Set.range (dual i)
  obtain ⟨firstPresentation, hfirstPresentationEdge⟩ :=
    existsThetaPresentationOnUnion first hfirstEmbedding p q hfirstZero
      hfirstOne hfirstInter
  obtain ⟨dualPresentation, hdualPresentationEdge⟩ :=
    existsThetaPresentationOnUnion dual hdualEmbedding r s hdualZero
      hdualOne hdualInter
  have hfirstThetaFinite : firstTheta =
      Set.range (first 0) ∪ Set.range (first 1) ∪ Set.range (first 2) := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      fin_cases i
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
    · rintro ((hy | hy) | hy)
      · exact Set.mem_iUnion.mpr ⟨0, hy⟩
      · exact Set.mem_iUnion.mpr ⟨1, hy⟩
      · exact Set.mem_iUnion.mpr ⟨2, hy⟩
  have hdualThetaFinite : dualTheta =
      Set.range (dual 0) ∪ Set.range (dual 1) ∪ Set.range (dual 2) := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      fin_cases i
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
    · rintro ((hy | hy) | hy)
      · exact Set.mem_iUnion.mpr ⟨0, hy⟩
      · exact Set.mem_iUnion.mpr ⟨1, hy⟩
      · exact Set.mem_iUnion.mpr ⟨2, hy⟩
  have hfirstCarrier : firstTheta ∪ Set.range a13 = X := by
    rw [hfirstThetaFinite, hfirstRange0, hfirstRange1, hfirstRange2,
      ha01Range, ha12Range, ha03Range, ha32Range, ha02Range, ha13Range]
    simpa only [e01, e12, e02, e03, e32, e13] using
      sixAmbientEdges_eq R X e
  have hdualCarrier : dualTheta ∪ Set.range a02 = X := by
    rw [hdualThetaFinite, hdualRange0, hdualRange1, hdualRange2,
      ha10Range, ha03Range, ha12Range, ha23Range, ha13Range, ha02Range]
    calc
      (((R.ambientEdge X e e01 ∪ R.ambientEdge X e e03) ∪
          (R.ambientEdge X e e12 ∪ R.ambientEdge X e e32)) ∪
          R.ambientEdge X e e13) ∪ R.ambientEdge X e e02 =
          (((R.ambientEdge X e e01 ∪ R.ambientEdge X e e12) ∪
            (R.ambientEdge X e e03 ∪ R.ambientEdge X e e32)) ∪
            R.ambientEdge X e e02) ∪ R.ambientEdge X e e13 := by
              ext y
              simp only [Set.mem_union]
              tauto
      _ = X := by
        simpa only [e01, e12, e02, e03, e32, e13] using
          sixAmbientEdges_eq R X e
  obtain ⟨firstRepresentative, hfirstBijective, hfirstFrontier0,
      hfirstFrontier1, hfirstFrontier2, hfirstPair⟩ :=
    existsIndexedThetaRegions firstTheta firstPresentation
  obtain ⟨dualRepresentative, hdualBijective, hdualFrontier0,
      hdualFrontier1, hdualFrontier2, hdualPair⟩ :=
    existsIndexedThetaRegions dualTheta dualPresentation
  rw [hfirstPresentationEdge 1, hfirstPresentationEdge 2] at hfirstFrontier0
  rw [hfirstPresentationEdge 0, hfirstPresentationEdge 2] at hfirstFrontier1
  rw [hfirstPresentationEdge 0, hfirstPresentationEdge 1] at hfirstFrontier2
  rw [hfirstPresentationEdge 0, hfirstPresentationEdge 1] at hfirstPair
  rw [hdualPresentationEdge 1, hdualPresentationEdge 2] at hdualFrontier0
  rw [hdualPresentationEdge 0, hdualPresentationEdge 2] at hdualFrontier1
  rw [hdualPresentationEdge 0, hdualPresentationEdge 1] at hdualFrontier2
  rw [hdualPresentationEdge 0, hdualPresentationEdge 1] at hdualPair
  have hambientVertexInjective : Function.Injective
      (fun i : Fin 4 ↦ (e (R.vertex i) : StandardSphere 2)) :=
    Subtype.val_injective.comp (e.injective.comp R.vertex_injective)
  have hrFirst : r ∈ Set.range (first 0) := by
    rw [hfirstRange0]
    exact Or.inl ⟨1, ha01One⟩
  have hsFirst : s ∈ Set.range (first 1) := by
    rw [hfirstRange1]
    exact Or.inl ⟨1, ha03One⟩
  have hpDual : p ∈ Set.range (dual 0) := by
    rw [hdualRange0]
    exact Or.inl ⟨1, ha10One⟩
  have hqDual : q ∈ Set.range (dual 1) := by
    rw [hdualRange1]
    exact Or.inl ⟨1, ha12One⟩
  have hrFirstOther (j : Fin 3) (hj : j ≠ 0) :
      r ∉ Set.range (first j) := by
    intro hrj
    have hrPair : r ∈ Set.range (first 0) ∩ Set.range (first j) :=
      ⟨hrFirst, hrj⟩
    rw [hfirstInter 0 j hj.symm] at hrPair
    rcases hrPair with hrp | hrq
    · exact (by decide : (1 : Fin 4) ≠ 0)
        (hambientVertexInjective hrp)
    · exact (by decide : (1 : Fin 4) ≠ 2)
        (hambientVertexInjective (Set.mem_singleton_iff.mp hrq))
  have hsFirstOther (j : Fin 3) (hj : j ≠ 1) :
      s ∉ Set.range (first j) := by
    intro hsj
    have hsPair : s ∈ Set.range (first 1) ∩ Set.range (first j) :=
      ⟨hsFirst, hsj⟩
    rw [hfirstInter 1 j hj.symm] at hsPair
    rcases hsPair with hsp | hsq
    · exact (by decide : (3 : Fin 4) ≠ 0)
        (hambientVertexInjective hsp)
    · exact (by decide : (3 : Fin 4) ≠ 2)
        (hambientVertexInjective (Set.mem_singleton_iff.mp hsq))
  have hpDualOther (j : Fin 3) (hj : j ≠ 0) :
      p ∉ Set.range (dual j) := by
    intro hpj
    have hpPair : p ∈ Set.range (dual 0) ∩ Set.range (dual j) :=
      ⟨hpDual, hpj⟩
    rw [hdualInter 0 j hj.symm] at hpPair
    rcases hpPair with hpr | hps
    · exact (by decide : (0 : Fin 4) ≠ 1)
        (hambientVertexInjective hpr)
    · exact (by decide : (0 : Fin 4) ≠ 3)
        (hambientVertexInjective (Set.mem_singleton_iff.mp hps))
  have hqDualOther (j : Fin 3) (hj : j ≠ 1) :
      q ∉ Set.range (dual j) := by
    intro hqj
    have hqPair : q ∈ Set.range (dual 1) ∩ Set.range (dual j) :=
      ⟨hqDual, hqj⟩
    rw [hdualInter 1 j hj.symm] at hqPair
    rcases hqPair with hqr | hqs
    · exact (by decide : (2 : Fin 4) ≠ 1)
        (hambientVertexInjective hqr)
    · exact (by decide : (2 : Fin 4) ≠ 3)
        (hambientVertexInjective (Set.mem_singleton_iff.mp hqs))
  have h13InteriorFirst : Set.range a13 \ {r, s} ⊆ firstThetaᶜ := by
    rintro y ⟨hy13, hyEnds⟩ hyFirst
    rw [hfirstThetaFinite, hfirstRange0, hfirstRange1, hfirstRange2] at hyFirst
    rcases hyFirst with h | hy02
    · rcases h with h | h
      · rcases h with hy01 | hy12
        · have hy : y ∈ Set.range a13 ∩ Set.range a01 := ⟨hy13, hy01⟩
          rw [h13_01] at hy
          exact hyEnds (Or.inl (Set.mem_singleton_iff.mp hy))
        · have hy : y ∈ Set.range a13 ∩ Set.range a12 := ⟨hy13, hy12⟩
          rw [h13_12] at hy
          exact hyEnds (Or.inl (Set.mem_singleton_iff.mp hy))
      · rcases h with hy03 | hy32
        · have hy : y ∈ Set.range a13 ∩ Set.range a03 := ⟨hy13, hy03⟩
          rw [h13_03] at hy
          exact hyEnds (Or.inr (Set.mem_singleton_iff.mpr
            (Set.mem_singleton_iff.mp hy)))
        · have hy : y ∈ Set.range a13 ∩ Set.range a32 := ⟨hy13, hy32⟩
          rw [h13_32] at hy
          exact hyEnds (Or.inr (Set.mem_singleton_iff.mpr
            (Set.mem_singleton_iff.mp hy)))
    · have hy : y ∈ Set.range a02 ∩ Set.range a13 := ⟨hy02, hy13⟩
      rw [h02_13] at hy
      exact hy.elim
  have h02InteriorDual : Set.range a02 \ {p, q} ⊆ dualThetaᶜ := by
    rintro y ⟨hy02, hyEnds⟩ hyDual
    rw [hdualThetaFinite, hdualRange0, hdualRange1, hdualRange2] at hyDual
    rcases hyDual with h | hy13
    · rcases h with h | h
      · rcases h with hy10 | hy03
        · have hy : y ∈ Set.range a02 ∩ Set.range a01 := by
            rw [ha10Range, ← ha01Range] at hy10
            exact ⟨hy02, hy10⟩
          rw [h02_01] at hy
          exact hyEnds (Or.inl (Set.mem_singleton_iff.mp hy))
        · have hy : y ∈ Set.range a02 ∩ Set.range a03 := ⟨hy02, hy03⟩
          rw [h02_03] at hy
          exact hyEnds (Or.inl (Set.mem_singleton_iff.mp hy))
      · rcases h with hy12 | hy23
        · have hy : y ∈ Set.range a02 ∩ Set.range a12 := ⟨hy02, hy12⟩
          rw [h02_12] at hy
          exact hyEnds (Or.inr (Set.mem_singleton_iff.mpr
            (Set.mem_singleton_iff.mp hy)))
        · have hy : y ∈ Set.range a02 ∩ Set.range a32 := by
            rw [ha23Range, ← ha32Range] at hy23
            exact ⟨hy02, hy23⟩
          rw [h02_32] at hy
          exact hyEnds (Or.inr (Set.mem_singleton_iff.mpr
            (Set.mem_singleton_iff.mp hy)))
    · have hy : y ∈ Set.range a02 ∩ Set.range a13 := ⟨hy02, hy13⟩
      rw [h02_13] at hy
      exact hy.elim
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
  let d : StandardSphere 2 := a13 t
  let b : StandardSphere 2 := a02 t
  have hdInterior : d ∈ Set.range a13 \ {r, s} := by
    refine ⟨Set.mem_range_self t, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h ↦ htZero (ha13Embedding.injective
      (h.trans ha13Zero.symm)), fun h ↦ htOne (ha13Embedding.injective
      (h.trans ha13One.symm))⟩
  have hbInterior : b ∈ Set.range a02 \ {p, q} := by
    refine ⟨Set.mem_range_self t, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h ↦ htZero (ha02Embedding.injective
      (h.trans ha02Zero.symm)), fun h ↦ htOne (ha02Embedding.injective
      (h.trans ha02One.symm))⟩
  have hdFirst : d ∈ firstThetaᶜ := h13InteriorFirst hdInterior
  have hbDual : b ∈ dualThetaᶜ := h02InteriorDual hbInterior
  have h13InteriorConnected : IsConnected (Set.range a13 \ {r, s}) := by
    simpa only [ha13Zero, ha13One] using
      embeddedArc_range_diff_endpoints_isConnected a13 ha13Embedding
  have h02InteriorConnected : IsConnected (Set.range a02 \ {p, q}) := by
    simpa only [ha02Zero, ha02One] using
      embeddedArc_range_diff_endpoints_isConnected a02 ha02Embedding
  have h13InteriorComponent : Set.range a13 \ {r, s} ⊆
      connectedComponentIn firstThetaᶜ d :=
    h13InteriorConnected.2.subset_connectedComponentIn hdInterior
      h13InteriorFirst
  have h02InteriorComponent : Set.range a02 \ {p, q} ⊆
      connectedComponentIn dualThetaᶜ b :=
    h02InteriorConnected.2.subset_connectedComponentIn hbInterior
      h02InteriorDual
  have h13Ends := embeddedArc_endpoints_mem_closure_interiorRange
    a13 ha13Embedding
  rw [ha13Zero, ha13One] at h13Ends
  have h02Ends := embeddedArc_endpoints_mem_closure_interiorRange
    a02 ha02Embedding
  rw [ha02Zero, ha02One] at h02Ends
  have hrClosure : r ∈ closure (connectedComponentIn firstThetaᶜ d) :=
    closure_mono h13InteriorComponent h13Ends.1
  have hsClosure : s ∈ closure (connectedComponentIn firstThetaᶜ d) :=
    closure_mono h13InteriorComponent h13Ends.2
  have hpClosure : p ∈ closure (connectedComponentIn dualThetaᶜ b) :=
    closure_mono h02InteriorComponent h02Ends.1
  have hqClosure : q ∈ closure (connectedComponentIn dualThetaᶜ b) :=
    closure_mono h02InteriorComponent h02Ends.2
  let dFirst : (firstThetaᶜ : Set (StandardSphere 2)) := ⟨d, hdFirst⟩
  let bDual : (dualThetaᶜ : Set (StandardSphere 2)) := ⟨b, hbDual⟩
  obtain ⟨firstIndex, hfirstIndex⟩ := hfirstBijective.2
    (dFirst : ConnectedComponents (firstThetaᶜ : Set (StandardSphere 2)))
  obtain ⟨dualIndex, hdualIndex⟩ := hdualBijective.2
    (bDual : ConnectedComponents (dualThetaᶜ : Set (StandardSphere 2)))
  have hdiagonalFirst : connectedComponentIn firstThetaᶜ d =
      connectedComponentIn firstThetaᶜ (firstRepresentative 2) := by
    have hcomponent := (connectedComponentIn_eq_of_componentClass_eq
      (firstRepresentative firstIndex) dFirst hfirstIndex).symm
    fin_cases firstIndex
    · have hrTheta : r ∈ firstTheta :=
        Set.mem_iUnion.mpr ⟨0, hrFirst⟩
      have hrOther : r ∉ Set.range (first 1) ∪ Set.range (first 2) :=
        fun hr ↦ hr.elim (hrFirstOther 1 (by decide))
          (hrFirstOther 2 (by decide))
      have hrNotClosure := not_mem_closure_connectedComponentIn_of_frontier_subset
        hrTheta hrOther hfirstFrontier0.le
      exact (hrNotClosure (hcomponent ▸ hrClosure)).elim
    · have hsTheta : s ∈ firstTheta :=
        Set.mem_iUnion.mpr ⟨1, hsFirst⟩
      have hsOther : s ∉ Set.range (first 0) ∪ Set.range (first 2) :=
        fun hs ↦ hs.elim (hsFirstOther 0 (by decide))
          (hsFirstOther 2 (by decide))
      have hsNotClosure := not_mem_closure_connectedComponentIn_of_frontier_subset
        hsTheta hsOther hfirstFrontier1.le
      exact (hsNotClosure (hcomponent ▸ hsClosure)).elim
    · exact hcomponent
  have hdiagonalDual : connectedComponentIn dualThetaᶜ b =
      connectedComponentIn dualThetaᶜ (dualRepresentative 2) := by
    have hcomponent := (connectedComponentIn_eq_of_componentClass_eq
      (dualRepresentative dualIndex) bDual hdualIndex).symm
    fin_cases dualIndex
    · have hpTheta : p ∈ dualTheta := Set.mem_iUnion.mpr ⟨0, hpDual⟩
      have hpOther : p ∉ Set.range (dual 1) ∪ Set.range (dual 2) :=
        fun hp ↦ hp.elim (hpDualOther 1 (by decide))
          (hpDualOther 2 (by decide))
      have hpNotClosure := not_mem_closure_connectedComponentIn_of_frontier_subset
        hpTheta hpOther hdualFrontier0.le
      exact (hpNotClosure (hcomponent ▸ hpClosure)).elim
    · have hqTheta : q ∈ dualTheta := Set.mem_iUnion.mpr ⟨1, hqDual⟩
      have hqOther : q ∉ Set.range (dual 0) ∪ Set.range (dual 2) :=
        fun hq ↦ hq.elim (hqDualOther 0 (by decide))
          (hqDualOther 2 (by decide))
      have hqNotClosure := not_mem_closure_connectedComponentIn_of_frontier_subset
        hqTheta hqOther hdualFrontier1.le
      exact (hqNotClosure (hcomponent ▸ hqClosure)).elim
    · exact hcomponent
  let outer : Set (StandardSphere 2) :=
    Set.range (first 0) ∪ Set.range (first 1)
  have houterDual : outer =
      Set.range (dual 0) ∪ Set.range (dual 1) := by
    unfold outer
    rw [hfirstRange0, hfirstRange1, hdualRange0, hdualRange1,
      ha10Range, ← ha01Range, ha23Range, ← ha32Range]
    exact union_pairs_exchange _ _ _ _
  have hpq : p ≠ q := hambientVertexInjective.ne (by decide)
  have houterCard : Cardinal.mk (ConnectedComponents
      (outerᶜ : Set (StandardSphere 2))) = 2 :=
    Set.separatesInto_iff.mp (embeddedArcPair_separatesIntoTwo
      (first 0) (first 1) (hfirstEmbedding 0) (hfirstEmbedding 1)
      p q hpq hfirst01)
  have hfirstPairOuter : connectedComponentIn firstThetaᶜ
      (firstRepresentative 2) =
      connectedComponentIn outerᶜ (firstRepresentative 2) := by
    simpa only [outer] using hfirstPair
  have hdualPairOuter : connectedComponentIn dualThetaᶜ
      (dualRepresentative 2) =
      connectedComponentIn outerᶜ (dualRepresentative 2) := by
    rw [houterDual]
    exact hdualPair
  have hbOuter : b ∈ outerᶜ := by
    intro hb
    rw [houterDual] at hb
    exact hbDual (hb.elim (fun hb0 ↦ Set.mem_iUnion.mpr ⟨0, hb0⟩)
      (fun hb1 ↦ Set.mem_iUnion.mpr ⟨1, hb1⟩))
  have hdOuter : d ∈ outerᶜ := by
    intro hd
    exact hdFirst (hd.elim (fun hd0 ↦ Set.mem_iUnion.mpr ⟨0, hd0⟩)
      (fun hd1 ↦ Set.mem_iUnion.mpr ⟨1, hd1⟩))
  have hbDualPair : b ∈ connectedComponentIn outerᶜ
      (dualRepresentative 2) := by
    have hbComponent : b ∈ connectedComponentIn dualThetaᶜ b :=
      mem_connectedComponentIn hbDual
    rw [hdiagonalDual, hdualPairOuter] at hbComponent
    exact hbComponent
  have hdFirstPair : d ∈ connectedComponentIn outerᶜ
      (firstRepresentative 2) := by
    have hdComponent : d ∈ connectedComponentIn firstThetaᶜ d :=
      mem_connectedComponentIn hdFirst
    rw [hdiagonalFirst, hfirstPairOuter] at hdComponent
    exact hdComponent
  have hpairDistinct : connectedComponentIn outerᶜ (firstRepresentative 2) ≠
      connectedComponentIn outerᶜ (dualRepresentative 2) := by
    intro heq
    have hbFirstOuter : b ∈ connectedComponentIn outerᶜ
        (firstRepresentative 2) := heq ▸ hbDualPair
    have hbFirstComponent : b ∈ connectedComponentIn firstThetaᶜ
        (firstRepresentative 2) := hfirstPairOuter.symm ▸ hbFirstOuter
    have hbFirstTheta : b ∈ firstTheta :=
      Set.mem_iUnion.mpr ⟨2, Set.mem_range_self t⟩
    exact (connectedComponentIn_subset firstThetaᶜ _ hbFirstComponent)
      hbFirstTheta
  have hfirstComponentNe (i : Fin 3) (hi : i ≠ 2) :
      connectedComponentIn firstThetaᶜ (firstRepresentative i) ≠
        connectedComponentIn firstThetaᶜ (firstRepresentative 2) := by
    intro heq
    have hclass := connectedComponents_coe_eq_of_connectedComponentIn_eq
      (firstRepresentative i) (firstRepresentative 2) heq
    exact hi (hfirstBijective.1 hclass)
  have hdualComponentNe (i : Fin 3) (hi : i ≠ 2) :
      connectedComponentIn dualThetaᶜ (dualRepresentative i) ≠
        connectedComponentIn dualThetaᶜ (dualRepresentative 2) := by
    intro heq
    have hclass := connectedComponents_coe_eq_of_connectedComponentIn_eq
      (dualRepresentative i) (dualRepresentative 2) heq
    exact hi (hdualBijective.1 hclass)
  have hfirstNonpairOuter (i : Fin 3) (hi : i ≠ 2) :
      connectedComponentIn outerᶜ (firstRepresentative i) =
        connectedComponentIn outerᶜ (dualRepresentative 2) := by
    have hiOuter : (firstRepresentative i : StandardSphere 2) ∈ outerᶜ := by
      intro hiOuter
      exact (firstRepresentative i).property
        (hiOuter.elim (fun hi0 ↦ Set.mem_iUnion.mpr ⟨0, hi0⟩)
          (fun hi1 ↦ Set.mem_iUnion.mpr ⟨1, hi1⟩))
    have hfirst2Outer : (firstRepresentative 2 : StandardSphere 2) ∈ outerᶜ := by
      intro hOuter
      exact (firstRepresentative 2).property
        (hOuter.elim (fun h0 ↦ Set.mem_iUnion.mpr ⟨0, h0⟩)
          (fun h1 ↦ Set.mem_iUnion.mpr ⟨1, h1⟩))
    have hdual2Outer : (dualRepresentative 2 : StandardSphere 2) ∈ outerᶜ := by
      intro hOuter
      rw [houterDual] at hOuter
      exact (dualRepresentative 2).property
        (hOuter.elim (fun h0 ↦ Set.mem_iUnion.mpr ⟨0, h0⟩)
          (fun h1 ↦ Set.mem_iUnion.mpr ⟨1, h1⟩))
    rcases connectedComponentIn_eq_or_eq_of_mk_eq_two
        (outerᶜ : Set (StandardSphere 2)) houterCard
        hiOuter hfirst2Outer hdual2Outer hpairDistinct with hsame | hother
    · have hiInPair : (firstRepresentative i : StandardSphere 2) ∈
          connectedComponentIn outerᶜ (firstRepresentative 2) := by
        rw [← hsame]
        exact mem_connectedComponentIn hiOuter
      have hiInThetaPair : (firstRepresentative i : StandardSphere 2) ∈
          connectedComponentIn firstThetaᶜ (firstRepresentative 2) :=
        hfirstPairOuter.symm ▸ hiInPair
      exact (hfirstComponentNe i hi
        (connectedComponentIn_eq hiInThetaPair).symm).elim
    · exact hother
  have hdualNonpairOuter (i : Fin 3) (hi : i ≠ 2) :
      connectedComponentIn outerᶜ (dualRepresentative i) =
        connectedComponentIn outerᶜ (firstRepresentative 2) := by
    have hiOuter : (dualRepresentative i : StandardSphere 2) ∈ outerᶜ := by
      intro hiOuter
      rw [houterDual] at hiOuter
      exact (dualRepresentative i).property
        (hiOuter.elim (fun hi0 ↦ Set.mem_iUnion.mpr ⟨0, hi0⟩)
          (fun hi1 ↦ Set.mem_iUnion.mpr ⟨1, hi1⟩))
    have hfirst2Outer : (firstRepresentative 2 : StandardSphere 2) ∈ outerᶜ := by
      intro hOuter
      exact (firstRepresentative 2).property
        (hOuter.elim (fun h0 ↦ Set.mem_iUnion.mpr ⟨0, h0⟩)
          (fun h1 ↦ Set.mem_iUnion.mpr ⟨1, h1⟩))
    have hdual2Outer : (dualRepresentative 2 : StandardSphere 2) ∈ outerᶜ := by
      intro hOuter
      rw [houterDual] at hOuter
      exact (dualRepresentative 2).property
        (hOuter.elim (fun h0 ↦ Set.mem_iUnion.mpr ⟨0, h0⟩)
          (fun h1 ↦ Set.mem_iUnion.mpr ⟨1, h1⟩))
    rcases connectedComponentIn_eq_or_eq_of_mk_eq_two
        (outerᶜ : Set (StandardSphere 2)) houterCard
        hiOuter hfirst2Outer hdual2Outer hpairDistinct with hother | hsame
    · exact hother
    · have hiInPair : (dualRepresentative i : StandardSphere 2) ∈
          connectedComponentIn outerᶜ (dualRepresentative 2) := by
        rw [← hsame]
        exact mem_connectedComponentIn hiOuter
      have hiInThetaPair : (dualRepresentative i : StandardSphere 2) ∈
          connectedComponentIn dualThetaᶜ (dualRepresentative 2) :=
        hdualPairOuter.symm ▸ hiInPair
      exact (hdualComponentNe i hi
        (connectedComponentIn_eq hiInThetaPair).symm).elim
  have hfirstComponentSubsetX (i : Fin 3) (hi : i ≠ 2) :
      connectedComponentIn firstThetaᶜ (firstRepresentative i) ⊆ Xᶜ := by
    intro y hyComponent hyX
    rw [← hfirstCarrier] at hyX
    rcases hyX with hyTheta | hy13
    · exact (connectedComponentIn_subset firstThetaᶜ _ hyComponent) hyTheta
    · by_cases hyEnds : y ∈ ({r, s} : Set (StandardSphere 2))
      · rcases hyEnds with hyr | hys
        · have hyrTheta : y ∈ firstTheta := hyr ▸
            Set.mem_iUnion.mpr ⟨0, hrFirst⟩
          exact (connectedComponentIn_subset firstThetaᶜ _ hyComponent)
            hyrTheta
        · rw [Set.mem_singleton_iff] at hys
          have hysTheta : y ∈ firstTheta := hys ▸
            Set.mem_iUnion.mpr ⟨1, hsFirst⟩
          exact (connectedComponentIn_subset firstThetaᶜ _ hyComponent)
            hysTheta
      · have hyDiagonal := h13InteriorComponent ⟨hy13, hyEnds⟩
        have heq : connectedComponentIn firstThetaᶜ (firstRepresentative i) =
            connectedComponentIn firstThetaᶜ (firstRepresentative 2) :=
          (connectedComponentIn_eq hyComponent).trans
            ((connectedComponentIn_eq hyDiagonal).symm.trans hdiagonalFirst)
        exact hfirstComponentNe i hi heq
  have hdualComponentSubsetX (i : Fin 3) (hi : i ≠ 2) :
      connectedComponentIn dualThetaᶜ (dualRepresentative i) ⊆ Xᶜ := by
    intro y hyComponent hyX
    rw [← hdualCarrier] at hyX
    rcases hyX with hyTheta | hy02
    · exact (connectedComponentIn_subset dualThetaᶜ _ hyComponent) hyTheta
    · by_cases hyEnds : y ∈ ({p, q} : Set (StandardSphere 2))
      · rcases hyEnds with hyp | hyq
        · have hypTheta : y ∈ dualTheta := hyp ▸
            Set.mem_iUnion.mpr ⟨0, hpDual⟩
          exact (connectedComponentIn_subset dualThetaᶜ _ hyComponent)
            hypTheta
        · rw [Set.mem_singleton_iff] at hyq
          have hyqTheta : y ∈ dualTheta := hyq ▸
            Set.mem_iUnion.mpr ⟨1, hqDual⟩
          exact (connectedComponentIn_subset dualThetaᶜ _ hyComponent)
            hyqTheta
      · have hyDiagonal := h02InteriorComponent ⟨hy02, hyEnds⟩
        have heq : connectedComponentIn dualThetaᶜ (dualRepresentative i) =
            connectedComponentIn dualThetaᶜ (dualRepresentative 2) :=
          (connectedComponentIn_eq hyComponent).trans
            ((connectedComponentIn_eq hyDiagonal).symm.trans hdiagonalDual)
        exact hdualComponentNe i hi heq
  have hXFirst : Xᶜ ⊆ firstThetaᶜ := by
    intro y hyX hyFirst
    exact hyX (hfirstCarrier ▸ Or.inl hyFirst)
  have hXDual : Xᶜ ⊆ dualThetaᶜ := by
    intro y hyX hyDual
    exact hyX (hdualCarrier ▸ Or.inl hyDual)
  have hfirstRepresentativeX (i : Fin 3) (hi : i ≠ 2) :
      (firstRepresentative i : StandardSphere 2) ∈ Xᶜ :=
    hfirstComponentSubsetX i hi
      (mem_connectedComponentIn (firstRepresentative i).property)
  have hdualRepresentativeX (i : Fin 3) (hi : i ≠ 2) :
      (dualRepresentative i : StandardSphere 2) ∈ Xᶜ :=
    hdualComponentSubsetX i hi
      (mem_connectedComponentIn (dualRepresentative i).property)
  have hfirstTransport (i : Fin 3) (hi : i ≠ 2) :
      connectedComponentIn Xᶜ (firstRepresentative i) =
        connectedComponentIn firstThetaᶜ (firstRepresentative i) :=
    connectedComponentIn_eq_of_subset_component hXFirst
      (hfirstRepresentativeX i hi) (hfirstComponentSubsetX i hi)
  have hdualTransport (i : Fin 3) (hi : i ≠ 2) :
      connectedComponentIn Xᶜ (dualRepresentative i) =
        connectedComponentIn dualThetaᶜ (dualRepresentative i) :=
    connectedComponentIn_eq_of_subset_component hXDual
      (hdualRepresentativeX i hi) (hdualComponentSubsetX i hi)
  -- Regard the two non-pair regions from each theta as points of `Xᶜ`.
  let dual₀ : (Xᶜ : Set (StandardSphere 2)) :=
    ⟨dualRepresentative 0, hdualRepresentativeX 0 (by decide)⟩
  let first₀ : (Xᶜ : Set (StandardSphere 2)) :=
    ⟨firstRepresentative 0, hfirstRepresentativeX 0 (by decide)⟩
  let dual₁ : (Xᶜ : Set (StandardSphere 2)) :=
    ⟨dualRepresentative 1, hdualRepresentativeX 1 (by decide)⟩
  let first₁ : (Xᶜ : Set (StandardSphere 2)) :=
    ⟨firstRepresentative 1, hfirstRepresentativeX 1 (by decide)⟩
  have hXOuter : Xᶜ ⊆ outerᶜ := by
    intro y hyX hyOuter
    apply hyX
    rw [← hfirstCarrier]
    exact Or.inl (hyOuter.elim
      (fun h₀ ↦ Set.mem_iUnion.mpr ⟨0, h₀⟩)
      (fun h₁ ↦ Set.mem_iUnion.mpr ⟨1, h₁⟩))
  have hXComponentOuter {x y : StandardSphere 2}
      (hx : x ∈ Xᶜ) (hy : y ∈ Xᶜ)
      (hxy : connectedComponentIn Xᶜ x = connectedComponentIn Xᶜ y) :
      connectedComponentIn outerᶜ x = connectedComponentIn outerᶜ y := by
    have hsubset : connectedComponentIn Xᶜ x ⊆
        connectedComponentIn outerᶜ x :=
      isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hx)
        ((connectedComponentIn_subset Xᶜ x).trans hXOuter)
    have hyComponent : y ∈ connectedComponentIn Xᶜ x := by
      rw [hxy]
      exact mem_connectedComponentIn hy
    exact connectedComponentIn_eq (hsubset hyComponent)
  have hfirstDistinct (i j : Fin 3) (hi : i ≠ 2) (hj : j ≠ 2)
      (hij : i ≠ j) :
      connectedComponentIn Xᶜ (firstRepresentative i) ≠
        connectedComponentIn Xᶜ (firstRepresentative j) := by
    intro heq
    rw [hfirstTransport i hi, hfirstTransport j hj] at heq
    have hclass := connectedComponents_coe_eq_of_connectedComponentIn_eq
      (firstRepresentative i) (firstRepresentative j) heq
    exact hij (hfirstBijective.1 hclass)
  have hdualDistinct (i j : Fin 3) (hi : i ≠ 2) (hj : j ≠ 2)
      (hij : i ≠ j) :
      connectedComponentIn Xᶜ (dualRepresentative i) ≠
        connectedComponentIn Xᶜ (dualRepresentative j) := by
    intro heq
    rw [hdualTransport i hi, hdualTransport j hj] at heq
    have hclass := connectedComponents_coe_eq_of_connectedComponentIn_eq
      (dualRepresentative i) (dualRepresentative j) heq
    exact hij (hdualBijective.1 hclass)
  have hcrossDistinct (i j : Fin 3) (hi : i ≠ 2) (hj : j ≠ 2) :
      connectedComponentIn Xᶜ (firstRepresentative i) ≠
        connectedComponentIn Xᶜ (dualRepresentative j) := by
    intro heq
    have houterEq := hXComponentOuter
      (hfirstRepresentativeX i hi) (hdualRepresentativeX j hj) heq
    apply hpairDistinct
    calc
      connectedComponentIn outerᶜ (firstRepresentative 2) =
          connectedComponentIn outerᶜ (dualRepresentative j) :=
        (hdualNonpairOuter j hj).symm
      _ = connectedComponentIn outerᶜ (firstRepresentative i) :=
        houterEq.symm
      _ = connectedComponentIn outerᶜ (dualRepresentative 2) :=
        hfirstNonpairOuter i hi
  -- Pairwise component inequalities give injectivity of the chosen ordering.
  have hclassDual₀First₀ :
      (dual₀ : ConnectedComponents (Xᶜ : Set (StandardSphere 2))) ≠ first₀ := by
    intro hclass
    exact hcrossDistinct 0 0 (by decide) (by decide)
      (connectedComponentIn_eq_of_componentClass_eq dual₀ first₀ hclass).symm
  have hclassDual₀Dual₁ :
      (dual₀ : ConnectedComponents (Xᶜ : Set (StandardSphere 2))) ≠ dual₁ := by
    intro hclass
    exact hdualDistinct 0 1 (by decide) (by decide) (by decide)
      (connectedComponentIn_eq_of_componentClass_eq dual₀ dual₁ hclass)
  have hclassDual₀First₁ :
      (dual₀ : ConnectedComponents (Xᶜ : Set (StandardSphere 2))) ≠ first₁ := by
    intro hclass
    exact hcrossDistinct 1 0 (by decide) (by decide)
      (connectedComponentIn_eq_of_componentClass_eq dual₀ first₁ hclass).symm
  have hclassFirst₀Dual₁ :
      (first₀ : ConnectedComponents (Xᶜ : Set (StandardSphere 2))) ≠ dual₁ := by
    intro hclass
    exact hcrossDistinct 0 1 (by decide) (by decide)
      (connectedComponentIn_eq_of_componentClass_eq first₀ dual₁ hclass)
  have hclassFirst₀First₁ :
      (first₀ : ConnectedComponents (Xᶜ : Set (StandardSphere 2))) ≠ first₁ := by
    intro hclass
    exact hfirstDistinct 0 1 (by decide) (by decide) (by decide)
      (connectedComponentIn_eq_of_componentClass_eq first₀ first₁ hclass)
  have hclassDual₁First₁ :
      (dual₁ : ConnectedComponents (Xᶜ : Set (StandardSphere 2))) ≠ first₁ := by
    intro hclass
    exact hcrossDistinct 1 1 (by decide) (by decide)
      (connectedComponentIn_eq_of_componentClass_eq dual₁ first₁ hclass).symm
  let representative : Fin 4 → (Xᶜ : Set (StandardSphere 2)) :=
    ![dual₀, first₀, dual₁, first₁]
  let regionClass : Fin 4 →
      ConnectedComponents (Xᶜ : Set (StandardSphere 2)) :=
    ![(dual₀ : ConnectedComponents (Xᶜ : Set (StandardSphere 2))),
      first₀, dual₁, first₁]
  have hregionInjective : Function.Injective regionClass := by
    simpa [regionClass, representative] using finFourVector_injective
      (dual₀ : ConnectedComponents (Xᶜ : Set (StandardSphere 2)))
      (first₀ : ConnectedComponents (Xᶜ : Set (StandardSphere 2)))
      (dual₁ : ConnectedComponents (Xᶜ : Set (StandardSphere 2)))
      (first₁ : ConnectedComponents (Xᶜ : Set (StandardSphere 2)))
      hclassDual₀First₀ hclassDual₀Dual₁ hclassDual₀First₁
      hclassFirst₀Dual₁ hclassFirst₀First₁ hclassDual₁First₁
  have hfirstClassifyX (i : Fin 3) (hi : i ≠ 2)
      (x : (Xᶜ : Set (StandardSphere 2)))
      (hclass : (firstRepresentative i : ConnectedComponents
        (firstThetaᶜ : Set (StandardSphere 2))) =
          (⟨x, hXFirst x.property⟩ :
            (firstThetaᶜ : Set (StandardSphere 2)))) :
      ((⟨firstRepresentative i, hfirstRepresentativeX i hi⟩ :
          (Xᶜ : Set (StandardSphere 2))) :
        ConnectedComponents (Xᶜ : Set (StandardSphere 2))) = x := by
    apply connectedComponents_coe_eq_of_connectedComponentIn_eq
    have htheta := connectedComponentIn_eq_of_componentClass_eq
      (firstRepresentative i)
      (⟨x, hXFirst x.property⟩ :
        (firstThetaᶜ : Set (StandardSphere 2))) hclass
    have hxTheta : (x : StandardSphere 2) ∈
        connectedComponentIn firstThetaᶜ (firstRepresentative i) := by
      rw [htheta]
      exact mem_connectedComponentIn (hXFirst x.property)
    have hxComponent : (x : StandardSphere 2) ∈
        connectedComponentIn Xᶜ (firstRepresentative i) := by
      rw [hfirstTransport i hi]
      exact hxTheta
    exact connectedComponentIn_eq hxComponent
  have hdualClassifyX (i : Fin 3) (hi : i ≠ 2)
      (x : (Xᶜ : Set (StandardSphere 2)))
      (hclass : (dualRepresentative i : ConnectedComponents
        (dualThetaᶜ : Set (StandardSphere 2))) =
          (⟨x, hXDual x.property⟩ :
            (dualThetaᶜ : Set (StandardSphere 2)))) :
      ((⟨dualRepresentative i, hdualRepresentativeX i hi⟩ :
          (Xᶜ : Set (StandardSphere 2))) :
        ConnectedComponents (Xᶜ : Set (StandardSphere 2))) = x := by
    apply connectedComponents_coe_eq_of_connectedComponentIn_eq
    have htheta := connectedComponentIn_eq_of_componentClass_eq
      (dualRepresentative i)
      (⟨x, hXDual x.property⟩ :
        (dualThetaᶜ : Set (StandardSphere 2))) hclass
    have hxTheta : (x : StandardSphere 2) ∈
        connectedComponentIn dualThetaᶜ (dualRepresentative i) := by
      rw [htheta]
      exact mem_connectedComponentIn (hXDual x.property)
    have hxComponent : (x : StandardSphere 2) ∈
        connectedComponentIn Xᶜ (dualRepresentative i) := by
      rw [hdualTransport i hi]
      exact hxTheta
    exact connectedComponentIn_eq hxComponent
  have hregionSurjective : Function.Surjective regionClass := by
    intro component
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe component
    let xFirst : (firstThetaᶜ : Set (StandardSphere 2)) :=
      ⟨x, hXFirst x.property⟩
    obtain ⟨firstIndex, hfirstIndex⟩ := hfirstBijective.2
      (xFirst : ConnectedComponents (firstThetaᶜ : Set (StandardSphere 2)))
    fin_cases firstIndex
    · refine ⟨1, ?_⟩
      simpa [regionClass, representative, first₀, xFirst] using
        hfirstClassifyX 0 (by decide) x hfirstIndex
    · refine ⟨3, ?_⟩
      simpa [regionClass, representative, first₁, xFirst] using
        hfirstClassifyX 1 (by decide) x hfirstIndex
    · let xDual : (dualThetaᶜ : Set (StandardSphere 2)) :=
        ⟨x, hXDual x.property⟩
      obtain ⟨dualIndex, hdualIndex⟩ := hdualBijective.2
        (xDual : ConnectedComponents (dualThetaᶜ : Set (StandardSphere 2)))
      fin_cases dualIndex
      · refine ⟨0, ?_⟩
        simpa [regionClass, representative, dual₀, xDual] using
          hdualClassifyX 0 (by decide) x hdualIndex
      · refine ⟨2, ?_⟩
        simpa [regionClass, representative, dual₁, xDual] using
          hdualClassifyX 1 (by decide) x hdualIndex
      · have hxFirstComponent : (x : StandardSphere 2) ∈
            connectedComponentIn outerᶜ (firstRepresentative 2) := by
          have hxTheta : (x : StandardSphere 2) ∈
              connectedComponentIn firstThetaᶜ (firstRepresentative 2) := by
            rw [connectedComponentIn_eq_of_componentClass_eq
              (firstRepresentative 2) xFirst hfirstIndex]
            exact mem_connectedComponentIn xFirst.property
          rw [hfirstPairOuter] at hxTheta
          exact hxTheta
        have hxDualComponent : (x : StandardSphere 2) ∈
            connectedComponentIn outerᶜ (dualRepresentative 2) := by
          have hxTheta : (x : StandardSphere 2) ∈
              connectedComponentIn dualThetaᶜ (dualRepresentative 2) := by
            rw [connectedComponentIn_eq_of_componentClass_eq
              (dualRepresentative 2) xDual hdualIndex]
            exact mem_connectedComponentIn xDual.property
          rw [hdualPairOuter] at hxTheta
          exact hxTheta
        exact (hpairDistinct ((connectedComponentIn_eq hxFirstComponent).trans
          (connectedComponentIn_eq hxDualComponent).symm)).elim
  -- The four theta frontier formulas now normalize to the four opposite
  -- triangles; the only spelling bridge is the orientation of edge `23`.
  have he32Canonical : e32 =
      (⟨s((2 : Fin 4), 3), of_decide_eq_true rfl⟩ :
        (SimpleGraph.completeGraph (Fin 4)).edgeSet) := by
    apply Subtype.ext
    rw [Sym2.eq_iff]
    exact Or.inr ⟨rfl, rfl⟩
  have hfrontierDual₀ :
      frontier (connectedComponentIn Xᶜ dual₀) =
        R.oppositeBoundary X e 0 := by
    calc
      frontier (connectedComponentIn Xᶜ dual₀) =
          frontier (connectedComponentIn dualThetaᶜ
            (dualRepresentative 0)) := by
        exact congrArg frontier (hdualTransport 0 (by decide))
      _ = Set.range (dual 1) ∪ Set.range (dual 2) := hdualFrontier0
      _ = (R.ambientEdge X e
            ⟨s(1, 2), of_decide_eq_true rfl⟩ ∪
          R.ambientEdge X e
            ⟨s(2, 3), of_decide_eq_true rfl⟩) ∪
          R.ambientEdge X e
            ⟨s(1, 3), of_decide_eq_true rfl⟩ := by
        rw [hdualRange1, hdualRange2, ha12Range, ha23Range, ha13Range,
          he32Canonical]
      _ = R.oppositeBoundary X e 0 := (oppositeBoundary_zero_eq R X e).symm
  have hfrontierFirst₀ :
      frontier (connectedComponentIn Xᶜ first₀) =
        R.oppositeBoundary X e 1 := by
    calc
      frontier (connectedComponentIn Xᶜ first₀) =
          frontier (connectedComponentIn firstThetaᶜ
            (firstRepresentative 0)) := by
        exact congrArg frontier (hfirstTransport 0 (by decide))
      _ = Set.range (first 1) ∪ Set.range (first 2) := hfirstFrontier0
      _ = R.oppositeBoundary X e 1 := by
        rw [hfirstRange1, hfirstRange2, ha03Range, ha32Range, ha02Range,
          he32Canonical, oppositeBoundary_one_eq]
        exact union_three_rotate _ _ _
  have hfrontierDual₁ :
      frontier (connectedComponentIn Xᶜ dual₁) =
        R.oppositeBoundary X e 2 := by
    calc
      frontier (connectedComponentIn Xᶜ dual₁) =
          frontier (connectedComponentIn dualThetaᶜ
            (dualRepresentative 1)) := by
        exact congrArg frontier (hdualTransport 1 (by decide))
      _ = Set.range (dual 0) ∪ Set.range (dual 2) := hdualFrontier1
      _ = R.oppositeBoundary X e 2 := by
        rw [hdualRange0, hdualRange2, ha10Range, ha03Range, ha13Range,
          oppositeBoundary_two_eq]
  have hfrontierFirst₁ :
      frontier (connectedComponentIn Xᶜ first₁) =
        R.oppositeBoundary X e 3 := by
    calc
      frontier (connectedComponentIn Xᶜ first₁) =
          frontier (connectedComponentIn firstThetaᶜ
            (firstRepresentative 1)) := by
        exact congrArg frontier (hfirstTransport 1 (by decide))
      _ = Set.range (first 0) ∪ Set.range (first 2) := hfirstFrontier1
      _ = R.oppositeBoundary X e 3 := by
        rw [hfirstRange0, hfirstRange2, ha01Range, ha12Range, ha02Range,
          oppositeBoundary_three_eq]
        exact union_three_swap_last _ _ _
  have hregionClass_eq : regionClass = fun i ↦
      (representative i : ConnectedComponents
        (Xᶜ : Set (StandardSphere 2))) := by
    funext i
    fin_cases i <;> rfl
  have hrepresentativeBijective : Function.Bijective (fun i ↦
      (representative i : ConnectedComponents
        (Xᶜ : Set (StandardSphere 2)))) := by
    rw [← hregionClass_eq]
    exact ⟨hregionInjective, hregionSurjective⟩
  refine ⟨representative, hrepresentativeBijective, ?_⟩
  intro i
  fin_cases i
  · simpa [representative] using hfrontierDual₀
  · simpa [representative] using hfrontierFirst₀
  · simpa [representative] using hfrontierDual₁
  · simpa [representative] using hfrontierFirst₁

/-- Lemma 64.3 (1): A realization of the complete graph on four vertices in the
standard two-sphere separates the sphere into exactly four components. -/
theorem separatesInto (X : Set (StandardSphere 2)) (e : R.Carrier ≃ₜ X) :
    X.SeparatesInto 4 := by
  -- The shared region interface gives an explicit equivalence between the
  -- four vertex indices and the complementary-component quotient.
  obtain ⟨representative, hrepresentative, -⟩ :=
    existsFourComplementaryRegions R X e
  rw [Set.separatesInto_iff, Cardinal.mk_eq_nat_iff]
  exact ⟨(Equiv.ofBijective
    (fun i ↦ (representative i : ConnectedComponents
      (Xᶜ : Set (StandardSphere 2)))) hrepresentative).symm⟩

/-- Lemma 64.3 (2): The frontiers of the complementary components are precisely
the four triangles obtained by omitting the edges incident to each vertex. -/
theorem frontier_range (X : Set (StandardSphere 2)) (e : R.Carrier ≃ₜ X) :
    Set.range (fun x : (Xᶜ : Set (StandardSphere 2)) ↦
      frontier (connectedComponentIn Xᶜ x)) =
      Set.range (R.oppositeBoundary X e) := by
  obtain ⟨representative, hrepresentative, hfrontier⟩ :=
    existsFourComplementaryRegions R X e
  ext S
  constructor
  · -- Surjectivity of the region representatives assigns every component
    -- the opposite triangle recorded by its representative.
    rintro ⟨x, rfl⟩
    obtain ⟨i, hi⟩ := hrepresentative.2
      (x : ConnectedComponents (Xᶜ : Set (StandardSphere 2)))
    refine ⟨i, ?_⟩
    have hcomponent := connectedComponentIn_eq_of_componentClass_eq
      (representative i) x hi
    exact (hfrontier i).symm.trans (congrArg frontier hcomponent)
  · -- Each indexed triangle occurs as the frontier of its chosen region.
    rintro ⟨i, rfl⟩
    exact ⟨representative i, hfrontier i⟩

end SimpleGraph.LinearRealization
