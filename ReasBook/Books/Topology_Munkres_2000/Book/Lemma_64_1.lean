module

public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Topology_Munkres_2000.Book.Definition_61_1.Separation
public import Topology_Munkres_2000.Book.Example_50_6.ComponentOmission
public import Topology_Munkres_2000.Book.Lemma_64_1.AmbientEdge
public import Topology_Munkres_2000.Book.Theorem_63_4
public import Topology_Munkres_2000.Book.Theorem_63_5

public section

open Set

namespace Topology.ThetaPresentation

/-- Helper for Lemma 64.1: an ambient theta edge has the expected interval
parameterization. -/
private def ambientArc {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (P : ThetaPresentation X) (i : Fin 3) : unitInterval → Y :=
  fun t ↦ P.arc i t

/-- Helper for Lemma 64.1: the ambient parameterization is an embedding. -/
private lemma ambientArc_isEmbedding
    {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (P : ThetaPresentation X) (i : Fin 3) :
    Topology.IsEmbedding (ambientArc P i) := by
  -- Compose the intrinsic edge embedding with the subtype inclusion.
  exact Topology.IsEmbedding.subtypeVal.comp (P.isEmbedding i)

/-- Helper for Lemma 64.1: the range of the ambient parameterization is the
ambient edge. -/
private lemma range_ambientArc
    {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (P : ThetaPresentation X) (i : Fin 3) :
    Set.range (ambientArc P i) = P.ambientEdge i := by
  -- Use the defining range equation exported by the ambient-edge owner.
  exact (P.ambientEdge_eq_range i).symm

/-- Helper for Lemma 64.1: an embedded interval range is closed and connected
in a Hausdorff ambient space. -/
private lemma embeddedArcRange_isClosed_isConnected
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (a : unitInterval → Y) (ha : Topology.IsEmbedding a) :
    IsClosed (Set.range a) ∧ IsConnected (Set.range a) := by
  constructor
  · -- Compactness of the interval gives closedness in the Hausdorff target.
    exact (isCompact_range ha.continuous).isClosed
  · -- The continuous image of the interval remains connected.
    exact isConnected_range ha.continuous

/-- Helper for Lemma 64.1: one half lies in the closed unit interval. -/
private lemma oneHalf_mem_unitInterval :
    (1 / 2 : ℝ) ∈ Set.Icc 0 1 := by
  -- Elementary arithmetic places the midpoint between the endpoints.
  norm_num

/-- Helper for Lemma 64.1: the fixed interior parameter used to distinguish
the three theta edges. -/
private noncomputable def arcMidpoint : unitInterval :=
  ⟨1 / 2, oneHalf_mem_unitInterval⟩

/-- Helper for Lemma 64.1: the fixed midpoint is not the initial parameter. -/
private lemma arcMidpoint_ne_zero : arcMidpoint ≠ 0 := by
  -- Equality of subtype values would force the false real equality `1/2 = 0`.
  intro h
  have hvalue := congrArg Subtype.val h
  norm_num [arcMidpoint] at hvalue

/-- Helper for Lemma 64.1: the fixed midpoint is not the terminal parameter. -/
private lemma arcMidpoint_ne_one : arcMidpoint ≠ 1 := by
  -- Equality of subtype values would force the false real equality `1/2 = 1`.
  intro h
  have hvalue := congrArg Subtype.val h
  norm_num [arcMidpoint] at hvalue

/-- Helper for Lemma 64.1: two embedded arcs with the same endpoints and no
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
  -- Inverse path parameters are continuous on their respective semicircles.
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
  -- Reversing the lower parameter makes the formulas agree at both endpoints.
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
  -- A cross-half collision can occur only at the shared circle endpoint.
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
  -- The compact-domain embedding is a homeomorphism onto the pasted range.
  rw [Topology.IsSimpleClosedCurve.iff_nonempty_homeomorph_circle]
  let hpastedEmbedding : Topology.IsEmbedding pasted :=
    hpastedContinuous.isClosedEmbedding hpastedInjective |>.isEmbedding
  exact ⟨(hpastedEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr hpastedRange)).symm⟩

/-- Helper for Lemma 64.1: in a set with exactly two components, the component
of a chosen point and the other component partition the set. -/
private lemma existsOtherComponentPartition
    {Y : Type*} [TopologicalSpace Y] (F : Set Y)
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
  · -- Every quotient class is either the class of `x` or the selected class.
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

/-- Helper for Lemma 64.1: a component is unchanged when a smaller ambient set
contains that component and is contained in the original set. -/
private lemma connectedComponentIn_eq_of_component_subset
    {Y : Type*} [TopologicalSpace Y] {F R : Set Y} {x : Y}
    (hx : x ∈ F) (hcomponent : connectedComponentIn F x ⊆ R)
    (hRF : R ⊆ F) :
    connectedComponentIn R x = connectedComponentIn F x := by
  -- The component containment first places the base point in the smaller set.
  have hxR : x ∈ R := hcomponent (mem_connectedComponentIn hx)
  apply Set.Subset.antisymm
  · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hxR)
      ((connectedComponentIn_subset R x).trans hRF)
  · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hx) hcomponent

/-- Helper for Lemma 64.1: two distinct components exhaust a space whose
component quotient has cardinality two. -/
private lemma connectedComponentIn_eq_or_eq_of_mk_eq_two
    {Y : Type*} [TopologicalSpace Y] (F : Set Y)
    (hcard : Cardinal.mk (ConnectedComponents F) = 2)
    {x x₀ x₁ : Y} (hx : x ∈ F) (hx₀ : x₀ ∈ F) (hx₁ : x₁ ∈ F)
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
  have componentEq {a b : Y} (ha : a ∈ F) (hb : b ∈ F)
      (hab : ((⟨a, ha⟩ : F) : ConnectedComponents F) =
        ((⟨b, hb⟩ : F) : ConnectedComponents F)) :
      connectedComponentIn F a = connectedComponentIn F b := by
    -- Taking ambient images transports equality of quotient components.
    rw [connectedComponentIn_eq_image ha, connectedComponentIn_eq_image hb]
    exact congrArg (Set.image Subtype.val) (ConnectedComponents.coe_eq_coe.mp hab)
  by_cases hclass : (xF : ConnectedComponents F) = x₀F
  · exact Or.inl (componentEq hx hx₀ hclass)
  · right
    have hxOther : (xF : ConnectedComponents F) = other := hunique xF hclass
    exact componentEq hx hx₁ (hxOther.trans hclass₁.symm)

/-- Helper for Lemma 64.1: adjoining a crosscut to the closure of the opposite
Jordan side leaves exactly the other two theta regions. -/
private lemma jordanSideUnionCrosscut_remainder
    (C A : Set (StandardSphere 2)) [Topology.IsSimpleClosedCurve C]
    (x : (Cᶜ : Set (StandardSphere 2)))
    (hAclosed : IsClosed A) (hAconnected : IsConnected A)
    (hAnonseparating : ¬ A.Separates)
    (p q : StandardSphere 2) (hpq : p ≠ q)
    (hinter : C ∩ A = {p, q})
    (hdisjoint : Disjoint (connectedComponentIn Cᶜ x) A) :
    (closure (connectedComponentIn Cᶜ x) ∪ A).SeparatesInto 2 ∧
      (closure (connectedComponentIn Cᶜ x) ∪ A)ᶜ =
        (C ∪ A)ᶜ \ connectedComponentIn Cᶜ x := by
  classical
  let V : Set (StandardSphere 2) := connectedComponentIn Cᶜ x
  -- Jordan's frontier theorem gives a stable normal form for the closed side.
  have hclosureV : closure V = V ∪ C := by
    rw [closure_eq_self_union_frontier, jordanCurveSphere_frontier_component C x]
  have hcomponents : Cardinal.mk (ConnectedComponents (Cᶜ : Set _)) = 2 :=
    Set.separatesInto_iff.mp (jordanCurveSphere_separatesInto C)
  obtain ⟨y, hVyDisjoint, hVyCover⟩ :=
    existsOtherComponentPartition Cᶜ hcomponents x
  let W : Set (StandardSphere 2) := connectedComponentIn Cᶜ y
  have hclosureVCompl : (closure V)ᶜ = W := by
    -- The complement of the selected closed side is the other Jordan component.
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
  have hVconnected : IsConnected (closure V) :=
    (isConnected_connectedComponentIn_iff.mpr x.property).closure
  have hVnonseparating : ¬ (closure V).Separates := by
    -- Connectedness of the other side witnesses nonseparation.
    intro hseparates
    apply Set.separates_iff.mp hseparates
    rw [hclosureVCompl]
    exact Subtype.preconnectedSpace
      (isConnected_connectedComponentIn_iff.mpr y.property).isPreconnected
  have hclosureInter : closure V ∩ A = {p, q} := by
    -- The selected side avoids the crosscut, leaving only the curve endpoints.
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
  · -- Theorem 63.5 counts the two components of the local remainder.
    exact union_separatesInto_two_of_inter_pair (closure V) A isClosed_closure
      hAclosed hVconnected hAconnected ⟨p, q, hpq, hclosureInter⟩
      hVnonseparating hAnonseparating
  · -- Expanding the closed side identifies the remainder set.
    rw [hclosureV]
    ext z
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_sdiff]
    tauto

/-- Helper for Lemma 64.1: the component opposite a third theta arc is also a
component of the two-edge complement, with frontier equal to those two edges. -/
private lemma existsPairArcComponent
    (arc : Fin 3 → unitInterval → StandardSphere 2)
    (harc : ∀ i, Topology.IsEmbedding (arc i))
    (p q : StandardSphere 2)
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
  let C : Set (StandardSphere 2) := Set.range (arc i) ∪ Set.range (arc j)
  let theta : Set (StandardSphere 2) := ⋃ l, Set.range (arc l)
  have hzeroPair : arc i 0 = arc j 0 := (hzero i).trans (hzero j).symm
  have honePair : arc i 1 = arc j 1 := (hone i).trans (hone j).symm
  have hinterPair : Set.range (arc i) ∩ Set.range (arc j) =
      {arc i 0, arc i 1} := by
    rw [hinter hij, hzero i, hone i]
  -- Local instance justification: the Jordan theorems consume the canonical
  -- circle structure supplied by the two pasted embedded arcs.
  letI : Topology.IsSimpleClosedCurve ↑C :=
    isSimpleClosedCurve_pairArcRanges (arc i) (arc j) (harc i) (harc j)
      hzeroPair honePair hinterPair
  have hcomponents : Cardinal.mk (ConnectedComponents (Cᶜ : Set _)) = 2 :=
    Set.separatesInto_iff.mp (jordanCurveSphere_separatesInto C)
  let t : unitInterval := arcMidpoint
  let y := arc k t
  let interiorArc : Set (StandardSphere 2) := Set.range (arc k) \ {p, q}
  have htZero : t ≠ 0 := arcMidpoint_ne_zero
  have htOne : t ≠ 1 := arcMidpoint_ne_one
  have hyInterior : y ∈ interiorArc := by
    refine ⟨Set.mem_range_self t, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro hyp
      exact htZero ((harc k).injective (hyp.trans (hzero k).symm))
    · intro hyq
      exact htOne ((harc k).injective (hyq.trans (hone k).symm))
  have hinteriorConnected : IsConnected interiorArc := by
    simpa only [interiorArc, hzero k, hone k] using
      embeddedArc_range_diff_endpoints_isConnected (arc k) (harc k)
  have hinteriorCcompl : interiorArc ⊆ Cᶜ := by
    rintro z ⟨hzk, hzEndpoints⟩
    rw [Set.mem_compl_iff]
    rintro (hzi | hzj)
    · have hzInter : z ∈ Set.range (arc k) ∩ Set.range (arc i) := ⟨hzk, hzi⟩
      rw [hinter hik.symm] at hzInter
      exact hzEndpoints hzInter
    · have hzInter : z ∈ Set.range (arc k) ∩ Set.range (arc j) := ⟨hzk, hzj⟩
      rw [hinter hjk.symm] at hzInter
      exact hzEndpoints hzInter
  let yC : (Cᶜ : Set (StandardSphere 2)) := ⟨y, hinteriorCcompl hyInterior⟩
  obtain ⟨x, hdisjoint, hpartition⟩ :=
    existsOtherComponentPartition Cᶜ hcomponents yC
  let U : Set (StandardSphere 2) := connectedComponentIn Cᶜ yC
  let V : Set (StandardSphere 2) := connectedComponentIn Cᶜ x
  have hinteriorU : interiorArc ⊆ U :=
    hinteriorConnected.2.subset_connectedComponentIn hyInterior hinteriorCcompl
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
  have hxV : (x : StandardSphere 2) ∈ V := mem_connectedComponentIn x.property
  have hxTheta : (x : StandardSphere 2) ∈ thetaᶜ := hVtheta hxV
  have hcomponentEq : connectedComponentIn thetaᶜ x = V := by
    apply Set.Subset.antisymm
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hxTheta)
        ((connectedComponentIn_subset thetaᶜ x).trans hthetaC)
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn hxV hVtheta
  refine ⟨x, hxTheta, hcomponentEq, ?_⟩
  -- The opposite theta component is unchanged from the selected Jordan side.
  rw [hcomponentEq]
  exact jordanCurveSphere_frontier_component C x

/-- Helper for Lemma 64.1: three embedded theta arcs have three controlled,
pair-bounded complementary components, and these exhaust all components. -/
private lemma existsThreeArcRegions
    (arc : Fin 3 → unitInterval → StandardSphere 2)
    (harc : ∀ i, Topology.IsEmbedding (arc i))
    (p q : StandardSphere 2) (hpq : p ≠ q)
    (hzero : ∀ i, arc i 0 = p) (hone : ∀ i, arc i 1 = q)
    (hinter : ∀ {i j}, i ≠ j →
      Set.range (arc i) ∩ Set.range (arc j) = {p, q}) :
    ∃ x₀ x₁ x₂,
      x₀ ∈ (⋃ i, Set.range (arc i))ᶜ ∧
      x₁ ∈ (⋃ i, Set.range (arc i))ᶜ ∧
      x₂ ∈ (⋃ i, Set.range (arc i))ᶜ ∧
      connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₀ =
        connectedComponentIn (Set.range (arc 1) ∪ Set.range (arc 2))ᶜ x₀ ∧
      frontier (connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₀) =
        Set.range (arc 1) ∪ Set.range (arc 2) ∧
      connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₁ =
        connectedComponentIn (Set.range (arc 0) ∪ Set.range (arc 2))ᶜ x₁ ∧
      frontier (connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₁) =
        Set.range (arc 0) ∪ Set.range (arc 2) ∧
      connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₂ =
        connectedComponentIn (Set.range (arc 0) ∪ Set.range (arc 1))ᶜ x₂ ∧
      frontier (connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₂) =
        Set.range (arc 0) ∪ Set.range (arc 1) ∧
      ∀ x, x ∈ (⋃ i, Set.range (arc i))ᶜ →
        connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x =
            connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₀ ∨
          connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x =
            connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₁ ∨
          connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x =
            connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₂ := by
  -- Local instance justification: the sphere chart supplies openness of
  -- complementary components used in the component comparison.
  letI : LocallyConnectedSpace (StandardSphere 2) :=
    ChartedSpace.locallyConnectedSpace
      (EuclideanSpace ℝ (Fin 2)) (StandardSphere 2)
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  -- Construct one component opposite each omitted arc.
  obtain ⟨x₀, hx₀, hcomponentPair₀, hfrontier₀⟩ :=
    existsPairArcComponent arc harc p q hzero hone hinter
      (i := 1) (j := 2) (k := 0) h12 h10 h20
  obtain ⟨x₁, hx₁, hcomponentPair₁, hfrontier₁⟩ :=
    existsPairArcComponent arc harc p q hzero hone hinter
      (i := 0) (j := 2) (k := 1) h02 h01 h21
  obtain ⟨x₂, hx₂, hcomponentPair₂, hfrontier₂⟩ :=
    existsPairArcComponent arc harc p q hzero hone hinter
      (i := 0) (j := 1) (k := 2) h01 h02 h12
  refine ⟨x₀, x₁, x₂, hx₀, hx₁, hx₂, hcomponentPair₀, hfrontier₀,
    hcomponentPair₁, hfrontier₁, hcomponentPair₂, hfrontier₂, ?_⟩
  intro x hx
  by_cases hcomponent₀ : connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x =
      connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₀
  · exact Or.inl hcomponent₀
  by_cases hcomponent₁ : connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x =
      connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₁
  · exact Or.inr (Or.inl hcomponent₁)
  by_cases hcomponent₂ : connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x =
      connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₂
  · exact Or.inr (Or.inr hcomponent₂)
  -- Route correction: direct global counting hides the controlled remainder.
  -- Remove the side opposite arc `2`; Theorem 63.5 counts that remainder.
  let C : Set (StandardSphere 2) := Set.range (arc 0) ∪ Set.range (arc 1)
  let A : Set (StandardSphere 2) := Set.range (arc 2)
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
  let x₂C : (Cᶜ : Set (StandardSphere 2)) := ⟨x₂, hthetaC hx₂⟩
  have hcomponentPair₂C :
      connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₂ =
        connectedComponentIn Cᶜ x₂C := by
    simpa only [C, x₂C] using hcomponentPair₂
  have hCzero : arc 0 0 = arc 1 0 := (hzero 0).trans (hzero 1).symm
  have hCone : arc 0 1 = arc 1 1 := (hone 0).trans (hone 1).symm
  have hCinter : Set.range (arc 0) ∩ Set.range (arc 1) =
      {arc 0 0, arc 0 1} := by
    rw [hinter h01, hzero 0, hone 0]
  -- Local instance justification: these two embedded arcs provide the Jordan
  -- curve required for the source's closed-side argument.
  letI : Topology.IsSimpleClosedCurve C :=
    isSimpleClosedCurve_pairArcRanges (arc 0) (arc 1) (harc 0) (harc 1)
      hCzero hCone hCinter
  -- Local instance justification: the third embedded range is canonically an arc.
  letI : Topology.IsArc A := ⟨⟨(harc 2).toHomeomorph.symm⟩⟩
  have hAgeometry : IsClosed A ∧ IsConnected A := by
    simpa only [A] using embeddedArcRange_isClosed_isConnected (arc 2) (harc 2)
  have hCAinter : C ∩ A = {p, q} := by
    ext z
    constructor
    · rintro ⟨hzC, hzA⟩
      rcases hzC with hz₀ | hz₁
      · have hzPair : z ∈ Set.range (arc 0) ∩ Set.range (arc 2) := ⟨hz₀, hzA⟩
        rw [hinter h02] at hzPair
        exact hzPair
      · have hzPair : z ∈ Set.range (arc 1) ∩ Set.range (arc 2) := ⟨hz₁, hzA⟩
        rw [hinter h12] at hzPair
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
  obtain ⟨hRtwo, hRident⟩ := jordanSideUnionCrosscut_remainder C A x₂C
    hAgeometry.1 hAgeometry.2 (arc_not_separates A) p q hpq hCAinter hV₂A
  let Remainder : Set (StandardSphere 2) :=
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
  let t : unitInterval := arcMidpoint
  have htZero : t ≠ 0 := arcMidpoint_ne_zero
  have htOne : t ≠ 1 := arcMidpoint_ne_one
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
    exact hmid.elim (hmidpointNotOther h10) (hmidpointNotOther h12)
  have hcomponent₀₂ :
      connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₀ ≠
        connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₂ := by
    intro heq
    have hfrontierEq := congrArg frontier heq
    rw [hfrontier₀, hfrontier₂] at hfrontierEq
    have hmid : arc 2 t ∈ Set.range (arc 1) ∪ Set.range (arc 2) :=
      Or.inr (Set.mem_range_self t)
    rw [hfrontierEq] at hmid
    exact hmid.elim (hmidpointNotOther h20) (hmidpointNotOther h21)
  have hcomponent₁₂ :
      connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₁ ≠
        connectedComponentIn (⋃ i, Set.range (arc i))ᶜ x₂ := by
    intro heq
    have hfrontierEq := congrArg frontier heq
    rw [hfrontier₁, hfrontier₂] at hfrontierEq
    have hmid : arc 2 t ∈ Set.range (arc 0) ∪ Set.range (arc 2) :=
      Or.inr (Set.mem_range_self t)
    rw [hfrontierEq] at hmid
    exact hmid.elim (hmidpointNotOther h20) (hmidpointNotOther h21)
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

/-- Helper for Lemma 64.1: equality of ambient complementary components gives
equality of their connected-component quotient classes. -/
private lemma connectedComponents_coe_eq_of_connectedComponentIn_eq
    {Y : Type*} [TopologicalSpace Y] {F : Set Y} (a b : F)
    (h : connectedComponentIn F a = connectedComponentIn F b) :
    (a : ConnectedComponents F) = b := by
  -- Put `a` in the ambient component of `b`, then lift that membership back.
  have ha : (a : Y) ∈ connectedComponentIn F b := h ▸ mem_connectedComponentIn a.property
  rw [connectedComponentIn_eq_image b.property] at ha
  obtain ⟨z, hz, hza⟩ := ha
  have hza' : z = a := Subtype.ext hza
  exact ConnectedComponents.coe_eq_coe'.mpr (hza' ▸ hz)

/-- Helper for Lemma 64.1: equality of connected-component quotient classes
gives equality of their ambient components. -/
private lemma connectedComponentIn_eq_of_connectedComponents_coe_eq
    {Y : Type*} [TopologicalSpace Y] {F : Set Y} (a b : F)
    (h : (a : ConnectedComponents F) = b) :
    connectedComponentIn F a = connectedComponentIn F b := by
  -- Equality of subtype components remains equality after ambient inclusion.
  rw [connectedComponentIn_eq_image a.property,
    connectedComponentIn_eq_image b.property]
  exact congrArg (Set.image Subtype.val) (ConnectedComponents.coe_eq_coe.mp h)

/-- Helper for Lemma 64.1: specialize the generic three-arc region interface
to the ambient edges of a theta presentation. -/
private lemma existsThreeRegions
    (X : Set (StandardSphere 2)) (P : ThetaPresentation X) :
    ∃ x₀ x₁ x₂ : (Xᶜ : Set (StandardSphere 2)),
      connectedComponentIn Xᶜ x₀ =
        connectedComponentIn (P.ambientEdge 1 ∪ P.ambientEdge 2)ᶜ x₀ ∧
      frontier (connectedComponentIn Xᶜ x₀) =
        P.ambientEdge 1 ∪ P.ambientEdge 2 ∧
      connectedComponentIn Xᶜ x₁ =
        connectedComponentIn (P.ambientEdge 0 ∪ P.ambientEdge 2)ᶜ x₁ ∧
      frontier (connectedComponentIn Xᶜ x₁) =
        P.ambientEdge 0 ∪ P.ambientEdge 2 ∧
      connectedComponentIn Xᶜ x₂ =
        connectedComponentIn (P.ambientEdge 0 ∪ P.ambientEdge 1)ᶜ x₂ ∧
      frontier (connectedComponentIn Xᶜ x₂) =
        P.ambientEdge 0 ∪ P.ambientEdge 1 ∧
      ∀ x : (Xᶜ : Set (StandardSphere 2)),
        connectedComponentIn Xᶜ x = connectedComponentIn Xᶜ x₀ ∨
          connectedComponentIn Xᶜ x = connectedComponentIn Xᶜ x₁ ∨
          connectedComponentIn Xᶜ x = connectedComponentIn Xᶜ x₂ := by
  let arc : Fin 3 → unitInterval → StandardSphere 2 := fun i ↦ ambientArc P i
  have harc : ∀ i, Topology.IsEmbedding (arc i) := by
    intro i
    exact ambientArc_isEmbedding P i
  have hzero : ∀ i, arc i 0 = (P.initial : StandardSphere 2) := by
    intro i
    simpa only [arc, ambientArc] using congrArg Subtype.val (P.map_zero i)
  have hone : ∀ i, arc i 1 = (P.terminal : StandardSphere 2) := by
    intro i
    simpa only [arc, ambientArc] using congrArg Subtype.val (P.map_one i)
  have hpq : (P.initial : StandardSphere 2) ≠ (P.terminal : StandardSphere 2) :=
    Subtype.val_injective.ne P.endpoint_ne
  have hinter : ∀ {i j}, i ≠ j →
      Set.range (arc i) ∩ Set.range (arc j) =
        {(P.initial : StandardSphere 2), (P.terminal : StandardSphere 2)} := by
    intro i j hij
    simpa only [arc, range_ambientArc] using
      P.ambientEdge_inter_ambientEdge i j hij
  have hcover : ⋃ i, Set.range (arc i) = X := by
    simpa only [arc, range_ambientArc] using P.iUnion_ambientEdge
  obtain ⟨x₀, x₁, x₂, hx₀, hx₁, hx₂, hpair₀, hfrontier₀,
      hpair₁, hfrontier₁, hpair₂, hfrontier₂, hexhaust⟩ :=
    existsThreeArcRegions arc harc (P.initial : StandardSphere 2)
      (P.terminal : StandardSphere 2) hpq hzero hone hinter
  -- Normalize the controlled union to the presented subspace before changing
  -- the three ambient witnesses into complement-subtype points.
  rw [hcover] at hx₀ hx₁ hx₂ hpair₀ hfrontier₀ hpair₁
  rw [hcover] at hfrontier₁ hpair₂ hfrontier₂ hexhaust
  let x₀' : (Xᶜ : Set (StandardSphere 2)) := ⟨x₀, hx₀⟩
  let x₁' : (Xᶜ : Set (StandardSphere 2)) := ⟨x₁, hx₁⟩
  let x₂' : (Xᶜ : Set (StandardSphere 2)) := ⟨x₂, hx₂⟩
  refine ⟨x₀', x₁', x₂', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [x₀', arc, range_ambientArc] using hpair₀
  · simpa only [x₀', arc, range_ambientArc] using hfrontier₀
  · simpa only [x₁', arc, range_ambientArc] using hpair₁
  · simpa only [x₁', arc, range_ambientArc] using hfrontier₁
  · simpa only [x₂', arc, range_ambientArc] using hpair₂
  · simpa only [x₂', arc, range_ambientArc] using hfrontier₂
  · intro x
    simpa only [x₀', x₁', x₂'] using hexhaust x x.property

/-- Lemma 64.1 (1): A theta subspace of the standard two-sphere separates it into
exactly three components. -/
theorem separatesInto (X : Set (StandardSphere 2)) (P : ThetaPresentation X) :
    X.SeparatesInto 3 := by
  classical
  -- Use the three source-controlled regions as representatives of all classes.
  obtain ⟨x₀, x₁, x₂, -, hfrontier₀, -, hfrontier₁, -, hfrontier₂,
      hexhaust⟩ := existsThreeRegions X P
  let t : unitInterval := arcMidpoint
  have htZero : t ≠ 0 := arcMidpoint_ne_zero
  have htOne : t ≠ 1 := arcMidpoint_ne_one
  have hzeroValue (i : Fin 3) :
      ambientArc P i 0 = (P.initial : StandardSphere 2) := by
    simpa only [ambientArc] using congrArg Subtype.val (P.map_zero i)
  have honeValue (i : Fin 3) :
      ambientArc P i 1 = (P.terminal : StandardSphere 2) := by
    simpa only [ambientArc] using congrArg Subtype.val (P.map_one i)
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have hmidpointNotOther {i j : Fin 3} (hij : i ≠ j) :
      ambientArc P i t ∉ P.ambientEdge j := by
    intro hmem
    have hcommon : ambientArc P i t ∈ P.ambientEdge i ∩ P.ambientEdge j :=
      ⟨range_ambientArc P i ▸ Set.mem_range_self t, hmem⟩
    rw [P.ambientEdge_inter_ambientEdge i j hij] at hcommon
    rcases hcommon with hcommon | hcommon
    · have hparameter : t = 0 := (ambientArc_isEmbedding P i).injective
          (hcommon.trans (hzeroValue i).symm)
      exact htZero hparameter
    · rw [Set.mem_singleton_iff] at hcommon
      have hparameter : t = 1 := (ambientArc_isEmbedding P i).injective
          (hcommon.trans (honeValue i).symm)
      exact htOne hparameter
  have hcomponent₀₁ : connectedComponentIn Xᶜ x₀ ≠
      connectedComponentIn Xᶜ x₁ := by
    intro heq
    have hfrontierEq := congrArg frontier heq
    rw [hfrontier₀, hfrontier₁] at hfrontierEq
    have hmid : ambientArc P 1 t ∈ P.ambientEdge 1 ∪ P.ambientEdge 2 :=
      Or.inl (range_ambientArc P 1 ▸ Set.mem_range_self t)
    rw [hfrontierEq] at hmid
    exact hmid.elim (hmidpointNotOther h10) (hmidpointNotOther h12)
  have hcomponent₀₂ : connectedComponentIn Xᶜ x₀ ≠
      connectedComponentIn Xᶜ x₂ := by
    intro heq
    have hfrontierEq := congrArg frontier heq
    rw [hfrontier₀, hfrontier₂] at hfrontierEq
    have hmid : ambientArc P 2 t ∈ P.ambientEdge 1 ∪ P.ambientEdge 2 :=
      Or.inr (range_ambientArc P 2 ▸ Set.mem_range_self t)
    rw [hfrontierEq] at hmid
    exact hmid.elim (hmidpointNotOther h20) (hmidpointNotOther h21)
  have hcomponent₁₂ : connectedComponentIn Xᶜ x₁ ≠
      connectedComponentIn Xᶜ x₂ := by
    intro heq
    have hfrontierEq := congrArg frontier heq
    rw [hfrontier₁, hfrontier₂] at hfrontierEq
    have hmid : ambientArc P 2 t ∈ P.ambientEdge 0 ∪ P.ambientEdge 2 :=
      Or.inr (range_ambientArc P 2 ▸ Set.mem_range_self t)
    rw [hfrontierEq] at hmid
    exact hmid.elim (hmidpointNotOther h20) (hmidpointNotOther h21)
  have hclass₀₁ :
      (x₀ : ConnectedComponents (Xᶜ : Set (StandardSphere 2))) ≠ x₁ := by
    intro h
    exact hcomponent₀₁
      (connectedComponentIn_eq_of_connectedComponents_coe_eq x₀ x₁ h)
  have hclass₀₂ :
      (x₀ : ConnectedComponents (Xᶜ : Set (StandardSphere 2))) ≠ x₂ := by
    intro h
    exact hcomponent₀₂
      (connectedComponentIn_eq_of_connectedComponents_coe_eq x₀ x₂ h)
  have hclass₁₂ :
      (x₁ : ConnectedComponents (Xᶜ : Set (StandardSphere 2))) ≠ x₂ := by
    intro h
    exact hcomponent₁₂
      (connectedComponentIn_eq_of_connectedComponents_coe_eq x₁ x₂ h)
  let representative : Fin 3 → (Xᶜ : Set (StandardSphere 2)) := ![x₀, x₁, x₂]
  let regionClass : Fin 3 →
      ConnectedComponents (Xᶜ : Set (StandardSphere 2)) := fun i ↦ representative i
  have hregionInjective : Function.Injective regionClass := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exfalso
      apply hclass₀₁
      simpa [regionClass, representative] using hij
    · exfalso
      apply hclass₀₂
      simpa [regionClass, representative] using hij
    · exfalso
      apply hclass₀₁
      simpa [regionClass, representative] using hij.symm
    · rfl
    · exfalso
      apply hclass₁₂
      simpa [regionClass, representative] using hij
    · exfalso
      apply hclass₀₂
      simpa [regionClass, representative] using hij.symm
    · exfalso
      apply hclass₁₂
      simpa [regionClass, representative] using hij.symm
    · rfl
  have hregionSurjective : Function.Surjective regionClass := by
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rcases hexhaust x with h | h | h
    · refine ⟨0, ?_⟩
      simpa [regionClass, representative] using
        (connectedComponents_coe_eq_of_connectedComponentIn_eq x x₀ h).symm
    · refine ⟨1, ?_⟩
      simpa [regionClass, representative] using
        (connectedComponents_coe_eq_of_connectedComponentIn_eq x x₁ h).symm
    · refine ⟨2, ?_⟩
      simpa [regionClass, representative] using
        (connectedComponents_coe_eq_of_connectedComponentIn_eq x x₂ h).symm
  -- The three exhaustive, distinct region classes give the required quotient size.
  rw [Set.separatesInto_iff, Cardinal.mk_eq_nat_iff]
  exact ⟨(Equiv.ofBijective regionClass
    ⟨hregionInjective, hregionSurjective⟩).symm⟩

/-- Lemma 64.1 (2): The frontiers of the three complementary components are the
three pairwise unions of the chosen edges. -/
theorem frontier_range (X : Set (StandardSphere 2)) (P : ThetaPresentation X) :
    Set.range (fun x : (Xᶜ : Set (StandardSphere 2)) ↦
      frontier (connectedComponentIn Xᶜ x)) =
      {P.ambientEdge 0 ∪ P.ambientEdge 1,
        P.ambientEdge 1 ∪ P.ambientEdge 2,
        P.ambientEdge 0 ∪ P.ambientEdge 2} := by
  -- Classify every component by the exhaustive three-region interface.
  obtain ⟨x₀, x₁, x₂, -, hfrontier₀, -, hfrontier₁, -, hfrontier₂,
      hexhaust⟩ := existsThreeRegions X P
  ext S
  constructor
  · rintro ⟨x, rfl⟩
    rcases hexhaust x with h | h | h
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inr (Or.inl ((congrArg frontier h).trans hfrontier₀))
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inr (Or.inr ((congrArg frontier h).trans hfrontier₁))
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inl ((congrArg frontier h).trans hfrontier₂)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl | rfl)
    · exact ⟨x₂, hfrontier₂⟩
    · exact ⟨x₀, hfrontier₀⟩
    · exact ⟨x₁, hfrontier₁⟩

/-- Lemma 64.1 (3): The complementary component bounded by the first two edges
is a component of the complement of their union. -/
theorem pairEdge_component (X : Set (StandardSphere 2)) (P : ThetaPresentation X) :
    ∃ x : (Xᶜ : Set (StandardSphere 2)),
      ∃ y : ((P.ambientEdge 0 ∪ P.ambientEdge 1)ᶜ : Set (StandardSphere 2)),
        frontier (connectedComponentIn Xᶜ x) = P.ambientEdge 0 ∪ P.ambientEdge 1 ∧
          connectedComponentIn Xᶜ x =
            connectedComponentIn (P.ambientEdge 0 ∪ P.ambientEdge 1)ᶜ y := by
  -- Select the region opposite the third edge and reuse its pair-complement identity.
  obtain ⟨-, -, x₂, -, -, -, -, hpair₂, hfrontier₂, -⟩ :=
    existsThreeRegions X P
  have hxPair : (x₂ : StandardSphere 2) ∈
      (P.ambientEdge 0 ∪ P.ambientEdge 1)ᶜ := by
    intro hx
    rcases hx with hx₀ | hx₁
    · exact x₂.property (P.ambientEdge_subset 0 hx₀)
    · exact x₂.property (P.ambientEdge_subset 1 hx₁)
  let y : ((P.ambientEdge 0 ∪ P.ambientEdge 1)ᶜ : Set (StandardSphere 2)) :=
    ⟨x₂, hxPair⟩
  exact ⟨x₂, y, hfrontier₂, hpair₂⟩

end Topology.ThetaPresentation
