module

public import Topology_Munkres_2000.Book.Theorem_63_5
public import Topology_Munkres_2000.Book.Theorem_63_4
public import Topology_Munkres_2000.Book.Example_50_6.ComponentOmission
public import Topology_Munkres_2000.Book.Theorem_63_6.JordanCrosscut

public section

open Set
open scoped Topology
private lemma embeddedArcPairUnion_homeomorphicCircle
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (a b : unitInterval → X) (ha : Topology.IsEmbedding a)
    (hb : Topology.IsEmbedding b) (hzero : a 0 = b 0)
    (hone : a 1 = b 1)
    (hinter : Set.range a ∩ Set.range b = {a 0, a 1}) :
    Nonempty (↥(Set.range a ∪ Set.range b) ≃ₜ Circle) := by
  classical
  -- Use the two standard closed semicircle paths as domains for the two arcs.
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
  have hcover : upper ∪ lower = Set.univ :=
    Circle.range_path_union_range_path (Circle.neg_ne_self 1).symm
  have hpathsInter : upper ∩ lower = {(1 : Circle), -1} :=
    Circle.range_path_inter_range_path (Circle.neg_ne_self 1).symm
  have hupperClosed : IsClosed upper :=
    (isCompact_range (Circle.path 1 (-1)).continuous).isClosed
  have hlowerClosed : IsClosed lower :=
    (isCompact_range (Circle.path (-1) 1).continuous).isClosed
  have hupperMapContinuous : ContinuousOn upperMap upper := by
    -- On the upper semicircle, the inverse path parameter is a homeomorphism.
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
    -- The lower semicircle uses the reversed interval parameter.
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
  have hmapsAgree : Set.EqOn upperMap lowerMap (upper ∩ lower) := by
    -- The endpoint equations make the two semicircle formulas agree on their overlap.
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
    -- Paste continuity across the two closed semicircles.
    rw [← continuousOn_univ, ← hcover]
    exact hpastedUpper.union_of_isClosed hpastedLower hupperClosed hlowerClosed
  have hpastedRange : Set.range pasted = Set.range a ∪ Set.range b := by
    -- Each half of the pasted map has exactly the corresponding arc range.
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
  have hcross (z w : Circle) (hzu : z ∈ upper) (hwl : w ∈ lower)
      (hwu : w ∉ upper) (hzw : pasted z = pasted w) : z = w := by
    -- Equality across opposite halves forces both images to be a common endpoint.
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
    -- Injectivity is immediate on each half and follows from `hcross` between halves.
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
          have hwCover : w ∈ upper ∪ lower := hcover.symm ▸ Set.mem_univ w
          exact hwCover.resolve_left hwu
        exact hcross z w hzu hwl hwu hzw
    · have hzl : z ∈ lower := by
        have hzCover : z ∈ upper ∪ lower := hcover.symm ▸ Set.mem_univ z
        exact hzCover.resolve_left hzu
      by_cases hwu : w ∈ upper
      · exact (hcross w z hwu hzl hzu hzw.symm).symm
      · have hwl : w ∈ lower := by
          have hwCover : w ∈ upper ∪ lower := hcover.symm ▸ Set.mem_univ w
          exact hwCover.resolve_left hwu
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
  -- A continuous injection from compact `Circle` is a homeomorphism onto its range.
  let hpastedEmbedding : Topology.IsEmbedding pasted :=
    hpastedContinuous.isClosedEmbedding hpastedInjective |>.isEmbedding
  exact ⟨(hpastedEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr hpastedRange)).symm⟩

/-- Helper for Theorem 63.6: oppositely oriented embedded paths meeting only at
their distinct endpoints have union homeomorphic to `Circle`. -/
theorem embeddedPathsUnion_homeomorphicCircle
    {X : Type*} [TopologicalSpace X] [T2Space X] {p q : X}
    (alpha : Path p q) (beta : Path q p)
    (halpha : Topology.IsEmbedding alpha) (hbeta : Topology.IsEmbedding beta)
    (hinter : Set.range alpha ∩ Set.range beta = {p, q}) :
    Nonempty (↥(Set.range alpha ∪ Set.range beta) ≃ₜ Circle) := by
  -- Reverse the second path so the generic arc-pasting lemma sees matching endpoints.
  let betaReverse : unitInterval → X := fun t ↦ beta (unitInterval.symm t)
  have hbetaReverseEmbedding : Topology.IsEmbedding betaReverse :=
    hbeta.comp unitInterval.symmHomeomorph.isEmbedding
  have hzero : alpha 0 = betaReverse 0 := by
    simp only [betaReverse, unitInterval.symm_zero, alpha.source, beta.target]
  have hone : alpha 1 = betaReverse 1 := by
    simp only [betaReverse, unitInterval.symm_one, alpha.target, beta.source]
  have hbetaReverseRange : Set.range betaReverse = Set.range beta := by
    apply Set.Subset.antisymm
    · rintro y ⟨t, rfl⟩
      exact ⟨unitInterval.symm t, rfl⟩
    · rintro y ⟨t, rfl⟩
      refine ⟨unitInterval.symm t, ?_⟩
      simp only [betaReverse, unitInterval.symm_symm]
  have hinterReverse :
      Set.range alpha ∩ Set.range betaReverse = {alpha 0, alpha 1} := by
    calc
      Set.range alpha ∩ Set.range betaReverse =
          Set.range alpha ∩ Set.range beta :=
        congrArg (fun S ↦ Set.range alpha ∩ S) hbetaReverseRange
      _ = {p, q} := hinter
      _ = {alpha 0, alpha 1} := by rw [alpha.source, alpha.target]
  obtain ⟨e⟩ := embeddedArcPairUnion_homeomorphicCircle alpha betaReverse
    halpha hbetaReverseEmbedding hzero hone hinterReverse
  have hUnion : Set.range alpha ∪ Set.range betaReverse =
      Set.range alpha ∪ Set.range beta :=
    congrArg (fun S ↦ Set.range alpha ∪ S) hbetaReverseRange
  exact ⟨(Homeomorph.setCongr hUnion).symm.trans e⟩

namespace Topology.IsSimpleClosedCurve

/-- Helper for Theorem 63.6: a simple closed curve splits into two embedded
ambient paths with prescribed distinct endpoints and no other common point. -/
theorem existsTwoEmbeddedPathDecomposition
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (D : Set X) [Topology.IsSimpleClosedCurve D]
    (p q : D) (hpq : p ≠ q) :
    ∃ alpha : Path (p : X) (q : X), ∃ beta : Path (q : X) (p : X),
      Topology.IsEmbedding alpha ∧ Topology.IsEmbedding beta ∧
        Set.range alpha ∪ Set.range beta = D ∧
        Set.range alpha ∩ Set.range beta = {(p : X), (q : X)} := by
  classical
  -- Transport the two directed circle arcs through a chosen curve homeomorphism.
  obtain ⟨e⟩ := Topology.IsSimpleClosedCurve.homeomorphic_circle (X := D)
  let f : Circle → X := fun z ↦ (e.symm z : X)
  have hfContinuous : Continuous f := continuous_subtype_val.comp e.symm.continuous
  have hfInjective : Function.Injective f :=
    Subtype.val_injective.comp e.symm.injective
  have hepq : e p ≠ e q := fun h ↦ hpq (e.injective h)
  have hfirstContinuous : Continuous (f ∘ Circle.path (e p) (e q)) :=
    hfContinuous.comp (Circle.path (e p) (e q)).continuous
  have hsecondContinuous : Continuous (f ∘ Circle.path (e q) (e p)) :=
    hfContinuous.comp (Circle.path (e q) (e p)).continuous
  have hfirstSource : (f ∘ Circle.path (e p) (e q)) 0 = (p : X) := by
    simp only [Function.comp_apply, Path.source, f, Homeomorph.symm_apply_apply]
  have hfirstTarget : (f ∘ Circle.path (e p) (e q)) 1 = (q : X) := by
    simp only [Function.comp_apply, Path.target, f, Homeomorph.symm_apply_apply]
  have hsecondSource : (f ∘ Circle.path (e q) (e p)) 0 = (q : X) := by
    simp only [Function.comp_apply, Path.source, f, Homeomorph.symm_apply_apply]
  have hsecondTarget : (f ∘ Circle.path (e q) (e p)) 1 = (p : X) := by
    simp only [Function.comp_apply, Path.target, f, Homeomorph.symm_apply_apply]
  let alpha : Path (p : X) (q : X) :=
    { toContinuousMap := ⟨f ∘ Circle.path (e p) (e q), hfirstContinuous⟩
      source' := hfirstSource
      target' := hfirstTarget }
  let beta : Path (q : X) (p : X) :=
    { toContinuousMap := ⟨f ∘ Circle.path (e q) (e p), hsecondContinuous⟩
      source' := hsecondSource
      target' := hsecondTarget }
  have halphaCoe : (alpha : unitInterval → X) = f ∘ Circle.path (e p) (e q) := rfl
  have hbetaCoe : (beta : unitInterval → X) = f ∘ Circle.path (e q) (e p) := rfl
  have halphaInjective : Function.Injective alpha := by
    rw [halphaCoe]
    exact hfInjective.comp (Circle.path_injective_of_ne hepq)
  have hbetaInjective : Function.Injective beta := by
    rw [hbetaCoe]
    exact hfInjective.comp (Circle.path_injective_of_ne hepq.symm)
  have halphaEmbedding : Topology.IsEmbedding alpha :=
    alpha.continuous.isClosedEmbedding halphaInjective |>.isEmbedding
  have hbetaEmbedding : Topology.IsEmbedding beta :=
    beta.continuous.isClosedEmbedding hbetaInjective |>.isEmbedding
  have hfRange : Set.range f = D := by
    apply Set.Subset.antisymm
    · rintro y ⟨z, rfl⟩
      exact (e.symm z).property
    · intro y hy
      refine ⟨e ⟨y, hy⟩, ?_⟩
      simp only [f, Homeomorph.symm_apply_apply]
  have hUnion : Set.range alpha ∪ Set.range beta = D := by
    -- The two canonical circle paths cover all of `Circle`.
    rw [halphaCoe, hbetaCoe, Set.range_comp, Set.range_comp, ← Set.image_union,
      Circle.range_path_union_range_path hepq, Set.image_univ, hfRange]
  have hInter :
      Set.range alpha ∩ Set.range beta = {(p : X), (q : X)} := by
    -- Injectivity of the ambient parameterization transports the endpoint intersection.
    rw [halphaCoe, hbetaCoe, Set.range_comp, Set.range_comp,
      ← Set.image_inter hfInjective,
      Circle.range_path_inter_range_path hepq, Set.image_pair]
    simp only [f, Homeomorph.symm_apply_apply]
  exact ⟨alpha, beta, halphaEmbedding, hbetaEmbedding, hUnion, hInter⟩

end Topology.IsSimpleClosedCurve

namespace JordanCrosscut

/-- Helper for Theorem 63.6: a Jordan crosscut has an ambient embedded path
parameterization with exactly its carrier as range. -/
theorem existsEmbeddedPath
    {X : Type*} [TopologicalSpace X]
    {U : Set X} {p q : X} (gamma : JordanCrosscut U p q) :
    ∃ crosscut : Path p q,
      Topology.IsEmbedding crosscut ∧ Set.range crosscut = gamma.carrier := by
  let crosscutMap : unitInterval → X :=
    fun t ↦ (gamma.parameterization t : X)
  have hcrosscutEmbedding : Topology.IsEmbedding crosscutMap :=
    Topology.IsEmbedding.subtypeVal.comp gamma.parameterization.isEmbedding
  have hcrosscutSource : crosscutMap 0 = p := gamma.source_eq
  have hcrosscutTarget : crosscutMap 1 = q := gamma.target_eq
  let crosscut : Path p q :=
    { toContinuousMap := ⟨crosscutMap, hcrosscutEmbedding.continuous⟩
      source' := hcrosscutSource
      target' := hcrosscutTarget }
  have hcrosscutCoe : (crosscut : unitInterval → X) = crosscutMap := rfl
  have hcrosscutRange : Set.range crosscut = gamma.carrier := by
    -- Surjectivity of the carrier parameterization identifies its ambient range.
    rw [hcrosscutCoe]
    apply Set.Subset.antisymm
    · rintro y ⟨t, rfl⟩
      exact (gamma.parameterization t).property
    · intro y hy
      obtain ⟨t, ht⟩ := gamma.parameterization.surjective ⟨y, hy⟩
      exact ⟨t, congrArg Subtype.val ht⟩
  exact ⟨crosscut, hcrosscutEmbedding, hcrosscutRange⟩

/-- Helper for Theorem 63.6: the frontier arcs determined by a crosscut's
endpoints each meet the crosscut exactly in those endpoints. -/
theorem existsBoundaryArcDecomposition
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {U : Set X} {p q : X} (gamma : JordanCrosscut U p q) (hpq : p ≠ q)
    [Topology.IsSimpleClosedCurve (frontier U)] :
    ∃ A₁ A₂ : Set X,
      frontier U = A₁ ∪ A₂ ∧ A₁ ∩ A₂ = {p, q} ∧
        IsClosed A₁ ∧ IsClosed A₂ ∧ IsConnected A₁ ∧ IsConnected A₂ ∧
        Topology.IsArc A₁ ∧ Topology.IsArc A₂ ∧
        gamma.carrier ∩ A₁ = {p, q} ∧ gamma.carrier ∩ A₂ = {p, q} := by
  -- Package the frontier endpoints for the prescribed-endpoint curve decomposition.
  have hendpoints := gamma.endpoints_mem_frontier
  let pFrontier : frontier U := ⟨p, hendpoints.1⟩
  let qFrontier : frontier U := ⟨q, hendpoints.2⟩
  have hpqFrontier : pFrontier ≠ qFrontier := by
    intro h
    exact hpq (congrArg Subtype.val h)
  obtain ⟨A₁, A₂, hUnion, hInter, hA₁Closed, hA₂Closed,
      hA₁Connected, hA₂Connected, hA₁Arc, hA₂Arc⟩ :=
    Topology.IsSimpleClosedCurve.existsTwoArcDecomposition
      (frontier U) pFrontier qFrontier hpqFrontier
  have hA₁Subset : A₁ ⊆ frontier U := by
    intro y hy
    rw [hUnion]
    exact Or.inl hy
  have hA₂Subset : A₂ ⊆ frontier U := by
    intro y hy
    rw [hUnion]
    exact Or.inr hy
  have hcarrierA₁ : gamma.carrier ∩ A₁ = {p, q} := by
    -- Restrict the crosscut-frontier equation to the first frontier arc.
    apply Set.Subset.antisymm
    · intro y hy
      rw [← gamma.carrier_inter_frontier]
      exact ⟨hy.1, hA₁Subset hy.2⟩
    · intro y hy
      have hyCarrierFrontier : y ∈ gamma.carrier ∩ frontier U := by
        rw [gamma.carrier_inter_frontier]
        exact hy
      have hyBoth : y ∈ A₁ ∩ A₂ := by
        rw [hInter]
        exact hy
      exact ⟨hyCarrierFrontier.1, hyBoth.1⟩
  have hcarrierA₂ : gamma.carrier ∩ A₂ = {p, q} := by
    -- The same endpoint argument applies to the second frontier arc.
    apply Set.Subset.antisymm
    · intro y hy
      rw [← gamma.carrier_inter_frontier]
      exact ⟨hy.1, hA₂Subset hy.2⟩
    · intro y hy
      have hyCarrierFrontier : y ∈ gamma.carrier ∩ frontier U := by
        rw [gamma.carrier_inter_frontier]
        exact hy
      have hyBoth : y ∈ A₁ ∩ A₂ := by
        rw [hInter]
        exact hy
      exact ⟨hyCarrierFrontier.1, hyBoth.2⟩
  exact ⟨A₁, A₂, hUnion, hInter, hA₁Closed, hA₂Closed,
    hA₁Connected, hA₂Connected, hA₁Arc, hA₂Arc, hcarrierA₁, hcarrierA₂⟩

/-- Helper for Theorem 63.6: a Jordan crosscut together with either of the two
frontier arcs between its endpoints forms a simple closed curve. -/
theorem existsSideJordanCurves
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {U : Set X} {p q : X} (gamma : JordanCrosscut U p q) (hpq : p ≠ q)
    [Topology.IsSimpleClosedCurve (frontier U)] :
    ∃ A₁ A₂ : Set X,
      frontier U = A₁ ∪ A₂ ∧ A₁ ∩ A₂ = {p, q} ∧
        Topology.IsArc A₁ ∧ Topology.IsArc A₂ ∧
        Nonempty (↥(gamma.carrier ∪ A₁) ≃ₜ Circle) ∧
        Nonempty (↥(gamma.carrier ∪ A₂) ≃ₜ Circle) := by
  -- Choose the two canonical embedded frontier paths between the crosscut endpoints.
  have hendpoints := gamma.endpoints_mem_frontier
  let pFrontier : frontier U := ⟨p, hendpoints.1⟩
  let qFrontier : frontier U := ⟨q, hendpoints.2⟩
  have hpqFrontier : pFrontier ≠ qFrontier := by
    intro h
    exact hpq (congrArg Subtype.val h)
  obtain ⟨alpha, beta, halpha, hbeta, hUnion, hInter⟩ :=
    Topology.IsSimpleClosedCurve.existsTwoEmbeddedPathDecomposition
      (frontier U) pFrontier qFrontier hpqFrontier
  obtain ⟨crosscut, hcrosscutEmbedding, hcrosscutRange⟩ :=
    gamma.existsEmbeddedPath
  have halphaSubset : Set.range alpha ⊆ frontier U := by
    intro y hy
    rw [← hUnion]
    exact Or.inl hy
  have hbetaSubset : Set.range beta ⊆ frontier U := by
    intro y hy
    rw [← hUnion]
    exact Or.inr hy
  have hcarrierAlpha :
      gamma.carrier ∩ Set.range alpha = {p, q} := by
    -- A boundary path can meet the crosscut only at the two frontier endpoints.
    apply Set.Subset.antisymm
    · intro y hy
      rw [← gamma.carrier_inter_frontier]
      exact ⟨hy.1, halphaSubset hy.2⟩
    · intro y hy
      have hyCarrierFrontier : y ∈ gamma.carrier ∩ frontier U := by
        rw [gamma.carrier_inter_frontier]
        exact hy
      have hyBoth : y ∈ Set.range alpha ∩ Set.range beta := by
        rw [hInter]
        exact hy
      exact ⟨hyCarrierFrontier.1, hyBoth.1⟩
  have hcarrierBeta :
      gamma.carrier ∩ Set.range beta = {p, q} := by
    -- The same frontier calculation controls the opposite boundary path.
    apply Set.Subset.antisymm
    · intro y hy
      rw [← gamma.carrier_inter_frontier]
      exact ⟨hy.1, hbetaSubset hy.2⟩
    · intro y hy
      have hyCarrierFrontier : y ∈ gamma.carrier ∩ frontier U := by
        rw [gamma.carrier_inter_frontier]
        exact hy
      have hyBoth : y ∈ Set.range alpha ∩ Set.range beta := by
        rw [hInter]
        exact hy
      exact ⟨hyCarrierFrontier.1, hyBoth.2⟩
  have hcrosscutAlpha :
      Set.range crosscut ∩ Set.range alpha = {p, q} := by
    rw [hcrosscutRange]
    exact hcarrierAlpha
  have hcrosscutBeta :
      Set.range crosscut ∩ Set.range beta = {p, q} := by
    rw [hcrosscutRange]
    exact hcarrierBeta
  have halphaSymmEmbedding : Topology.IsEmbedding alpha.symm := by
    exact halpha.comp unitInterval.symmHomeomorph.isEmbedding
  have hcrosscutAlphaSymm :
      Set.range crosscut ∩ Set.range alpha.symm = {p, q} := by
    rw [Path.symm_range]
    exact hcrosscutAlpha
  obtain ⟨hside₁⟩ := embeddedPathsUnion_homeomorphicCircle
    crosscut alpha.symm hcrosscutEmbedding halphaSymmEmbedding hcrosscutAlphaSymm
  obtain ⟨hside₂⟩ := embeddedPathsUnion_homeomorphicCircle
    crosscut beta hcrosscutEmbedding hbeta hcrosscutBeta
  have hside₁Set : Set.range crosscut ∪ Set.range alpha.symm =
      gamma.carrier ∪ Set.range alpha := by
    rw [hcrosscutRange, Path.symm_range]
  have hside₂Set : Set.range crosscut ∪ Set.range beta =
      gamma.carrier ∪ Set.range beta := by
    rw [hcrosscutRange]
  have hside₁Homeomorph :
      Nonempty (↥(gamma.carrier ∪ Set.range alpha) ≃ₜ Circle) :=
    ⟨(Homeomorph.setCongr hside₁Set).symm.trans hside₁⟩
  have hside₂Homeomorph :
      Nonempty (↥(gamma.carrier ∪ Set.range beta) ≃ₜ Circle) :=
    ⟨(Homeomorph.setCongr hside₂Set).symm.trans hside₂⟩
  have halphaArc : Topology.IsArc (Set.range alpha) :=
    ⟨⟨halpha.toHomeomorph.symm⟩⟩
  have hbetaArc : Topology.IsArc (Set.range beta) :=
    ⟨⟨hbeta.toHomeomorph.symm⟩⟩
  exact ⟨Set.range alpha, Set.range beta, hUnion.symm, hInter,
    halphaArc, hbetaArc, hside₁Homeomorph, hside₂Homeomorph⟩

end JordanCrosscut

namespace Schoenflies

/-- Helper for Theorem 63.6: when a set has exactly two connected components,
the component of a chosen point and the other component partition the set. -/
theorem existsOtherComponentPartition
    {X : Type*} [TopologicalSpace X] (F : Set X)
    (hF : Cardinal.mk (ConnectedComponents F) = 2) (x : F) :
    ∃ y : F, Disjoint (connectedComponentIn F x) (connectedComponentIn F y) ∧
      connectedComponentIn F x ∪ connectedComponentIn F y = F := by
  classical
  -- Select the unique quotient component different from the class of `x`.
  obtain ⟨q, hqx, hqunique⟩ :=
    (Cardinal.mk_eq_two_iff' (ConnectedComponents.mk x)).mp hF
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe q
  have hxy : (x : ConnectedComponents F) ≠ y := hqx.symm
  have hcomponentDisjoint : Disjoint (connectedComponent x) (connectedComponent y) :=
    connectedComponent_disjoint (ConnectedComponents.coe_ne_coe.mp hxy)
  refine ⟨y, ?_, ?_⟩
  · -- Injectivity of subtype inclusion transports disjointness to the ambient space.
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

/-- Helper for Theorem 63.6: restricting the ambient set around a whole
connected component does not change that component. -/
theorem connectedComponentIn_eq_of_component_subset
    {X : Type*} [TopologicalSpace X] {F R : Set X} {x : X}
    (hx : x ∈ F) (hcomponent : connectedComponentIn F x ⊆ R)
    (hRF : R ⊆ F) :
    connectedComponentIn R x = connectedComponentIn F x := by
  have hxR : x ∈ R := hcomponent (mem_connectedComponentIn hx)
  -- Maximality in each ambient set supplies the two inclusions.
  apply Set.Subset.antisymm
  · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hxR)
      ((connectedComponentIn_subset R x).trans hRF)
  · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hx) hcomponent

/-- Helper for Theorem 63.6: in a two-component set, two known distinct
components exhaust the component of every point. -/
theorem connectedComponentIn_eq_or_eq_of_mk_eq_two
    {X : Type*} [TopologicalSpace X] (F : Set X)
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
  obtain ⟨other, -, hunique⟩ :=
    (Cardinal.mk_eq_two_iff' (ConnectedComponents.mk x₀F)).mp hcard
  have hclass₁ : (x₁F : ConnectedComponents F) = other :=
    hunique x₁F hclass₁ne
  have componentEq {a b : X} (ha : a ∈ F) (hb : b ∈ F)
      (hab : ((⟨a, ha⟩ : F) : ConnectedComponents F) =
        ((⟨b, hb⟩ : F) : ConnectedComponents F)) :
      connectedComponentIn F a = connectedComponentIn F b := by
    -- Taking ambient images converts quotient-class equality back to components.
    rw [connectedComponentIn_eq_image ha, connectedComponentIn_eq_image hb]
    exact congrArg (Set.image Subtype.val) (ConnectedComponents.coe_eq_coe.mp hab)
  by_cases hclass : (xF : ConnectedComponents F) = x₀F
  · exact Or.inl (componentEq hx hx₀ hclass)
  · right
    have hxOther : (xF : ConnectedComponents F) = other := hunique xF hclass
    exact componentEq hx hx₁ (hxOther.trans hclass₁.symm)

/-- Helper for Theorem 63.6: two distinct connected components exhaust a set
that has exactly two connected components. -/
theorem union_eq_of_two_connectedComponents
    {X : Type*} [TopologicalSpace X] {F U V : Set X}
    (hcard : Cardinal.mk (ConnectedComponents F) = 2)
    (hU : IsConnectedComponentIn F U) (hV : IsConnectedComponentIn F V)
    (hne : U ≠ V) :
    U ∪ V = F := by
  -- Choose representatives so the two-component classification applies directly.
  obtain ⟨x, hxU⟩ := hU.nonempty
  obtain ⟨y, hyV⟩ := hV.nonempty
  have hx : x ∈ F := hU.subset hxU
  have hy : y ∈ F := hV.subset hyV
  have hUeq : U = connectedComponentIn F x :=
    hU.eq_connectedComponentIn hxU
  have hVeq : V = connectedComponentIn F y :=
    hV.eq_connectedComponentIn hyV
  have hcomponentNe : connectedComponentIn F x ≠ connectedComponentIn F y := by
    intro hxy
    exact hne (hUeq.trans (hxy.trans hVeq.symm))
  apply Set.Subset.antisymm
  · exact Set.union_subset hU.subset hV.subset
  · intro z hz
    rcases connectedComponentIn_eq_or_eq_of_mk_eq_two
        F hcard hz hx hy hcomponentNe with hzX | hzY
    · left
      rw [hUeq, ← hzX]
      exact mem_connectedComponentIn hz
    · right
      rw [hVeq, ← hzY]
      exact mem_connectedComponentIn hz

/-- Helper for Theorem 63.6: adjoining an endpoint-only crosscut to the closure
of the opposite Jordan side leaves exactly two complementary components. -/
theorem oppositeJordanComponent_remainder
    (C A : Set (StandardSphere 2))
    (hCcurve : Topology.IsSimpleClosedCurve C)
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
  have hclosureV : closure V = V ∪ C := by
    -- Jordan's frontier theorem gives a stable normal form for the closed side.
    rw [closure_eq_self_union_frontier,
      @jordanCurveSphere_frontier_component C hCcurve x]
  have hcomponents : Cardinal.mk (ConnectedComponents (Cᶜ : Set _)) = 2 :=
    Set.separatesInto_iff.mp (@jordanCurveSphere_separatesInto C hCcurve)
  obtain ⟨y, hVyDisjoint, hVyCover⟩ :=
    Schoenflies.existsOtherComponentPartition Cᶜ hcomponents x
  let W : Set (StandardSphere 2) := connectedComponentIn Cᶜ y
  have hclosureVCompl : (closure V)ᶜ = W := by
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
    -- The complement is the other connected Jordan component.
    intro hseparates
    apply Set.separates_iff.mp hseparates
    rw [hclosureVCompl]
    exact Subtype.preconnectedSpace
      (isConnected_connectedComponentIn_iff.mpr y.property).isPreconnected
  have hclosureInter : closure V ∩ A = {p, q} := by
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
  · -- Expanding the closed side identifies the remainder inside the theta complement.
    rw [hclosureV]
    ext z
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_sdiff]
    tauto

/-- Helper for Theorem 63.6: three embedded spherical paths with common distinct
endpoints and pairwise endpoint-only intersections form a parameterized theta graph. -/
structure SphericalThetaTriple (p q : StandardSphere 2) where
  endpoint_ne : p ≠ q
  arm : Fin 3 → Path p q
  arm_embedding : ∀ i, Topology.IsEmbedding (arm i)
  arm_inter : ∀ {i j}, i ≠ j → Set.range (arm i) ∩ Set.range (arm j) = {p, q}

namespace SphericalThetaTriple

/-- Helper for Theorem 63.6: the carrier of a spherical theta triple is the
union of its three embedded arms. -/
def carrier {p q : StandardSphere 2} (T : SphericalThetaTriple p q) :
    Set (StandardSphere 2) :=
  Set.range (T.arm 0) ∪ Set.range (T.arm 1) ∪ Set.range (T.arm 2)

/-- Helper for Theorem 63.6: the pair-carrier opposite an arm is the union of
the other two arms. -/
def pairCarrier {p q : StandardSphere 2} (T : SphericalThetaTriple p q) :
    Fin 3 → Set (StandardSphere 2) :=
  fun i ↦ if i = 0 then Set.range (T.arm 1) ∪ Set.range (T.arm 2)
    else if i = 1 then Set.range (T.arm 0) ∪ Set.range (T.arm 2)
    else Set.range (T.arm 0) ∪ Set.range (T.arm 1)

/-- Helper for Theorem 63.6: every arm of a spherical theta triple is an arc. -/
theorem arm_isArc {p q : StandardSphere 2} (T : SphericalThetaTriple p q)
    (i : Fin 3) : Topology.IsArc (Set.range (T.arm i)) := by
  -- The embedding homeomorphism identifies the arm range with the unit interval.
  exact ⟨⟨(T.arm_embedding i).toHomeomorph.symm⟩⟩

/-- Helper for Theorem 63.6: every arm of a spherical theta triple is closed. -/
theorem arm_isClosed {p q : StandardSphere 2} (T : SphericalThetaTriple p q)
    (i : Fin 3) : IsClosed (Set.range (T.arm i)) := by
  -- Compactness of the parameter interval makes the continuous path range closed.
  exact (isCompact_range (T.arm i).continuous).isClosed

/-- Helper for Theorem 63.6: every arm of a spherical theta triple is connected. -/
theorem arm_isConnected {p q : StandardSphere 2} (T : SphericalThetaTriple p q)
    (i : Fin 3) : IsConnected (Set.range (T.arm i)) := by
  -- A continuous image of the connected unit interval remains connected.
  exact isConnected_range (T.arm i).continuous

/-- Helper for Theorem 63.6: every arm of a spherical theta triple is
nonseparating in the two-sphere. -/
theorem arm_not_separates {p q : StandardSphere 2} (T : SphericalThetaTriple p q)
    (i : Fin 3) : ¬ (Set.range (T.arm i)).Separates := by
  -- Apply arc nonseparation after installing the canonical range arc.
  letI : Topology.IsArc (Set.range (T.arm i)) := T.arm_isArc i
  exact arc_not_separates (Set.range (T.arm i))

/-- Helper for Theorem 63.6: each pair-carrier of a spherical theta triple is
homeomorphic to the circle. -/
theorem pairCarrier_homeomorphicCircle {p q : StandardSphere 2}
    (T : SphericalThetaTriple p q) (i : Fin 3) :
    Nonempty (↥(T.pairCarrier i) ≃ₜ Circle) := by
  -- Enumerate the omitted arm and paste the remaining oppositely oriented paths.
  fin_cases i
  · have hinter : Set.range (T.arm 1) ∩ Set.range (T.arm 2).symm = {p, q} := by
      rw [Path.symm_range]
      exact T.arm_inter (by decide)
    obtain ⟨e⟩ := embeddedPathsUnion_homeomorphicCircle (T.arm 1) (T.arm 2).symm
      (T.arm_embedding 1)
      ((T.arm_embedding 2).comp unitInterval.symmHomeomorph.isEmbedding) hinter
    have hcarrier : Set.range (T.arm 1) ∪ Set.range (T.arm 2).symm =
        T.pairCarrier 0 := by
      rw [Path.symm_range]
      rfl
    exact ⟨(Homeomorph.setCongr hcarrier).symm.trans e⟩
  · have hinter : Set.range (T.arm 0) ∩ Set.range (T.arm 2).symm = {p, q} := by
      rw [Path.symm_range]
      exact T.arm_inter (by decide)
    obtain ⟨e⟩ := embeddedPathsUnion_homeomorphicCircle (T.arm 0) (T.arm 2).symm
      (T.arm_embedding 0)
      ((T.arm_embedding 2).comp unitInterval.symmHomeomorph.isEmbedding) hinter
    have hcarrier : Set.range (T.arm 0) ∪ Set.range (T.arm 2).symm =
        T.pairCarrier 1 := by
      rw [Path.symm_range]
      rfl
    exact ⟨(Homeomorph.setCongr hcarrier).symm.trans e⟩
  · have hinter : Set.range (T.arm 0) ∩ Set.range (T.arm 1).symm = {p, q} := by
      rw [Path.symm_range]
      exact T.arm_inter (by decide)
    obtain ⟨e⟩ := embeddedPathsUnion_homeomorphicCircle (T.arm 0) (T.arm 1).symm
      (T.arm_embedding 0)
      ((T.arm_embedding 1).comp unitInterval.symmHomeomorph.isEmbedding) hinter
    have hcarrier : Set.range (T.arm 0) ∪ Set.range (T.arm 1).symm =
        T.pairCarrier 2 := by
      rw [Path.symm_range]
      rfl
    exact ⟨(Homeomorph.setCongr hcarrier).symm.trans e⟩

/-- Helper for Theorem 63.6: every pair-carrier of a spherical theta triple is
a simple closed curve. -/
theorem pairCarrier_isSimpleClosedCurve {p q : StandardSphere 2}
    (T : SphericalThetaTriple p q) (i : Fin 3) :
    Topology.IsSimpleClosedCurve (T.pairCarrier i) := by
  -- Use the defining circle-homeomorphism characterization.
  exact (Topology.IsSimpleClosedCurve.iff_nonempty_homeomorph_circle
    (T.pairCarrier i)).mpr (T.pairCarrier_homeomorphicCircle i)

/-- Helper for Theorem 63.6: adding the omitted arm back to its pair-carrier
recovers the full theta carrier. -/
theorem pairCarrier_union_arm {p q : StandardSphere 2}
    (T : SphericalThetaTriple p q) (i : Fin 3) :
    T.pairCarrier i ∪ Set.range (T.arm i) = T.carrier := by
  -- There are only three arms, so the assertion is union associativity and commutativity.
  fin_cases i
  · have hunion : Set.range (T.arm 1) ∪ Set.range (T.arm 2) ∪
        Set.range (T.arm 0) =
        Set.range (T.arm 0) ∪ Set.range (T.arm 1) ∪ Set.range (T.arm 2) := by
      ext z
      simp only [Set.mem_union]
      tauto
    simpa [pairCarrier, carrier] using hunion
  · have hunion : Set.range (T.arm 0) ∪ Set.range (T.arm 2) ∪
        Set.range (T.arm 1) =
        Set.range (T.arm 0) ∪ Set.range (T.arm 1) ∪ Set.range (T.arm 2) := by
      ext z
      simp only [Set.mem_union]
      tauto
    simpa [pairCarrier, carrier] using hunion
  · simp [pairCarrier, carrier]

/-- Helper for Theorem 63.6: every opposite pair-carrier lies in the full
theta carrier. -/
theorem pairCarrier_subset_carrier {p q : StandardSphere 2}
    (T : SphericalThetaTriple p q) (i : Fin 3) :
    T.pairCarrier i ⊆ T.carrier := by
  -- Add the omitted arm and use the full-carrier identity.
  intro z hz
  rw [← T.pairCarrier_union_arm i]
  exact Or.inl hz

/-- Helper for Theorem 63.6: the explicit three-arm carrier equals the indexed
union of all theta arms. -/
theorem carrier_eq_iUnion {p q : StandardSphere 2}
    (T : SphericalThetaTriple p q) :
    T.carrier = ⋃ i, Set.range (T.arm i) := by
  -- Expand membership and enumerate the three possible arm indices.
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

/-- Helper for Theorem 63.6: opposite any arm of a spherical theta triple is a
complementary component whose frontier is the union of the other two arms. -/
theorem existsOppositeComponent {p q : StandardSphere 2}
    (T : SphericalThetaTriple p q) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ x, x ∈ T.carrierᶜ ∧
      connectedComponentIn T.carrierᶜ x =
        connectedComponentIn (Set.range (T.arm i) ∪ Set.range (T.arm j))ᶜ x ∧
      frontier (connectedComponentIn T.carrierᶜ x) =
        Set.range (T.arm i) ∪ Set.range (T.arm j) := by
  classical
  let C : Set (StandardSphere 2) :=
    Set.range (T.arm i) ∪ Set.range (T.arm j)
  let theta : Set (StandardSphere 2) := ⋃ l, Set.range (T.arm l)
  have hinterSymm : Set.range (T.arm i) ∩ Set.range (T.arm j).symm = {p, q} := by
    rw [Path.symm_range]
    exact T.arm_inter hij
  obtain ⟨e⟩ := embeddedPathsUnion_homeomorphicCircle (T.arm i) (T.arm j).symm
    (T.arm_embedding i)
    ((T.arm_embedding j).comp unitInterval.symmHomeomorph.isEmbedding) hinterSymm
  have hpairSet : Set.range (T.arm i) ∪ Set.range (T.arm j).symm = C := by
    rw [Path.symm_range]
  have hCcircle : Nonempty (C ≃ₜ Circle) :=
    ⟨(Homeomorph.setCongr hpairSet).symm.trans e⟩
  have hCcurve : Topology.IsSimpleClosedCurve C :=
    (Topology.IsSimpleClosedCurve.iff_nonempty_homeomorph_circle C).mpr hCcircle
  have hcomponents : Cardinal.mk (ConnectedComponents (Cᶜ : Set _)) = 2 :=
    Set.separatesInto_iff.mp (@jordanCurveSphere_separatesInto C hCcurve)
  let t : unitInterval := ⟨1 / 2, by norm_num⟩
  let y := T.arm k t
  let interiorArm : Set (StandardSphere 2) := Set.range (T.arm k) \ {p, q}
  have htZero : t ≠ 0 := by
    intro ht
    have hval := congrArg Subtype.val ht
    norm_num [t] at hval
  have htOne : t ≠ 1 := by
    intro ht
    have hval := congrArg Subtype.val ht
    norm_num [t] at hval
  have hyInterior : y ∈ interiorArm := by
    refine ⟨Set.mem_range_self t, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro hyp
      exact htZero ((T.arm_embedding k).injective
        (hyp.trans (T.arm k).source.symm))
    · intro hyq
      exact htOne ((T.arm_embedding k).injective
        (hyq.trans (T.arm k).target.symm))
  have hinteriorConnected : IsConnected interiorArm := by
    -- Removing the endpoints of an embedded interval leaves its open connected core.
    simpa only [interiorArm, (T.arm k).source, (T.arm k).target] using
      embeddedArc_range_diff_endpoints_isConnected (T.arm k) (T.arm_embedding k)
  have hinteriorCcompl : interiorArm ⊆ Cᶜ := by
    rintro z ⟨hzk, hzEndpoints⟩
    rw [Set.mem_compl_iff]
    rintro (hzi | hzj)
    · have hzInter : z ∈ Set.range (T.arm k) ∩ Set.range (T.arm i) := ⟨hzk, hzi⟩
      rw [T.arm_inter hik.symm] at hzInter
      exact hzEndpoints hzInter
    · have hzInter : z ∈ Set.range (T.arm k) ∩ Set.range (T.arm j) := ⟨hzk, hzj⟩
      rw [T.arm_inter hjk.symm] at hzInter
      exact hzEndpoints hzInter
  let yC : (Cᶜ : Set (StandardSphere 2)) := ⟨y, hinteriorCcompl hyInterior⟩
  obtain ⟨x, hdisjoint, hpartition⟩ :=
    Schoenflies.existsOtherComponentPartition Cᶜ hcomponents yC
  let U : Set (StandardSphere 2) := connectedComponentIn Cᶜ yC
  let V : Set (StandardSphere 2) := connectedComponentIn Cᶜ x
  have hinteriorU : interiorArm ⊆ U :=
    hinteriorConnected.2.subset_connectedComponentIn hyInterior hinteriorCcompl
  have hVavoidsThird : V ∩ Set.range (T.arm k) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨hzV, hzk⟩
    by_cases hzEndpoints : z ∈ ({p, q} : Set _)
    · have hzC : z ∈ C := by
        rcases hzEndpoints with rfl | hzq
        · left
          exact ⟨0, (T.arm i).source⟩
        · rw [Set.mem_singleton_iff] at hzq
          subst z
          left
          exact ⟨1, (T.arm i).target⟩
      exact (connectedComponentIn_subset Cᶜ x hzV) hzC
    · exact Set.disjoint_left.mp hdisjoint
        (hinteriorU ⟨hzk, hzEndpoints⟩) hzV
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
    -- Component maximality in both ambient complements proves the sandwich equality.
    apply Set.Subset.antisymm
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hxTheta)
        ((connectedComponentIn_subset thetaᶜ x).trans hthetaC)
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn hxV hVtheta
  have hthetaCarrier : theta = T.carrier := T.carrier_eq_iUnion.symm
  have hxCarrier : (x : StandardSphere 2) ∈ T.carrierᶜ := by
    rw [← hthetaCarrier]
    exact hxTheta
  refine ⟨x, hxCarrier, ?_, ?_⟩
  · rw [← hthetaCarrier, hcomponentEq]
  · rw [← hthetaCarrier, hcomponentEq]
    exact @jordanCurveSphere_frontier_component C hCcurve x

/-- Helper for Theorem 63.6: a spherical theta triple has exactly three
pairwise disjoint complementary regions, one opposite each arm. -/
theorem existsComplementaryRegions {p q : StandardSphere 2}
    (T : SphericalThetaTriple p q) :
    ∃ region : Fin 3 → Set (StandardSphere 2),
      (∀ i, IsConnectedComponentIn T.carrierᶜ (region i)) ∧
      (∀ i, IsConnectedComponentIn (T.pairCarrier i)ᶜ (region i)) ∧
      (∀ i, frontier (region i) = T.pairCarrier i) ∧
      (∀ ⦃i j⦄, i ≠ j → Disjoint (region i) (region j)) ∧
      (⋃ i, region i) = T.carrierᶜ := by
  classical
  -- Choose the three components supplied by the opposite-arm theorem.
  obtain ⟨x₀, hx₀, hcomponentPair₀, hfrontier₀⟩ :=
    T.existsOppositeComponent (i := 1) (j := 2) (k := 0)
      (by decide) (by decide) (by decide)
  obtain ⟨x₁, hx₁, hcomponentPair₁, hfrontier₁⟩ :=
    T.existsOppositeComponent (i := 0) (j := 2) (k := 1)
      (by decide) (by decide) (by decide)
  obtain ⟨x₂, hx₂, hcomponentPair₂, hfrontier₂⟩ :=
    T.existsOppositeComponent (i := 0) (j := 1) (k := 2)
      (by decide) (by decide) (by decide)
  let t : unitInterval := ⟨1 / 2, by norm_num⟩
  have htZero : t ≠ 0 := by
    intro ht
    have hval := congrArg Subtype.val ht
    norm_num [t] at hval
  have htOne : t ≠ 1 := by
    intro ht
    have hval := congrArg Subtype.val ht
    norm_num [t] at hval
  have hmidpointNotOther {i j : Fin 3} (hij : i ≠ j) :
      T.arm i t ∉ Set.range (T.arm j) := by
    intro hmem
    have hcommon : T.arm i t ∈ Set.range (T.arm i) ∩ Set.range (T.arm j) :=
      ⟨Set.mem_range_self t, hmem⟩
    rw [T.arm_inter hij] at hcommon
    rcases hcommon with hcommon | hcommon
    · exact htZero ((T.arm_embedding i).injective
        (hcommon.trans (T.arm i).source.symm))
    · rw [Set.mem_singleton_iff] at hcommon
      exact htOne ((T.arm_embedding i).injective
        (hcommon.trans (T.arm i).target.symm))
  have hcomponent₀₁ : connectedComponentIn T.carrierᶜ x₀ ≠
      connectedComponentIn T.carrierᶜ x₁ := by
    intro heq
    have hfrontierEq := congrArg frontier heq
    rw [hfrontier₀, hfrontier₁] at hfrontierEq
    have hmid : T.arm 1 t ∈ Set.range (T.arm 1) ∪ Set.range (T.arm 2) :=
      Or.inl (Set.mem_range_self t)
    rw [hfrontierEq] at hmid
    exact hmid.elim (hmidpointNotOther (by decide))
      (hmidpointNotOther (by decide))
  have hcomponent₀₂ : connectedComponentIn T.carrierᶜ x₀ ≠
      connectedComponentIn T.carrierᶜ x₂ := by
    intro heq
    have hfrontierEq := congrArg frontier heq
    rw [hfrontier₀, hfrontier₂] at hfrontierEq
    have hmid : T.arm 2 t ∈ Set.range (T.arm 1) ∪ Set.range (T.arm 2) :=
      Or.inr (Set.mem_range_self t)
    rw [hfrontierEq] at hmid
    exact hmid.elim (hmidpointNotOther (by decide))
      (hmidpointNotOther (by decide))
  have hcomponent₁₂ : connectedComponentIn T.carrierᶜ x₁ ≠
      connectedComponentIn T.carrierᶜ x₂ := by
    intro heq
    have hfrontierEq := congrArg frontier heq
    rw [hfrontier₁, hfrontier₂] at hfrontierEq
    have hmid : T.arm 2 t ∈ Set.range (T.arm 0) ∪ Set.range (T.arm 2) :=
      Or.inr (Set.mem_range_self t)
    rw [hfrontierEq] at hmid
    exact hmid.elim (hmidpointNotOther (by decide))
      (hmidpointNotOther (by decide))
  -- Remove the component opposite arm `2`; Theorem 63.5 counts the remainder.
  let C : Set (StandardSphere 2) := Set.range (T.arm 0) ∪ Set.range (T.arm 1)
  let A : Set (StandardSphere 2) := Set.range (T.arm 2)
  have hthetaEq : C ∪ A = T.carrier := by
    simpa [C, A, pairCarrier] using T.pairCarrier_union_arm 2
  have hthetaC : T.carrierᶜ ⊆ Cᶜ := by
    intro z hzTheta hzC
    exact hzTheta (hthetaEq ▸ Or.inl hzC)
  let x₂C : (Cᶜ : Set (StandardSphere 2)) := ⟨x₂, hthetaC hx₂⟩
  have hcomponentPair₂C : connectedComponentIn T.carrierᶜ x₂ =
      connectedComponentIn Cᶜ x₂C := by
    simpa only [C, x₂C] using hcomponentPair₂
  obtain ⟨pairEquiv⟩ := T.pairCarrier_homeomorphicCircle 2
  have hpairCarrierC : T.pairCarrier 2 = C := by
    rfl
  have hCcircle : Nonempty (C ≃ₜ Circle) :=
    ⟨(Homeomorph.setCongr hpairCarrierC).symm.trans pairEquiv⟩
  have hCcurve : Topology.IsSimpleClosedCurve C :=
    (Topology.IsSimpleClosedCurve.iff_nonempty_homeomorph_circle C).mpr hCcircle
  have hAclosed : IsClosed A := by
    simpa only [A] using T.arm_isClosed 2
  have hAconnected : IsConnected A := by
    simpa only [A] using T.arm_isConnected 2
  have hAarc : Topology.IsArc A := by
    simpa only [A] using T.arm_isArc 2
  have hAnonseparating : ¬ A.Separates := @arc_not_separates A hAarc
  have hCAinter : C ∩ A = {p, q} := by
    ext z
    constructor
    · rintro ⟨hzC, hzA⟩
      rcases hzC with hz₀ | hz₁
      · have hzPair : z ∈ Set.range (T.arm 0) ∩ Set.range (T.arm 2) :=
          ⟨hz₀, hzA⟩
        rw [T.arm_inter (by decide)] at hzPair
        exact hzPair
      · have hzPair : z ∈ Set.range (T.arm 1) ∩ Set.range (T.arm 2) :=
          ⟨hz₁, hzA⟩
        rw [T.arm_inter (by decide)] at hzPair
        exact hzPair
    · intro hzPair
      rcases hzPair with rfl | hzq
      · exact ⟨Or.inl ⟨0, (T.arm 0).source⟩, ⟨0, (T.arm 2).source⟩⟩
      · rw [Set.mem_singleton_iff] at hzq
        subst z
        exact ⟨Or.inl ⟨1, (T.arm 0).target⟩, ⟨1, (T.arm 2).target⟩⟩
  have hV₂A : Disjoint (connectedComponentIn Cᶜ x₂C) A := by
    apply Set.disjoint_left.mpr
    intro z hzV hzA
    rw [← hcomponentPair₂C] at hzV
    exact (connectedComponentIn_subset T.carrierᶜ x₂ hzV)
      (hthetaEq ▸ Or.inr hzA)
  obtain ⟨hRtwo, hRident⟩ := Schoenflies.oppositeJordanComponent_remainder
    C A hCcurve x₂C hAclosed hAconnected hAnonseparating
    p q T.endpoint_ne hCAinter hV₂A
  let Remainder : Set (StandardSphere 2) :=
    (closure (connectedComponentIn Cᶜ x₂C) ∪ A)ᶜ
  have hRidentTheta : Remainder =
      T.carrierᶜ \ connectedComponentIn T.carrierᶜ x₂ := by
    calc
      Remainder = (C ∪ A)ᶜ \ connectedComponentIn Cᶜ x₂C := hRident
      _ = T.carrierᶜ \ connectedComponentIn T.carrierᶜ x₂ := by
        rw [hthetaEq, hcomponentPair₂C]
  have hRcard : Cardinal.mk (ConnectedComponents Remainder) = 2 := by
    have hcard := Set.separatesInto_iff.mp hRtwo
    change Cardinal.mk (ConnectedComponents
      ((closure (connectedComponentIn Cᶜ x₂C) ∪ A)ᶜ : Set _)) = 2
    norm_num at hcard ⊢
    exact hcard
  have mem_remainder_of_component_ne {z : StandardSphere 2}
      (hz : z ∈ T.carrierᶜ)
      (hne : connectedComponentIn T.carrierᶜ z ≠
        connectedComponentIn T.carrierᶜ x₂) :
      z ∈ Remainder := by
    rw [hRidentTheta]
    refine ⟨hz, ?_⟩
    intro hzV
    exact hne (connectedComponentIn_eq hzV).symm
  have component_subset_remainder {z : StandardSphere 2}
      (hne : connectedComponentIn T.carrierᶜ z ≠
        connectedComponentIn T.carrierᶜ x₂) :
      connectedComponentIn T.carrierᶜ z ⊆ Remainder := by
    rw [hRidentTheta]
    intro w hw
    refine ⟨connectedComponentIn_subset _ z hw, ?_⟩
    intro hw₂
    exact hne ((connectedComponentIn_eq hw).trans
      (connectedComponentIn_eq hw₂).symm)
  have hRsubsetTheta : Remainder ⊆ T.carrierᶜ := by
    rw [hRidentTheta]
    exact Set.sdiff_subset
  have component_remainder_eq {z : StandardSphere 2}
      (hz : z ∈ T.carrierᶜ)
      (hne : connectedComponentIn T.carrierᶜ z ≠
        connectedComponentIn T.carrierᶜ x₂) :
      connectedComponentIn Remainder z = connectedComponentIn T.carrierᶜ z :=
    Schoenflies.connectedComponentIn_eq_of_component_subset hz
      (component_subset_remainder hne) hRsubsetTheta
  have hcomponentClassification (z : StandardSphere 2) (hz : z ∈ T.carrierᶜ) :
      connectedComponentIn T.carrierᶜ z = connectedComponentIn T.carrierᶜ x₀ ∨
      connectedComponentIn T.carrierᶜ z = connectedComponentIn T.carrierᶜ x₁ ∨
      connectedComponentIn T.carrierᶜ z = connectedComponentIn T.carrierᶜ x₂ := by
    by_cases hcomponent₂ : connectedComponentIn T.carrierᶜ z =
        connectedComponentIn T.carrierᶜ x₂
    · exact Or.inr (Or.inr hcomponent₂)
    · have hzR := mem_remainder_of_component_ne hz hcomponent₂
      have hx₀R := mem_remainder_of_component_ne hx₀ hcomponent₀₂
      have hx₁R := mem_remainder_of_component_ne hx₁ hcomponent₁₂
      have hRcomponent₀₁ : connectedComponentIn Remainder x₀ ≠
          connectedComponentIn Remainder x₁ := by
        rw [component_remainder_eq hx₀ hcomponent₀₂,
          component_remainder_eq hx₁ hcomponent₁₂]
        exact hcomponent₀₁
      rcases Schoenflies.connectedComponentIn_eq_or_eq_of_mk_eq_two
          Remainder hRcard hzR hx₀R hx₁R hRcomponent₀₁ with hzEq | hzEq
      · left
        rwa [component_remainder_eq hz hcomponent₂,
          component_remainder_eq hx₀ hcomponent₀₂] at hzEq
      · right
        left
        rwa [component_remainder_eq hz hcomponent₂,
          component_remainder_eq hx₁ hcomponent₁₂] at hzEq
  have hdisjoint₀₁ : Disjoint (connectedComponentIn T.carrierᶜ x₀)
      (connectedComponentIn T.carrierᶜ x₁) := by
    apply Set.disjoint_left.mpr
    intro z hz₀ hz₁
    apply hcomponent₀₁
    exact (connectedComponentIn_eq hz₀).trans (connectedComponentIn_eq hz₁).symm
  have hdisjoint₀₂ : Disjoint (connectedComponentIn T.carrierᶜ x₀)
      (connectedComponentIn T.carrierᶜ x₂) := by
    apply Set.disjoint_left.mpr
    intro z hz₀ hz₂
    apply hcomponent₀₂
    exact (connectedComponentIn_eq hz₀).trans (connectedComponentIn_eq hz₂).symm
  have hdisjoint₁₂ : Disjoint (connectedComponentIn T.carrierᶜ x₁)
      (connectedComponentIn T.carrierᶜ x₂) := by
    apply Set.disjoint_left.mpr
    intro z hz₁ hz₂
    apply hcomponent₁₂
    exact (connectedComponentIn_eq hz₁).trans (connectedComponentIn_eq hz₂).symm
  let region : Fin 3 → Set (StandardSphere 2) := fun i ↦
    if i = 0 then connectedComponentIn T.carrierᶜ x₀
    else if i = 1 then connectedComponentIn T.carrierᶜ x₁
    else connectedComponentIn T.carrierᶜ x₂
  have hx₀Pair : (x₀ : StandardSphere 2) ∈ (T.pairCarrier 0)ᶜ := by
    intro hxPair
    exact hx₀ (T.pairCarrier_subset_carrier 0 hxPair)
  have hx₁Pair : (x₁ : StandardSphere 2) ∈ (T.pairCarrier 1)ᶜ := by
    intro hxPair
    exact hx₁ (T.pairCarrier_subset_carrier 1 hxPair)
  have hx₂Pair : (x₂ : StandardSphere 2) ∈ (T.pairCarrier 2)ᶜ := by
    intro hxPair
    exact hx₂ (T.pairCarrier_subset_carrier 2 hxPair)
  have hselected₀ : region 0 =
      connectedComponentIn (T.pairCarrier 0)ᶜ x₀ := by
    calc
      region 0 = connectedComponentIn T.carrierᶜ x₀ := by simp [region]
      _ = connectedComponentIn
          (Set.range (T.arm 1) ∪ Set.range (T.arm 2))ᶜ x₀ := hcomponentPair₀
      _ = connectedComponentIn (T.pairCarrier 0)ᶜ x₀ := by rfl
  have hselected₁ : region 1 =
      connectedComponentIn (T.pairCarrier 1)ᶜ x₁ := by
    calc
      region 1 = connectedComponentIn T.carrierᶜ x₁ := by simp [region]
      _ = connectedComponentIn
          (Set.range (T.arm 0) ∪ Set.range (T.arm 2))ᶜ x₁ := hcomponentPair₁
      _ = connectedComponentIn (T.pairCarrier 1)ᶜ x₁ := by rfl
  have hselected₂ : region 2 =
      connectedComponentIn (T.pairCarrier 2)ᶜ x₂ := by
    calc
      region 2 = connectedComponentIn T.carrierᶜ x₂ := by simp [region]
      _ = connectedComponentIn
          (Set.range (T.arm 0) ∪ Set.range (T.arm 1))ᶜ x₂ := hcomponentPair₂
      _ = connectedComponentIn (T.pairCarrier 2)ᶜ x₂ := by rfl
  have hpairComponent₀ :
      IsConnectedComponentIn (T.pairCarrier 0)ᶜ (region 0) := by
    rw [hselected₀]
    exact IsConnectedComponentIn.of_mem hx₀Pair
  have hpairComponent₁ :
      IsConnectedComponentIn (T.pairCarrier 1)ᶜ (region 1) := by
    rw [hselected₁]
    exact IsConnectedComponentIn.of_mem hx₁Pair
  have hpairComponent₂ :
      IsConnectedComponentIn (T.pairCarrier 2)ᶜ (region 2) := by
    rw [hselected₂]
    exact IsConnectedComponentIn.of_mem hx₂Pair
  refine ⟨region, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa [region] using IsConnectedComponentIn.of_mem hx₀
    · simpa [region] using IsConnectedComponentIn.of_mem hx₁
    · simpa [region] using IsConnectedComponentIn.of_mem hx₂
  · -- Use the dependent `Fin.cases` eliminator to preserve the carrier instances.
    exact Fin.cases hpairComponent₀
      (Fin.cases hpairComponent₁
        (Fin.cases hpairComponent₂ (fun i ↦ Fin.elim0 i)))
  · intro i
    fin_cases i
    · simpa [region, pairCarrier] using hfrontier₀
    · simpa [region, pairCarrier] using hfrontier₁
    · simpa [region, pairCarrier] using hfrontier₂
  · intro i j hij
    fin_cases i
    · fin_cases j
      · exact (hij rfl).elim
      · simpa [region] using hdisjoint₀₁
      · simpa [region] using hdisjoint₀₂
    · fin_cases j
      · simpa [region] using hdisjoint₀₁.symm
      · exact (hij rfl).elim
      · simpa [region] using hdisjoint₁₂
    · fin_cases j
      · simpa [region] using hdisjoint₀₂.symm
      · simpa [region] using hdisjoint₁₂.symm
      · exact (hij rfl).elim
  · apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      fin_cases i
      · exact connectedComponentIn_subset T.carrierᶜ x₀ (by simpa [region] using hi)
      · exact connectedComponentIn_subset T.carrierᶜ x₁ (by simpa [region] using hi)
      · exact connectedComponentIn_subset T.carrierᶜ x₂ (by simpa [region] using hi)
    · intro z hz
      rcases hcomponentClassification z hz with hz₀ | hz₁ | hz₂
      · refine Set.mem_iUnion.mpr ⟨0, ?_⟩
        have hzOwn : z ∈ connectedComponentIn T.carrierᶜ z :=
          mem_connectedComponentIn hz
        rw [hz₀] at hzOwn
        simpa [region] using hzOwn
      · refine Set.mem_iUnion.mpr ⟨1, ?_⟩
        have hzOwn : z ∈ connectedComponentIn T.carrierᶜ z :=
          mem_connectedComponentIn hz
        rw [hz₁] at hzOwn
        simpa [region] using hzOwn
      · refine Set.mem_iUnion.mpr ⟨2, ?_⟩
        have hzOwn : z ∈ connectedComponentIn T.carrierᶜ z :=
          mem_connectedComponentIn hz
        rw [hz₂] at hzOwn
        simpa [region] using hzOwn

end SphericalThetaTriple

end Schoenflies

namespace JordanCrosscut

/-- Helper for Theorem 63.6: a spherical Jordan crosscut and the two boundary
arcs between its endpoints form a theta triple with the expected carrier. -/
theorem existsSphericalThetaTriple
    {U : Set (StandardSphere 2)} {p q : StandardSphere 2}
    (gamma : JordanCrosscut U p q) (hpq : p ≠ q)
    [Topology.IsSimpleClosedCurve (frontier U)] :
    ∃ T : Schoenflies.SphericalThetaTriple p q,
      Set.range (T.arm 0) = gamma.carrier ∧
      Set.range (T.arm 1) ∪ Set.range (T.arm 2) = frontier U ∧
      T.carrier = gamma.carrier ∪ frontier U := by
  have hendpoints := gamma.endpoints_mem_frontier
  let pFrontier : frontier U := ⟨p, hendpoints.1⟩
  let qFrontier : frontier U := ⟨q, hendpoints.2⟩
  have hpqFrontier : pFrontier ≠ qFrontier := by
    intro h
    exact hpq (congrArg Subtype.val h)
  obtain ⟨alpha, beta, halpha, hbeta, hboundary, hAlphaBeta⟩ :=
    Topology.IsSimpleClosedCurve.existsTwoEmbeddedPathDecomposition
      (frontier U) pFrontier qFrontier hpqFrontier
  obtain ⟨crosscut, hcrosscutEmbedding, hcrosscutRange⟩ :=
    gamma.existsEmbeddedPath
  have halphaSubset : Set.range alpha ⊆ frontier U := by
    intro y hy
    rw [← hboundary]
    exact Or.inl hy
  have hbetaSubset : Set.range beta ⊆ frontier U := by
    intro y hy
    rw [← hboundary]
    exact Or.inr hy
  have hcarrierAlpha : gamma.carrier ∩ Set.range alpha = {p, q} := by
    -- Intersect the global crosscut-frontier equation with the first boundary arc.
    apply Set.Subset.antisymm
    · intro y hy
      rw [← gamma.carrier_inter_frontier]
      exact ⟨hy.1, halphaSubset hy.2⟩
    · intro y hy
      have hyCarrierFrontier : y ∈ gamma.carrier ∩ frontier U := by
        rw [gamma.carrier_inter_frontier]
        exact hy
      have hyBoth : y ∈ Set.range alpha ∩ Set.range beta := by
        rw [hAlphaBeta]
        exact hy
      exact ⟨hyCarrierFrontier.1, hyBoth.1⟩
  have hcarrierBeta : gamma.carrier ∩ Set.range beta = {p, q} := by
    -- The second boundary arc satisfies the symmetric endpoint calculation.
    apply Set.Subset.antisymm
    · intro y hy
      rw [← gamma.carrier_inter_frontier]
      exact ⟨hy.1, hbetaSubset hy.2⟩
    · intro y hy
      have hyCarrierFrontier : y ∈ gamma.carrier ∩ frontier U := by
        rw [gamma.carrier_inter_frontier]
        exact hy
      have hyBoth : y ∈ Set.range alpha ∩ Set.range beta := by
        rw [hAlphaBeta]
        exact hy
      exact ⟨hyCarrierFrontier.1, hyBoth.2⟩
  have hcrosscutAlpha : Set.range crosscut ∩ Set.range alpha = {p, q} := by
    rw [hcrosscutRange]
    exact hcarrierAlpha
  have hcrosscutBetaSymm :
      Set.range crosscut ∩ Set.range beta.symm = {p, q} := by
    rw [Path.symm_range, hcrosscutRange]
    exact hcarrierBeta
  have hAlphaBetaSymm : Set.range alpha ∩ Set.range beta.symm = {p, q} := by
    rw [Path.symm_range]
    exact hAlphaBeta
  have hAlphaCrosscut : Set.range alpha ∩ Set.range crosscut = {p, q} := by
    rw [Set.inter_comm]
    exact hcrosscutAlpha
  have hBetaSymmCrosscut : Set.range beta.symm ∩ Set.range crosscut = {p, q} := by
    rw [Set.inter_comm]
    exact hcrosscutBetaSymm
  have hBetaSymmAlpha : Set.range beta.symm ∩ Set.range alpha = {p, q} := by
    rw [Set.inter_comm]
    exact hAlphaBetaSymm
  let arm : Fin 3 → Path p q := fun i ↦
    if i = 0 then crosscut else if i = 1 then alpha else beta.symm
  have hbetaSymmEmbedding : Topology.IsEmbedding beta.symm := by
    -- Record the path-reversal spelling once so the arm family stays uniform.
    exact hbeta.comp unitInterval.symmHomeomorph.isEmbedding
  have harmEmbedding : ∀ i, Topology.IsEmbedding (arm i) := by
    intro i
    fin_cases i
    · simpa [arm] using hcrosscutEmbedding
    · simpa [arm] using halpha
    · simpa [arm] using hbetaSymmEmbedding
  have harmInter : ∀ {i j}, i ≠ j →
      Set.range (arm i) ∩ Set.range (arm j) = {p, q} := by
    intro i j hij
    fin_cases i
    · fin_cases j
      · exact (hij rfl).elim
      · simpa [arm] using hcrosscutAlpha
      · simpa [arm] using hcrosscutBetaSymm
    · fin_cases j
      · simpa [arm] using hAlphaCrosscut
      · exact (hij rfl).elim
      · simpa [arm] using hAlphaBetaSymm
    · fin_cases j
      · simpa [arm] using hBetaSymmCrosscut
      · simpa [arm] using hBetaSymmAlpha
      · exact (hij rfl).elim
  let T : Schoenflies.SphericalThetaTriple p q :=
    ⟨hpq, arm, harmEmbedding, harmInter⟩
  have hzeroRange : Set.range (T.arm 0) = gamma.carrier := by
    simpa [T, arm] using hcrosscutRange
  have hboundaryRange : Set.range (T.arm 1) ∪ Set.range (T.arm 2) =
      frontier U := by
    simpa [T, arm, Path.symm_range] using hboundary
  have hcarrierNormalize : T.carrier =
      Set.range (T.arm 0) ∪ (Set.range (T.arm 1) ∪ Set.range (T.arm 2)) := by
    -- Normalize the explicit three-fold union before applying the range specifications.
    ext z
    simp only [Schoenflies.SphericalThetaTriple.carrier, Set.mem_union]
    tauto
  have hcarrier : T.carrier = gamma.carrier ∪ frontier U := by
    calc
      T.carrier = Set.range (T.arm 0) ∪
          (Set.range (T.arm 1) ∪ Set.range (T.arm 2)) := hcarrierNormalize
      _ = gamma.carrier ∪ frontier U := by rw [hzeroRange, hboundaryRange]
  exact ⟨T, hzeroRange, hboundaryRange, hcarrier⟩

/-- Helper for Theorem 63.6: a spherical crosscut split records the two child
Jordan domains and their exact closure-incidence relations. -/
structure SphericalSplit
    {U : Set (StandardSphere 2)} {p q : StandardSphere 2}
    (gamma : JordanCrosscut U p q) where
  left : Set (StandardSphere 2)
  right : Set (StandardSphere 2)
  leftFrontierSimple : Topology.IsSimpleClosedCurve (frontier left)
  rightFrontierSimple : Topology.IsSimpleClosedCurve (frontier right)
  leftComponent : IsConnectedComponentIn (frontier left)ᶜ left
  rightComponent : IsConnectedComponentIn (frontier right)ᶜ right
  cover : U \ gamma.carrier = left ∪ right
  disjoint : Disjoint left right
  closureUnion : closure left ∪ closure right = closure U
  closureInter : closure left ∩ closure right = gamma.carrier

/-- Helper for Theorem 63.6: complementary child interiors whose frontiers
cover a crosscut and the parent frontier have closures covering the parent closure. -/
theorem closure_union_of_split_boundaries
    {X : Type*} [TopologicalSpace X] {U G L R F₁ F₂ : Set X}
    (hcover : U \ G = L ∪ R) (hfrontierL : frontier L = F₁)
    (hfrontierR : frontier R = F₂)
    (hboundary : F₁ ∪ F₂ = G ∪ frontier U)
    (hGclosure : G ⊆ closure U) :
    closure L ∪ closure R = closure U := by
  -- Normalize all three closures and dispatch membership through the two covers.
  rw [closure_eq_self_union_frontier, closure_eq_self_union_frontier,
    hfrontierL, hfrontierR, closure_eq_self_union_frontier]
  ext z
  constructor
  · rintro ((hzL | hzF₁) | hzR | hzF₂)
    · have hzDiff : z ∈ U \ G := hcover.symm ▸ Or.inl hzL
      exact Or.inl hzDiff.1
    · have hzBoundary : z ∈ G ∪ frontier U := by
        rw [← hboundary]
        exact Or.inl hzF₁
      rcases hzBoundary with hzG | hzFrontier
      · have hzClosure := hGclosure hzG
        rw [closure_eq_self_union_frontier] at hzClosure
        exact hzClosure
      · exact Or.inr hzFrontier
    · have hzDiff : z ∈ U \ G := hcover.symm ▸ Or.inr hzR
      exact Or.inl hzDiff.1
    · have hzBoundary : z ∈ G ∪ frontier U := by
        rw [← hboundary]
        exact Or.inr hzF₂
      rcases hzBoundary with hzG | hzFrontier
      · have hzClosure := hGclosure hzG
        rw [closure_eq_self_union_frontier] at hzClosure
        exact hzClosure
      · exact Or.inr hzFrontier
  · rintro (hzU | hzFrontier)
    · by_cases hzG : z ∈ G
      · have hzBoundary : z ∈ F₁ ∪ F₂ := by
          rw [hboundary]
          exact Or.inl hzG
        rcases hzBoundary with hzF₁ | hzF₂
        · exact Or.inl (Or.inr hzF₁)
        · exact Or.inr (Or.inr hzF₂)
      · have hzChildren : z ∈ L ∪ R := by
          rw [← hcover]
          exact ⟨hzU, hzG⟩
        rcases hzChildren with hzL | hzR
        · exact Or.inl (Or.inl hzL)
        · exact Or.inr (Or.inl hzR)
    · have hzBoundary : z ∈ F₁ ∪ F₂ := by
        rw [hboundary]
        exact Or.inr hzFrontier
      rcases hzBoundary with hzF₁ | hzF₂
      · exact Or.inl (Or.inr hzF₁)
      · exact Or.inr (Or.inr hzF₂)

/-- Helper for Theorem 63.6: disjoint regions on the complement of a carrier
meet after closure exactly where their two frontiers meet. -/
theorem closure_inter_eq_of_split_frontiers
    {X : Type*} [TopologicalSpace X] {K L R F₁ F₂ G : Set X}
    (hL : L ⊆ Kᶜ) (hR : R ⊆ Kᶜ) (hF₁ : F₁ ⊆ K) (hF₂ : F₂ ⊆ K)
    (hdisjoint : Disjoint L R) (hfrontierL : frontier L = F₁)
    (hfrontierR : frontier R = F₂) (hfrontierInter : F₁ ∩ F₂ = G) :
    closure L ∩ closure R = G := by
  -- After expanding the closures, three mixed cases are disjointness contradictions.
  rw [closure_eq_self_union_frontier, closure_eq_self_union_frontier,
    hfrontierL, hfrontierR]
  ext z
  constructor
  · rintro ⟨hzL | hzF₁, hzR | hzF₂⟩
    · exact (Set.disjoint_left.mp hdisjoint hzL hzR).elim
    · exact (hL hzL (hF₂ hzF₂)).elim
    · exact (hR hzR (hF₁ hzF₁)).elim
    · exact hfrontierInter ▸ ⟨hzF₁, hzF₂⟩
  · intro hzG
    have hzFrontiers : z ∈ F₁ ∩ F₂ := hfrontierInter.symm ▸ hzG
    exact ⟨Or.inr hzFrontiers.1, Or.inr hzFrontiers.2⟩

/-- Helper for Theorem 63.6: a crosscut of a spherical Jordan domain produces
two child Jordan domains with the expected coverage and closure incidence. -/
theorem existsSphericalSplit
    {U : Set (StandardSphere 2)} {p q : StandardSphere 2}
    (gamma : JordanCrosscut U p q) (hpq : p ≠ q)
    [Topology.IsSimpleClosedCurve (frontier U)]
    (hU : IsConnectedComponentIn (frontier U)ᶜ U) :
    Nonempty (SphericalSplit gamma) := by
  classical
  -- Convert the crosscut and its two boundary arcs into the three-arm model.
  obtain ⟨T, hcrosscutRange, hboundaryRange, hcarrier⟩ :=
    gamma.existsSphericalThetaTriple hpq
  obtain ⟨region, hthetaComponent, hpairComponent, hregionFrontier,
      hregionDisjoint, hregionCover⟩ := T.existsComplementaryRegions
  have hpairZero : T.pairCarrier 0 = frontier U := by
    simpa [Schoenflies.SphericalThetaTriple.pairCarrier] using hboundaryRange
  have hpairOne : T.pairCarrier 1 =
      gamma.carrier ∪ Set.range (T.arm 2) := by
    rw [Schoenflies.SphericalThetaTriple.pairCarrier, if_neg (by decide),
      if_pos rfl, hcrosscutRange]
  have hpairTwo : T.pairCarrier 2 =
      gamma.carrier ∪ Set.range (T.arm 1) := by
    rw [Schoenflies.SphericalThetaTriple.pairCarrier, if_neg (by decide),
      if_neg (by decide), hcrosscutRange]
  have hpairUnion : T.pairCarrier 1 ∪ T.pairCarrier 2 =
      gamma.carrier ∪ frontier U := by
    rw [hpairOne, hpairTwo, ← hboundaryRange]
    ext z
    simp only [Set.mem_union]
    tauto
  have hpairInter : T.pairCarrier 1 ∩ T.pairCarrier 2 =
      gamma.carrier := by
    rw [hpairOne, hpairTwo]
    ext z
    constructor
    · rintro ⟨hzCrosscut | hzTwo, hzCrosscut' | hzOne⟩
      · exact hzCrosscut
      · exact hzCrosscut
      · exact hzCrosscut'
      · have hzEndpoints : z ∈
            Set.range (T.arm 2) ∩ Set.range (T.arm 1) := ⟨hzTwo, hzOne⟩
        rw [T.arm_inter (by decide)] at hzEndpoints
        rcases hzEndpoints with rfl | hzq
        · exact gamma.endpoints_mem.1
        · rw [Set.mem_singleton_iff] at hzq
          subst z
          exact gamma.endpoints_mem.2
    · exact fun hz ↦ ⟨Or.inl hz, Or.inl hz⟩
  have houtsideComponent :
      IsConnectedComponentIn (frontier U)ᶜ (region 0) := by
    rw [← hpairZero]
    exact hpairComponent 0
  have hleftFrontier : frontier (region 1) = T.pairCarrier 1 :=
    hregionFrontier 1
  have hrightFrontier : frontier (region 2) = T.pairCarrier 2 :=
    hregionFrontier 2
  have hleftFrontierSimple :
      Topology.IsSimpleClosedCurve (frontier (region 1)) := by
    rw [hleftFrontier]
    exact T.pairCarrier_isSimpleClosedCurve 1
  have hrightFrontierSimple :
      Topology.IsSimpleClosedCurve (frontier (region 2)) := by
    rw [hrightFrontier]
    exact T.pairCarrier_isSimpleClosedCurve 2
  have hleftComponent :
      IsConnectedComponentIn (frontier (region 1))ᶜ (region 1) := by
    rw [hleftFrontier]
    exact hpairComponent 1
  have hrightComponent :
      IsConnectedComponentIn (frontier (region 2))ᶜ (region 2) := by
    rw [hrightFrontier]
    exact hpairComponent 2
  -- A midpoint of the crosscut lies in the parent domain, so the region
  -- opposite the crosscut is the other parent complementary component.
  let t : unitInterval := ⟨1 / 2, by norm_num⟩
  let y : StandardSphere 2 := T.arm 0 t
  have htZero : t ≠ 0 := by
    intro ht
    have hval := congrArg Subtype.val ht
    norm_num [t] at hval
  have htOne : t ≠ 1 := by
    intro ht
    have hval := congrArg Subtype.val ht
    norm_num [t] at hval
  have hyCrosscut : y ∈ gamma.carrier := by
    rw [← hcrosscutRange]
    exact Set.mem_range_self t
  have hyNotFrontier : y ∉ frontier U := by
    intro hyFrontier
    have hyEndpoints : y ∈ ({p, q} : Set (StandardSphere 2)) := by
      rw [← gamma.carrier_inter_frontier]
      exact ⟨hyCrosscut, hyFrontier⟩
    rcases hyEndpoints with hyp | hyq
    · exact htZero ((T.arm_embedding 0).injective
        (hyp.trans (T.arm 0).source.symm))
    · rw [Set.mem_singleton_iff] at hyq
      exact htOne ((T.arm_embedding 0).injective
        (hyq.trans (T.arm 0).target.symm))
  have hyU : y ∈ U := by
    have hyClosure := gamma.carrier_subset_closure hyCrosscut
    rw [closure_eq_self_union_frontier] at hyClosure
    exact hyClosure.resolve_right hyNotFrontier
  have hyNotOutside : y ∉ region 0 := by
    intro hyOutside
    exact (hthetaComponent 0).subset hyOutside
      (hcarrier.symm ▸ Or.inl hyCrosscut)
  have houtsideNe : region 0 ≠ U := by
    intro heq
    exact hyNotOutside (heq.symm ▸ hyU)
  have houtsideDisjointU : Disjoint (region 0) U := by
    apply Set.disjoint_left.mpr
    intro z hzOutside hzU
    apply houtsideNe
    calc
      region 0 = connectedComponentIn (frontier U)ᶜ z :=
        houtsideComponent.eq_connectedComponentIn hzOutside
      _ = U := (hU.eq_connectedComponentIn hzU).symm
  have hparentCard :
      Cardinal.mk (ConnectedComponents ((frontier U)ᶜ : Set _)) = 2 :=
    Set.separatesInto_iff.mp (jordanCurveSphere_separatesInto (frontier U))
  have hparentCover : region 0 ∪ U = (frontier U)ᶜ :=
    Schoenflies.union_eq_of_two_connectedComponents hparentCard
      houtsideComponent hU houtsideNe
  have houtsideLeft : Disjoint (region 0) (region 1) :=
    hregionDisjoint (by decide)
  have houtsideRight : Disjoint (region 0) (region 2) :=
    hregionDisjoint (by decide)
  have hleftSubset : region 1 ⊆ U := by
    intro z hzLeft
    have hzTheta := (hthetaComponent 1).subset hzLeft
    have hzParent : z ∈ (frontier U)ᶜ := by
      intro hzFrontier
      exact hzTheta (hcarrier.symm ▸ Or.inr hzFrontier)
    rcases hparentCover.symm ▸ hzParent with hzOutside | hzU
    · exact (Set.disjoint_left.mp houtsideLeft hzOutside hzLeft).elim
    · exact hzU
  have hrightSubset : region 2 ⊆ U := by
    intro z hzRight
    have hzTheta := (hthetaComponent 2).subset hzRight
    have hzParent : z ∈ (frontier U)ᶜ := by
      intro hzFrontier
      exact hzTheta (hcarrier.symm ▸ Or.inr hzFrontier)
    rcases hparentCover.symm ▸ hzParent with hzOutside | hzU
    · exact (Set.disjoint_left.mp houtsideRight hzOutside hzRight).elim
    · exact hzU
  have hchildrenCover : U \ gamma.carrier = region 1 ∪ region 2 := by
    apply Set.Subset.antisymm
    · intro z hz
      have hzTheta : z ∈ T.carrierᶜ := by
        intro hzCarrier
        rw [hcarrier] at hzCarrier
        rcases hzCarrier with hzCrosscut | hzFrontier
        · exact hz.2 hzCrosscut
        · exact hU.subset hz.1 hzFrontier
      have hzRegions : z ∈ ⋃ i, region i := by
        rw [hregionCover]
        exact hzTheta
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hzRegions
      fin_cases i
      · exact (Set.disjoint_left.mp houtsideDisjointU hi hz.1).elim
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro z (hzLeft | hzRight)
      · refine ⟨hleftSubset hzLeft, ?_⟩
        intro hzCrosscut
        exact (hthetaComponent 1).subset hzLeft
          (hcarrier.symm ▸ Or.inl hzCrosscut)
      · refine ⟨hrightSubset hzRight, ?_⟩
        intro hzCrosscut
        exact (hthetaComponent 2).subset hzRight
          (hcarrier.symm ▸ Or.inl hzCrosscut)
  have hclosureUnion : closure (region 1) ∪ closure (region 2) =
      closure U :=
    closure_union_of_split_boundaries hchildrenCover hleftFrontier
      hrightFrontier hpairUnion gamma.carrier_subset_closure
  have hclosureInter : closure (region 1) ∩ closure (region 2) =
      gamma.carrier :=
    closure_inter_eq_of_split_frontiers
      (hthetaComponent 1).subset (hthetaComponent 2).subset
      (T.pairCarrier_subset_carrier 1) (T.pairCarrier_subset_carrier 2)
      (hregionDisjoint (by decide)) hleftFrontier hrightFrontier hpairInter
  -- Package the two theta regions as the stable recursive split interface.
  exact ⟨⟨region 1, region 2, hleftFrontierSimple, hrightFrontierSimple,
    hleftComponent, hrightComponent, hchildrenCover,
    hregionDisjoint (by decide), hclosureUnion, hclosureInter⟩⟩

end JordanCrosscut
