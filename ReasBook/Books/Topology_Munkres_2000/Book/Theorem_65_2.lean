module

public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Topology_Munkres_2000.Book.Definition_61_3.SimpleClosedCurve
public import Topology_Munkres_2000.Book.Lemma_55_1.Inclusions
public import Topology_Munkres_2000.Book.Remark_65_1
public import Topology_Munkres_2000.Book.Remark_65_1.PairComplement
public import Mathlib.Topology.Connected.Basic

public section

open Set

/-- A subset lies in the complement of any two points of its complement. -/
theorem subset_pairComplement {X : Type*} (C : Set X) (p q : (Cᶜ : Set X)) :
    C ⊆ ({(p : X), (q : X)}ᶜ : Set X) := by
  intro x hx
  simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
  exact ⟨fun h ↦ p.property (h ▸ hx), fun h ↦ q.property (h ▸ hx)⟩

/-- Helper for Theorem 65.2: a point outside two punctures is, in particular,
outside the first puncture. -/
private def pairComplementToFirstPuncture
    (p q : StandardSphere 2) (x : ({p, q}ᶜ : Set (StandardSphere 2))) :
    ({p}ᶜ : Set (StandardSphere 2)) :=
  ⟨x.1, fun hp ↦ x.2 (Or.inl hp)⟩

/-- Helper for Theorem 65.2: forgetting the second puncture gives the nested
punctured-sphere point used by the stereographic chart. -/
private def pairComplementToNestedPuncture (p q : StandardSphere 2) :
    ({p, q}ᶜ : Set (StandardSphere 2)) →
      {x : ({p}ᶜ : Set (StandardSphere 2)) // x.1 ≠ q} :=
  fun x ↦ ⟨pairComplementToFirstPuncture p q x, fun hq ↦ x.2 (Or.inr hq)⟩

/-- Helper for Theorem 65.2: flattening a nested puncture gives a point outside
the corresponding two-point set. -/
private def nestedPunctureToPairComplement (p q : StandardSphere 2) :
    {x : ({p}ᶜ : Set (StandardSphere 2)) // x.1 ≠ q} →
      ({p, q}ᶜ : Set (StandardSphere 2)) :=
  fun x ↦ ⟨x.1.1, fun h ↦ h.elim x.1.2 x.2⟩

/-- Helper for Theorem 65.2: nesting a point outside two punctures is continuous. -/
private lemma continuous_pairComplementToNestedPuncture (p q : StandardSphere 2) :
    Continuous (pairComplementToNestedPuncture p q) := by
  -- Build continuity through the two successive subtype constructors.
  have hinner : Continuous (pairComplementToFirstPuncture p q) :=
    continuous_subtype_val.subtype_mk
      (fun (x : ({p, q}ᶜ : Set (StandardSphere 2))) hp ↦ x.2 (Or.inl hp))
  exact hinner.subtype_mk (fun x hq ↦ x.2 (Or.inr hq))

/-- Helper for Theorem 65.2: flattening a nested puncture is continuous. -/
private lemma continuous_nestedPunctureToPairComplement (p q : StandardSphere 2) :
    Continuous (nestedPunctureToPairComplement p q) := by
  -- The underlying map is the composite of the two subtype projections.
  exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
    (fun x h ↦ h.elim x.1.2 x.2)

/-- Helper for Theorem 65.2: flattening after nesting fixes a pair-complement point. -/
private lemma nestedPunctureToPairComplement_leftInverse (p q : StandardSphere 2) :
    Function.LeftInverse (nestedPunctureToPairComplement p q)
      (pairComplementToNestedPuncture p q) := by
  -- Compare the ambient sphere values; subtype membership proofs are irrelevant.
  intro x
  apply Subtype.ext
  rfl

/-- Helper for Theorem 65.2: nesting after flattening fixes a nested puncture point. -/
private lemma nestedPunctureToPairComplement_rightInverse (p q : StandardSphere 2) :
    Function.RightInverse (nestedPunctureToPairComplement p q)
      (pairComplementToNestedPuncture p q) := by
  -- The outer subtype is determined by its once-punctured-sphere value.
  intro x
  apply Subtype.ext
  rfl

/-- Helper for Theorem 65.2: the two-point complement is canonically the
one-point complement inside a punctured sphere. -/
private def pairComplementHomeomorphNestedPuncture (p q : StandardSphere 2) :
    ({p, q}ᶜ : Set (StandardSphere 2)) ≃ₜ
      {x : ({p}ᶜ : Set (StandardSphere 2)) // x.1 ≠ q} :=
  { toFun := pairComplementToNestedPuncture p q
    invFun := nestedPunctureToPairComplement p q
    left_inv := nestedPunctureToPairComplement_leftInverse p q
    right_inv := nestedPunctureToPairComplement_rightInverse p q
    continuous_toFun := continuous_pairComplementToNestedPuncture p q
    continuous_invFun := continuous_nestedPunctureToPairComplement p q }

/-- Helper for Theorem 65.2: the second puncture belongs to the sphere with the
first puncture removed. -/
private lemma secondPoint_mem_firstPointComplement
    (p q : StandardSphere 2) (hpq : p ≠ q) :
    q ∈ ({p}ᶜ : Set (StandardSphere 2)) := by
  -- Complement membership reverses the displayed inequality.
  simpa using hpq.symm

/-- Helper for Theorem 65.2: stereographic coordinates translated by the
second puncture give a plane chart sending that puncture to the origin. -/
private noncomputable def StandardSphere.translatedPuncturedHomeomorphPlane
    (p q : StandardSphere 2) (hpq : p ≠ q) :
    ({p}ᶜ : Set (StandardSphere 2)) ≃ₜ EuclideanSpace ℝ (Fin 2) :=
  (StandardSphere.puncturedHomeomorphPlane p).trans
    (Homeomorph.subRight
      (StandardSphere.puncturedHomeomorphPlane p
        ⟨q, secondPoint_mem_firstPointComplement p q hpq⟩))

/-- Helper for Theorem 65.2: translated stereographic coordinates avoid the
origin exactly when the sphere point avoids the second puncture. -/
private lemma translatedPuncturedHomeomorphPlane_mem_punctured_iff
    (p q : StandardSphere 2) (hpq : p ≠ q)
    (x : ({p}ᶜ : Set (StandardSphere 2))) :
    x.1 ≠ q ↔
      StandardSphere.translatedPuncturedHomeomorphPlane p q hpq x ∈
        EuclideanPlane.punctured := by
  -- Translation turns nonvanishing into inequality of stereographic images.
  rw [EuclideanPlane.mem_punctured_iff]
  simp only [StandardSphere.translatedPuncturedHomeomorphPlane,
    Homeomorph.trans_apply, Homeomorph.subRight_apply, sub_ne_zero]
  rw [(StandardSphere.puncturedHomeomorphPlane p).injective.ne_iff]
  simpa using (Subtype.coe_ne_coe (a := x)
    (b := (⟨q, secondPoint_mem_firstPointComplement p q hpq⟩ :
      ({p}ᶜ : Set (StandardSphere 2)))))

/-- Helper for Theorem 65.2: the complement of two distinct sphere points is
homeomorphic to the punctured Euclidean plane. -/
private noncomputable def StandardSphere.pairComplementHomeomorphPuncturedPlane
    (p q : StandardSphere 2) (hpq : p ≠ q) :
    ({p, q}ᶜ : Set (StandardSphere 2)) ≃ₜ EuclideanPlane.punctured :=
  (pairComplementHomeomorphNestedPuncture p q).trans
    ((StandardSphere.translatedPuncturedHomeomorphPlane p q hpq).subtype
      (translatedPuncturedHomeomorphPlane_mem_punctured_iff p q hpq))

/-- Helper for Theorem 65.2: the twice-punctured-sphere chart is the restriction
of translated stereographic coordinates. -/
private lemma StandardSphere.pairComplementHomeomorphPuncturedPlane_apply
    (p q : StandardSphere 2) (hpq : p ≠ q)
    (x : ({p, q}ᶜ : Set (StandardSphere 2))) :
    ((StandardSphere.pairComplementHomeomorphPuncturedPlane p q hpq x :
      EuclideanPlane.punctured) : EuclideanSpace ℝ (Fin 2)) =
      StandardSphere.translatedPuncturedHomeomorphPlane p q hpq
        (pairComplementToFirstPuncture p q x) := by
  -- The chart is the translated stereographic map restricted to the two-point complement.
  simp [StandardSphere.pairComplementHomeomorphPuncturedPlane,
    pairComplementHomeomorphNestedPuncture, pairComplementToNestedPuncture]

/-- Helper for Theorem 65.2: when the two punctures lie in different
complementary components, the origin component outside the charted curve is bounded. -/
private lemma jordanCurvePairComplementImage_originComponent_bounded
    (C : Set (StandardSphere 2)) [Topology.IsSimpleClosedCurve C]
    (p q : (Cᶜ : Set (StandardSphere 2)))
    (hpq : (p : StandardSphere 2) ≠ q)
    (hcomponents : connectedComponentIn Cᶜ p ≠ connectedComponentIn Cᶜ q) :
    Bornology.IsBounded
      (connectedComponentIn
        (((fun x : ({(p : StandardSphere 2), (q : StandardSphere 2)}ᶜ :
            Set (StandardSphere 2)) ↦
              (StandardSphere.pairComplementHomeomorphPuncturedPlane p q hpq x :
                EuclideanSpace ℝ (Fin 2))) '' (Subtype.val ⁻¹' C))ᶜ)
        (0 : EuclideanSpace ℝ (Fin 2))) := by
  classical
  -- Compactness of the curve is transported from its circle model.
  obtain ⟨curveEquiv⟩ := Topology.IsSimpleClosedCurve.homeomorphic_circle (X := C)
  letI : CompactSpace C := curveEquiv.symm.compactSpace
  have hCcompact : IsCompact C := isCompact_iff_compactSpace.mpr inferInstance
  let U : Set (StandardSphere 2) := connectedComponentIn Cᶜ q
  have hUComponent : IsConnectedComponentIn Cᶜ U :=
    IsConnectedComponentIn.of_mem q.property
  have hpU : (p : StandardSphere 2) ∉ U := by
    intro hpU
    exact hcomponents (connectedComponentIn_eq hpU).symm
  let planeChart := StandardSphere.translatedPuncturedHomeomorphPlane p q hpq
  obtain ⟨hImageComponent, hImageBounded⟩ :=
    puncturedSphere_componentImage_bounded C U p planeChart hCcompact p.property
      hUComponent hpU
  have hzeroImage :
      (0 : EuclideanSpace ℝ (Fin 2)) ∈ planeChart '' (Subtype.val ⁻¹' U) := by
    let qAway : ({(p : StandardSphere 2)}ᶜ : Set (StandardSphere 2)) :=
      ⟨q, secondPoint_mem_firstPointComplement p q hpq⟩
    refine ⟨qAway, mem_connectedComponentIn q.property, ?_⟩
    simp [planeChart, StandardSphere.translatedPuncturedHomeomorphPlane, qAway]
  have hImageCurve :
      planeChart '' (Subtype.val ⁻¹' C) =
        (fun x : ({(p : StandardSphere 2), (q : StandardSphere 2)}ᶜ :
            Set (StandardSphere 2)) ↦
              (StandardSphere.pairComplementHomeomorphPuncturedPlane p q hpq x :
                EuclideanSpace ℝ (Fin 2))) '' (Subtype.val ⁻¹' C) := by
    ext z
    constructor
    · rintro ⟨x, hxC, rfl⟩
      let xAway : ({(p : StandardSphere 2), (q : StandardSphere 2)}ᶜ :
          Set (StandardSphere 2)) :=
        ⟨x.1, fun hx ↦ hx.elim x.2 (fun hxq ↦ q.property (hxq ▸ hxC))⟩
      refine ⟨xAway, hxC, ?_⟩
      exact StandardSphere.pairComplementHomeomorphPuncturedPlane_apply p q hpq xAway
    · rintro ⟨x, hxC, rfl⟩
      refine ⟨pairComplementToFirstPuncture p q x, hxC, ?_⟩
      exact StandardSphere.pairComplementHomeomorphPuncturedPlane_apply p q hpq x
  -- The component supplied by Lemma 61.1 contains zero, hence is its component.
  have hImageComponent_eq := hImageComponent.eq_connectedComponentIn hzeroImage
  rw [hImageComponent_eq, hImageCurve] at hImageBounded
  exact hImageBounded

/-- Helper for Theorem 65.2: functoriality identifies the induced map of a
composite with the composite of the induced maps. -/
private lemma fundamentalGroupMap_comp_eq
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (x : X) :
    FundamentalGroup.map (g.comp f) x =
      (FundamentalGroup.map g (f x)).comp (FundamentalGroup.map f x) := by
  -- Evaluate both homomorphisms on a loop and use quotient-level map composition.
  ext loop
  simp only [FundamentalGroup.map_apply]
  exact Path.Homotopic.Quotient.map_comp

/-- Helper for Theorem 65.2: winding number `1` or `-1` makes the induced
fundamental-group homomorphism bijective. -/
private lemma fundamentalGroupMapBijective_of_windingNumber_eq_one_or_neg_one
    (h : C(Circle, EuclideanPlane.punctured))
    (sourceCoordinates : Circle.FundamentalOrientation)
    (targetCoordinates : FundamentalGroup EuclideanPlane.punctured (h 1) ≃*
      Multiplicative ℤ)
    (hwinding : PuncturedPlaneMap.windingNumber sourceCoordinates h targetCoordinates = 1 ∨
      PuncturedPlaneMap.windingNumber sourceCoordinates h targetCoordinates = -1) :
    Function.Bijective (FundamentalGroup.map h 1) := by
  -- Conjugate the induced map by the chosen infinite-cyclic coordinates.
  let coordinateMap : Multiplicative ℤ →* Multiplicative ℤ :=
    targetCoordinates.toMonoidHom.comp
      ((FundamentalGroup.map h 1).comp sourceCoordinates.symm.toMonoidHom)
  let additiveCoordinateMap : ℤ →+ ℤ := coordinateMap.toAdditive
  have generatorImage :
      additiveCoordinateMap 1 =
        PuncturedPlaneMap.windingNumber sourceCoordinates h targetCoordinates := by
    have windingSpec := PuncturedPlaneMap.windingNumber_spec
      sourceCoordinates h targetCoordinates
    have coordinateSpec := congrArg targetCoordinates windingSpec
    have coordinateGenerator :
        coordinateMap (Multiplicative.ofAdd 1) =
          Multiplicative.ofAdd
            (PuncturedPlaneMap.windingNumber sourceCoordinates h targetCoordinates) := by
      simpa only [coordinateMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply] using coordinateSpec
    exact congrArg Multiplicative.toAdd coordinateGenerator
  have additiveCoordinateMap_bijective : Function.Bijective additiveCoordinateMap := by
    rcases hwinding with hwinding | hwinding
    · have generatorImage_one : additiveCoordinateMap 1 = 1 := by
        rw [generatorImage, hwinding]
      have map_eq (n : ℤ) : additiveCoordinateMap n = n := by
        calc
          additiveCoordinateMap n = additiveCoordinateMap (n • (1 : ℤ)) := by simp
          _ = n • additiveCoordinateMap 1 := additiveCoordinateMap.map_zsmul n 1
          _ = n := by rw [generatorImage_one]; simp
      constructor
      · intro m n hmn
        simpa only [map_eq] using hmn
      · intro n
        exact ⟨n, map_eq n⟩
    · have generatorImage_negOne : additiveCoordinateMap 1 = -1 := by
        rw [generatorImage, hwinding]
      have map_eq (n : ℤ) : additiveCoordinateMap n = -n := by
        calc
          additiveCoordinateMap n = additiveCoordinateMap (n • (1 : ℤ)) := by simp
          _ = n • additiveCoordinateMap 1 := additiveCoordinateMap.map_zsmul n 1
          _ = -n := by rw [generatorImage_negOne]; simp
      constructor
      · intro m n hmn
        simpa only [map_eq, neg_inj] using hmn
      · intro n
        have hpreimage : additiveCoordinateMap (-n) = n := by
          simp only [map_eq, neg_neg]
        exact ⟨-n, hpreimage⟩
  have coordinateMap_bijective : Function.Bijective coordinateMap := by
    -- Multiplicative/additive conversion has the same underlying integer carrier.
    constructor
    · intro m n hmn
      apply Multiplicative.toAdd.injective
      exact additiveCoordinateMap_bijective.injective
        (congrArg Multiplicative.toAdd hmn)
    · intro n
      obtain ⟨m, hm⟩ := additiveCoordinateMap_bijective.surjective
        (Multiplicative.toAdd n)
      refine ⟨Multiplicative.ofAdd m, ?_⟩
      apply Multiplicative.toAdd.injective
      exact hm
  -- Cancel the coordinate equivalences to return to the original induced map.
  constructor
  · intro x y hxy
    apply sourceCoordinates.injective
    apply coordinateMap_bijective.injective
    simpa only [coordinateMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] using congrArg targetCoordinates hxy
  · intro y
    obtain ⟨n, hn⟩ := coordinateMap_bijective.surjective (targetCoordinates y)
    refine ⟨sourceCoordinates.symm n, ?_⟩
    apply targetCoordinates.injective
    simpa only [coordinateMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] using hn

/-- Theorem 65.2. If `p` and `q` lie in different components of the complement
of a simple closed curve `C` in the standard two-sphere, then the inclusion of
`C` into the sphere with `p` and `q` removed induces a bijective homomorphism on
fundamental groups. -/
theorem jordanCurve_inclusionMap_bijective
    (C : Set (StandardSphere 2)) [Topology.IsSimpleClosedCurve C]
    (p q : (Cᶜ : Set (StandardSphere 2)))
    (h_components : connectedComponentIn Cᶜ p ≠ connectedComponentIn Cᶜ q) (c : C) :
    Function.Bijective
      (FundamentalGroup.mapOfSubset (subset_pairComplement C p q) c) := by
  classical
  -- Distinct complementary components force the two punctures to be distinct.
  have hpq : (p : StandardSphere 2) ≠ q := by
    intro hpq
    apply h_components
    have hpqSubtype : p = q := Subtype.ext hpq
    rw [hpqSubtype]
  -- Parametrize the curve from the circle and rotate the parameter so that `1` maps to `c`.
  obtain ⟨curveEquiv⟩ := Topology.IsSimpleClosedCurve.homeomorphic_circle (X := C)
  let circleParam : Circle ≃ₜ C :=
    (Homeomorph.mulLeft (curveEquiv c)).trans curveEquiv.symm
  have circleParam_one : circleParam 1 = c := by
    simp [circleParam]
  let inclusion : C(C,
      ({(p : StandardSphere 2), (q : StandardSphere 2)}ᶜ : Set (StandardSphere 2))) :=
    ContinuousMap.inclusion (subset_pairComplement C p q)
  let chart := StandardSphere.pairComplementHomeomorphPuncturedPlane p q hpq
  let chartMap : C(
      ({(p : StandardSphere 2), (q : StandardSphere 2)}ᶜ : Set (StandardSphere 2)),
      EuclideanPlane.punctured) :=
    ⟨chart, chart.continuous⟩
  let circleParamMap : C(Circle, C) :=
    ⟨circleParam, circleParam.continuous⟩
  have circleParamMap_one : circleParamMap 1 = c := circleParam_one
  let h : C(Circle, EuclideanPlane.punctured) :=
    ⟨fun x ↦ chartMap (inclusion (circleParamMap x)),
      (chartMap.comp (inclusion.comp circleParamMap)).continuous⟩
  have h_injective : Function.Injective h := by
    -- Each of the parametrization, inclusion, and chart is injective.
    exact chart.injective.comp
      ((Set.inclusion_injective (subset_pairComplement C p q)).comp circleParam.injective)
  have hRange :
      Set.range (fun x : Circle ↦ (h x : EuclideanSpace ℝ (Fin 2))) =
        (fun x : ({(p : StandardSphere 2), (q : StandardSphere 2)}ᶜ :
            Set (StandardSphere 2)) ↦ (chart x : EuclideanSpace ℝ (Fin 2))) ''
          (Subtype.val ⁻¹' C) := by
    -- Surjectivity of the curve parametrization identifies the two ambient images.
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨inclusion (circleParam x), (circleParam x).property, rfl⟩
    · rintro ⟨y, hyC, rfl⟩
      let yCurve : C := ⟨y.1, hyC⟩
      refine ⟨circleParam.symm yCurve, ?_⟩
      have hparam := circleParam.apply_symm_apply yCurve
      have hinclusion : inclusion (circleParam (circleParam.symm yCurve)) = y := by
        apply Subtype.ext
        exact congrArg (fun z : C ↦ (z : StandardSphere 2)) hparam
      have hchart :
          chart (inclusion (circleParam (circleParam.symm yCurve))) = chart y :=
        congrArg chart hinclusion
      exact congrArg (fun z : EuclideanPlane.punctured ↦
        (z : EuclideanSpace ℝ (Fin 2))) hchart
  have h_bounded : Bornology.IsBounded
      (connectedComponentIn
        (Set.range (fun x : Circle ↦ (h x : EuclideanSpace ℝ (Fin 2))))ᶜ 0) := by
    -- The component containing `q` becomes the bounded origin component in the chart.
    rw [hRange]
    exact jordanCurvePairComplementImage_originComponent_bounded
      C p q hpq h_components
  let sourceCoordinates : Circle.FundamentalOrientation :=
    Circle.nonemptyFundamentalOrientation.some
  let pairCoordinates :
      FundamentalGroup
          ({(p : StandardSphere 2), (q : StandardSphere 2)}ᶜ : Set (StandardSphere 2))
          (chart.symm (h 1)) ≃* Multiplicative ℤ :=
    (StandardSphere.pairComplementFundamentalGroupEquivInt p q hpq
      (chart.symm (h 1))).some
  let targetCoordinates :
      FundamentalGroup EuclideanPlane.punctured (h 1) ≃* Multiplicative ℤ :=
    (chart.symm.fundamentalGroupMulEquiv (h 1)).trans pairCoordinates
  have hwinding :=
    PuncturedPlaneMap.windingNumber_eq_one_or_neg_one_of_originComponent_bounded
      h h_injective sourceCoordinates targetCoordinates h_bounded
  have hMap_bijective : Function.Bijective (FundamentalGroup.map h 1) :=
    fundamentalGroupMapBijective_of_windingNumber_eq_one_or_neg_one
      h sourceCoordinates targetCoordinates hwinding
  have hfactorization :
      FundamentalGroup.map h 1 =
        (FundamentalGroup.map chartMap (inclusion (circleParamMap 1))).comp
          ((FundamentalGroup.map inclusion (circleParamMap 1)).comp
            (FundamentalGroup.map circleParamMap 1)) := by
    -- Expand the three-map composite at its natural parametrized basepoint.
    calc
      FundamentalGroup.map h 1 =
          (FundamentalGroup.map chartMap (inclusion (circleParamMap 1))).comp
            (FundamentalGroup.map (inclusion.comp circleParamMap) 1) :=
        fundamentalGroupMap_comp_eq (inclusion.comp circleParamMap) chartMap 1
      _ = (FundamentalGroup.map chartMap (inclusion (circleParamMap 1))).comp
          ((FundamentalGroup.map inclusion (circleParamMap 1)).comp
            (FundamentalGroup.map circleParamMap 1)) := by
        rw [fundamentalGroupMap_comp_eq]
  have circleMap_surjective :
      Function.Surjective (FundamentalGroup.map circleParamMap 1) :=
    (circleParam.fundamentalGroupMulEquiv 1).surjective
  have chartMap_injective :
      Function.Injective
        (FundamentalGroup.map chartMap (inclusion (circleParamMap 1))) :=
    (chart.fundamentalGroupMulEquiv (inclusion (circleParamMap 1))).injective
  rw [FundamentalGroup.mapOfSubset_eq_map_inclusion, ← circleParamMap_one]
  constructor
  · -- Lift two source loops through the parametrization and cancel the chart map.
    intro x y hxy
    obtain ⟨x', rfl⟩ := circleMap_surjective x
    obtain ⟨y', rfl⟩ := circleMap_surjective y
    apply congrArg (FundamentalGroup.map circleParamMap 1)
    apply hMap_bijective.injective
    rw [hfactorization]
    simp only [MonoidHom.comp_apply]
    exact congrArg
      (FundamentalGroup.map chartMap (inclusion (circleParamMap 1))) hxy
  · -- Lift the charted target through the bijective composite and cancel the chart map.
    intro y
    obtain ⟨x, hx⟩ := hMap_bijective.surjective
      (FundamentalGroup.map chartMap (inclusion (circleParamMap 1)) y)
    refine ⟨FundamentalGroup.map circleParamMap 1 x, ?_⟩
    apply chartMap_injective
    rw [← hx, hfactorization]
    simp only [MonoidHom.comp_apply]
    rfl
