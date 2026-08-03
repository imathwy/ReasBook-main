module

public import Topology_Munkres_2000.Book.Exercise_72_2
public import Topology_Munkres_2000.Book.Theorem_72_1
public import Topology_Munkres_2000.Book.Exercise_66_1.LoopQuotient
public import Topology_Munkres_2000.Book.Exercise_58_9.BasedClassification
public import Topology_Munkres_2000.Book.Lemma_55_1.Inclusions
public import Topology_Munkres_2000.Book.Theorem_9_0_1.BorsukNoRetraction
public import Topology_Munkres_2000.Book.Definition_9_0_2
public import Mathlib.GroupTheory.QuotientGroup.Basic

public section

universe u v

/-- Helper for Exercise 72.3: attaching a two-cell to a path-connected space
produces a path-connected adjunction space. -/
private theorem AdjunctionSpace.twoCellPathConnectedSpace
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (f : C(StandardSphere.boundary 1, X)) :
    PathConnectedSpace (AdjunctionSpace (StandardSphere.boundary 1) f) := by
  -- The disk image and the canonical copy of `X` are individually path-connected.
  have zero_le_one_real : (0 : ℝ) ≤ 1 := by
    norm_num
  letI : PathConnectedSpace B² :=
    isPathConnected_iff_pathConnectedSpace.mp
      (Metric.isPathConnected_closedBall zero_le_one_real)
  let diskRange : Set (AdjunctionSpace (StandardSphere.boundary 1) f) :=
    Set.range (AdjunctionSpace.includeX (StandardSphere.boundary 1) f)
  let baseRange : Set (AdjunctionSpace (StandardSphere.boundary 1) f) :=
    Set.range (AdjunctionSpace.includeY (StandardSphere.boundary 1) f)
  have diskPathConnected : IsPathConnected diskRange :=
    isPathConnected_range
      (AdjunctionSpace.continuous_includeX (StandardSphere.boundary 1) f)
  have basePathConnected : IsPathConnected baseRange :=
    isPathConnected_range
      (AdjunctionSpace.continuous_includeY (StandardSphere.boundary 1) f)
  -- The attaching equation supplies a point in the intersection of the two images.
  let p : StandardSphere.boundary 1 :=
    closedUnitDiskBoundaryHomeomorphCircle.symm 1
  have rangesMeet : (diskRange ∩ baseRange).Nonempty := by
    refine ⟨AdjunctionSpace.includeX (StandardSphere.boundary 1) f p, ?_, ?_⟩
    · exact ⟨p, rfl⟩
    · exact ⟨f p, (AdjunctionSpace.glue (StandardSphere.boundary 1) f p).symm⟩
  have unionPathConnected : IsPathConnected (diskRange ∪ baseRange) :=
    diskPathConnected.union basePathConnected rangesMeet
  -- Every quotient point has a representative in one of the two canonical images.
  have rangesCover : diskRange ∪ baseRange = Set.univ := by
    ext q
    constructor
    · intro _
      exact Set.mem_univ q
    · intro _
      rcases AdjunctionSpace.exists_eq_includeX_or_eq_includeY
          (StandardSphere.boundary 1) f q with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · exact Or.inl ⟨z, rfl⟩
      · exact Or.inr ⟨z, rfl⟩
  rw [pathConnectedSpace_iff_univ, ← rangesCover]
  exact unionPathConnected

/-- Helper for Exercise 72.3: the positive one-turn loop generates the
fundamental group of the circle. -/
private lemma CircleMap.standardTurnLoopGenerates :
    Subgroup.zpowers
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk CircleMap.standardTurnLoop)) = ⊤ := by
  -- The public lifting computation says that the turn lift ends at `1`.
  let q : FundamentalGroup Circle 1 :=
    FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk CircleMap.standardTurnLoop)
  let turnMap : C(ℝ, Circle) :=
    ⟨Circle.turnExp, Circle.isCoveringMap_turnExp.continuous⟩
  let turnE0 : Circle.turnExp ⁻¹' ({1} : Set Circle) :=
    ⟨0, Circle.turnExp_zero⟩
  let turnE1 : Circle.turnExp ⁻¹' ({1} : Set Circle) :=
    ⟨1, Circle.turnExp_one⟩
  let circleIdentity : C(Circle, Circle) := ⟨id, continuous_id⟩
  let realIdentity : C(ℝ, ℝ) := ⟨id, continuous_id⟩
  have identityLift : Circle.turnExp ∘ realIdentity =
      circleIdentity.comp turnMap := by
    funext z
    rfl
  have turnMonodromyValue :
      (Circle.isCoveringMap_turnExp.monodromy q turnE0 : ℝ) = 1 := by
    have mapIdentity :
        (Path.Homotopic.Quotient.mk CircleMap.standardTurnLoop).map
            circleIdentity =
          Path.Homotopic.Quotient.mk CircleMap.standardTurnLoop := by
      simp only [circleIdentity]
      rw [← Path.Homotopic.Quotient.mk_map, Path.map_id]
      rfl
    have liftedEndpoint := CircleMap.monodromy_map_turnPath_eq_lift_one
      circleIdentity rfl realIdentity rfl identityLift
    calc
      (Circle.isCoveringMap_turnExp.monodromy q turnE0 : ℝ) =
          (Circle.isCoveringMap_turnExp.monodromy
            (((Path.Homotopic.Quotient.mk CircleMap.standardTurnLoop).map
              circleIdentity).cast rfl rfl) turnE0 : ℝ) := by
        congr 2
      _ = realIdentity 1 := liftedEndpoint
      _ = 1 := rfl
  have turnMonodromy :
      Circle.isCoveringMap_turnExp.monodromy q turnE0 = turnE1 :=
    Subtype.ext turnMonodromyValue
  -- Scaling a lift through `turnExp` by `2π` gives a lift through `Circle.exp`.
  have scaleContinuous : Continuous (fun z : ℝ ↦ 2 * Real.pi * z) := by
    fun_prop
  let scale : C(ℝ, ℝ) := ⟨fun z ↦ 2 * Real.pi * z, scaleContinuous⟩
  let expMap : C(ℝ, Circle) := ⟨Circle.exp, Circle.isCoveringMap_exp.continuous⟩
  have expZero : Circle.exp 0 = 1 := by
    simp
  have expPeriod : Circle.exp (2 * Real.pi) = 1 := by
    simp
  let e0 : Circle.exp ⁻¹' ({1} : Set Circle) := ⟨0, expZero⟩
  let e1 : Circle.exp ⁻¹' ({1} : Set Circle) :=
    ⟨2 * Real.pi, expPeriod⟩
  have expScale : expMap.comp scale = turnMap := by
    apply ContinuousMap.ext
    intro z
    exact (congrFun Circle.turnExp_eq_exp_scale z).symm
  have monodromy_eq : Circle.isCoveringMap_exp.monodromy q e0 = e1 := by
    let lifted := Circle.isCoveringMap_turnExp.liftPathQuotient q turnE0
    have liftedMaps :=
      Circle.isCoveringMap_turnExp.map_liftPathQuotient q turnE0
    have scaleSource : (0 : ℝ) = scale (turnE0 : ℝ) := by
      norm_num [scale, turnE0]
    have scaleTarget : (2 * Real.pi : ℝ) =
        scale (Circle.isCoveringMap_turnExp.monodromy q turnE0 : ℝ) := by
      rw [turnMonodromyValue]
      norm_num [scale]
    let scaledLift := (lifted.map scale).cast scaleSource scaleTarget
    have mappedScaled :
        (lifted.map (expMap.comp scale)) ≍ lifted.map turnMap :=
      congr_arg_heq (fun h : C(ℝ, Circle) ↦ lifted.map h) expScale
    apply Circle.isCoveringMap_exp.monodromy_eq_of_map_eq
      scaledLift
    simp only [scaledLift, Path.Homotopic.Quotient.map_cast,
      ← Path.Homotopic.Quotient.map_comp]
    apply eq_of_heq
    exact (Path.Homotopic.Quotient.cast_heq _ _).trans
      (mappedScaled.trans
        ((heq_of_eq liftedMaps).trans
          ((Path.Homotopic.Quotient.cast_heq _ _).trans
            (Path.Homotopic.Quotient.cast_heq _ _).symm)))
  have oneSmulPeriod : (1 : ℤ) • (2 * Real.pi) = 2 * Real.pi := by
    simp
  have periodMem : 2 * Real.pi ∈ AddSubgroup.zmultiples (2 * Real.pi) :=
    ⟨1, oneSmulPeriod⟩
  let period : AddSubgroup.zmultiples (2 * Real.pi) :=
    ⟨2 * Real.pi, periodMem⟩
  have coveringCoordinate :
      Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv e0 q =
        MulOpposite.op (Multiplicative.ofAdd period) := by
    apply Circle.isAddQuotientCoveringMap_exp.fundamentalGroupToMulOpposite_apply_eq_Iff.mpr
    change (period : ℝ) + (e0 : ℝ) =
      (Circle.isCoveringMap_exp.monodromy q e0 : ℝ)
    rw [monodromy_eq]
    simp only [period, e0, e1, add_zero]
  -- Every period is an integer multiple of `2π`, hence a power of this loop's image.
  let coveringEquiv :=
    Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv e0
  rw [Subgroup.eq_top_iff']
  intro z
  have image_mem : coveringEquiv z ∈
      Subgroup.zpowers (MulOpposite.op (Multiplicative.ofAdd period)) := by
    rw [Subgroup.mem_zpowers_iff]
    rcases (coveringEquiv z).unop.toAdd.property with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have additivePower : n • period = (coveringEquiv z).unop.toAdd := by
      apply Subtype.ext
      exact hn
    calc
      MulOpposite.op (Multiplicative.ofAdd period) ^ n =
          MulOpposite.op (Multiplicative.ofAdd period ^ n) := rfl
      _ = MulOpposite.op (Multiplicative.ofAdd (n • period)) :=
        congrArg MulOpposite.op (ofAdd_zsmul n period).symm
      _ = MulOpposite.op
          (Multiplicative.ofAdd (coveringEquiv z).unop.toAdd) :=
        congrArg (fun a ↦ MulOpposite.op (Multiplicative.ofAdd a)) additivePower
      _ = coveringEquiv z := rfl
  rw [← coveringCoordinate] at image_mem
  rw [Subgroup.mem_zpowers_iff] at image_mem ⊢
  obtain ⟨n, hn⟩ := image_mem
  refine ⟨n, coveringEquiv.injective ?_⟩
  rwa [map_zpow]

/-- Helper for Exercise 72.3: pointed fundamental-group maps respect composition,
independently of the chosen endpoint equalities. -/
private lemma FundamentalGroup.mapOfEq_comp
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) {x : X} {y : Y} {z : Z}
    (hf : f x = y) (hg : g y = z) (hgf : (g.comp f) x = z) :
    (FundamentalGroup.mapOfEq g hg).comp (FundamentalGroup.mapOfEq f hf) =
      FundamentalGroup.mapOfEq (g.comp f) hgf := by
  -- Remove the intermediate endpoint transports, then apply functoriality of path mapping.
  subst y
  subst z
  have hgRefl : hg = rfl := Subsingleton.elim _ _
  cases hgRefl
  ext loop
  simp only [MonoidHom.coe_comp, Function.comp_apply, FundamentalGroup.mapOfEq_apply,
    Path.Homotopic.Quotient.cast_rfl_rfl, Path.Homotopic.Quotient.map_comp]
  apply eq_of_heq
  exact Path.Homotopic.Quotient.cast_heq _ _

/-- Helper for Exercise 72.3: a pointed homeomorphism induces a bijective map
on fundamental groups. -/
private lemma Homeomorph.fundamentalGroupMapOfEq_bijective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) (y : Y) (hxy : e x = y) :
    Function.Bijective (FundamentalGroup.mapOfEq (e : C(X, Y)) hxy) := by
  -- Once the target point is identified with the image point, use the homeomorphism equivalence.
  subst y
  have inducedEq : FundamentalGroup.mapOfEq (e : C(X, Y)) rfl =
      (e.fundamentalGroupMulEquiv x).toMonoidHom := by
    calc
      FundamentalGroup.mapOfEq (e : C(X, Y)) rfl =
          FundamentalGroup.map (e : C(X, Y)) x := by
        ext loop
        simp only [FundamentalGroup.mapOfEq_apply,
          Path.Homotopic.Quotient.cast_rfl_rfl, FundamentalGroup.map_apply]
      _ = (e.fundamentalGroupMulEquiv x).toMonoidHom :=
        (Homeomorph.fundamentalGroupMulEquiv_toMonoidHom e x).symm
  rw [inducedEq]
  exact (e.fundamentalGroupMulEquiv x).bijective

/-- Helper for Exercise 72.3: equal continuous maps induce the same pointed
fundamental-group homomorphism, regardless of endpoint proof choices. -/
private lemma FundamentalGroup.mapOfEq_congr
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f g : C(X, Y)) {x : X} {y : Y} (hfg : f = g)
    (hf : f x = y) (hg : g x = y) :
    FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg := by
  -- Substitution leaves only proof-irrelevant endpoint witnesses.
  subst g
  rfl

/-- Helper for Exercise 72.3: a reflexive endpoint witness gives the ordinary
induced map on fundamental groups. -/
private lemma FundamentalGroup.mapOfEq_refl
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    FundamentalGroup.mapOfEq f (rfl : f x = f x) =
      FundamentalGroup.map f x := by
  -- Evaluate both maps and remove the reflexive endpoint transport.
  ext loop
  simp only [FundamentalGroup.mapOfEq_apply,
    Path.Homotopic.Quotient.cast_rfl_rfl, FundamentalGroup.map_apply]

/-- Helper for Exercise 72.3: normally closing the cyclic subgroup generated by
an element is the same as normally closing the singleton containing it. -/
private lemma Subgroup.normalClosure_zpowers_eq_normalClosure_singleton
    {G : Type*} [Group G] (g : G) :
    Subgroup.normalClosure (Subgroup.zpowers g : Set G) =
      Subgroup.normalClosure ({g} : Set G) := by
  -- Powers of the generator already lie in the normal closure of the singleton.
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Subgroup.normalClosure ({g} : Set G)).zpow_mem
      (Subgroup.subset_normalClosure (Set.mem_singleton g)) n
  · -- Conversely, the generator itself belongs to its cyclic subgroup.
    apply Subgroup.normalClosure_mono
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact Subgroup.mem_zpowers g

/-- Helper for Exercise 72.3: the quotient of the unit interval traverses
`UnitAddCircle` once continuously. -/
private lemma continuous_unitAddCircleTurn :
    Continuous (fun t : unitInterval ↦ ((t : ℝ) : UnitAddCircle)) := by
  -- Compose the interval inclusion with the additive-circle quotient map.
  exact (AddCircle.continuous_mk' 1).comp continuous_subtype_val

/-- Helper for Exercise 72.3: the once-around additive-circle path starts at
the additive identity. -/
private lemma unitAddCircleTurn_source :
    (((0 : unitInterval) : ℝ) : UnitAddCircle) = 0 := by
  -- The quotient map preserves zero.
  simp

/-- Helper for Exercise 72.3: the once-around additive-circle path ends at
the additive identity. -/
private lemma unitAddCircleTurn_target :
    (((1 : unitInterval) : ℝ) : UnitAddCircle) = 0 := by
  -- The quotient identifies one full period with zero.
  simpa only [Set.Icc.coe_one] using (AddCircle.coe_period (1 : ℝ))

/-- Helper for Exercise 72.3: the canonical path traversing `UnitAddCircle`
once in the positive direction. -/
private def unitAddCircleTurn : Path (0 : UnitAddCircle) 0 :=
  { toFun := fun t ↦ ((t : ℝ) : UnitAddCircle)
    continuous_toFun := continuous_unitAddCircleTurn
    source' := unitAddCircleTurn_source
    target' := unitAddCircleTurn_target }

/-- Helper for Exercise 72.3: an endpoint-compatible loop descends
continuously to `UnitAddCircle`. -/
private lemma continuous_loopToUnitAddCircleMap
    {X : Type*} [TopologicalSpace X] {a : X} (gamma : Path a a) :
    Continuous (AddCircle.liftIco (1 : ℝ) 0 gamma.extend) := by
  -- The half-open quotient lift is continuous because the endpoint values agree.
  apply AddCircle.liftIco_zero_continuous
  · simp
  · exact gamma.extend.continuous.continuousOn

/-- Helper for Exercise 72.3: the continuous additive-circle map obtained by
identifying the endpoints of a based loop. -/
private noncomputable def Path.toUnitAddCircleMap
    {X : Type*} [TopologicalSpace X] {a : X} (gamma : Path a a) :
    C(UnitAddCircle, X) :=
  ⟨AddCircle.liftIco (1 : ℝ) 0 gamma.extend,
    continuous_loopToUnitAddCircleMap gamma⟩

/-- Helper for Exercise 72.3: the descended map is definitionally the
half-open quotient lift. -/
private lemma Path.toUnitAddCircleMap_apply
    {X : Type*} [TopologicalSpace X] {a : X} (gamma : Path a a)
    (z : UnitAddCircle) :
    gamma.toUnitAddCircleMap z =
      AddCircle.liftIco (1 : ℝ) 0 gamma.extend z := by
  -- Expose only the function field of the local quotient construction.
  rfl

/-- Helper for Exercise 72.3: the descended additive-circle map agrees with
the loop on representatives in the half-open unit interval. -/
private lemma Path.toUnitAddCircleMap_coe_apply
    {X : Type*} [TopologicalSpace X] {a : X} (gamma : Path a a)
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) (1 : ℝ)) :
    gamma.toUnitAddCircleMap (t : UnitAddCircle) =
      gamma ⟨t, ht.1, ht.2.le⟩ := by
  -- Evaluate the quotient lift at its canonical representative.
  rw [gamma.toUnitAddCircleMap_apply,
    AddCircle.liftIco_zero_coe_apply ht]
  exact gamma.extend_extends' ⟨t, ht.1, ht.2.le⟩

/-- Helper for Exercise 72.3: the descended additive-circle map preserves the
chosen loop basepoint. -/
private lemma Path.toUnitAddCircleMap_zero
    {X : Type*} [TopologicalSpace X] {a : X} (gamma : Path a a) :
    gamma.toUnitAddCircleMap 0 = a := by
  -- Evaluate at the lower endpoint of the unit interval.
  calc
    gamma.toUnitAddCircleMap (0 : UnitAddCircle) = gamma (0 : unitInterval) :=
      gamma.toUnitAddCircleMap_coe_apply ⟨le_rfl, zero_lt_one⟩
    _ = a := gamma.source

/-- Helper for Exercise 72.3: the descended additive-circle map sends its
canonical once-around loop back to the original loop. -/
private lemma Path.unitAddCircleTurn_map_toUnitAddCircleMap
    {X : Type*} [TopologicalSpace X] {a : X} (gamma : Path a a) :
    (unitAddCircleTurn.map gamma.toUnitAddCircleMap.continuous).cast
        gamma.toUnitAddCircleMap_zero.symm
        gamma.toUnitAddCircleMap_zero.symm = gamma := by
  -- Compare representatives, treating the identified upper endpoint separately.
  ext t
  rw [Path.cast_coe]
  by_cases ht : (t : ℝ) < 1
  · exact gamma.toUnitAddCircleMap_coe_apply ⟨t.2.1, ht⟩
  · have htOne : t = 1 := by
      apply Subtype.ext
      exact le_antisymm t.2.2 (not_lt.mp ht)
    subst t
    calc
      gamma.toUnitAddCircleMap
          (((1 : unitInterval) : ℝ) : UnitAddCircle) =
          gamma.toUnitAddCircleMap (0 : UnitAddCircle) := by
        rw [unitAddCircleTurn_target]
      _ = gamma (0 : unitInterval) :=
        gamma.toUnitAddCircleMap_coe_apply ⟨le_rfl, zero_lt_one⟩
      _ = gamma (1 : unitInterval) := gamma.source.trans gamma.target.symm

/-- Helper for Exercise 72.3: the canonical once-around loop generates the
fundamental group of `UnitAddCircle`. -/
private lemma unitAddCircleTurnGenerates :
    Subgroup.zpowers
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk unitAddCircleTurn)) = ⊤ := by
  -- Compute the generator by lifting it from zero to one in the universal cover.
  let covering := AddCircle.isAddQuotientCoveringMap_coe (1 : ℝ)
  have zeroFiberMem : ((0 : ℝ) : UnitAddCircle) ∈
      ({0} : Set UnitAddCircle) := by
    simp
  have oneFiberMem : ((1 : ℝ) : UnitAddCircle) ∈
      ({0} : Set UnitAddCircle) := by
    simp
  let e0 : ((↑) : ℝ → UnitAddCircle) ⁻¹' ({0} : Set UnitAddCircle) :=
    ⟨0, zeroFiberMem⟩
  let e1 : ((↑) : ℝ → UnitAddCircle) ⁻¹' ({0} : Set UnitAddCircle) :=
    ⟨1, oneFiberMem⟩
  have realTurnTarget : ((1 : unitInterval) : ℝ) = 1 := rfl
  let realTurn : Path (0 : ℝ) 1 :=
    { toFun := fun t ↦ (t : ℝ)
      continuous_toFun := continuous_subtype_val
      source' := rfl
      target' := realTurnTarget }
  let generator : FundamentalGroup UnitAddCircle 0 :=
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk unitAddCircleTurn)
  have monodromyGenerator :
      covering.isCoveringMap.monodromy generator e0 = e1 := by
    apply covering.isCoveringMap.monodromy_eq_of_map_eq
      (Path.Homotopic.Quotient.mk realTurn)
    rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    rfl
  have oneSmul : (1 : ℤ) • (1 : ℝ) = 1 := by
    simp
  have oneMem : (1 : ℝ) ∈ AddSubgroup.zmultiples (1 : ℝ) := ⟨1, oneSmul⟩
  let period : AddSubgroup.zmultiples (1 : ℝ) := ⟨1, oneMem⟩
  have generatorCoordinate :
      covering.fundamentalGroupEquiv e0 generator =
        MulOpposite.op (Multiplicative.ofAdd period) := by
    apply covering.fundamentalGroupToMulOpposite_apply_eq_Iff.mpr
    change (period : ℝ) + (e0 : ℝ) =
      (covering.isCoveringMap.monodromy generator e0 : ℝ)
    rw [monodromyGenerator]
    norm_num [period, e0, e1]
  -- Every deck period is an integral power of the period-one generator.
  let coveringEquiv := covering.fundamentalGroupEquiv e0
  rw [Subgroup.eq_top_iff']
  intro z
  have imageMem : coveringEquiv z ∈
      Subgroup.zpowers (MulOpposite.op (Multiplicative.ofAdd period)) := by
    rw [Subgroup.mem_zpowers_iff]
    rcases (coveringEquiv z).unop.toAdd.property with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have additivePower : n • period = (coveringEquiv z).unop.toAdd := by
      apply Subtype.ext
      exact hn
    calc
      MulOpposite.op (Multiplicative.ofAdd period) ^ n =
          MulOpposite.op (Multiplicative.ofAdd period ^ n) := rfl
      _ = MulOpposite.op (Multiplicative.ofAdd (n • period)) :=
        congrArg MulOpposite.op (ofAdd_zsmul n period).symm
      _ = MulOpposite.op
          (Multiplicative.ofAdd (coveringEquiv z).unop.toAdd) :=
        congrArg (fun b ↦ MulOpposite.op (Multiplicative.ofAdd b)) additivePower
      _ = coveringEquiv z := rfl
  rw [← generatorCoordinate] at imageMem
  rw [Subgroup.mem_zpowers_iff] at imageMem ⊢
  obtain ⟨n, hn⟩ := imageMem
  refine ⟨n, coveringEquiv.injective ?_⟩
  rwa [map_zpow]

/-- Helper for Exercise 72.3: every based loop gives a disk-boundary attaching
map whose induced image has the same normal closure as the loop class. -/
private lemma FundamentalGroup.existsBoundaryMapNormalClosureEqLoopClass
    {X : Type u} [TopologicalSpace X] {a : X} (gamma : Path a a) :
    ∃ (f : C(StandardSphere.boundary 1, X))
      (p : StandardSphere.boundary 1), ∃ hp : f p = a,
      Subgroup.normalClosure (Set.range (FundamentalGroup.mapOfEq f hp)) =
        Subgroup.normalClosure
          ({FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk gamma)} :
            Set (FundamentalGroup X a)) := by
  -- Descend the loop to the additive circle and pull it back from the disk boundary.
  let circleMap := gamma.toUnitAddCircleMap
  have circleMap_zero : circleMap 0 = a := gamma.toUnitAddCircleMap_zero
  let boundaryEquiv := closedUnitDiskBoundaryHomeomorphCircle.trans
    (AddCircle.homeomorphCircle one_ne_zero).symm
  let p : StandardSphere.boundary 1 := boundaryEquiv.symm 0
  have boundaryEquiv_p : boundaryEquiv p = 0 := boundaryEquiv.apply_symm_apply 0
  let f : C(StandardSphere.boundary 1, X) :=
    circleMap.comp (boundaryEquiv : C(StandardSphere.boundary 1, UnitAddCircle))
  have hp : f p = a := by
    change circleMap (boundaryEquiv p) = a
    rw [boundaryEquiv_p]
    exact circleMap_zero
  refine ⟨f, p, hp, ?_⟩
  -- First compute the image of the additive-circle map from its fixed generator.
  let generator : FundamentalGroup UnitAddCircle 0 :=
    FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk unitAddCircleTurn)
  let loopClass : FundamentalGroup X a :=
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk gamma)
  let circleHom := FundamentalGroup.mapOfEq circleMap circleMap_zero
  have generatorImage : circleHom generator = loopClass := by
    rw [FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map,
      ← Path.Homotopic.Quotient.mk_cast,
      gamma.unitAddCircleTurn_map_toUnitAddCircleMap]
  have circleRange : circleHom.range = Subgroup.zpowers loopClass := by
    calc
      circleHom.range =
          (⊤ : Subgroup (FundamentalGroup UnitAddCircle 0)).map circleHom :=
        MonoidHom.range_eq_map circleHom
      _ = (Subgroup.zpowers generator).map circleHom :=
        congrArg
          (fun H : Subgroup (FundamentalGroup UnitAddCircle 0) ↦ H.map circleHom)
          unitAddCircleTurnGenerates.symm
      _ = Subgroup.zpowers (circleHom generator) :=
        MonoidHom.map_zpowers circleHom generator
      _ = Subgroup.zpowers loopClass := congrArg Subgroup.zpowers generatorImage
  -- The boundary homeomorphism is surjective on fundamental groups, so it does
  -- not alter the range after composition with the descended circle map.
  let boundaryHom := FundamentalGroup.mapOfEq
    (boundaryEquiv : C(StandardSphere.boundary 1, UnitAddCircle)) boundaryEquiv_p
  have boundaryHomSurjective : Function.Surjective boundaryHom :=
    (boundaryEquiv.fundamentalGroupMapOfEq_bijective p 0 boundaryEquiv_p).2
  have inducedComposite : circleHom.comp boundaryHom =
      FundamentalGroup.mapOfEq f hp := by
    exact FundamentalGroup.mapOfEq_comp
      (boundaryEquiv : C(StandardSphere.boundary 1, UnitAddCircle)) circleMap
      boundaryEquiv_p circleMap_zero hp
  have boundaryRange : (FundamentalGroup.mapOfEq f hp).range = circleHom.range := by
    calc
      (FundamentalGroup.mapOfEq f hp).range =
          (circleHom.comp boundaryHom).range :=
        congrArg MonoidHom.range inducedComposite.symm
      _ = boundaryHom.range.map circleHom :=
        MonoidHom.range_comp circleHom boundaryHom
      _ = (⊤ : Subgroup (FundamentalGroup UnitAddCircle 0)).map circleHom := by
        rw [MonoidHom.range_eq_top.mpr boundaryHomSurjective]
      _ = circleHom.range := (MonoidHom.range_eq_map circleHom).symm
  -- Replace the induced range by the cyclic subgroup and then normally close it.
  change Subgroup.normalClosure
      ((FundamentalGroup.mapOfEq f hp).range : Set (FundamentalGroup X a)) =
    Subgroup.normalClosure ({loopClass} : Set (FundamentalGroup X a))
  rw [boundaryRange, circleRange,
    Subgroup.normalClosure_zpowers_eq_normalClosure_singleton]

/-- Helper for Exercise 72.3: a surjective homomorphism carries the normal
closure of a homomorphic range to the normal closure of the composite range. -/
private lemma Subgroup.map_normalClosure_range_comp
    {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G →* H) (g : H →* K) (hg : Function.Surjective g) :
    (Subgroup.normalClosure (Set.range f)).map g =
      Subgroup.normalClosure (Set.range (g.comp f)) := by
  -- Move normal closure through the surjection, then identify the mapped range.
  rw [Subgroup.map_normalClosure _ g hg]
  change Subgroup.normalClosure ((f.range.map g : Subgroup K) : Set K) =
    Subgroup.normalClosure ((g.comp f).range : Set K)
  rw [← MonoidHom.range_comp]

/-- Helper for Exercise 72.3: adjoining one two-cell quotients the fundamental
group by the normal closure of the attaching-circle image. -/
private theorem AdjunctionSpace.twoCellFundamentalGroupQuotient
    {X : Type u} [TopologicalSpace X] [T4Space X] [PathConnectedSpace X]
    (f : C(StandardSphere.boundary 1, X)) (p : StandardSphere.boundary 1)
    (a : X) (hp : f p = a) :
    Nonempty
      (FundamentalGroup (AdjunctionSpace (StandardSphere.boundary 1) f)
          (AdjunctionSpace.includeY (StandardSphere.boundary 1) f a) ≃*
        FundamentalGroup X a ⧸
          Subgroup.normalClosure (Set.range (FundamentalGroup.mapOfEq f hp))) := by
  -- Name the canonical copy of `X` and the boundary restriction used by Theorem 72.1.
  let Y := AdjunctionSpace (StandardSphere.boundary 1) f
  let includeX : X → Y := AdjunctionSpace.includeY (StandardSphere.boundary 1) f
  let A : Set Y := Set.range includeX
  obtain ⟨hAClosed, hAPathConnected, hBoundary, hInterior⟩ :=
    twoCellAdjunctionSpace_attachmentSpec f
  let attachingMap : C(StandardSphere.boundary 1, A) :=
    ClosedUnitDisk.boundaryMap A (twoCellMap f) hBoundary
  let attachingPoint : A := attachingMap p
  let inclusionHom := FundamentalGroup.mapOfSubtype A attachingPoint
  have inclusionSurjective : Function.Surjective inclusionHom := by
    exact adjoinTwoCell_inclusion_surjective A hAClosed hAPathConnected
      (twoCellMap f) hBoundary hInterior p
  have inclusionKernel : inclusionHom.ker =
      Subgroup.normalClosure
        (Set.range (FundamentalGroup.map attachingMap p)) := by
    exact adjoinTwoCell_inclusion_ker A hAClosed hAPathConnected
      (twoCellMap f) hBoundary hInterior p
  -- The closed embedding identifies `X` homeomorphically with its canonical range.
  let rangeHomeomorph : X ≃ₜ A :=
    (twoCellIncludeA_isClosedEmbedding f).isEmbedding.toHomeomorph
  have attachingPointEq : attachingPoint = rangeHomeomorph a := by
    apply Subtype.ext
    change AdjunctionSpace.includeX (StandardSphere.boundary 1) f p =
      AdjunctionSpace.includeY (StandardSphere.boundary 1) f a
    rw [AdjunctionSpace.glue, hp]
  let sourceHom := FundamentalGroup.mapOfEq
    (rangeHomeomorph : C(X, A)) attachingPointEq.symm
  have sourceBijective : Function.Bijective sourceHom := by
    exact rangeHomeomorph.fundamentalGroupMapOfEq_bijective
      a attachingPoint attachingPointEq.symm
  let sourceEquiv := MulEquiv.ofBijective sourceHom sourceBijective
  -- The attaching map in the canonical range is the composite of `f` with that homeomorphism.
  have attachingComposite :
      (rangeHomeomorph : C(X, A)).comp f = attachingMap := by
    apply ContinuousMap.ext
    intro q
    apply Subtype.ext
    change AdjunctionSpace.includeY (StandardSphere.boundary 1) f (f q) =
      AdjunctionSpace.includeX (StandardSphere.boundary 1) f q
    exact (AdjunctionSpace.glue (StandardSphere.boundary 1) f q).symm
  have compositeBasepoint :
      ((rangeHomeomorph : C(X, A)).comp f) p = attachingPoint := by
    rw [attachingComposite]
  have inducedSquare : sourceHom.comp (FundamentalGroup.mapOfEq f hp) =
      FundamentalGroup.map attachingMap p := by
    calc
      sourceHom.comp (FundamentalGroup.mapOfEq f hp) =
          FundamentalGroup.mapOfEq
            ((rangeHomeomorph : C(X, A)).comp f) compositeBasepoint :=
        FundamentalGroup.mapOfEq_comp f (rangeHomeomorph : C(X, A))
          hp attachingPointEq.symm compositeBasepoint
      _ = FundamentalGroup.mapOfEq attachingMap rfl :=
        FundamentalGroup.mapOfEq_congr _ _ attachingComposite _ _
      _ = FundamentalGroup.map attachingMap p :=
        FundamentalGroup.mapOfEq_refl attachingMap p
  have normalClosureMap :
      (Subgroup.normalClosure
          (Set.range (FundamentalGroup.mapOfEq f hp))).map sourceHom =
        Subgroup.normalClosure
          (Set.range (FundamentalGroup.map attachingMap p)) := by
    calc
      (Subgroup.normalClosure
          (Set.range (FundamentalGroup.mapOfEq f hp))).map sourceHom =
          Subgroup.normalClosure
            (Set.range
              (sourceHom.comp (FundamentalGroup.mapOfEq f hp))) :=
        Subgroup.map_normalClosure_range_comp _ _ sourceBijective.2
      _ = Subgroup.normalClosure
          (Set.range (FundamentalGroup.map attachingMap p)) :=
        by rw [inducedSquare]
  have quotientSubgroup :
      (Subgroup.normalClosure
          (Set.range (FundamentalGroup.mapOfEq f hp))).map sourceEquiv =
        inclusionHom.ker := by
    calc
      (Subgroup.normalClosure
          (Set.range (FundamentalGroup.mapOfEq f hp))).map sourceEquiv =
          (Subgroup.normalClosure
            (Set.range (FundamentalGroup.mapOfEq f hp))).map sourceHom := rfl
      _ = Subgroup.normalClosure
          (Set.range (FundamentalGroup.map attachingMap p)) := normalClosureMap
      _ = inclusionHom.ker := inclusionKernel.symm
  let quotientEquiv := QuotientGroup.congr
    (Subgroup.normalClosure (Set.range (FundamentalGroup.mapOfEq f hp)))
    inclusionHom.ker sourceEquiv quotientSubgroup
  let firstEquiv :=
    QuotientGroup.quotientKerEquivOfSurjective inclusionHom inclusionSurjective
  have ambientBasepoint : (attachingPoint : Y) = includeX a := by
    exact congrArg Subtype.val attachingPointEq
  -- Compose basepoint transport, the first isomorphism theorem, and subgroup transport.
  let resultEquiv : FundamentalGroup Y (includeX a) ≃*
      FundamentalGroup X a ⧸
        Subgroup.normalClosure (Set.range (FundamentalGroup.mapOfEq f hp)) :=
    (MulEquiv.cast ambientBasepoint).symm.trans
      (firstEquiv.symm.trans quotientEquiv.symm)
  exact ⟨resultEquiv⟩

/-- Exercise 72.3: If a group is realized as the fundamental group of a normal,
path-connected space, then its quotient by the least normal subgroup containing
`x` is also realized by a normal, path-connected space. -/
theorem exists_t4Space_fundamentalGroup_quotient {G : Type u} [Group G] (x : G)
    (hG : ∃ (X : Type v) (_ : TopologicalSpace X) (_ : T4Space X)
      (_ : PathConnectedSpace X) (a : X), Nonempty (FundamentalGroup X a ≃* G)) :
    ∃ (Y : Type v) (_ : TopologicalSpace Y) (_ : T4Space Y)
      (_ : PathConnectedSpace Y) (b : Y),
      Nonempty
        (FundamentalGroup Y b ≃* G ⧸ Subgroup.normalClosure ({x} : Set G)) := by
  -- Choose the realizing space and install its packaged topological instances.
  obtain ⟨X, topologyX, t4X, pathConnectedX, a, ⟨e⟩⟩ := hG
  letI : TopologicalSpace X := topologyX
  letI : T4Space X := t4X
  letI : PathConnectedSpace X := pathConnectedX
  -- Represent the group element by an actual based loop in `X`.
  obtain ⟨gamma, hgamma⟩ :=
    Path.Homotopic.Quotient.mk_surjective
      (FundamentalGroup.toPath (e.symm x))
  have loopClassEq :
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk gamma) = e.symm x := by
    calc
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk gamma) =
          FundamentalGroup.fromPath (FundamentalGroup.toPath (e.symm x)) :=
        congrArg FundamentalGroup.fromPath hgamma
      _ = e.symm x := rfl
  obtain ⟨f, p, hp, attachingClosure⟩ :=
    FundamentalGroup.existsBoundaryMapNormalClosureEqLoopClass gamma
  -- Attach one disk along that loop and use the two-cell quotient interface.
  let Y := AdjunctionSpace (StandardSphere.boundary 1) f
  letI : T4Space Y := twoCellAdjunctionSpaceT4Space f
  letI : PathConnectedSpace Y := AdjunctionSpace.twoCellPathConnectedSpace f
  let b : Y := AdjunctionSpace.includeY (StandardSphere.boundary 1) f a
  obtain ⟨cellEquiv⟩ :=
    AdjunctionSpace.twoCellFundamentalGroupQuotient f p a hp
  have attachingClosureEq :
      Subgroup.normalClosure (Set.range (FundamentalGroup.mapOfEq f hp)) =
        Subgroup.normalClosure ({e.symm x} : Set (FundamentalGroup X a)) := by
    calc
      Subgroup.normalClosure (Set.range (FundamentalGroup.mapOfEq f hp)) =
          Subgroup.normalClosure
            ({FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk gamma)} :
              Set (FundamentalGroup X a)) := attachingClosure
      _ = Subgroup.normalClosure ({e.symm x} : Set (FundamentalGroup X a)) := by
        rw [loopClassEq]
  let sourceQuotientEquiv :=
    QuotientGroup.quotientMulEquivOfEq attachingClosureEq
  -- The given group equivalence carries the chosen normal closure to that of `x`.
  have mappedClosure :
      (Subgroup.normalClosure ({e.symm x} : Set (FundamentalGroup X a))).map e =
        Subgroup.normalClosure ({x} : Set G) := by
    have mappedGenerator :
        (e : FundamentalGroup X a →* G) (e.symm x) = x :=
      e.apply_symm_apply x
    calc
      (Subgroup.normalClosure
          ({e.symm x} : Set (FundamentalGroup X a))).map e =
          Subgroup.normalClosure
            ((e : FundamentalGroup X a →* G) '' {e.symm x}) :=
        Subgroup.map_normalClosure _ (e : FundamentalGroup X a →* G) e.surjective
      _ = Subgroup.normalClosure ({x} : Set G) := by
        rw [Set.image_singleton, mappedGenerator]
  let targetQuotientEquiv := QuotientGroup.congr
    (Subgroup.normalClosure ({e.symm x} : Set (FundamentalGroup X a)))
    (Subgroup.normalClosure ({x} : Set G)) e mappedClosure
  let resultEquiv : FundamentalGroup Y b ≃*
      G ⧸ Subgroup.normalClosure ({x} : Set G) :=
    cellEquiv.trans (sourceQuotientEquiv.trans targetQuotientEquiv)
  -- Package the attached space, its canonical basepoint, and the composite equivalence.
  exact ⟨Y, inferInstance, inferInstance, inferInstance, b, ⟨resultEquiv⟩⟩

end
