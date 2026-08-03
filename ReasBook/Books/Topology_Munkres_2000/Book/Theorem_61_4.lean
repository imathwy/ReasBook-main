module

public import Topology_Munkres_2000.Book.Theorem_61_3

import Topology_Munkres_2000.Book.Definition_9_0_2
import all Topology_Munkres_2000.Book.Lemma_55_1.Inclusions
import Mathlib.Topology.Separation.Connected

public section

open Set
open scoped Topology

/-- Helper for Theorem 61.4: the endpoints in an intersection equal to
`{p, q}` belong to both intersecting sets. -/
private lemma pair_mem_of_inter_eq_pair
    {X : Type*} {A₁ A₂ : Set X} {p q : X} (hinter : A₁ ∩ A₂ = {p, q}) :
    p ∈ A₁ ∧ p ∈ A₂ ∧ q ∈ A₁ ∧ q ∈ A₂ := by
  -- Rewrite both endpoints through the given intersection equation.
  have hp : p ∈ A₁ ∩ A₂ := by
    rw [hinter]
    simp
  have hq : q ∈ A₁ ∩ A₂ := by
    rw [hinter]
    simp
  exact ⟨hp.1, hp.2, hq.1, hq.2⟩

/-- Helper for Theorem 61.4: the complements of two sets meeting at the
punctures cover the twice-punctured ambient space. -/
private lemma pairComplement_preimage_compl_union_eq_univ
    {X : Type*} (A₁ A₂ : Set X) (p q : X) (hinter : A₁ ∩ A₂ = {p, q}) :
    (Subtype.val ⁻¹' A₁ᶜ : Set ({p, q}ᶜ : Set X)) ∪
        Subtype.val ⁻¹' A₂ᶜ = Set.univ := by
  -- A point outside `{p, q}` cannot belong to both sets.
  ext x
  simp only [Set.mem_union, Set.mem_preimage, Set.mem_compl_iff, Set.mem_univ, iff_true]
  by_contra h
  push Not at h
  have hx : x.1 ∈ A₁ ∩ A₂ := ⟨h.1, h.2⟩
  rw [hinter] at hx
  exact x.2 hx

/-- Helper for Theorem 61.4: the overlap of the two complement preimages is
the preimage of the complement of their union. -/
private lemma pairComplement_preimage_compl_inter
    {X : Type*} (A₁ A₂ : Set X) (p q : X) :
    (Subtype.val ⁻¹' A₁ᶜ : Set ({p, q}ᶜ : Set X)) ∩
        Subtype.val ⁻¹' A₂ᶜ = Subtype.val ⁻¹' (A₁ ∪ A₂)ᶜ := by
  -- Membership on each side is the same pair of nonmembership conditions.
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_union,
    not_or]

/-- Helper for Theorem 61.4: a point outside `{p, q}` avoids the first puncture. -/
private lemma pairComplement_ne_firstPuncture (p q : StandardSphere 2)
    (x : ({p, q}ᶜ : Set (StandardSphere 2))) : x.1 ≠ p := by
  -- First-puncture equality would put the point in the deleted pair.
  intro hxp
  exact x.2 (Or.inl hxp)

/-- Helper for Theorem 61.4: a point outside `{p, q}` avoids the second puncture. -/
private lemma pairComplement_ne_secondPuncture (p q : StandardSphere 2)
    (x : ({p, q}ᶜ : Set (StandardSphere 2))) : x.1 ≠ q := by
  -- Second-puncture equality would put the point in the deleted pair.
  intro hxq
  exact x.2 (Or.inr hxq)

/-- Helper for Theorem 61.4: a nested point avoiding both punctures belongs
to the complement of their pair. -/
private lemma nestedPuncture_mem_pairComplement (p q : StandardSphere 2)
    (x : {y : ({p}ᶜ : Set (StandardSphere 2)) // y.1 ≠ q}) :
    x.1.1 ∈ ({p, q}ᶜ : Set (StandardSphere 2)) := by
  -- Membership in the pair splits into the two excluded equalities.
  intro hx
  exact hx.elim x.1.2 x.2

/-- Helper for Theorem 61.4: forgetting the second puncture gives a nested
point of the once-punctured sphere. -/
private def pairComplementToNestedPuncture (p q : StandardSphere 2) :
    ({p, q}ᶜ : Set (StandardSphere 2)) →
      {x : ({p}ᶜ : Set (StandardSphere 2)) // x.1 ≠ q} :=
  fun x ↦ ⟨⟨x.1, pairComplement_ne_firstPuncture p q x⟩,
    pairComplement_ne_secondPuncture p q x⟩

/-- Helper for Theorem 61.4: flattening a nested puncture gives a point of
the twice-punctured sphere. -/
private def nestedPunctureToPairComplement (p q : StandardSphere 2) :
    {x : ({p}ᶜ : Set (StandardSphere 2)) // x.1 ≠ q} →
      ({p, q}ᶜ : Set (StandardSphere 2)) :=
  fun x ↦ ⟨x.1.1, nestedPuncture_mem_pairComplement p q x⟩

/-- Helper for Theorem 61.4: the nesting map between punctured spheres is
continuous. -/
private lemma continuous_pairComplementToNestedPuncture (p q : StandardSphere 2) :
    Continuous (pairComplementToNestedPuncture p q) := by
  -- Build continuity through the two subtype constructors.
  have hinner : Continuous (fun x : ({p, q}ᶜ : Set (StandardSphere 2)) ↦
      (⟨x.1, pairComplement_ne_firstPuncture p q x⟩ :
        ({p}ᶜ : Set (StandardSphere 2)))) :=
    continuous_subtype_val.subtype_mk
      (pairComplement_ne_firstPuncture p q)
  exact hinner.subtype_mk (pairComplement_ne_secondPuncture p q)

/-- Helper for Theorem 61.4: flattening the nested puncture is continuous. -/
private lemma continuous_nestedPunctureToPairComplement (p q : StandardSphere 2) :
    Continuous (nestedPunctureToPairComplement p q) := by
  -- The two subtype projections are continuous.
  exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
    (nestedPuncture_mem_pairComplement p q)

/-- Helper for Theorem 61.4: flattening after nesting fixes the pair
complement. -/
private lemma nestedPunctureToPairComplement_leftInverse (p q : StandardSphere 2) :
    Function.LeftInverse (nestedPunctureToPairComplement p q)
      (pairComplementToNestedPuncture p q) := by
  -- Subtype extensionality reduces the claim to the ambient point.
  intro x
  exact Subtype.coe_eta x _

/-- Helper for Theorem 61.4: nesting after flattening fixes the nested
puncture. -/
private lemma nestedPunctureToPairComplement_rightInverse (p q : StandardSphere 2) :
    Function.RightInverse (nestedPunctureToPairComplement p q)
      (pairComplementToNestedPuncture p q) := by
  -- Apply subtype extensionality at both nested levels.
  intro x
  exact Subtype.ext (Subtype.coe_eta x.1 _)

/-- Helper for Theorem 61.4: the pair complement is the second-point
complement inside the once-punctured sphere. -/
private def pairComplementHomeomorphNestedPuncture (p q : StandardSphere 2) :
    ({p, q}ᶜ : Set (StandardSphere 2)) ≃ₜ
      {x : ({p}ᶜ : Set (StandardSphere 2)) // x.1 ≠ q} :=
  { toFun := pairComplementToNestedPuncture p q
    invFun := nestedPunctureToPairComplement p q
    left_inv := nestedPunctureToPairComplement_leftInverse p q
    right_inv := nestedPunctureToPairComplement_rightInverse p q
    continuous_toFun := continuous_pairComplementToNestedPuncture p q
    continuous_invFun := continuous_nestedPunctureToPairComplement p q }

/-- Helper for Theorem 61.4: the second point belongs to the complement of
the first distinct point. -/
private lemma secondPoint_mem_firstPointComplement
    (p q : StandardSphere 2) (hpq : p ≠ q) : q ∈ ({p}ᶜ : Set (StandardSphere 2)) := by
  -- Complement membership is reversed distinctness.
  simpa using hpq.symm

/-- Helper for Theorem 61.4: stereographic coordinates identify a punctured
two-sphere with the complex plane. -/
private noncomputable def puncturedSphereHomeomorphComplex (p : StandardSphere 2) :
    ({p}ᶜ : Set (StandardSphere 2)) ≃ₜ ℂ :=
  (StandardSphere.puncturedHomeomorphPlane p).trans
    Complex.orthonormalBasisOneI.repr.symm.toHomeomorph

/-- Helper for Theorem 61.4: translated stereographic coordinates send the
second puncture to zero. -/
private noncomputable def translatedPuncturedSphereChart
    (p q : StandardSphere 2) (hpq : p ≠ q) :
    ({p}ᶜ : Set (StandardSphere 2)) ≃ₜ ℂ :=
  (puncturedSphereHomeomorphComplex p).trans
    (Homeomorph.subRight
      (puncturedSphereHomeomorphComplex p
        ⟨q, secondPoint_mem_firstPointComplement p q hpq⟩))

/-- Helper for Theorem 61.4: the translated chart is nonzero exactly away
from the second puncture. -/
private lemma translatedPuncturedSphereChart_ne_zero_iff
    (p q : StandardSphere 2) (hpq : p ≠ q)
    (x : ({p}ᶜ : Set (StandardSphere 2))) :
    x.1 ≠ q ↔ translatedPuncturedSphereChart p q hpq x ≠ 0 := by
  -- Translation changes nonvanishing into inequality with the chart image of `q`.
  simp only [translatedPuncturedSphereChart, Homeomorph.trans_apply,
    Homeomorph.subRight_apply, sub_ne_zero]
  rw [(puncturedSphereHomeomorphComplex p).injective.ne_iff]
  simpa using (Subtype.coe_ne_coe (a := x)
    (b := (⟨q, secondPoint_mem_firstPointComplement p q hpq⟩ :
      ({p}ᶜ : Set (StandardSphere 2)))))

/-- Helper for Theorem 61.4: stereographic projection and translation
identify the twice-punctured sphere with the punctured complex plane. -/
private noncomputable def twicePuncturedSphereHomeomorphPuncturedComplexPlane
    (p q : StandardSphere 2) (hpq : p ≠ q) :
    ({p, q}ᶜ : Set (StandardSphere 2)) ≃ₜ {z : ℂ // z ≠ 0} :=
  (pairComplementHomeomorphNestedPuncture p q).trans
    ((translatedPuncturedSphereChart p q hpq).subtype
      (translatedPuncturedSphereChart_ne_zero_iff p q hpq))

/-- Helper for Theorem 61.4: polar and logarithmic coordinates identify the
punctured complex plane with the infinite cylinder. -/
private noncomputable def puncturedComplexPlaneHomeomorphInfiniteCylinder :
    {z : ℂ // z ≠ 0} ≃ₜ Circle × ℝ :=
  Complex.polarHomeomorph.symm.trans
    ((Homeomorph.refl Circle).prodCongr Real.expOrderIso.toHomeomorph.symm)

/-- Helper for Theorem 61.4: the infinite cylinder has infinite-cyclic
fundamental group at every basepoint. -/
private lemma fundamentalGroupInfiniteCylinderEquivInt (p : Circle × ℝ) :
    Nonempty (FundamentalGroup (Circle × ℝ) p ≃* Multiplicative ℤ) := by
  -- Remove the contractible real factor and change the circle basepoint.
  exact ⟨(FundamentalGroup.prodMulEquivLeftOfSubsingleton p.1 p.2 inferInstance).trans
    ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected p.1 1).trans
      Circle.fundamentalGroupEquivInt)⟩

/-- Helper for Theorem 61.4: the punctured complex plane has infinite-cyclic
fundamental group at every basepoint. -/
private lemma puncturedComplexPlaneFundamentalGroupEquivInt
    (z : {z : ℂ // z ≠ 0}) :
    Nonempty (FundamentalGroup {z : ℂ // z ≠ 0} z ≃* Multiplicative ℤ) := by
  -- Transport the cylinder calculation through polar coordinates.
  let e := puncturedComplexPlaneHomeomorphInfiniteCylinder
  exact ⟨(e.fundamentalGroupMulEquiv z).trans
    (fundamentalGroupInfiniteCylinderEquivInt (e z)).some⟩

/-- Helper for Theorem 61.4: the twice-punctured two-sphere has
infinite-cyclic fundamental group at every basepoint. -/
private lemma pairComplementFundamentalGroupEquivInt
    (p q : StandardSphere 2) (hpq : p ≠ q)
    (x : ({p, q}ᶜ : Set (StandardSphere 2))) :
    Nonempty (FundamentalGroup ({p, q}ᶜ : Set (StandardSphere 2)) x ≃*
      Multiplicative ℤ) := by
  -- Transport first to the punctured plane and then to the cylinder.
  let e := twicePuncturedSphereHomeomorphPuncturedComplexPlane p q hpq
  exact ⟨(e.fundamentalGroupMulEquiv x).trans
    (puncturedComplexPlaneFundamentalGroupEquivInt (e x)).some⟩

/-- Helper for Theorem 61.4: the unit interval traverses the additive circle
once continuously. -/
private lemma continuous_unitAddCircleLoop :
    Continuous (fun t : unitInterval ↦ ((t : ℝ) : UnitAddCircle)) := by
  -- Compose interval inclusion with the quotient map.
  exact continuous_quotient_mk'.comp continuous_subtype_val

/-- Helper for Theorem 61.4: the once-around additive-circle loop starts at
the additive identity. -/
private lemma unitAddCircleLoop_source : (((0 : unitInterval) : ℝ) : UnitAddCircle) = 0 := by
  -- The quotient map preserves zero.
  simp

/-- Helper for Theorem 61.4: one period returns the additive-circle loop to
the additive identity. -/
private lemma unitAddCircleLoop_target : (((1 : unitInterval) : ℝ) : UnitAddCircle) = 0 := by
  -- The quotient identifies one period with zero.
  simpa only [Set.Icc.coe_one] using (AddCircle.coe_period (1 : ℝ))

/-- Helper for Theorem 61.4: the canonical loop traversing `UnitAddCircle`
once. -/
private def unitAddCircleLoop : Path (0 : UnitAddCircle) 0 :=
  { toFun := fun t ↦ ((t : ℝ) : UnitAddCircle)
    continuous_toFun := continuous_unitAddCircleLoop
    source' := unitAddCircleLoop_source
    target' := unitAddCircleLoop_target }

/-- Helper for Theorem 61.4: an endpoint-compatible loop descends
continuously to `UnitAddCircle`. -/
private lemma continuous_loopToUnitAddCircleMap
    {X : Type*} [TopologicalSpace X] {x : X} (gamma : Path x x) :
    Continuous (AddCircle.liftIco 1 0
      (gamma.toContinuousMap.comp ContinuousMap.projIccCM)) := by
  -- Use continuity of the half-open quotient lift and endpoint compatibility.
  apply AddCircle.liftIco_zero_continuous
  · simp [ContinuousMap.projIccCM, Set.projIcc, gamma.source, gamma.target]
  · exact (gamma.toContinuousMap.comp ContinuousMap.projIccCM).continuous.continuousOn

/-- Helper for Theorem 61.4: the continuous map on `UnitAddCircle` obtained
by identifying a loop's endpoints. -/
private noncomputable def loopToUnitAddCircleMap
    {X : Type*} [TopologicalSpace X] {x : X} (gamma : Path x x) :
    C(UnitAddCircle, X) :=
  ⟨AddCircle.liftIco 1 0
      (gamma.toContinuousMap.comp ContinuousMap.projIccCM),
    continuous_loopToUnitAddCircleMap gamma⟩

/-- Helper for Theorem 61.4: the descended loop is its half-open quotient
lift. -/
private lemma loopToUnitAddCircleMap_apply
    {X : Type*} [TopologicalSpace X] {x : X} (gamma : Path x x)
    (z : UnitAddCircle) :
    loopToUnitAddCircleMap gamma z =
      AddCircle.liftIco 1 0
        (gamma.toContinuousMap.comp ContinuousMap.projIccCM) z := by
  -- This is the defining application equation.
  rfl

/-- Helper for Theorem 61.4: away from the upper endpoint, the descended
loop agrees with its interval representative. -/
private lemma loopToUnitAddCircleMap_coe_apply
    {X : Type*} [TopologicalSpace X] {x : X} (gamma : Path x x)
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    loopToUnitAddCircleMap gamma (t : UnitAddCircle) =
      gamma ⟨t, ht.1, ht.2.le⟩ := by
  -- Evaluate the quotient lift on its canonical representative.
  rw [loopToUnitAddCircleMap_apply, AddCircle.liftIco_zero_coe_apply ht]
  exact ContinuousMap.IccExtendCM_of_mem ⟨ht.1, ht.2.le⟩

/-- Helper for Theorem 61.4: the descended loop sends the additive identity
to the original basepoint. -/
private lemma loopToUnitAddCircleMap_apply_zero
    {X : Type*} [TopologicalSpace X] {x : X} (gamma : Path x x) :
    loopToUnitAddCircleMap gamma (0 : UnitAddCircle) = x := by
  -- Evaluate at the interval's lower endpoint.
  calc
    loopToUnitAddCircleMap gamma (0 : UnitAddCircle) = gamma (0 : unitInterval) :=
      loopToUnitAddCircleMap_coe_apply gamma ⟨le_rfl, zero_lt_one⟩
    _ = x := gamma.source

/-- Helper for Theorem 61.4: pulling the descended map back along the
once-around loop recovers the original loop. -/
private lemma unitAddCircleLoop_map_loopToUnitAddCircleMap
    {X : Type*} [TopologicalSpace X] {x : X} (gamma : Path x x) :
    (unitAddCircleLoop.map (loopToUnitAddCircleMap gamma).continuous).cast
      (loopToUnitAddCircleMap_apply_zero gamma).symm
      (loopToUnitAddCircleMap_apply_zero gamma).symm = gamma := by
  -- Compare interval points, treating the identified upper endpoint separately.
  ext t
  rw [Path.cast_coe]
  by_cases ht : (t : ℝ) < 1
  · exact loopToUnitAddCircleMap_coe_apply gamma ⟨t.2.1, ht⟩
  · have htOne : t = 1 := by
      apply Subtype.ext
      exact le_antisymm t.2.2 (not_lt.mp ht)
    subst t
    have hperiod :
        loopToUnitAddCircleMap gamma (((1 : unitInterval) : ℝ) : UnitAddCircle) =
          loopToUnitAddCircleMap gamma (0 : UnitAddCircle) := by
      rw [unitAddCircleLoop_target]
    have hzeroValue :
        loopToUnitAddCircleMap gamma (0 : UnitAddCircle) =
          gamma (0 : unitInterval) := by
      exact loopToUnitAddCircleMap_coe_apply gamma ⟨le_rfl, zero_lt_one⟩
    calc
      loopToUnitAddCircleMap gamma (((1 : unitInterval) : ℝ) : UnitAddCircle) =
          loopToUnitAddCircleMap gamma (0 : UnitAddCircle) := hperiod
      _ = gamma (0 : unitInterval) := hzeroValue
      _ = gamma (1 : unitInterval) := gamma.source.trans gamma.target.symm

/-- Helper for Theorem 61.4: inclusion of the complement of a connected set
containing both punctures induces the trivial fundamental-group map. -/
private lemma fundamentalGroupMapPairComplementInclusion_eq_one
    (A : Set (StandardSphere 2)) (hAconnected : IsConnected A)
    (p q : StandardSphere 2) (hp : p ∈ A) (hq : q ∈ A)
    (x : (Subtype.val ⁻¹' Aᶜ : Set ({p, q}ᶜ : Set (StandardSphere 2)))) :
    FundamentalGroup.mapOfSubtype (Subtype.val ⁻¹' Aᶜ) x = 1 := by
  unfold FundamentalGroup.mapOfSubtype
  let inclusion : C((Subtype.val ⁻¹' Aᶜ :
      Set ({p, q}ᶜ : Set (StandardSphere 2))),
      ({p, q}ᶜ : Set (StandardSphere 2))) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  -- Represent an arbitrary loop through the compact additive circle.
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
      -- The preceding nulhomotopy lemma applies because both punctures lie in
      -- the connected set `A` disjoint from the circle map.
      have hcircleNull : circleMap.Nullhomotopic :=
        nulhomotopyLemma p q circleMap hqComponent
      have hcircleMapLeft :=
        fundamentalGroupMap_eq_one_of_nullhomotopic
          circleMap (0 : UnitAddCircle) hcircleNull
      have hcircleMap : FundamentalGroup.map circleMap (0 : UnitAddCircle) = 1 :=
        MonoidHom.op.injective hcircleMapLeft
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
      -- Recover the original mapped loop class from the once-around circle class.
      rw [FundamentalGroup.map_apply, FundamentalGroup.one_def,
        ← Path.Homotopic.Quotient.mk_map]
      have hreflCast :
          (Path.Homotopic.Quotient.refl (circleMap 0)).cast
              hbase.symm hbase.symm =
            Path.Homotopic.Quotient.refl (inclusion x) := by
        rw [← Path.Homotopic.Quotient.mk_refl,
          ← Path.Homotopic.Quotient.mk_cast]
        congr 1
        apply DFunLike.ext _ _
        intro t
        rw [Path.cast_coe]
        exact hbase
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
        _ = Path.Homotopic.Quotient.refl (inclusion x) := hreflCast

/-- Helper for Theorem 61.4: a connected subset of a T1 space containing
two distinct points contains a point different from both. -/
private lemma exists_mem_ne_pair_of_isConnected
    {X : Type*} [TopologicalSpace X] [T1Space X] {A : Set X}
    {p q : X} (hAconnected : IsConnected A) (hp : p ∈ A) (hq : q ∈ A)
    (hpq : p ≠ q) :
    ∃ r ∈ A, r ≠ p ∧ r ≠ q := by
  classical
  -- Connectedness and the two distinct members make the set infinite.
  have hAinfinite : A.Infinite :=
    hAconnected.isPreconnected.infinite_of_nontrivial
      (Set.nontrivial_of_mem_mem_ne hp hq hpq)
  -- Avoid the prescribed pair inside that infinite set.
  obtain ⟨r, hrA, hr⟩ :=
    hAinfinite.exists_notMem_finset ({p, q} : Finset X)
  refine ⟨r, hrA, ?_, ?_⟩
  · intro hrp
    apply hr
    exact Finset.mem_insert.mpr (Or.inl hrp)
  · intro hrq
    apply hr
    exact Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton.mpr hrq))

/-- Helper for Theorem 61.4: two closed connected sets meeting in exactly two
distinct points cannot cover an ambient space whose pair complement is preconnected. -/
private lemma union_ne_univ_of_inter_pair
    {X : Type*} [TopologicalSpace X] [T1Space X]
    (A₁ A₂ : Set X) (p q : X) (hpq : p ≠ q)
    (hinter : A₁ ∩ A₂ = {p, q})
    (hA₁closed : IsClosed A₁) (hA₂closed : IsClosed A₂)
    (hA₁connected : IsConnected A₁) (hA₂connected : IsConnected A₂)
    (hpairPreconnected : IsPreconnected ({p, q}ᶜ : Set X)) :
    A₁ ∪ A₂ ≠ Set.univ := by
  classical
  -- View the two ambient complements as an open cover of the pair complement.
  have hpqMem := pair_mem_of_inter_eq_pair hinter
  let P : Set X := {p, q}ᶜ
  let U : Set P := Subtype.val ⁻¹' A₁ᶜ
  let V : Set P := Subtype.val ⁻¹' A₂ᶜ
  have hUopen : IsOpen U :=
    hA₁closed.isOpen_compl.preimage continuous_subtype_val
  have hVopen : IsOpen V :=
    hA₂closed.isOpen_compl.preimage continuous_subtype_val
  have hcover : U ∪ V = Set.univ :=
    pairComplement_preimage_compl_union_eq_univ A₁ A₂ p q hinter
  -- A third point in each connected set witnesses that neither cover member is universal.
  have hUcompl : Uᶜ.Nonempty := by
    obtain ⟨r, hrA₁, hrp, hrq⟩ :=
      exists_mem_ne_pair_of_isConnected hA₁connected hpqMem.1 hpqMem.2.2.1 hpq
    have hrP : r ∈ P := by
      simpa only [P, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] using
        ⟨hrp, hrq⟩
    let rP : P := ⟨r, hrP⟩
    refine ⟨rP, ?_⟩
    simpa only [U, mem_compl_iff, mem_preimage, not_not] using hrA₁
  have hVcompl : Vᶜ.Nonempty := by
    obtain ⟨r, hrA₂, hrp, hrq⟩ :=
      exists_mem_ne_pair_of_isConnected hA₂connected hpqMem.2.1 hpqMem.2.2.2 hpq
    have hrP : r ∈ P := by
      simpa only [P, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] using
        ⟨hrp, hrq⟩
    let rP : P := ⟨r, hrP⟩
    refine ⟨rP, ?_⟩
    simpa only [V, mem_compl_iff, mem_preimage, not_not] using hrA₂
  have hPpreconnected : IsPreconnected P := by
    simpa only [P] using hpairPreconnected
  letI : PreconnectedSpace P :=
    isPreconnected_iff_preconnectedSpace.mp hPpreconnected
  -- If the union were universal, the cover would be disjoint, contradicting preconnectedness.
  intro hunion
  have hdisjoint : Disjoint U V := by
    rw [Set.disjoint_iff_inter_eq_empty]
    dsimp only [U, V]
    rw [pairComplement_preimage_compl_inter A₁ A₂ p q, hunion]
    simp
  have hcoverSubset : (Set.univ : Set P) ⊆ U ∪ V := by
    rw [hcover]
  obtain hPU | hPV := isPreconnected_univ.subset_or_subset
    hUopen hVopen hdisjoint hcoverSubset
  · obtain ⟨x, hx⟩ := hUcompl
    exact hx (hPU (mem_univ x))
  · obtain ⟨x, hx⟩ := hVcompl
    exact hx (hPV (mem_univ x))

/-- Theorem 61.4 (A general separation theorem): If `A₁` and `A₂` are closed
connected subsets of the standard two-sphere whose intersection is exactly the
two-point set `{a, b}`, where `a ≠ b`, then `A₁ ∪ A₂` separates the sphere. -/
theorem union_separates_of_inter_pair
    (A₁ A₂ : Set (StandardSphere 2)) (a b : StandardSphere 2)
    (ha_ne_b : a ≠ b) (hinter : A₁ ∩ A₂ = {a, b})
    (hA₁closed : IsClosed A₁) (hA₂closed : IsClosed A₂)
    (hA₁connected : IsConnected A₁) (hA₂connected : IsConnected A₂) :
    (A₁ ∪ A₂).Separates := by
  classical
  rw [Set.separates_iff]
  intro hpreconnected
  -- Work in the sphere with the two common points removed.
  have habMem := pair_mem_of_inter_eq_pair hinter
  let P : Set (StandardSphere 2) := {a, b}ᶜ
  let U : Set P := Subtype.val ⁻¹' A₁ᶜ
  let V : Set P := Subtype.val ⁻¹' A₂ᶜ
  let W : Set (StandardSphere 2) := (A₁ ∪ A₂)ᶜ
  have hUopen : IsOpen U :=
    hA₁closed.isOpen_compl.preimage continuous_subtype_val
  have hVopen : IsOpen V :=
    hA₂closed.isOpen_compl.preimage continuous_subtype_val
  have hcover : U ∪ V = Set.univ :=
    pairComplement_preimage_compl_union_eq_univ A₁ A₂ a b hinter
  have hWinter : U ∩ V = Subtype.val ⁻¹' W :=
    pairComplement_preimage_compl_inter A₁ A₂ a b
  have hWsubset : W ⊆ P := by
    intro x hxW hxPair
    rcases hxPair with hxa | hxb
    · exact hxW (Or.inl (hxa ▸ habMem.1))
    · exact hxW (Or.inl (hxb ▸ habMem.2.2.1))
  let chart := twicePuncturedSphereHomeomorphPuncturedComplexPlane a b ha_ne_b
  -- Exponential coordinates show that the twice-punctured sphere is path connected.
  let exponential : C(ℂ, {z : ℂ // z ≠ 0}) :=
    ⟨fun z ↦ ⟨Complex.exp z, Complex.exp_ne_zero z⟩,
      Complex.continuous_exp.subtype_mk _⟩
  have hexponentialSurjective : Function.Surjective exponential := by
    intro z
    refine ⟨Complex.log z, ?_⟩
    exact Subtype.ext (Complex.exp_log z.2)
  letI : PathConnectedSpace {z : ℂ // z ≠ 0} :=
    hexponentialSurjective.pathConnectedSpace exponential.continuous
  letI : PathConnectedSpace P :=
    chart.symm.surjective.pathConnectedSpace chart.symm.continuous
  -- The source's non-universality step supplies a point in the overlap.
  have hpairPreconnected : IsPreconnected P :=
    isPreconnected_iff_preconnectedSpace.mpr inferInstance
  have hpairComplementPreconnected :
      IsPreconnected ({a, b}ᶜ : Set (StandardSphere 2)) := by
    simpa only [P] using hpairPreconnected
  have hunionNe : A₁ ∪ A₂ ≠ Set.univ :=
    union_ne_univ_of_inter_pair A₁ A₂ a b ha_ne_b hinter hA₁closed hA₂closed
      hA₁connected hA₂connected hpairComplementPreconnected
  have hWnonempty : W.Nonempty := by
    simpa only [W] using Set.nonempty_compl.mpr hunionNe
  obtain ⟨w₀, hw₀⟩ := hWnonempty
  let x₀ : P := ⟨w₀, hWsubset hw₀⟩
  have hx₀ : x₀ ∈ U ∩ V := by
    rw [hWinter]
    exact hw₀
  -- Transfer the assumed preconnectedness of the ambient complement to the overlap.
  letI : PreconnectedSpace W := by
    simpa only [W] using hpreconnected
  have hWpreconnected : IsPreconnected W :=
    isPreconnected_iff_preconnectedSpace.mpr inferInstance
  have hoverlapImage :
      ((fun x : P ↦ x.1) '' (U ∩ V)) = W := by
    rw [hWinter, Subtype.image_preimage_coe,
      Set.inter_eq_right.mpr hWsubset]
  have hoverlapPreconnected : IsPreconnected (U ∩ V) := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [hoverlapImage]
    exact hWpreconnected
  have hoverlapConnected : IsConnected (U ∩ V) :=
    ⟨⟨x₀, hx₀⟩, hoverlapPreconnected⟩
  -- The overlap is open in a locally path-connected punctured sphere.
  letI : LocallyPathConnectedSpace (StandardSphere 2) :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin 2)) (StandardSphere 2)
  have hPopen : IsOpen P := by
    dsimp only [P]
    exact ((Set.finite_singleton b).insert a).isClosed.isOpen_compl
  letI : LocallyPathConnectedSpace P := hPopen.locallyPathConnectedSpace
  have hoverlapOpen : IsOpen (U ∩ V) := hUopen.inter hVopen
  have hoverlapPathConnected : IsPathConnected (U ∩ V) :=
    hoverlapOpen.isConnected_iff_isPathConnected.mp hoverlapConnected
  letI : PathConnectedSpace (U ∩ V : Set P) :=
    isPathConnected_iff_pathConnectedSpace.mp hoverlapPathConnected
  -- Connectedness of each `Aᵢ` makes the two van Kampen generators trivial.
  have hUmap : FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩ = 1 :=
    fundamentalGroupMapPairComplementInclusion_eq_one A₁ hA₁connected
      a b habMem.1 habMem.2.2.1 ⟨x₀, hx₀.1⟩
  have hVmap : FundamentalGroup.mapOfSubtype V ⟨x₀, hx₀.2⟩ = 1 :=
    fundamentalGroupMapPairComplementInclusion_eq_one A₂ hA₂connected
      a b habMem.2.1 habMem.2.2.2 ⟨x₀, hx₀.2⟩
  have hgenerated :=
    fundamentalGroupMap_range_sup_range_eq_top U V x₀ hx₀ hUopen hVopen hcover
  have hbotTop : (⊥ : Subgroup (FundamentalGroup P x₀)) = ⊤ := by
    simpa only [hUmap, hVmap, MonoidHom.range_one, sup_idem] using hgenerated
  have hgroup : Subsingleton (FundamentalGroup P x₀) :=
    Subgroup.subsingleton_iff.mp (subsingleton_iff_bot_eq_top.mp hbotTop)
  -- This contradicts the infinite-cyclic fundamental group of the pair complement.
  let cyclic := (pairComplementFundamentalGroupEquivInt a b ha_ne_b x₀).some
  have hcyclic : Subsingleton (Multiplicative ℤ) :=
    cyclic.toEquiv.subsingleton_congr.mp hgroup
  have hone : Multiplicative.ofAdd (1 : ℤ) = 1 := hcyclic.elim _ _
  norm_num at hone
