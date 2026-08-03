module

public import Topology_Munkres_2000.Book.Definition_61_1.Separation
public import Topology_Munkres_2000.Book.Definition_61_2.Arc
public import Topology_Munkres_2000.Book.Definition_61_3.SimpleClosedCurve
public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Topology_Munkres_2000.Book.Corollary_58_6
public import Topology_Munkres_2000.Book.Example_53_6.Polar
public import Topology_Munkres_2000.Book.Exercise_54_7.Product
public import Topology_Munkres_2000.Book.Lemma_55_1.Inclusions
public import Topology_Munkres_2000.Book.Lemma_61_2
public import Topology_Munkres_2000.Book.Proposition_61_1.Stereographic
public import Topology_Munkres_2000.Book.Theorem_54_5.FundamentalGroup
public import Topology_Munkres_2000.Book.Theorem_59_1
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Topology.ContinuousMap.Interval

import Topology_Munkres_2000.Book.Definition_9_0_2
import all Topology_Munkres_2000.Book.Lemma_55_1.Inclusions

public section

open Set
open scoped Topology

/-- Helper for Theorem 61.3: the endpoints in an intersection equal to
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

/-- Helper for Theorem 61.3: the complements of two sets meeting at the
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

/-- Helper for Theorem 61.3: the overlap of the two complement preimages is
the preimage of the complement of their union. -/
private lemma pairComplement_preimage_compl_inter
    {X : Type*} (A₁ A₂ : Set X) (p q : X) :
    (Subtype.val ⁻¹' A₁ᶜ : Set ({p, q}ᶜ : Set X)) ∩
        Subtype.val ⁻¹' A₂ᶜ = Subtype.val ⁻¹' (A₁ ∪ A₂)ᶜ := by
  -- Membership on each side is the same pair of nonmembership conditions.
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_union,
    not_or]

/-- Helper for Theorem 61.3: a spherical arc is closed and connected. -/
private lemma isClosed_and_isConnected_of_isArc
    (A : Set (StandardSphere 2)) [Topology.IsArc A] :
    IsClosed A ∧ IsConnected A := by
  classical
  -- Transport compactness and connectedness from the unit interval model.
  obtain ⟨e⟩ := Topology.IsArc.homeomorphic_unitInterval (X := A)
  letI : CompactSpace A := e.symm.compactSpace
  letI : ConnectedSpace A := e.symm.surjective.connectedSpace e.symm.continuous
  have hcompact : IsCompact A := isCompact_iff_compactSpace.mpr inferInstance
  exact ⟨hcompact.isClosed, isConnected_iff_connectedSpace.mpr inferInstance⟩

/-- Helper for Theorem 61.3: an arc contains a point distinct from any two
prescribed points of the arc. -/
private lemma exists_mem_arc_ne_pair
    (A : Set (StandardSphere 2)) [Topology.IsArc A]
    (p q : StandardSphere 2) (hp : p ∈ A) (hq : q ∈ A) :
    ∃ r ∈ A, r ≠ p ∧ r ≠ q := by
  classical
  -- Transfer infinitude from the unit interval and avoid the two endpoints.
  obtain ⟨e⟩ := Topology.IsArc.homeomorphic_unitInterval (X := A)
  have hzeroOne : (0 : ℝ) < 1 := by
    norm_num
  letI : Infinite unitInterval := Set.Icc.infinite hzeroOne
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

/-- Helper for Theorem 61.3: forgetting the second puncture gives a nested
point of the once-punctured sphere. -/
private def pairComplementToNestedPuncture (p q : StandardSphere 2) :
    ({p, q}ᶜ : Set (StandardSphere 2)) →
      {x : ({p}ᶜ : Set (StandardSphere 2)) // x.1 ≠ q} :=
  fun x ↦ ⟨⟨x.1, fun hp ↦ x.2 (Or.inl hp)⟩, fun hq ↦ x.2 (Or.inr hq)⟩

/-- Helper for Theorem 61.3: flattening a nested puncture gives a point of
the twice-punctured sphere. -/
private def nestedPunctureToPairComplement (p q : StandardSphere 2) :
    {x : ({p}ᶜ : Set (StandardSphere 2)) // x.1 ≠ q} →
      ({p, q}ᶜ : Set (StandardSphere 2)) :=
  fun x ↦ ⟨x.1.1, fun h ↦ h.elim x.1.2 x.2⟩

/-- Helper for Theorem 61.3: the nesting map between punctured spheres is
continuous. -/
private lemma continuous_pairComplementToNestedPuncture (p q : StandardSphere 2) :
    Continuous (pairComplementToNestedPuncture p q) := by
  -- Build continuity through the two subtype constructors.
  have hinner : Continuous (fun x : ({p, q}ᶜ : Set (StandardSphere 2)) ↦
      (⟨x.1, fun hp ↦ x.2 (Or.inl hp)⟩ : ({p}ᶜ : Set (StandardSphere 2)))) :=
    continuous_subtype_val.subtype_mk
      (fun (x : ({p, q}ᶜ : Set (StandardSphere 2))) hp ↦ x.2 (Or.inl hp))
  exact hinner.subtype_mk (fun x hq ↦ x.2 (Or.inr hq))

/-- Helper for Theorem 61.3: flattening the nested puncture is continuous. -/
private lemma continuous_nestedPunctureToPairComplement (p q : StandardSphere 2) :
    Continuous (nestedPunctureToPairComplement p q) := by
  -- The two subtype projections are continuous.
  exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
    (fun x h ↦ h.elim x.1.2 x.2)

/-- Helper for Theorem 61.3: flattening after nesting fixes the pair
complement. -/
private lemma nestedPunctureToPairComplement_leftInverse (p q : StandardSphere 2) :
    Function.LeftInverse (nestedPunctureToPairComplement p q)
      (pairComplementToNestedPuncture p q) := by
  -- Subtype extensionality reduces the claim to the ambient point.
  intro x
  apply Subtype.ext
  rfl

/-- Helper for Theorem 61.3: nesting after flattening fixes the nested
puncture. -/
private lemma nestedPunctureToPairComplement_rightInverse (p q : StandardSphere 2) :
    Function.RightInverse (nestedPunctureToPairComplement p q)
      (pairComplementToNestedPuncture p q) := by
  -- Apply subtype extensionality at both nested levels.
  intro x
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- Helper for Theorem 61.3: the pair complement is the second-point
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

/-- Helper for Theorem 61.3: the second point belongs to the complement of
the first distinct point. -/
private lemma secondPoint_mem_firstPointComplement
    (p q : StandardSphere 2) (hpq : p ≠ q) : q ∈ ({p}ᶜ : Set (StandardSphere 2)) := by
  -- Complement membership is reversed distinctness.
  simpa using hpq.symm

/-- Helper for Theorem 61.3: stereographic coordinates identify a punctured
two-sphere with the complex plane. -/
private noncomputable def puncturedSphereHomeomorphComplex (p : StandardSphere 2) :
    ({p}ᶜ : Set (StandardSphere 2)) ≃ₜ ℂ :=
  (StandardSphere.puncturedHomeomorphPlane p).trans
    Complex.orthonormalBasisOneI.repr.symm.toHomeomorph

/-- Helper for Theorem 61.3: translated stereographic coordinates send the
second puncture to zero. -/
private noncomputable def translatedPuncturedSphereChart
    (p q : StandardSphere 2) (hpq : p ≠ q) :
    ({p}ᶜ : Set (StandardSphere 2)) ≃ₜ ℂ :=
  (puncturedSphereHomeomorphComplex p).trans
    (Homeomorph.subRight
      (puncturedSphereHomeomorphComplex p
        ⟨q, secondPoint_mem_firstPointComplement p q hpq⟩))

/-- Helper for Theorem 61.3: the translated chart is nonzero exactly away
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

/-- Helper for Theorem 61.3: stereographic projection and translation
identify the twice-punctured sphere with the punctured complex plane. -/
private noncomputable def twicePuncturedSphereHomeomorphPuncturedComplexPlane
    (p q : StandardSphere 2) (hpq : p ≠ q) :
    ({p, q}ᶜ : Set (StandardSphere 2)) ≃ₜ {z : ℂ // z ≠ 0} :=
  (pairComplementHomeomorphNestedPuncture p q).trans
    ((translatedPuncturedSphereChart p q hpq).subtype
      (translatedPuncturedSphereChart_ne_zero_iff p q hpq))

/-- Helper for Theorem 61.3: reconstructing a nested subtype after forgetting
its outer carrier fixes it. -/
private lemma nestedSubtypeToAmbient_leftInverse
    {X : Type*} [TopologicalSpace X] (P S : Set X) (hSP : S ⊆ P) :
    Function.LeftInverse
      (fun x : S ↦ (⟨⟨x.1, hSP x.2⟩, x.2⟩ :
        (Subtype.val ⁻¹' S : Set P)))
      (fun x : (Subtype.val ⁻¹' S : Set P) ↦ (⟨x.1.1, x.2⟩ : S)) := by
  -- Extensionality reduces the nested carrier equality to its ambient value.
  intro x
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- Helper for Theorem 61.3: forgetting the outer carrier after nested
reconstruction fixes the ambient subtype. -/
private lemma nestedSubtypeToAmbient_rightInverse
    {X : Type*} [TopologicalSpace X] (P S : Set X) (hSP : S ⊆ P) :
    Function.RightInverse
      (fun x : S ↦ (⟨⟨x.1, hSP x.2⟩, x.2⟩ :
        (Subtype.val ⁻¹' S : Set P)))
      (fun x : (Subtype.val ⁻¹' S : Set P) ↦ (⟨x.1.1, x.2⟩ : S)) := by
  -- Extensionality reduces the equality to the ambient value.
  intro x
  apply Subtype.ext
  rfl

/-- Helper for Theorem 61.3: a set inside a larger subtype is homeomorphic
to the same set viewed in the ambient space. -/
private def nestedSubtypeHomeomorph
    {X : Type*} [TopologicalSpace X] (P S : Set X) (hSP : S ⊆ P) :
    (Subtype.val ⁻¹' S : Set P) ≃ₜ S :=
  { toFun := fun x ↦ ⟨x.1.1, x.2⟩
    invFun := fun x ↦ ⟨⟨x.1, hSP x.2⟩, x.2⟩
    left_inv := nestedSubtypeToAmbient_leftInverse P S hSP
    right_inv := nestedSubtypeToAmbient_rightInverse P S hSP
    continuous_toFun :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk (fun x ↦ x.2)
    continuous_invFun :=
      (continuous_subtype_val.subtype_mk (fun x ↦ hSP x.2)).subtype_mk (fun x ↦ x.2) }

/-- Helper for Theorem 61.3: polar and logarithmic coordinates identify the
punctured complex plane with the infinite cylinder. -/
private noncomputable def puncturedComplexPlaneHomeomorphInfiniteCylinder :
    {z : ℂ // z ≠ 0} ≃ₜ Circle × ℝ :=
  Complex.polarHomeomorph.symm.trans
    ((Homeomorph.refl Circle).prodCongr Real.expOrderIso.toHomeomorph.symm)

/-- Helper for Theorem 61.3: the infinite cylinder has infinite-cyclic
fundamental group at every basepoint. -/
private lemma fundamentalGroupInfiniteCylinderEquivInt (p : Circle × ℝ) :
    Nonempty (FundamentalGroup (Circle × ℝ) p ≃* Multiplicative ℤ) := by
  -- Remove the contractible real factor and change the circle basepoint.
  exact ⟨(FundamentalGroup.prodMulEquivLeftOfSubsingleton p.1 p.2 inferInstance).trans
    ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected p.1 1).trans
      Circle.fundamentalGroupEquivInt)⟩

/-- Helper for Theorem 61.3: the punctured complex plane has infinite-cyclic
fundamental group at every basepoint. -/
private lemma fundamentalGroup_puncturedComplexPlane_equiv_int
    (z : {z : ℂ // z ≠ 0}) :
    Nonempty (FundamentalGroup {z : ℂ // z ≠ 0} z ≃* Multiplicative ℤ) := by
  -- Transport the cylinder calculation through polar coordinates.
  let e := puncturedComplexPlaneHomeomorphInfiniteCylinder
  exact ⟨(e.fundamentalGroupMulEquiv z).trans
    (fundamentalGroupInfiniteCylinderEquivInt (e z)).some⟩

/-- Helper for Theorem 61.3: the twice-punctured two-sphere has
infinite-cyclic fundamental group at every basepoint. -/
private lemma pairComplementFundamentalGroupEquivInt
    (p q : StandardSphere 2) (hpq : p ≠ q)
    (x : ({p, q}ᶜ : Set (StandardSphere 2))) :
    Nonempty (FundamentalGroup ({p, q}ᶜ : Set (StandardSphere 2)) x ≃*
      Multiplicative ℤ) := by
  -- Transport first to the punctured plane and then to the cylinder.
  let e := twicePuncturedSphereHomeomorphPuncturedComplexPlane p q hpq
  exact ⟨(e.fundamentalGroupMulEquiv x).trans
    (fundamentalGroup_puncturedComplexPlane_equiv_int (e x)).some⟩

/-- Helper for Theorem 61.3: the unit interval traverses the additive circle
once continuously. -/
private lemma continuous_unitAddCircleLoop :
    Continuous (fun t : unitInterval ↦ ((t : ℝ) : UnitAddCircle)) := by
  -- Compose interval inclusion with the quotient map.
  exact continuous_quotient_mk'.comp continuous_subtype_val

/-- Helper for Theorem 61.3: the once-around additive-circle loop starts at
the additive identity. -/
private lemma unitAddCircleLoop_source : (((0 : unitInterval) : ℝ) : UnitAddCircle) = 0 := by
  -- The quotient map preserves zero.
  simp

/-- Helper for Theorem 61.3: one period returns the additive-circle loop to
the additive identity. -/
private lemma unitAddCircleLoop_target : (((1 : unitInterval) : ℝ) : UnitAddCircle) = 0 := by
  -- The quotient identifies one period with zero.
  simpa only [Set.Icc.coe_one] using (AddCircle.coe_period (1 : ℝ))

/-- Helper for Theorem 61.3: the canonical loop traversing `UnitAddCircle`
once. -/
private def unitAddCircleLoop : Path (0 : UnitAddCircle) 0 :=
  { toFun := fun t ↦ ((t : ℝ) : UnitAddCircle)
    continuous_toFun := continuous_unitAddCircleLoop
    source' := unitAddCircleLoop_source
    target' := unitAddCircleLoop_target }

/-- Helper for Theorem 61.3: an endpoint-compatible loop descends
continuously to `UnitAddCircle`. -/
private lemma continuous_loopToUnitAddCircleMap
    {X : Type*} [TopologicalSpace X] {x : X} (gamma : Path x x) :
    Continuous (AddCircle.liftIco 1 0
      (gamma.toContinuousMap.comp ContinuousMap.projIccCM)) := by
  -- Use continuity of the half-open quotient lift and endpoint compatibility.
  apply AddCircle.liftIco_zero_continuous
  · simp [ContinuousMap.projIccCM, Set.projIcc, gamma.source, gamma.target]
  · exact (gamma.toContinuousMap.comp ContinuousMap.projIccCM).continuous.continuousOn

/-- Helper for Theorem 61.3: the continuous map on `UnitAddCircle` obtained
by identifying a loop's endpoints. -/
private noncomputable def loopToUnitAddCircleMap
    {X : Type*} [TopologicalSpace X] {x : X} (gamma : Path x x) :
    C(UnitAddCircle, X) :=
  ⟨AddCircle.liftIco 1 0
      (gamma.toContinuousMap.comp ContinuousMap.projIccCM),
    continuous_loopToUnitAddCircleMap gamma⟩

/-- Helper for Theorem 61.3: the descended loop is its half-open quotient
lift. -/
private lemma loopToUnitAddCircleMap_apply
    {X : Type*} [TopologicalSpace X] {x : X} (gamma : Path x x)
    (z : UnitAddCircle) :
    loopToUnitAddCircleMap gamma z =
      AddCircle.liftIco 1 0
        (gamma.toContinuousMap.comp ContinuousMap.projIccCM) z := by
  -- This is the defining application equation.
  rfl

/-- Helper for Theorem 61.3: away from the upper endpoint, the descended
loop agrees with its interval representative. -/
private lemma loopToUnitAddCircleMap_coe_apply
    {X : Type*} [TopologicalSpace X] {x : X} (gamma : Path x x)
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    loopToUnitAddCircleMap gamma (t : UnitAddCircle) =
      gamma ⟨t, ht.1, ht.2.le⟩ := by
  -- Evaluate the quotient lift on its canonical representative.
  rw [loopToUnitAddCircleMap_apply, AddCircle.liftIco_zero_coe_apply ht]
  exact ContinuousMap.IccExtendCM_of_mem ⟨ht.1, ht.2.le⟩

/-- Helper for Theorem 61.3: the descended loop sends the additive identity
to the original basepoint. -/
private lemma loopToUnitAddCircleMap_apply_zero
    {X : Type*} [TopologicalSpace X] {x : X} (gamma : Path x x) :
    loopToUnitAddCircleMap gamma (0 : UnitAddCircle) = x := by
  -- Evaluate at the interval's lower endpoint.
  calc
    loopToUnitAddCircleMap gamma (0 : UnitAddCircle) = gamma (0 : unitInterval) :=
      loopToUnitAddCircleMap_coe_apply gamma ⟨le_rfl, zero_lt_one⟩
    _ = x := gamma.source

/-- Helper for Theorem 61.3: pulling the descended map back along the
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
    calc
      loopToUnitAddCircleMap gamma (((1 : unitInterval) : ℝ) : UnitAddCircle) =
          loopToUnitAddCircleMap gamma (0 : UnitAddCircle) := by
            rw [unitAddCircleLoop_target]
      _ = gamma (0 : unitInterval) := by
        exact loopToUnitAddCircleMap_coe_apply gamma ⟨le_rfl, zero_lt_one⟩
      _ = gamma (1 : unitInterval) := gamma.source.trans gamma.target.symm

/-- Helper for Theorem 61.3: inclusion of the complement of a connected set
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

/-- Helper for Theorem 61.3: two spherical arcs meeting exactly at distinct
endpoints have separating union. -/
private lemma sphereArcPairUnionSeparates
    (A₁ A₂ : Set (StandardSphere 2)) [Topology.IsArc A₁] [Topology.IsArc A₂]
    (p q : StandardSphere 2) (hpq : p ≠ q) (hinter : A₁ ∩ A₂ = {p, q}) :
    (A₁ ∪ A₂).Separates := by
  classical
  rw [Set.separates_iff]
  intro hpreconnected
  -- Form the two open complements in the twice-punctured sphere.
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
  -- Interior arc points show neither open cover member is universal.
  have hUcompl : Uᶜ.Nonempty := by
    obtain ⟨r, hrA₁, hrp, hrq⟩ :=
      exists_mem_arc_ne_pair A₁ p q hpqMem.1 hpqMem.2.2.1
    have hrP : r ∈ P := by
      simpa only [P, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] using
        ⟨hrp, hrq⟩
    let rP : P := ⟨r, hrP⟩
    refine ⟨rP, ?_⟩
    simpa only [U, mem_compl_iff, mem_preimage, not_not] using hrA₁
  have hVcompl : Vᶜ.Nonempty := by
    obtain ⟨r, hrA₂, hrp, hrq⟩ :=
      exists_mem_arc_ne_pair A₂ p q hpqMem.2.1 hpqMem.2.2.2
    have hrP : r ∈ P := by
      simpa only [P, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] using
        ⟨hrp, hrq⟩
    let rP : P := ⟨r, hrP⟩
    refine ⟨rP, ?_⟩
    simpa only [V, mem_compl_iff, mem_preimage, not_not] using hrA₂
  -- The punctured plane, hence the pair complement, is path connected.
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
  -- Openness and the assumed preconnected complement make the overlap path connected.
  have hxWinter : x₀ ∈ Subtype.val ⁻¹' W := by
    rw [← hWinter]
    exact hx₀
  let w₀ : W := ⟨x₀.1, hxWinter⟩
  have hWopen : IsOpen W :=
    (hA₁geometry.1.union hA₂geometry.1).isOpen_compl
  letI : LocallyPathConnectedSpace (StandardSphere 2) :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin 2)) (StandardSphere 2)
  letI : LocallyPathConnectedSpace W := hWopen.locallyPathConnectedSpace
  letI : PreconnectedSpace W := by
    simpa only [W] using hpreconnected
  have hWconnected : IsConnected W :=
    ⟨⟨w₀.1, w₀.2⟩, isPreconnected_iff_preconnectedSpace.mpr inferInstance⟩
  letI : ConnectedSpace W := isConnected_iff_connectedSpace.mp hWconnected
  letI : PathConnectedSpace W := PathConnectedSpace.of_locallyPathConnectedSpace
  letI : PathConnectedSpace (U ∩ V : Set P) :=
    overlapHomeomorph.symm.surjective.pathConnectedSpace
      overlapHomeomorph.symm.continuous
  -- The nulhomotopy lemma trivializes both inclusion maps.
  have hUmap : FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩ = 1 :=
    fundamentalGroupMapPairComplementInclusion_eq_one A₁ hA₁geometry.2
      p q hpqMem.1 hpqMem.2.2.1 ⟨x₀, hx₀.1⟩
  have hVmap : FundamentalGroup.mapOfSubtype V ⟨x₀, hx₀.2⟩ = 1 :=
    fundamentalGroupMapPairComplementInclusion_eq_one A₂ hA₂geometry.2
      p q hpqMem.2.1 hpqMem.2.2.2 ⟨x₀, hx₀.2⟩
  have hgenerated :=
    fundamentalGroupMap_range_sup_range_eq_top U V x₀ hx₀ hUopen hVopen hcover
  have hbotTop : (⊥ : Subgroup (FundamentalGroup P x₀)) = ⊤ := by
    simpa only [hUmap, hVmap, MonoidHom.range_one, sup_idem] using hgenerated
  have hgroup : Subsingleton (FundamentalGroup P x₀) :=
    Subgroup.subsingleton_iff.mp (subsingleton_iff_bot_eq_top.mp hbotTop)
  -- The pair complement instead has fundamental group equivalent to `ℤ`.
  let cyclic := (pairComplementFundamentalGroupEquivInt p q hpq x₀).some
  have hcyclic : Subsingleton (Multiplicative ℤ) :=
    cyclic.toEquiv.subsingleton_congr.mp hgroup
  have hone : Multiplicative.ofAdd (1 : ℤ) = 1 := hcyclic.elim _ _
  norm_num at hone

/-- Helper for Theorem 61.3: every simple closed curve in a Hausdorff space
is the union of two arcs meeting exactly at distinct endpoints. -/
private lemma existsTwoArcDecomposition
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (D : Set X) [Topology.IsSimpleClosedCurve D] :
    ∃ D₁ D₂ : Set X, ∃ p q : X,
      p ≠ q ∧ D = D₁ ∪ D₂ ∧ D₁ ∩ D₂ = {p, q} ∧
        Topology.IsArc D₁ ∧ Topology.IsArc D₂ := by
  classical
  -- Transport the two canonical semicircular paths through a circle parametrization.
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
  -- The complementary semicircles cover the circle and meet at their endpoints.
  have hUnion : D = D₁ ∪ D₂ := by
    rw [hD₁image, hD₂image, ← Set.image_union,
      Circle.range_path_union_range_path (Circle.neg_ne_self 1).symm, Set.image_univ]
    exact hRange.symm
  have hInter : D₁ ∩ D₂ = {p, q} := by
    rw [hD₁image, hD₂image, ← Set.image_inter hfInjective,
      Circle.range_path_inter_range_path (Circle.neg_ne_self 1).symm, Set.image_pair]
  exact ⟨D₁, D₂, p, q, hpq, hUnion, hInter, hD₁Arc, hD₂Arc⟩

/-- Theorem 61.3 (The Jordan separation theorem): Every simple closed curve in
the standard two-sphere separates the sphere. -/
theorem jordanSeparation (C : Set (StandardSphere 2))
    [Topology.IsSimpleClosedCurve C] : C.Separates := by
  -- Decompose the curve into its two canonical arcs and apply the arc-pair result.
  obtain ⟨C₁, C₂, p, q, hpq, hUnion, hInter, hC₁Arc, hC₂Arc⟩ :=
    existsTwoArcDecomposition C
  letI : Topology.IsArc C₁ := hC₁Arc
  letI : Topology.IsArc C₂ := hC₂Arc
  rw [hUnion]
  exact sphereArcPairUnionSeparates C₁ C₂ p q hpq hInter
