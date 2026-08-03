module

public import Topology_Munkres_2000.Book.Definition_66_1.WindingNumber
public import Topology_Munkres_2000.Book.Definition_66_3.SimpleLoop
public import Topology_Munkres_2000.Book.Theorem_65_2
public import Mathlib.Topology.Connected.Basic

public section

open Set

namespace PlaneLoop

/-- Helper for Theorem 66.2: recentering at `a` and using the standard complex coordinates
identifies the complex plane with the Euclidean plane. -/
private noncomputable def recenteringHomeomorph (a : ℂ) :
    ℂ ≃ₜ EuclideanSpace ℝ (Fin 2) :=
  (Homeomorph.subRight a).trans
    Complex.orthonormalBasisOneI.repr.toHomeomorph

/-- Helper for Theorem 66.2: recentering sends the distinguished point to the origin. -/
private lemma recenteringHomeomorph_apply_self (a : ℂ) :
    recenteringHomeomorph a a = 0 := by
  -- Translation first produces zero, which the linear coordinate map preserves.
  simp [recenteringHomeomorph]

/-- Helper for Theorem 66.2: recentering preserves all pairwise distances. -/
private lemma recenteringHomeomorph_dist (a z w : ℂ) :
    dist (recenteringHomeomorph a z) (recenteringHomeomorph a w) = dist z w := by
  -- Both translation and the orthonormal coordinate map are isometries.
  calc
    dist (recenteringHomeomorph a z) (recenteringHomeomorph a w) =
        dist (z - a) (w - a) := by
      exact Complex.orthonormalBasisOneI.repr.isometry.dist_eq (z - a) (w - a)
    _ = dist z w := dist_sub_right z w a

/-- Helper for Theorem 66.2: recentering preserves boundedness of arbitrary sets. -/
private lemma recenteringHomeomorph_isBounded_image_iff (a : ℂ) (s : Set ℂ) :
    Bornology.IsBounded (recenteringHomeomorph a '' s) ↔ Bornology.IsBounded s := by
  -- Express boundedness by a uniform pairwise-distance bound and use the isometry formula.
  rw [Metric.isBounded_image_iff, Metric.isBounded_iff]
  constructor
  · rintro ⟨C, hC⟩
    have hbound (z : ℂ) (hz : z ∈ s) (w : ℂ) (hw : w ∈ s) :
        dist z w ≤ C := by
      simpa only [recenteringHomeomorph_dist] using hC z hz w hw
    exact ⟨C, hbound⟩
  · rintro ⟨C, hC⟩
    have hbound (z : ℂ) (hz : z ∈ s) (w : ℂ) (hw : w ∈ s) :
        dist (recenteringHomeomorph a z) (recenteringHomeomorph a w) ≤ C := by
      simpa only [recenteringHomeomorph_dist] using hC hz hw
    exact ⟨C, hbound⟩

/-- Helper for Theorem 66.2: the descended additive-circle loop agrees with the original
loop at every parameter of the closed unit interval. -/
private lemma toUnitAddCircleMap_coe_unitInterval {x : ℂ} (f : Path x x)
    (h_loop : f.toContinuousMap.IsLoop) (t : unitInterval) :
    h_loop.toUnitAddCircleMap ((t : ℝ) : UnitAddCircle) = f t := by
  -- Away from the terminal endpoint this is the quotient computation rule; at the endpoint,
  -- use the loop equation and the fact that one period is zero in `UnitAddCircle`.
  rcases lt_or_eq_of_le t.property.2 with ht | ht
  · exact h_loop.toUnitAddCircleMap_coe_apply ⟨t.property.1, ht⟩
  · have ht_one : t = 1 := Subtype.ext ht
    subst t
    have hzeroMem : (0 : ℝ) ∈ Set.Ico 0 1 := by
      norm_num
    calc
      h_loop.toUnitAddCircleMap (((1 : unitInterval) : ℝ) : UnitAddCircle) =
          h_loop.toUnitAddCircleMap ((0 : ℝ) : UnitAddCircle) := by
        congr 1
        simp
      _ = f ⟨0, hzeroMem.1, hzeroMem.2.le⟩ :=
        h_loop.toUnitAddCircleMap_coe_apply hzeroMem
      _ = f 0 := congrArg f (Subtype.ext rfl)
      _ = f 1 := ContinuousMap.isLoop_iff.mp h_loop

/-- Helper for Theorem 66.2: the ambient recentered parametrization of a simple loop. -/
private noncomputable def recenteredCircleMap {x : ℂ} (f : Path x x) (a : ℂ)
    (h_simple : f.toContinuousMap.IsSimpleLoop) :
    C(Circle, EuclideanSpace ℝ (Fin 2)) :=
  (recenteringHomeomorph a : C(ℂ, EuclideanSpace ℝ (Fin 2))).comp
    (h_simple.isLoop.toUnitAddCircleMap.comp
      ((AddCircle.homeomorphCircle one_ne_zero).symm : C(Circle, UnitAddCircle)))

/-- Helper for Theorem 66.2: the recentered parametrization has its expected value. -/
private lemma recenteredCircleMap_apply {x : ℂ} (f : Path x x) (a : ℂ)
    (h_simple : f.toContinuousMap.IsSimpleLoop) (z : Circle) :
    recenteredCircleMap f a h_simple z =
      recenteringHomeomorph a
        (h_simple.isLoop.toUnitAddCircleMap
          ((AddCircle.homeomorphCircle one_ne_zero).symm z)) := by
  -- This is the pointwise computation rule for the composite continuous map.
  rfl

/-- Helper for Theorem 66.2: every value of the recentered parametrization is nonzero. -/
private lemma recenteredCircleMap_ne_zero {x : ℂ} (f : Path x x) (a : ℂ)
    (h_simple : f.toContinuousMap.IsSimpleLoop) (h_avoid : a ∉ Set.range f)
    (z : Circle) : recenteredCircleMap f a h_simple z ≠ 0 := by
  -- A zero value would say that the corresponding value of the descended loop is `a`.
  intro hz
  have hvalue :
      h_simple.isLoop.toUnitAddCircleMap
          ((AddCircle.homeomorphCircle one_ne_zero).symm z) = a := by
    apply (recenteringHomeomorph a).injective
    rw [recenteredCircleMap_apply] at hz
    exact hz.trans (recenteringHomeomorph_apply_self a).symm
  apply h_avoid
  change a ∈ Set.range f.toContinuousMap
  rw [← h_simple.range_toUnitAddCircleMap]
  exact ⟨(AddCircle.homeomorphCircle one_ne_zero).symm z, hvalue⟩

/-- Helper for Theorem 66.2: the recentered loop as a circle map into the punctured plane. -/
private noncomputable def recenteredPuncturedCircleMap {x : ℂ} (f : Path x x) (a : ℂ)
    (h_simple : f.toContinuousMap.IsSimpleLoop) (h_avoid : a ∉ Set.range f) :
    C(Circle, EuclideanPlane.punctured) :=
  ⟨fun z ↦ ⟨recenteredCircleMap f a h_simple z,
      (EuclideanPlane.mem_punctured_iff _).mpr
        (recenteredCircleMap_ne_zero f a h_simple h_avoid z)⟩,
    (recenteredCircleMap f a h_simple).continuous.subtype_mk _⟩

/-- Helper for Theorem 66.2: forgetting the punctured-plane subtype recovers the ambient
recentered parametrization. -/
private lemma recenteredPuncturedCircleMap_coe {x : ℂ} (f : Path x x) (a : ℂ)
    (h_simple : f.toContinuousMap.IsSimpleLoop) (h_avoid : a ∉ Set.range f)
    (z : Circle) :
    (recenteredPuncturedCircleMap f a h_simple h_avoid z :
      EuclideanSpace ℝ (Fin 2)) = recenteredCircleMap f a h_simple z := by
  -- The subtype construction stores exactly the ambient recentered value.
  rfl

/-- Helper for Theorem 66.2: the ambient range of the recentered circle map is the image of
the original loop range under recentering. -/
private lemma recenteredPuncturedCircleMap_range {x : ℂ} (f : Path x x) (a : ℂ)
    (h_simple : f.toContinuousMap.IsSimpleLoop) (h_avoid : a ∉ Set.range f) :
    Set.range (fun z : Circle ↦
      (recenteredPuncturedCircleMap f a h_simple h_avoid z :
        EuclideanSpace ℝ (Fin 2))) = recenteringHomeomorph a '' Set.range f := by
  -- Surjectivity of the circle homeomorphism and the range formula for the descended loop
  -- identify both parametrized sets pointwise.
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨h_simple.isLoop.toUnitAddCircleMap
      ((AddCircle.homeomorphCircle one_ne_zero).symm z), ?_, ?_⟩
    · change _ ∈ Set.range f.toContinuousMap
      rw [← h_simple.range_toUnitAddCircleMap]
      exact ⟨(AddCircle.homeomorphCircle one_ne_zero).symm z, rfl⟩
    · symm
      change (recenteredPuncturedCircleMap f a h_simple h_avoid z :
        EuclideanSpace ℝ (Fin 2)) = _
      rw [recenteredPuncturedCircleMap_coe, recenteredCircleMap_apply]
  · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
    have ht : f t ∈ Set.range f.toContinuousMap := ⟨t, rfl⟩
    rw [← h_simple.range_toUnitAddCircleMap] at ht
    obtain ⟨u, hu⟩ := ht
    refine ⟨AddCircle.homeomorphCircle one_ne_zero u, ?_⟩
    change (recenteredPuncturedCircleMap f a h_simple h_avoid
      (AddCircle.homeomorphCircle one_ne_zero u) : EuclideanSpace ℝ (Fin 2)) = _
    rw [recenteredPuncturedCircleMap_coe, recenteredCircleMap_apply,
      (AddCircle.homeomorphCircle one_ne_zero).symm_apply_apply, hu]

/-- Helper for Theorem 66.2: the recentered punctured-plane circle map is injective. -/
private lemma recenteredPuncturedCircleMap_injective {x : ℂ} (f : Path x x) (a : ℂ)
    (h_simple : f.toContinuousMap.IsSimpleLoop) (h_avoid : a ∉ Set.range f) :
    Function.Injective (recenteredPuncturedCircleMap f a h_simple h_avoid) := by
  -- Cancel the punctured subtype, recentering, the descended simple-loop map, and finally the
  -- circle homeomorphism.
  intro z w hzw
  apply (AddCircle.homeomorphCircle one_ne_zero).symm.injective
  apply h_simple.toUnitAddCircleMap_injective
  apply (recenteringHomeomorph a).injective
  rw [← recenteredCircleMap_apply f a h_simple z,
    ← recenteredCircleMap_apply f a h_simple w]
  exact congrArg Subtype.val hzw

/-- Helper for Theorem 66.2: boundedness of the complementary component is unchanged by
recentring the omitted point to the origin. -/
private lemma componentBounded_recenteredPuncturedCircleMap_iff {x : ℂ}
    (f : Path x x) (a : ℂ) (h_simple : f.toContinuousMap.IsSimpleLoop)
    (h_avoid : a ∉ Set.range f) :
    Bornology.IsBounded
        (connectedComponentIn
          (Set.range (fun z : Circle ↦
            (recenteredPuncturedCircleMap f a h_simple h_avoid z :
              EuclideanSpace ℝ (Fin 2))))ᶜ 0) ↔
      Bornology.IsBounded (connectedComponentIn (Set.range f)ᶜ a) := by
  -- Transport the connected component through the recentering homeomorphism, then use its
  -- distance-preserving boundedness interface.
  have hcomponent :
      recenteringHomeomorph a '' connectedComponentIn (Set.range f)ᶜ a =
        connectedComponentIn
          (Set.range (fun z : Circle ↦
            (recenteredPuncturedCircleMap f a h_simple h_avoid z :
              EuclideanSpace ℝ (Fin 2))))ᶜ 0 := by
    rw [(recenteringHomeomorph a).image_connectedComponentIn h_avoid,
      (recenteringHomeomorph a).image_compl,
      recenteredPuncturedCircleMap_range,
      recenteringHomeomorph_apply_self]
  rw [← hcomponent, recenteringHomeomorph_isBounded_image_iff]

/-- Helper for Theorem 66.2: the integer `n` determines the corresponding element of the
period-one deck subgroup of `ℝ`. -/
private def unitPeriodMultiple (n : ℤ) : AddSubgroup.zmultiples (1 : ℝ) :=
  ⟨n • (1 : ℝ), ⟨n, rfl⟩⟩

/-- Helper for Theorem 66.2: the zero integer determines the zero deck transformation. -/
private lemma unitPeriodMultiple_zero : unitPeriodMultiple 0 = 0 := by
  -- Compare the real values of the two subgroup elements.
  apply Subtype.ext
  simp [unitPeriodMultiple]

/-- Helper for Theorem 66.2: addition of integers agrees with addition in the deck subgroup. -/
private lemma unitPeriodMultiple_add (m n : ℤ) :
    unitPeriodMultiple (m + n) = unitPeriodMultiple m + unitPeriodMultiple n := by
  -- Compare real values and distribute integer scalar multiplication.
  apply Subtype.ext
  simp [unitPeriodMultiple, add_smul]

/-- Helper for Theorem 66.2: integer multiples form an additive homomorphism into the
period-one deck subgroup. -/
private def unitPeriodHom : ℤ →+ AddSubgroup.zmultiples (1 : ℝ) :=
  { toFun := unitPeriodMultiple
    map_zero' := unitPeriodMultiple_zero
    map_add' := unitPeriodMultiple_add }

/-- Helper for Theorem 66.2: the period-one deck homomorphism is injective. -/
private lemma unitPeriodHom_injective : Function.Injective unitPeriodHom := by
  -- Equality of deck transformations is equality of their integer real values.
  intro m n hmn
  have hvalues := congrArg Subtype.val hmn
  simpa [unitPeriodHom, unitPeriodMultiple] using hvalues

/-- Helper for Theorem 66.2: every period-one deck transformation comes from an integer. -/
private lemma unitPeriodHom_surjective : Function.Surjective unitPeriodHom := by
  -- This is exactly the defining membership property of `AddSubgroup.zmultiples`.
  intro x
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp x.property
  refine ⟨n, ?_⟩
  apply Subtype.ext
  simpa [unitPeriodHom, unitPeriodMultiple] using hn

/-- Helper for Theorem 66.2: integers are additively equivalent to the period-one deck group. -/
private noncomputable def unitPeriodAddEquiv :
    ℤ ≃+ AddSubgroup.zmultiples (1 : ℝ) :=
  AddEquiv.ofBijective unitPeriodHom
    ⟨unitPeriodHom_injective, unitPeriodHom_surjective⟩

/-- Helper for Theorem 66.2: the explicit period equivalence has underlying real value `n`. -/
private lemma unitPeriodAddEquiv_coe (n : ℤ) :
    (unitPeriodAddEquiv n : ℝ) = (n : ℝ) := by
  -- Unfold the equivalence and normalize integer scalar multiplication by one.
  simp [unitPeriodAddEquiv, unitPeriodHom, unitPeriodMultiple]

/-- Helper for Theorem 66.2: a chosen real point over `b` gives integer coordinates on
`π₁ (UnitAddCircle, b)` through the standard period-one covering. -/
private noncomputable def unitAddCircleFundamentalGroupEquivInt
    (b : UnitAddCircle) (r : ℝ) (hr : (r : UnitAddCircle) = b) :
    FundamentalGroup UnitAddCircle b ≃* Multiplicative ℤ :=
  ((AddCircle.isAddQuotientCoveringMap_coe (1 : ℝ)).fundamentalGroupEquiv
      (⟨r, hr⟩ : ((↑) : ℝ → UnitAddCircle) ⁻¹' ({b} : Set UnitAddCircle))).trans
    (MulOpposite.opMulEquiv.symm.trans
      (AddEquiv.toMultiplicative unitPeriodAddEquiv).symm)

/-- Helper for Theorem 66.2: a lift whose endpoint differs by `n` has fundamental-group
coordinate `n` for the period-one circle covering. -/
private lemma unitAddCircleFundamentalGroupCoordinate_of_lift
    (b : UnitAddCircle) (hr : ((0 : ℝ) : UnitAddCircle) = b) (n : ℤ)
    (gamma : Path b b) (lift : Path (0 : ℝ) (n : ℝ))
    (hprojection : ∀ t, (lift t : UnitAddCircle) = gamma t) :
    unitAddCircleFundamentalGroupEquivInt b 0 hr
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk gamma)) =
      Multiplicative.ofAdd n := by
  let covering := AddCircle.isAddQuotientCoveringMap_coe (1 : ℝ)
  let baseFiber : ((↑) : ℝ → UnitAddCircle) ⁻¹' ({b} : Set UnitAddCircle) :=
    ⟨0, hr⟩
  have hendpoint : ((n : ℝ) : UnitAddCircle) = b := by
    calc
      ((n : ℝ) : UnitAddCircle) = 0 := by
        simp
      _ = b := hr
  let endpointFiber : ((↑) : ℝ → UnitAddCircle) ⁻¹' ({b} : Set UnitAddCircle) :=
    ⟨(n : ℝ), hendpoint⟩
  have hmonodromy : covering.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk gamma) baseFiber = endpointFiber := by
    -- The supplied real path is the lift selected by monodromy uniqueness.
    apply covering.isCoveringMap.monodromy_eq_of_map_eq
      (Path.Homotopic.Quotient.mk lift)
    rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    exact hprojection t
  have hcoveringCoordinate :
      covering.fundamentalGroupEquiv baseFiber
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk gamma)) =
        MulOpposite.op (Multiplicative.ofAdd (unitPeriodAddEquiv n)) := by
    -- The deck transformation indexed by `n` carries the initial lift point to its endpoint.
    change covering.fundamentalGroupToMulOpposite baseFiber
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk gamma)) = _
    rw [covering.fundamentalGroupToMulOpposite_apply_eq_Iff, hmonodromy]
    change (unitPeriodAddEquiv n : ℝ) + 0 = (n : ℝ)
    rw [unitPeriodAddEquiv_coe, add_zero]
  -- Remove the opposite tag and convert the deck subgroup coordinate back to an integer.
  unfold unitAddCircleFundamentalGroupEquivInt
  simp only [MulEquiv.trans_apply]
  rw [hcoveringCoordinate]
  exact (AddEquiv.toMultiplicative unitPeriodAddEquiv).symm_apply_apply
    (Multiplicative.ofAdd n)

/-- Helper for Theorem 66.2: the standard closed-interval turn is continuous as a
`UnitAddCircle`-valued map. -/
private lemma continuous_unitAddCircleTurn :
    Continuous (fun t : unitInterval ↦ ((t : ℝ) : UnitAddCircle)) := by
  -- Compose interval inclusion with the quotient map.
  exact continuous_quotient_mk'.comp continuous_subtype_val

/-- Helper for Theorem 66.2: the standard additive-circle turn starts at zero. -/
private lemma unitAddCircleTurn_source :
    (((0 : unitInterval) : ℝ) : UnitAddCircle) = 0 := by
  -- The quotient map preserves zero.
  simp

/-- Helper for Theorem 66.2: the standard additive-circle turn ends at zero. -/
private lemma unitAddCircleTurn_target :
    (((1 : unitInterval) : ℝ) : UnitAddCircle) = 0 := by
  -- One real period is zero in the quotient.
  simpa only [Set.Icc.coe_one] using AddCircle.coe_period (1 : ℝ)

/-- Helper for Theorem 66.2: the canonical loop traversing `UnitAddCircle` once. -/
private def unitAddCircleTurn : Path (0 : UnitAddCircle) 0 :=
  { toFun := fun t ↦ ((t : ℝ) : UnitAddCircle)
    continuous_toFun := continuous_unitAddCircleTurn
    source' := unitAddCircleTurn_source
    target' := unitAddCircleTurn_target }

/-- Helper for Theorem 66.2: the endpoint of the real unit turn is the integer one in `ℝ`. -/
private lemma realUnitTurn_target :
    ((1 : unitInterval) : ℝ) = ((1 : ℤ) : ℝ) := by
  -- Both coercions reduce to the real number one.
  norm_num

/-- Helper for Theorem 66.2: the inclusion of the unit interval is a real path from zero
to the integer one. -/
private def realUnitTurn : Path (0 : ℝ) ((1 : ℤ) : ℝ) :=
  { toFun := fun t ↦ (t : ℝ)
    continuous_toFun := continuous_subtype_val
    source' := rfl
    target' := realUnitTurn_target }

/-- Helper for Theorem 66.2: the real unit turn lifts the standard additive-circle turn. -/
private lemma realUnitTurn_lifts_unitAddCircleTurn (t : unitInterval) :
    (realUnitTurn t : UnitAddCircle) = unitAddCircleTurn t := by
  -- Both sides are the quotient class of the same real parameter.
  rfl

/-- Helper for Theorem 66.2: the standard once-around loop is continuous in `Circle`. -/
private lemma continuous_standardCircleTurn :
    Continuous (fun t : unitInterval ↦
      AddCircle.homeomorphCircle one_ne_zero ((t : ℝ) : UnitAddCircle)) := by
  -- Transport the additive-circle turn through the standard circle homeomorphism.
  exact (AddCircle.homeomorphCircle one_ne_zero).continuous.comp
    continuous_unitAddCircleTurn

/-- Helper for Theorem 66.2: the standard circle turn starts at the circle identity. -/
private lemma standardCircleTurn_source :
    AddCircle.homeomorphCircle one_ne_zero
      (((0 : unitInterval) : ℝ) : UnitAddCircle) = 1 := by
  -- The zero additive angle corresponds to the circle identity.
  simp [AddCircle.homeomorphCircle_apply]

/-- Helper for Theorem 66.2: the standard circle turn ends at the circle identity. -/
private lemma standardCircleTurn_target :
    AddCircle.homeomorphCircle one_ne_zero
      (((1 : unitInterval) : ℝ) : UnitAddCircle) = 1 := by
  -- The terminal angle is one full period.
  rw [unitAddCircleTurn_target]
  simp [AddCircle.homeomorphCircle_apply]

/-- Helper for Theorem 66.2: the canonical positive once-around loop in `Circle`. -/
private noncomputable def standardCircleTurn : Path (1 : Circle) 1 :=
  { toFun := fun t ↦
      AddCircle.homeomorphCircle one_ne_zero ((t : ℝ) : UnitAddCircle)
    continuous_toFun := continuous_standardCircleTurn
    source' := standardCircleTurn_source
    target' := standardCircleTurn_target }

/-- Helper for Theorem 66.2: the standard circle turn has the expected pointwise value. -/
private lemma standardCircleTurn_apply (t : unitInterval) :
    standardCircleTurn t =
      AddCircle.homeomorphCircle one_ne_zero ((t : ℝ) : UnitAddCircle) := by
  -- This is the function field of the standard turn.
  rfl

/-- Helper for Theorem 66.2: transporting the standard circle turn back to `UnitAddCircle`
recovers the quotient class of its real parameter. -/
private lemma standardCircleTurn_toUnitAddCircle (t : unitInterval) :
    (AddCircle.homeomorphCircle one_ne_zero).symm (standardCircleTurn t) =
      ((t : ℝ) : UnitAddCircle) := by
  -- Cancel the circle homeomorphism pointwise.
  rw [standardCircleTurn_apply,
    (AddCircle.homeomorphCircle one_ne_zero).symm_apply_apply]

/-- Helper for Theorem 66.2: complex coordinates carry a nonzero Euclidean-plane point to a
nonzero complex number. -/
private lemma euclideanPlane_mem_punctured_iff_complex_ne_zero
    (z : EuclideanSpace ℝ (Fin 2)) :
    z ∈ EuclideanPlane.punctured ↔
      Complex.orthonormalBasisOneI.repr.symm z ≠ 0 := by
  -- The inverse coordinate isometry is injective and preserves zero.
  rw [EuclideanPlane.mem_punctured_iff]
  constructor
  · intro hz hcomplex
    apply hz
    apply Complex.orthonormalBasisOneI.repr.symm.injective
    simpa using hcomplex
  · intro hcomplex hz
    subst z
    exact hcomplex (map_zero Complex.orthonormalBasisOneI.repr.symm)

/-- Helper for Theorem 66.2: complex coordinates identify the punctured Euclidean plane with
the punctured complex plane. -/
private noncomputable def puncturedEuclideanPlaneHomeomorphPuncturedComplex :
    EuclideanPlane.punctured ≃ₜ {z : ℂ // z ≠ 0} :=
  Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.subtype
    euclideanPlane_mem_punctured_iff_complex_ne_zero

/-- Helper for Theorem 66.2: complexifying a recentered punctured-circle value recovers the
translated descended-loop value. -/
private lemma puncturedComplexCoordinate_recenteredPuncturedCircleMap {x : ℂ}
    (f : Path x x) (a : ℂ) (h_simple : f.toContinuousMap.IsSimpleLoop)
    (h_avoid : a ∉ Set.range f) (z : Circle) :
    (puncturedEuclideanPlaneHomeomorphPuncturedComplex
        (recenteredPuncturedCircleMap f a h_simple h_avoid z) : ℂ) =
      h_simple.isLoop.toUnitAddCircleMap
          ((AddCircle.homeomorphCircle one_ne_zero).symm z) - a := by
  -- Cancel the Euclidean-complex coordinate isometry after exposing the recentered value.
  change Complex.orthonormalBasisOneI.repr.symm
      (recenteredCircleMap f a h_simple z) = _
  rw [recenteredCircleMap_apply]
  exact Complex.orthonormalBasisOneI.repr.symm_apply_apply _

/-- Helper for Theorem 66.2: polar coordinates identify the punctured Euclidean plane with a
period-one angular circle times a real radial coordinate. -/
private noncomputable def puncturedPlaneHomeomorphUnitCylinder :
    EuclideanPlane.punctured ≃ₜ UnitAddCircle × ℝ :=
  puncturedEuclideanPlaneHomeomorphPuncturedComplex.trans
    (Complex.polarHomeomorph.symm.trans
      ((AddCircle.homeomorphCircle one_ne_zero).symm.prodCongr
        Real.expOrderIso.toHomeomorph.symm))

/-- Helper for Theorem 66.2: the angular component of the punctured-plane cylinder chart is
the normalized complex direction. -/
private lemma puncturedPlaneHomeomorphUnitCylinder_angular (q : EuclideanPlane.punctured) :
    AddCircle.homeomorphCircle one_ne_zero
        (puncturedPlaneHomeomorphUnitCylinder q).1 =
      Complex.polarDirection (puncturedEuclideanPlaneHomeomorphPuncturedComplex q) := by
  -- Unfold only the angular projections of the two homeomorphism composites.
  change AddCircle.homeomorphCircle one_ne_zero
      ((AddCircle.homeomorphCircle one_ne_zero).symm
        (Complex.polarDirection
          (puncturedEuclideanPlaneHomeomorphPuncturedComplex q))) = _
  exact (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply _

/-- Helper for Theorem 66.2: centering the cylinder angle at `q` gives a homeomorphism whose
angular coordinate at `q` is zero. -/
private noncomputable def centeredPuncturedPlaneHomeomorph (q : EuclideanPlane.punctured) :
    EuclideanPlane.punctured ≃ₜ UnitAddCircle × ℝ :=
  puncturedPlaneHomeomorphUnitCylinder.trans
    ((Homeomorph.subRight (puncturedPlaneHomeomorphUnitCylinder q).1).prodCongr
      (Homeomorph.refl ℝ))

/-- Helper for Theorem 66.2: the centered cylinder chart has zero angular coordinate at its
center. -/
private lemma centeredPuncturedPlaneHomeomorph_fst_self (q : EuclideanPlane.punctured) :
    (centeredPuncturedPlaneHomeomorph q q).1 = 0 := by
  -- Centering subtracts the angular coordinate from itself.
  simp [centeredPuncturedPlaneHomeomorph]

/-- Helper for Theorem 66.2: along the standard circle turn, the angular coordinate of the
recentered simple loop is exactly `angularLoop`. -/
private lemma recenteredPuncturedCircleMap_angular_standardTurn {x : ℂ}
    (f : Path x x) (a : ℂ) (h_simple : f.toContinuousMap.IsSimpleLoop)
    (h_avoid : a ∉ Set.range f) (t : unitInterval) :
    (puncturedPlaneHomeomorphUnitCylinder
      (recenteredPuncturedCircleMap f a h_simple h_avoid (standardCircleTurn t))).1 =
      angularLoop f a h_avoid t := by
  -- Pass to `Circle`, where both sides are the normalized direction of `f t - a`.
  apply (AddCircle.homeomorphCircle one_ne_zero).injective
  rw [puncturedPlaneHomeomorphUnitCylinder_angular]
  have hangular : AddCircle.homeomorphCircle one_ne_zero
      (angularLoop f a h_avoid t) = normalizedLoop f a h_avoid t := by
    -- Compare both circle values through the canonical real lift.
    calc
      AddCircle.homeomorphCircle one_ne_zero (angularLoop f a h_avoid t) =
          AddCircle.homeomorphCircle one_ne_zero
            (angularLift f a h_avoid t : UnitAddCircle) := by
        exact congrArg (AddCircle.homeomorphCircle one_ne_zero)
          (angularLift_lifts_angularLoop f a h_avoid t).symm
      _ = standardCircleCovering (angularLift f a h_avoid t) := rfl
      _ = normalizedLoop f a h_avoid t := angularLift_lifts f a h_avoid t
  rw [hangular]
  rw [normalizedLoop_apply]
  apply Circle.ext
  simp only [Complex.polarDirection, Complex.polarDirectionValue, direction_coe]
  rw [puncturedComplexCoordinate_recenteredPuncturedCircleMap,
    standardCircleTurn_toUnitAddCircle,
    toUnitAddCircleMap_coe_unitInterval f h_simple.isLoop]

/-- Helper for Theorem 66.2: the centered cylinder chart subtracts the angular coordinate of
its center. -/
private lemma centeredPuncturedPlaneHomeomorph_fst_apply
    (q z : EuclideanPlane.punctured) :
    (centeredPuncturedPlaneHomeomorph q z).1 =
      (puncturedPlaneHomeomorphUnitCylinder z).1 -
        (puncturedPlaneHomeomorphUnitCylinder q).1 := by
  -- This is the first projection of the product translation.
  rfl

/-- Helper for Theorem 66.2: mapping the standard circle turn through the recentered curve and
the centered cylinder produces its relative angular loop. -/
private noncomputable def recenteredCenteredAngularPath {x : ℂ}
    (f : Path x x) (a : ℂ) (h_simple : f.toContinuousMap.IsSimpleLoop)
    (h_avoid : a ∉ Set.range f) :
    Path
      ((centeredPuncturedPlaneHomeomorph
        (recenteredPuncturedCircleMap f a h_simple h_avoid 1)
        (recenteredPuncturedCircleMap f a h_simple h_avoid 1)).1)
      ((centeredPuncturedPlaneHomeomorph
        (recenteredPuncturedCircleMap f a h_simple h_avoid 1)
        (recenteredPuncturedCircleMap f a h_simple h_avoid 1)).1) :=
  (((standardCircleTurn.map
      (recenteredPuncturedCircleMap f a h_simple h_avoid).continuous).map
        (centeredPuncturedPlaneHomeomorph
          (recenteredPuncturedCircleMap f a h_simple h_avoid 1)).continuous).map
      continuous_fst)

/-- Helper for Theorem 66.2: the centered angular path evaluates as the difference of the
uncentered angular coordinates. -/
private lemma recenteredCenteredAngularPath_apply {x : ℂ}
    (f : Path x x) (a : ℂ) (h_simple : f.toContinuousMap.IsSimpleLoop)
    (h_avoid : a ∉ Set.range f) (t : unitInterval) :
    recenteredCenteredAngularPath f a h_simple h_avoid t =
      (puncturedPlaneHomeomorphUnitCylinder
        (recenteredPuncturedCircleMap f a h_simple h_avoid (standardCircleTurn t))).1 -
      (puncturedPlaneHomeomorphUnitCylinder
        (recenteredPuncturedCircleMap f a h_simple h_avoid 1)).1 := by
  -- Evaluate the three path maps and then the centered cylinder projection.
  exact centeredPuncturedPlaneHomeomorph_fst_apply _ _

/-- Helper for Theorem 66.2: the shifted canonical angular lift starts at zero. -/
private lemma shiftedAngularLift_source {x : ℂ} (f : Path x x) (a : ℂ)
    (h_avoid : a ∉ Set.range f) :
    angularLift f a h_avoid 0 - angularLift f a h_avoid 0 = 0 := by
  -- Subtracting the initial lift value centers the lift at zero.
  exact sub_self _

/-- Helper for Theorem 66.2: the shifted canonical angular lift ends at the winding number. -/
private lemma shiftedAngularLift_target {x : ℂ} (f : Path x x) (a : ℂ)
    (h_avoid : a ∉ Set.range f) :
    angularLift f a h_avoid 1 - angularLift f a h_avoid 0 =
      (windingNumber f a h_avoid : ℝ) := by
  -- The canonical lift itself satisfies the winding-number displacement specification.
  exact windingNumber_spec_angularLoop f a h_avoid (angularLift f a h_avoid)
    (angularLift_lifts_angularLoop f a h_avoid)

/-- Helper for Theorem 66.2: the canonical angular lift shifted to start at zero. -/
private noncomputable def shiftedAngularLiftPath {x : ℂ} (f : Path x x) (a : ℂ)
    (h_avoid : a ∉ Set.range f) :
    Path (0 : ℝ) (windingNumber f a h_avoid : ℝ) :=
  { toFun := fun t ↦ angularLift f a h_avoid t - angularLift f a h_avoid 0
    continuous_toFun := (angularLift f a h_avoid).continuous.sub continuous_const
    source' := shiftedAngularLift_source f a h_avoid
    target' := shiftedAngularLift_target f a h_avoid }

/-- Helper for Theorem 66.2: the shifted angular lift projects to the centered cylinder angular
path of the recentered curve. -/
private lemma shiftedAngularLiftPath_lifts_recenteredCenteredAngularPath {x : ℂ}
    (f : Path x x) (a : ℂ) (h_simple : f.toContinuousMap.IsSimpleLoop)
    (h_avoid : a ∉ Set.range f) (t : unitInterval) :
    (shiftedAngularLiftPath f a h_avoid t : UnitAddCircle) =
      recenteredCenteredAngularPath f a h_simple h_avoid t := by
  -- Project the real difference, identify both angular values, and use the standard turn's
  -- basepoint computation for the centered term.
  have hshifted : (shiftedAngularLiftPath f a h_avoid t : ℝ) =
      angularLift f a h_avoid t - angularLift f a h_avoid 0 := rfl
  rw [hshifted]
  rw [AddCircle.coe_sub, angularLift_lifts_angularLoop,
    angularLift_lifts_angularLoop, recenteredCenteredAngularPath_apply,
    recenteredPuncturedCircleMap_angular_standardTurn]
  have hbaseAngle :
      (puncturedPlaneHomeomorphUnitCylinder
        (recenteredPuncturedCircleMap f a h_simple h_avoid 1)).1 =
        angularLoop f a h_avoid 0 := by
    calc
      (puncturedPlaneHomeomorphUnitCylinder
          (recenteredPuncturedCircleMap f a h_simple h_avoid 1)).1 =
          (puncturedPlaneHomeomorphUnitCylinder
            (recenteredPuncturedCircleMap f a h_simple h_avoid
              (standardCircleTurn 0))).1 := by
        exact congrArg
          (fun z : EuclideanPlane.punctured ↦
            (puncturedPlaneHomeomorphUnitCylinder z).1)
          (congrArg (recenteredPuncturedCircleMap f a h_simple h_avoid)
            standardCircleTurn.source.symm)
      _ = angularLoop f a h_avoid 0 :=
        recenteredPuncturedCircleMap_angular_standardTurn f a h_simple h_avoid 0
  rw [hbaseAngle]

/-- Helper for Theorem 66.2: the standard circle turn represents coordinate one for a suitable
fundamental orientation of `Circle`. -/
private lemma exists_circleOrientation_standardCircleTurn :
    ∃ orientation : Circle.FundamentalOrientation,
      orientation
          (FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk standardCircleTurn)) =
        Multiplicative.ofAdd 1 := by
  let circleToUnit := (AddCircle.homeomorphCircle one_ne_zero).symm
  let additiveTurn := standardCircleTurn.map circleToUnit.continuous
  have hbase : (((0 : ℝ) : UnitAddCircle)) = circleToUnit 1 := by
    -- Apply the circle homeomorphism and cancel it on the right.
    apply (AddCircle.homeomorphCircle one_ne_zero).injective
    rw [(AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply]
    simp [AddCircle.homeomorphCircle_apply]
  let orientation : Circle.FundamentalOrientation :=
    (circleToUnit.fundamentalGroupMulEquiv 1).trans
      (unitAddCircleFundamentalGroupEquivInt (circleToUnit 1) 0 hbase)
  have hprojection (t : unitInterval) :
      (realUnitTurn t : UnitAddCircle) = additiveTurn t := by
    -- The inverse circle homeomorphism cancels the forward homeomorphism pointwise.
    change ((t : ℝ) : UnitAddCircle) =
      circleToUnit
        (AddCircle.homeomorphCircle one_ne_zero ((t : ℝ) : UnitAddCircle))
    exact (AddCircle.homeomorphCircle one_ne_zero).symm_apply_apply _ |>.symm
  have hcoordinate := unitAddCircleFundamentalGroupCoordinate_of_lift
    (circleToUnit 1) hbase 1 additiveTurn realUnitTurn hprojection
  have hmap :
      FundamentalGroup.map (circleToUnit : C(Circle, UnitAddCircle)) 1
          (FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk standardCircleTurn)) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk additiveTurn) := by
    rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]
  refine ⟨orientation, ?_⟩
  -- The homeomorphism-induced map sends the standard turn to `additiveTurn`.
  change unitAddCircleFundamentalGroupEquivInt (circleToUnit 1) 0 hbase
      (FundamentalGroup.map (circleToUnit : C(Circle, UnitAddCircle)) 1
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk standardCircleTurn))) = _
  rw [hmap]
  exact hcoordinate

/-- Helper for Theorem 66.2: the recentered punctured-plane curve has target coordinates in
which the standard-turn class maps to the lift-defined winding number. -/
private lemma exists_puncturedPlaneCoordinates_standardCircleTurn {x : ℂ}
    (f : Path x x) (a : ℂ) (h_simple : f.toContinuousMap.IsSimpleLoop)
    (h_avoid : a ∉ Set.range f) :
    ∃ targetCoordinates :
        FundamentalGroup EuclideanPlane.punctured
          (recenteredPuncturedCircleMap f a h_simple h_avoid 1) ≃*
            Multiplicative ℤ,
      targetCoordinates
          (FundamentalGroup.map (recenteredPuncturedCircleMap f a h_simple h_avoid) 1
            (FundamentalGroup.fromPath
              (Path.Homotopic.Quotient.mk standardCircleTurn))) =
        Multiplicative.ofAdd (windingNumber f a h_avoid) := by
  let h := recenteredPuncturedCircleMap f a h_simple h_avoid
  let q := h 1
  let cylinder := centeredPuncturedPlaneHomeomorph q
  let angularPath := recenteredCenteredAngularPath f a h_simple h_avoid
  have hbase : (((0 : ℝ) : UnitAddCircle)) = (cylinder q).1 := by
    -- The centered cylinder chart sends its center to angular coordinate zero.
    symm
    exact centeredPuncturedPlaneHomeomorph_fst_self q
  let cylinderCoordinates :=
    FundamentalGroup.prodMulEquivLeftOfSubsingleton
      (cylinder q).1 (cylinder q).2
      (inferInstance : Subsingleton (FundamentalGroup ℝ (cylinder q).2))
  let targetCoordinates : FundamentalGroup EuclideanPlane.punctured q ≃* Multiplicative ℤ :=
    (cylinder.fundamentalGroupMulEquiv q).trans
      (cylinderCoordinates.trans
        (unitAddCircleFundamentalGroupEquivInt (cylinder q).1 0 hbase))
  have hcoordinate := unitAddCircleFundamentalGroupCoordinate_of_lift
    (cylinder q).1 hbase (windingNumber f a h_avoid) angularPath
      (shiftedAngularLiftPath f a h_avoid)
      (shiftedAngularLiftPath_lifts_recenteredCenteredAngularPath
        f a h_simple h_avoid)
  have hclass :
      cylinderCoordinates
          (FundamentalGroup.map (cylinder :
              C(EuclideanPlane.punctured, UnitAddCircle × ℝ)) q
            (FundamentalGroup.map h 1
              (FundamentalGroup.fromPath
                (Path.Homotopic.Quotient.mk standardCircleTurn)))) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk angularPath) := by
    -- Functoriality through the cylinder chart followed by first projection is precisely the
    -- threefold path map used to define `angularPath`.
    simp only [cylinderCoordinates,
      FundamentalGroup.prodMulEquivLeftOfSubsingleton_apply,
      FundamentalGroup.map_apply]
    rfl
  refine ⟨targetCoordinates, ?_⟩
  -- Evaluate the target-coordinate composite, normalize its path class, and apply monodromy.
  change unitAddCircleFundamentalGroupEquivInt (cylinder q).1 0 hbase
      (cylinderCoordinates
        (FundamentalGroup.map (cylinder :
            C(EuclideanPlane.punctured, UnitAddCircle × ℝ)) q
          (FundamentalGroup.map h 1
            (FundamentalGroup.fromPath
              (Path.Homotopic.Quotient.mk standardCircleTurn))))) = _
  rw [hclass]
  exact hcoordinate

/-- Helper for Theorem 66.2: suitable source and target fundamental-group coordinates identify
the abstract punctured-plane winding number with `PlaneLoop.windingNumber`. -/
private lemma exists_puncturedPlaneCoordinates_windingNumber_eq {x : ℂ}
    (f : Path x x) (a : ℂ) (h_simple : f.toContinuousMap.IsSimpleLoop)
    (h_avoid : a ∉ Set.range f) :
    ∃ sourceCoordinates : Circle.FundamentalOrientation,
      ∃ targetCoordinates :
          FundamentalGroup EuclideanPlane.punctured
            (recenteredPuncturedCircleMap f a h_simple h_avoid 1) ≃*
              Multiplicative ℤ,
        PuncturedPlaneMap.windingNumber sourceCoordinates
            (recenteredPuncturedCircleMap f a h_simple h_avoid) targetCoordinates =
          windingNumber f a h_avoid := by
  obtain ⟨sourceCoordinates, hsource⟩ := exists_circleOrientation_standardCircleTurn
  obtain ⟨targetCoordinates, htarget⟩ :=
    exists_puncturedPlaneCoordinates_standardCircleTurn f a h_simple h_avoid
  refine ⟨sourceCoordinates, targetCoordinates, ?_⟩
  -- The chosen source coordinate identifies its generator with the standard-turn class; the
  -- chosen target coordinate evaluates that class by the angular-lift displacement.
  have hgenerator :
      sourceCoordinates.symm (Multiplicative.ofAdd 1) =
        FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk standardCircleTurn) := by
    apply sourceCoordinates.injective
    rw [sourceCoordinates.apply_symm_apply, hsource]
  have hspec := PuncturedPlaneMap.windingNumber_spec sourceCoordinates
    (recenteredPuncturedCircleMap f a h_simple h_avoid) targetCoordinates
  rw [hgenerator] at hspec
  have hcoordinate := congrArg targetCoordinates hspec
  rw [htarget, targetCoordinates.apply_symm_apply] at hcoordinate
  exact congrArg Multiplicative.toAdd hcoordinate |>.symm

/-- Theorem 66.2 (1): A simple plane loop has winding number zero about a point in the
unbounded component of its complement. -/
theorem windingNumber_eq_zero_of_component_unbounded {x : ℂ} (f : Path x x) (a : ℂ)
    (h_simple : f.toContinuousMap.IsSimpleLoop) (h_avoid : a ∉ Set.range f)
    (h_unbounded : ¬ Bornology.IsBounded (connectedComponentIn (Set.range f)ᶜ a)) :
    windingNumber f a h_avoid = 0 := by
  -- Route correction: this declaration proves only the unbounded-component conclusion; the
  -- bounded-component conclusion remains the independent companion theorem below.
  let h := recenteredPuncturedCircleMap f a h_simple h_avoid
  have h_injective : Function.Injective h :=
    recenteredPuncturedCircleMap_injective f a h_simple h_avoid
  have h_unbounded' : ¬ Bornology.IsBounded
      (connectedComponentIn
        (Set.range (fun z : Circle ↦ (h z : EuclideanSpace ℝ (Fin 2))))ᶜ 0) := by
    -- Recentring transports the supplied unbounded complementary component to the origin.
    intro hbounded
    apply h_unbounded
    exact (componentBounded_recenteredPuncturedCircleMap_iff
      f a h_simple h_avoid).mp hbounded
  have hnull : h.Nullhomotopic :=
    PuncturedPlaneMap.nullhomotopic_of_originComponent_unbounded
      h h_injective h_unbounded'
  obtain ⟨sourceCoordinates, targetCoordinates, hbridge⟩ :=
    exists_puncturedPlaneCoordinates_windingNumber_eq f a h_simple h_avoid
  have hmap : FundamentalGroup.map h 1 = 1 :=
    MonoidHom.op.injective
      (fundamentalGroupMap_eq_one_of_nullhomotopic h 1 hnull)
  have habstract :
      PuncturedPlaneMap.windingNumber sourceCoordinates h targetCoordinates = 0 := by
    -- Nullhomotopy makes the induced fundamental-group map trivial in every coordinate system.
    have hspec := PuncturedPlaneMap.windingNumber_spec sourceCoordinates h targetCoordinates
    rw [hmap, MonoidHom.one_apply] at hspec
    have hcoordinate := congrArg targetCoordinates hspec
    rw [targetCoordinates.map_one, targetCoordinates.apply_symm_apply] at hcoordinate
    exact (congrArg Multiplicative.toAdd hcoordinate).symm
  -- The monodromy coordinate bridge turns the abstract zero into the lift-defined invariant.
  exact hbridge.symm.trans habstract

/-- Theorem 66.2 (2): A simple plane loop has winding number `1` or `-1` about a point in a
bounded component of its complement. -/
theorem windingNumber_eq_one_or_neg_one_of_component_bounded {x : ℂ} (f : Path x x) (a : ℂ)
    (h_simple : f.toContinuousMap.IsSimpleLoop) (h_avoid : a ∉ Set.range f)
    (h_bounded : Bornology.IsBounded (connectedComponentIn (Set.range f)ᶜ a)) :
    windingNumber f a h_avoid = 1 ∨ windingNumber f a h_avoid = -1 := by
  let h := recenteredPuncturedCircleMap f a h_simple h_avoid
  have h_injective : Function.Injective h :=
    recenteredPuncturedCircleMap_injective f a h_simple h_avoid
  have h_bounded' : Bornology.IsBounded
      (connectedComponentIn
        (Set.range (fun z : Circle ↦ (h z : EuclideanSpace ℝ (Fin 2))))ᶜ 0) := by
    -- Recentring transports the supplied bounded complementary component to the origin.
    exact (componentBounded_recenteredPuncturedCircleMap_iff
      f a h_simple h_avoid).mpr h_bounded
  obtain ⟨sourceCoordinates, targetCoordinates, hbridge⟩ :=
    exists_puncturedPlaneCoordinates_windingNumber_eq f a h_simple h_avoid
  have habstract :=
    PuncturedPlaneMap.windingNumber_eq_one_or_neg_one_of_originComponent_bounded
      h h_injective sourceCoordinates targetCoordinates h_bounded'
  -- The same coordinate bridge identifies the planar theorem's abstract winding number with
  -- the endpoint displacement defining `PlaneLoop.windingNumber`.
  rwa [hbridge] at habstract

end PlaneLoop
