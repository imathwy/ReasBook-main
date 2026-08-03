module

public import Topology_Munkres_2000.Book.Definition_57_2.Antipodal
public import Topology_Munkres_2000.Book.Exercise_54_6
public import Topology_Munkres_2000.Book.Theorem_54_5.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Homotopy.Lifting

public section

noncomputable section

open CategoryTheory

/-- Helper for Theorem 57.1: complex coordinates preserve the unit-sphere predicate. -/
private lemma euclideanPlaneComplex_mem_unitSphere (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
      Complex.orthonormalBasisOneI.repr.symm x ∈ Metric.sphere (0 : ℂ) 1 := by
  -- Both predicates reduce to the norm-one equation, which the linear isometry preserves.
  simp only [Metric.mem_sphere, dist_zero_right]
  exact (Complex.orthonormalBasisOneI.repr.symm.norm_map x).symm ▸ Iff.rfl

/-- Helper for Theorem 57.1: complex coordinates identify `StandardSphere 1` with `Circle`. -/
private noncomputable def standardSphereOneHomeomorphCircle : StandardSphere 1 ≃ₜ Circle :=
  -- Restrict the ambient linear isometry using the sphere-membership interface above.
  Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.subtype
    euclideanPlaneComplex_mem_unitSphere

/-- Helper for Theorem 57.1: the sphere-circle coordinate intertwines antipodes. -/
private lemma standardSphereOneHomeomorphCircle_neg (x : StandardSphere 1) :
    standardSphereOneHomeomorphCircle (-x) = -standardSphereOneHomeomorphCircle x := by
  -- Equality in the circle follows from linearity of the ambient complex coordinate.
  apply Circle.ext
  exact map_neg Complex.orthonormalBasisOneI.repr.symm x.1

namespace Circle

/-- Helper for Theorem 57.1: projecting a path through a covering and aligning its
endpoints makes monodromy recover the endpoint upstairs. -/
private lemma coveringMonodromy_map_cast {E B : Type*} [TopologicalSpace E]
    [TopologicalSpace B] {p : E → B} (hp : IsCoveringMap p) {e₀ e₁ : E}
    {b₀ b₁ : B} (h₀ : p e₀ = b₀) (h₁ : p e₁ = b₁)
    (path : Path.Homotopic.Quotient e₀ e₁) :
    hp.monodromy ((path.map ⟨p, hp.continuous⟩).cast h₀.symm h₁.symm) ⟨e₀, h₀⟩ =
      ⟨e₁, h₁⟩ := by
  -- The general monodromy comparison cancels the two endpoint alignments.
  refine hp.monodromy_eq_of_map_eq path ?_
  simp only [Path.Homotopic.Quotient.cast_cast,
    Path.Homotopic.Quotient.cast_rfl_rfl]

/-- Helper for Theorem 57.1: left translation normalizes a circle map at `1`. -/
private def normalizeAtOne (g : C(Circle, Circle)) : C(Circle, Circle) :=
  -- Multiply pointwise by the inverse of the value at the chosen basepoint.
  ContinuousMap.const Circle (g 1)⁻¹ * g

/-- Helper for Theorem 57.1: the normalized circle map fixes `1`. -/
private lemma normalizeAtOne_one (g : C(Circle, Circle)) : normalizeAtOne g 1 = 1 := by
  -- The normalizing factor cancels the value of the map at the basepoint.
  exact inv_mul_cancel (g 1)

/-- Helper for Theorem 57.1: normalization by left translation preserves oddness. -/
private lemma odd_normalizeAtOne (g : C(Circle, Circle)) (hodd : Function.Odd g) :
    Function.Odd (normalizeAtOne g) := by
  -- Pull the sign through the fixed left-translation factor.
  intro z
  apply Circle.ext
  simp only [normalizeAtOne, ContinuousMap.mul_apply, ContinuousMap.const_apply]
  rw [hodd z]
  exact mul_neg _ _

/-- Helper for Theorem 57.1: equal continuous maps give heterogeneously equal mapped
path classes, even when their endpoint types use different spellings. -/
private lemma quotientMap_heq_of_eq {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {x₀ x₁ : X} (path : Path.Homotopic.Quotient x₀ x₁)
    {f g : C(X, Y)} (hfg : f = g) : HEq (path.map f) (path.map g) := by
  subst g
  rfl

/-- Helper for Theorem 57.1: casting a constant path along an endpoint equality
gives the constant path at the new endpoint. -/
private lemma quotientRefl_cast {X : Type*} [TopologicalSpace X] {x y : X}
    (hxy : x = y) :
    (Path.Homotopic.Quotient.refl x).cast hxy.symm hxy.symm =
      Path.Homotopic.Quotient.refl y := by
  subst y
  exact Path.Homotopic.Quotient.cast_rfl_rfl _

/-- Helper for Theorem 57.1: squaring a point of `Circle` is unchanged by negation. -/
private lemma neg_sq_circle (z : Circle) : (-z) ^ (2 : ℕ) = z ^ (2 : ℕ) := by
  apply Circle.ext
  simp only [Circle.coe_pow, Circle.coe_neg]
  ring

/-- Helper for Theorem 57.1: the square of an odd circle map descends through the square map. -/
private lemma existsSquareDescendant (g : C(Circle, Circle)) (hodd : Function.Odd g)
    (hg1 : g 1 = 1) :
    ∃ k : C(Circle, Circle), k 1 = 1 ∧
      k.comp (CircleMap.zpower (2 : ℤ)) = (CircleMap.zpower (2 : ℤ)).comp g := by
  classical
  let q := CircleMap.zpower (2 : ℤ)
  have hfactors : Function.FactorsThrough (q.comp g) q := by
    intro z w hzw
    have hsqCircle : z ^ (2 : ℕ) = w ^ (2 : ℕ) := by
      simpa only [q, CircleMap.zpower_apply, zpow_ofNat] using hzw
    have hsq : (z : ℂ) ^ 2 = (w : ℂ) ^ 2 := by
      simpa only [Circle.coe_pow] using congrArg Subtype.val hsqCircle
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact congrArg (fun u : Circle ↦ q (g u)) (Subtype.ext h)
    · have hcircle : z = -w := by
        apply Circle.ext
        exact h
      rw [hcircle]
      simp only [ContinuousMap.comp_apply]
      rw [hodd w]
      simpa only [ContinuousMap.comp_apply, q, CircleMap.zpower_apply, zpow_ofNat] using
        neg_sq_circle (g w)
  have hqFunction : (q : Circle → Circle) = fun z ↦ z ^ (2 : ℤ) := by
    funext z
    exact CircleMap.zpower_apply (2 : ℤ) z
  have hqQuotient : Topology.IsQuotientMap q := by
    rw [hqFunction]
    exact (Circle.isQuotientCoveringMap_zpow (2 : ℤ)).toIsQuotientMap
  let k := hqQuotient.lift (q.comp g) hfactors
  refine ⟨k, ?_, ?_⟩
  · -- Evaluate the quotient-lift equation at `1` and use that both maps fix the basepoint.
    have hbase := congrArg (fun f : C(Circle, Circle) ↦ f 1)
      (hqQuotient.lift_comp (q.comp g) hfactors)
    simpa only [ContinuousMap.comp_apply, q, CircleMap.zpower_one, hg1] using hbase
  · -- Expose the quotient lift only through its defining commutative triangle.
    exact hqQuotient.lift_comp (q.comp g) hfactors

/-- Helper for Theorem 57.1: an odd square descendant induces a nontrivial
endomorphism of the circle fundamental group. -/
private lemma squareDescendant_inducedMap_ne_one (g k : C(Circle, Circle))
    (hodd : Function.Odd g) (hg1 : g 1 = 1) (hk1 : k 1 = 1)
    (hcomm : k.comp (CircleMap.zpower (2 : ℤ)) =
      (CircleMap.zpower (2 : ℤ)).comp g) :
    FundamentalGroup.mapOfEq k hk1 ≠ 1 := by
  let q := CircleMap.zpower (2 : ℤ)
  have hq1 : q 1 = 1 := CircleMap.zpower_one (2 : ℤ)
  have hqFunction : (q : Circle → Circle) = fun z ↦ z ^ (2 : ℤ) := by
    funext z
    exact CircleMap.zpower_apply (2 : ℤ) z
  have hqCovering : IsCoveringMap q := by
    rw [hqFunction]
    exact (Circle.isQuotientCoveringMap_zpow (2 : ℤ)).isCoveringMap
  have hqneg1 : q (-1) = 1 := by
    apply Circle.ext
    norm_num [q, CircleMap.zpower_apply]
  have hgneg1 : g (-1) = -1 := by
    calc
      g (-1) = -g 1 := by simpa using hodd (1 : Circle)
      _ = -1 := congrArg Neg.neg hg1
  let path : Path.Homotopic.Quotient (1 : Circle) (-1) :=
    Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath (1 : Circle) (-1))
  let projected : FundamentalGroup Circle 1 :=
    (path.map q).cast hq1.symm hqneg1.symm
  let mappedPath : Path.Homotopic.Quotient (1 : Circle) (-1) :=
    (path.map g).cast hg1.symm hgneg1.symm
  let mappedProjection : FundamentalGroup Circle 1 :=
    (mappedPath.map q).cast hq1.symm hqneg1.symm
  have himage : FundamentalGroup.mapOfEq k hk1 projected = mappedProjection := by
    have hleft : FundamentalGroup.mapOfEq k hk1 projected ≍ (path.map q).map k := by
      simp only [FundamentalGroup.mapOfEq_apply, projected,
        Path.Homotopic.Quotient.map_cast, Path.Homotopic.Quotient.cast_cast]
      exact Path.Homotopic.Quotient.cast_heq _ _
    have hcore : (path.map q).map k ≍ (path.map g).map q := by
      rw [← Path.Homotopic.Quotient.map_comp,
        ← Path.Homotopic.Quotient.map_comp]
      exact quotientMap_heq_of_eq path hcomm
    have hright : mappedProjection ≍ (path.map g).map q := by
      simp only [mappedProjection, mappedPath, Path.Homotopic.Quotient.map_cast,
        Path.Homotopic.Quotient.cast_cast]
      exact Path.Homotopic.Quotient.cast_heq _ _
    -- Endpoint transports are proof-irrelevant; the central uncast paths agree by the square.
    exact eq_of_heq (hleft.trans hcore |>.trans hright.symm)
  have hmonodromy :
      hqCovering.monodromy mappedProjection ⟨(1 : Circle), hq1⟩ =
        ⟨(-1 : Circle), hqneg1⟩ := by
    exact coveringMonodromy_map_cast hqCovering hq1 hqneg1 mappedPath
  intro htrivial
  have himageOne : FundamentalGroup.mapOfEq k hk1 projected = 1 := by
    rw [htrivial]
    rfl
  have hmappedOne : mappedProjection = 1 := himage.symm.trans himageOne
  have hendpoint := congrArg
    (fun loop : FundamentalGroup Circle 1 ↦
      hqCovering.monodromy loop ⟨(1 : Circle), hq1⟩)
    hmappedOne
  rw [hmonodromy, FundamentalGroup.one_def,
    hqCovering.monodromy_refl] at hendpoint
  have hfalse := congrArg Subtype.val hendpoint
  exact Circle.neg_ne_self 1 hfalse

/-- Helper for Theorem 57.1: a nontrivial endomorphism of the infinite cyclic
fundamental group of `Circle` is injective. -/
private lemma fundamentalGroupEndomorphism_injective_of_ne_one
    (f : FundamentalGroup Circle 1 →* FundamentalGroup Circle 1) (hf : f ≠ 1) :
    Function.Injective f := by
  -- Conjugate into multiplicative integers, where an endomorphism is fixed by one generator.
  let e := Circle.fundamentalGroupEquivInt
  let conjugate : Multiplicative ℤ →* Multiplicative ℤ :=
    e.toMonoidHom.comp (f.comp e.symm.toMonoidHom)
  have hconjugate : conjugate ≠ 1 := by
    intro htrivial
    apply hf
    ext x
    apply e.injective
    have hat := DFunLike.congr_fun htrivial (e x)
    have hback : e.symm.toMonoidHom (e x) = x := e.symm_apply_apply x
    simpa only [conjugate, MonoidHom.coe_comp, Function.comp_apply, hback,
      map_one, MonoidHom.one_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] using hat
  have hgenerator : conjugate (Multiplicative.ofAdd 1) ≠ 1 := by
    intro hgen
    apply hconjugate
    apply MonoidHom.ext_mint
    simpa using hgen
  have hgeneratorInt : (conjugate (Multiplicative.ofAdd 1)).toAdd ≠ 0 := by
    intro hzero
    apply hgenerator
    apply Multiplicative.ext
    simpa using hzero
  -- Cancel the nonzero generator image in the resulting integer multiplication equation.
  intro x y hxy
  apply e.injective
  have hbackX : e.symm.toMonoidHom (e x) = x := e.symm_apply_apply x
  have hbackY : e.symm.toMonoidHom (e y) = y := e.symm_apply_apply y
  have hconjugateEq : conjugate (e x) = conjugate (e y) := by
    simpa only [conjugate, MonoidHom.coe_comp, Function.comp_apply, hbackX,
      hbackY, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using
        congrArg e hxy
  have hpowers :
      conjugate (Multiplicative.ofAdd 1) ^ (e x).toAdd =
        conjugate (Multiplicative.ofAdd 1) ^ (e y).toAdd := by
    calc
      _ = conjugate (e x) :=
        (MonoidHom.apply_mint (Multiplicative ℤ) conjugate (e x)).symm
      _ = conjugate (e y) := hconjugateEq
      _ = _ := MonoidHom.apply_mint (Multiplicative ℤ) conjugate (e y)
  have hpowersInt := congrArg Multiplicative.toAdd hpowers
  apply Multiplicative.ext
  apply mul_right_cancel₀ hgeneratorInt
  simpa only [toAdd_zpow, zsmul_eq_mul, Int.cast_id] using hpowersInt

/-- Helper for Theorem 57.1: the endomorphism induced by the square map on the
circle fundamental group is injective. -/
private lemma square_inducedMap_injective :
    Function.Injective
      (FundamentalGroup.mapOfEq (CircleMap.zpower (2 : ℤ))
        (CircleMap.zpower_one (2 : ℤ))) := by
  -- In integer coordinates this map is multiplication by two.
  intro x y hxy
  rw [CircleMap.mapOfEq_apply_zpower, CircleMap.mapOfEq_apply_zpower] at hxy
  apply (Circle.fundamentalGroupEquivInt).injective
  apply Multiplicative.ext
  have hpowers := congrArg Circle.fundamentalGroupEquivInt hxy
  have hintegers := congrArg Multiplicative.toAdd hpowers
  norm_num only [map_zpow, toAdd_zpow, zsmul_eq_mul] at hintegers
  omega

/-- Helper for Theorem 57.1: pointed fundamental-group maps preserve composition,
including the chosen endpoint equalities. -/
private lemma fundamentalGroupMapOfEq_comp
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) {x : X} {y : Y} {z : Z}
    (hf : f x = y) (hg : g y = z) (hgf : (g.comp f) x = z) :
    (FundamentalGroup.mapOfEq g hg).comp (FundamentalGroup.mapOfEq f hf) =
      FundamentalGroup.mapOfEq (g.comp f) hgf := by
  -- Eliminate the intermediate basepoints, then use functoriality of mapped path classes.
  subst y
  subst z
  have hgRefl : hg = rfl := Subsingleton.elim _ _
  cases hgRefl
  ext loop
  simp only [MonoidHom.coe_comp, Function.comp_apply, FundamentalGroup.mapOfEq_apply,
    Path.Homotopic.Quotient.cast_rfl_rfl, Path.Homotopic.Quotient.map_comp]
  apply eq_of_heq
  exact Path.Homotopic.Quotient.cast_heq _ _

/-- Helper for Theorem 57.1: equal pointed maps induce the same fundamental-group
homomorphism, independently of endpoint proof choices. -/
private lemma fundamentalGroupMapOfEq_congr
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f g : C(X, Y)) {x : X} {y : Y} (hfg : f = g)
    (hf : f x = y) (hg : g x = y) :
    FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg := by
  -- Substitution leaves only proof-irrelevant endpoint witnesses.
  subst g
  rfl

/-- Helper for Theorem 57.1: a constant map sends every path class to the
constant path class. -/
private lemma quotientMap_const {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} (loop : Path.Homotopic.Quotient x x) (y : Y) :
    loop.map (ContinuousMap.const X y) = Path.Homotopic.Quotient.refl y := by
  -- Reduce to a representative path, whose constant image is pointwise constant.
  induction loop using Path.Homotopic.Quotient.ind with
  | mk path =>
      rw [← Path.Homotopic.Quotient.mk_map]
      congr 1

/-- Helper for Theorem 57.1: a nullhomotopic based circle map induces the trivial
endomorphism of the fundamental group. -/
private lemma inducedMap_eq_one_of_nullhomotopic (g : C(Circle, Circle))
    (hg1 : g 1 = 1) (hnull : g.Nullhomotopic) :
    FundamentalGroup.mapOfEq g hg1 = 1 := by
  -- Naturality of the homotopy identifies every mapped loop with a constant loop.
  obtain ⟨y, homotopy⟩ := hnull
  ext loop
  rw [FundamentalGroup.mapOfEq_apply]
  let pathClass : FundamentalGroupoid.mk (g 1) ⟶ FundamentalGroupoid.mk y :=
    (FundamentalGroupoidFunctor.homotopicMapsNatIso homotopy.some).app
      (FundamentalGroupoid.mk 1)
  have hnaturality :
      Path.Homotopic.Quotient.map (FundamentalGroup.toPath loop) g ≫ pathClass =
        pathClass := by
    have h := (FundamentalGroupoidFunctor.homotopicMapsNatIso homotopy.some).naturality loop
    simp only [FundamentalGroupoid.map_map, quotientMap_const] at h
    exact h.trans (Category.comp_id pathClass)
  have hmapped : Path.Homotopic.Quotient.map (FundamentalGroup.toPath loop) g =
      Path.Homotopic.Quotient.refl (g 1) := by
    apply (CategoryTheory.cancel_mono pathClass).mp
    exact hnaturality.trans (Category.id_comp pathClass).symm
  rw [hmapped, quotientRefl_cast hg1, MonoidHom.one_apply]
  exact FundamentalGroup.one_def.symm

/-- Helper for Theorem 57.1: normalizing a nullhomotopic circle map at `1`
preserves nullhomotopy. -/
private lemma normalizeAtOne_nullhomotopic (g : C(Circle, Circle))
    (hnull : g.Nullhomotopic) : (normalizeAtOne g).Nullhomotopic := by
  let translation : C(Circle, Circle) :=
    ContinuousMap.const Circle (g 1)⁻¹ * ContinuousMap.id Circle
  have hcomp : translation.comp g = normalizeAtOne g := by
    ext z
    rfl
  -- Postcompose the nullhomotopy with the fixed left translation.
  rw [← hcomp]
  exact hnull.comp_right translation

/-- Helper for Theorem 57.1: every odd continuous self-map of the complex circle
is not nullhomotopic. -/
private lemma oddMap_not_nullhomotopic (g : C(Circle, Circle))
    (hodd : Function.Odd g) : ¬ g.Nullhomotopic := by
  -- Normalize at `1`, descend through the square covering, and compare induced maps.
  intro hnull
  let normalized := normalizeAtOne g
  have hnormalizedOdd : Function.Odd normalized := odd_normalizeAtOne g hodd
  have hnormalizedOne : normalized 1 = 1 := normalizeAtOne_one g
  obtain ⟨k, hk1, hcomm⟩ :=
    existsSquareDescendant normalized hnormalizedOdd hnormalizedOne
  let q := CircleMap.zpower (2 : ℤ)
  have hq1 : q 1 = 1 := CircleMap.zpower_one (2 : ℤ)
  let inducedK := FundamentalGroup.mapOfEq k hk1
  let inducedQ := FundamentalGroup.mapOfEq q hq1
  let inducedNormalized := FundamentalGroup.mapOfEq normalized hnormalizedOne
  have hinducedKNe : inducedK ≠ 1 :=
    squareDescendant_inducedMap_ne_one normalized k hnormalizedOdd
      hnormalizedOne hk1 hcomm
  have hinducedKInjective : Function.Injective inducedK :=
    fundamentalGroupEndomorphism_injective_of_ne_one inducedK hinducedKNe
  have hinducedQInjective : Function.Injective inducedQ := by
    exact square_inducedMap_injective
  have hkq1 : (k.comp q) 1 = 1 := by
    simp only [ContinuousMap.comp_apply, hq1, hk1]
  have hqNormalized1 : (q.comp normalized) 1 = 1 := by
    simp only [ContinuousMap.comp_apply, hnormalizedOne, hq1]
  have hinducedSquare : inducedK.comp inducedQ =
      inducedQ.comp inducedNormalized := by
    calc
      inducedK.comp inducedQ = FundamentalGroup.mapOfEq (k.comp q) hkq1 :=
        fundamentalGroupMapOfEq_comp q k hq1 hk1 hkq1
      _ = FundamentalGroup.mapOfEq (q.comp normalized) hqNormalized1 :=
        fundamentalGroupMapOfEq_congr (k.comp q) (q.comp normalized) hcomm
          hkq1 hqNormalized1
      _ = inducedQ.comp inducedNormalized :=
        (fundamentalGroupMapOfEq_comp normalized q hnormalizedOne hq1
          hqNormalized1).symm
  have hinducedNormalizedInjective : Function.Injective inducedNormalized := by
    -- Injectivity of both outer maps in the commutative square forces injectivity in the middle.
    intro a b hab
    apply hinducedQInjective
    apply hinducedKInjective
    have ha := DFunLike.congr_fun hinducedSquare a
    have hb := DFunLike.congr_fun hinducedSquare b
    simpa only [MonoidHom.coe_comp, Function.comp_apply] using
      ha.trans ((congrArg inducedQ hab).trans hb.symm)
  have hnormalizedNull : normalized.Nullhomotopic :=
    normalizeAtOne_nullhomotopic g hnull
  have hinducedNormalizedOne : inducedNormalized = 1 :=
    inducedMap_eq_one_of_nullhomotopic normalized hnormalizedOne hnormalizedNull
  -- A trivial injective endomorphism would make the infinite cyclic group a subsingleton.
  have hsubsingleton : Subsingleton (FundamentalGroup Circle 1) := by
    constructor
    intro a b
    apply hinducedNormalizedInjective
    rw [hinducedNormalizedOne]
    simp only [MonoidHom.one_apply]
  have hsubsingletonInt : Subsingleton (Multiplicative ℤ) :=
    Circle.fundamentalGroupEquivInt.toEquiv.subsingleton_congr.mp hsubsingleton
  exact not_subsingleton_iff_nontrivial.mpr inferInstance hsubsingletonInt

end Circle

/-- Theorem 57.1. Every continuous antipode-preserving self-map of `S¹` is not
nullhomotopic. -/
theorem oddCircleMap_not_nullhomotopic
    (h : C(StandardSphere 1, StandardSphere 1))
    (h_odd : Function.Odd h) : ¬ h.Nullhomotopic := by
  -- Conjugate by complex coordinates, which preserve antipodes and nullhomotopy.
  let e := standardSphereOneHomeomorphCircle
  let g : C(Circle, Circle) :=
    (e : C(StandardSphere 1, Circle)).comp
      (h.comp (e.symm : C(Circle, StandardSphere 1)))
  have hinverseNeg (z : Circle) : e.symm (-z) = -e.symm z := by
    apply e.injective
    rw [e.apply_symm_apply, standardSphereOneHomeomorphCircle_neg,
      e.apply_symm_apply]
  have hgOdd : Function.Odd g := by
    intro z
    calc
      g (-z) = e (h (e.symm (-z))) := rfl
      _ = e (h (-e.symm z)) := congrArg (fun x ↦ e (h x)) (hinverseNeg z)
      _ = e (-h (e.symm z)) := congrArg e (h_odd (e.symm z))
      _ = -e (h (e.symm z)) := standardSphereOneHomeomorphCircle_neg _
      _ = -g z := rfl
  have hgNull (hnull : h.Nullhomotopic) : g.Nullhomotopic := by
    exact (hnull.comp_left (e.symm : C(Circle, StandardSphere 1))).comp_right
      (e : C(StandardSphere 1, Circle))
  -- The complex-circle theorem contradicts the transported nullhomotopy.
  intro hnull
  exact Circle.oddMap_not_nullhomotopic g hgOdd (hgNull hnull)
