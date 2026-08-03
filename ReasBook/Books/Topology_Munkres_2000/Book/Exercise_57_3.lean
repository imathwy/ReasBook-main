module

public import Topology_Munkres_2000.Book.Theorem_57_1
public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Analysis.Complex.Circle

public section

noncomputable section

namespace Circle

/-- Helper for Exercise 57.3: squaring a point of `Circle` is unchanged by negation. -/
private lemma neg_sq_circle (z : Circle) : (-z) ^ (2 : ℕ) = z ^ (2 : ℕ) := by
  -- Pass to complex coordinates, where the equality is a ring identity.
  apply Circle.ext
  simp only [Circle.coe_pow, Circle.coe_neg]
  ring

/-- Helper for Exercise 57.3: an odd based circle map has a descendant through
the square covering. -/
private lemma existsSquareDescendant (h : C(Circle, Circle)) (hodd : Function.Odd h)
    (hh1 : h 1 = 1) :
    ∃ k : C(Circle, Circle), k 1 = 1 ∧
      k.comp (CircleMap.zpower (2 : ℤ)) = (CircleMap.zpower (2 : ℤ)).comp h := by
  classical
  let q := CircleMap.zpower (2 : ℤ)
  have hfactors : Function.FactorsThrough (q.comp h) q := by
    intro z w hzw
    have hsqCircle : z ^ (2 : ℕ) = w ^ (2 : ℕ) := by
      simpa only [q, CircleMap.zpower_apply, zpow_ofNat] using hzw
    have hsq : (z : ℂ) ^ 2 = (w : ℂ) ^ 2 := by
      simpa only [Circle.coe_pow] using congrArg Subtype.val hsqCircle
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hpositive | hnegative
    · exact congrArg (fun u : Circle ↦ q (h u)) (Subtype.ext hpositive)
    · have hcircle : z = -w := by
        apply Circle.ext
        exact hnegative
      rw [hcircle]
      simp only [ContinuousMap.comp_apply]
      rw [hodd w]
      simpa only [ContinuousMap.comp_apply, q, CircleMap.zpower_apply, zpow_ofNat] using
        neg_sq_circle (h w)
  have hqFunction : (q : Circle → Circle) = fun z ↦ z ^ (2 : ℤ) := by
    funext z
    exact CircleMap.zpower_apply (2 : ℤ) z
  have hqQuotient : Topology.IsQuotientMap q := by
    rw [hqFunction]
    exact (Circle.isQuotientCoveringMap_zpow (2 : ℤ)).toIsQuotientMap
  let k := hqQuotient.lift (q.comp h) hfactors
  refine ⟨k, ?_, ?_⟩
  · -- The defining lift equation evaluated at `1` shows that the descendant is based.
    have hbase := congrArg (fun f : C(Circle, Circle) ↦ f 1)
      (hqQuotient.lift_comp (q.comp h) hfactors)
    simpa only [ContinuousMap.comp_apply, q, CircleMap.zpower_one, hh1] using hbase
  · -- Keep the quotient construction opaque behind its commutative-square equation.
    exact hqQuotient.lift_comp (q.comp h) hfactors

/-- Helper for Exercise 57.3: the induced endomorphism of the square map on the
circle fundamental group is injective. -/
private lemma square_inducedMap_injective :
    Function.Injective
      (FundamentalGroup.mapOfEq (CircleMap.zpower (2 : ℤ))
        (CircleMap.zpower_one (2 : ℤ))) := by
  -- Integer coordinates turn the induced square map into multiplication by two.
  intro x y hxy
  rw [CircleMap.mapOfEq_apply_zpower, CircleMap.mapOfEq_apply_zpower] at hxy
  apply (Circle.fundamentalGroupEquivInt).injective
  apply Multiplicative.ext
  have hpowers := congrArg Circle.fundamentalGroupEquivInt hxy
  have hintegers := congrArg Multiplicative.toAdd hpowers
  norm_num only [map_zpow, toAdd_zpow, zsmul_eq_mul] at hintegers
  omega

/-- Helper for Exercise 57.3: a generator of the circle fundamental group is not
in the range of the induced square map. -/
private lemma generator_not_mem_squareMapRange
    (g : FundamentalGroup Circle 1) (hgenerator : Subgroup.zpowers g = ⊤) :
    g ∉ (FundamentalGroup.mapOfEq (CircleMap.zpower (2 : ℤ))
      (CircleMap.zpower_one (2 : ℤ))).range := by
  letI : Infinite (FundamentalGroup Circle 1) :=
    Infinite.of_injective Circle.fundamentalGroupEquivInt.symm
      Circle.fundamentalGroupEquivInt.symm.injective
  -- A putative square root has an integer exponent relative to the chosen generator.
  rintro ⟨x, hx⟩
  rw [CircleMap.mapOfEq_apply_zpower] at hx
  have hxmem : x ∈ Subgroup.zpowers g := by
    rw [hgenerator]
    exact Subgroup.mem_top x
  obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp hxmem
  have hcoordinates := congrArg (intEquivOfZPowersEqTop g hgenerator).symm hx
  -- Its coordinate would satisfy `2 * r = 1`, which is impossible over `ℤ`.
  rw [← hr, map_zpow, map_zpow,
    intEquivOfZPowersEqTop_symm_self hgenerator] at hcoordinates
  have hintegers := congrArg Multiplicative.toAdd hcoordinates
  norm_num only [toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul] at hintegers
  omega

/-- Helper for Exercise 57.3: projecting a path through a covering and aligning
its endpoints makes monodromy recover the endpoint upstairs. -/
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

/-- Helper for Exercise 57.3: equal continuous maps give heterogeneously equal
mapped path classes, independently of endpoint spellings. -/
private lemma quotientMap_heq_of_eq {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {x₀ x₁ : X} (path : Path.Homotopic.Quotient x₀ x₁)
    {f g : C(X, Y)} (hfg : f = g) : HEq (path.map f) (path.map g) := by
  -- Substitution leaves two identically typed mapped path classes.
  subst g
  rfl

/-- Helper for Exercise 57.3: equal pointed maps induce the same fundamental-group
homomorphism, independently of endpoint proof choices. -/
private lemma fundamentalGroupMapOfEq_congr
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f g : C(X, Y)) {x : X} {y : Y} (hfg : f = g)
    (hf : f x = y) (hg : g x = y) :
    FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg := by
  -- Substitution leaves only proof-irrelevant endpoint witnesses.
  subst g
  rfl

/-- Helper for Exercise 57.3: an odd square descendant sends a generator outside
the range of the induced square map. -/
private lemma squareDescendant_image_not_mem_squareMapRange
    (h k : C(Circle, Circle)) (hodd : Function.Odd h) (hh1 : h 1 = 1)
    (hk1 : k 1 = 1)
    (hcomm : k.comp (CircleMap.zpower (2 : ℤ)) =
      (CircleMap.zpower (2 : ℤ)).comp h)
    (g : FundamentalGroup Circle 1) (hgenerator : Subgroup.zpowers g = ⊤) :
    FundamentalGroup.mapOfEq k hk1 g ∉
      (FundamentalGroup.mapOfEq (CircleMap.zpower (2 : ℤ))
        (CircleMap.zpower_one (2 : ℤ))).range := by
  let q := CircleMap.zpower (2 : ℤ)
  have hq1 : q 1 = 1 := CircleMap.zpower_one (2 : ℤ)
  have hqFunction : (q : Circle → Circle) = fun z ↦ z ^ (2 : ℤ) := by
    funext z
    exact CircleMap.zpower_apply (2 : ℤ) z
  have hqQuotient :
      IsQuotientCoveringMap q (zpowGroupHom (α := Circle) (2 : ℤ)).ker := by
    rw [hqFunction]
    exact Circle.isQuotientCoveringMap_zpow (2 : ℤ)
  let hqCovering := hqQuotient.isCoveringMap
  let e : q ⁻¹' {1} := ⟨1, hq1⟩
  have hqMapEq : (⟨q, hqQuotient.continuous⟩ : C(Circle, Circle)) = q := by
    ext z
    rfl
  have hinducedQ :
      FundamentalGroup.mapOfEq ⟨q, hqQuotient.continuous⟩ e.2 =
        FundamentalGroup.mapOfEq q hq1 :=
    fundamentalGroupMapOfEq_congr _ q hqMapEq e.2 hq1
  have hgeneratorNotRange := generator_not_mem_squareMapRange g hgenerator
  have hgeneratorNotKer :
      g ∉ (hqCovering.monodromyPerm (1 : Circle)).ker := by
    rw [hqQuotient.ker_monodromyPerm e, hinducedQ]
    simpa only [q] using hgeneratorNotRange
  have hendpointNe : (hqCovering.monodromy g e : Circle) ≠ 1 := by
    intro hendpoint
    apply hgeneratorNotKer
    rw [MonoidHom.mem_ker]
    apply Equiv.ext
    intro x
    exact congr_fun
      ((hqQuotient.monodromy_eq_id_iff e).mpr (Subtype.ext hendpoint)) x
  have hendpointSq : ((hqCovering.monodromy g e : Circle) : ℂ) ^ 2 = 1 := by
    have hfiber := (hqCovering.monodromy g e).property
    simpa only [Set.mem_singleton_iff, q, CircleMap.zpower_apply, zpow_ofNat,
      Circle.coe_pow, Circle.coe_one] using congrArg Subtype.val hfiber
  have hendpointNeg : (hqCovering.monodromy g e : Circle) = -1 := by
    rcases sq_eq_one_iff.mp hendpointSq with hpositive | hnegative
    · exact False.elim (hendpointNe (Circle.ext hpositive))
    · exact Circle.ext hnegative
  have hhneg1 : h (-1) = -1 := by
    calc
      h (-1) = -h 1 := by simpa using hodd (1 : Circle)
      _ = -1 := congrArg Neg.neg hh1
  have hmappedEndpoint : h (hqCovering.monodromy g e : Circle) = -1 := by
    rw [hendpointNeg, hhneg1]
  have hqneg1 : q (-1) = 1 := by
    apply Circle.ext
    norm_num [q, CircleMap.zpower_apply]
  let path := hqCovering.liftPathQuotient g e
  let projected : FundamentalGroup Circle 1 :=
    (path.map q).cast hq1.symm (hqCovering.monodromy g e).property.symm
  let mappedPath : Path.Homotopic.Quotient (1 : Circle) (-1) :=
    (path.map h).cast hh1.symm hmappedEndpoint.symm
  let mappedProjection : FundamentalGroup Circle 1 :=
    (mappedPath.map q).cast hq1.symm hqneg1.symm
  have hprojected : projected = g := by
    -- Mapping the canonical lift back down and cancelling its endpoint casts recovers `g`.
    have hqCoveringMapEq :
        (⟨q, hqCovering.continuous⟩ : C(Circle, Circle)) = q := by
      ext z
      rfl
    have hmap : path.map q =
        Path.Homotopic.Quotient.cast g e.2
          (hqCovering.monodromy g e).property := by
      have hmapCovering := hqCovering.map_liftPathQuotient g e
      have hmapEq : HEq (path.map q)
          (path.map ⟨q, hqCovering.continuous⟩) :=
        (quotientMap_heq_of_eq path hqCoveringMapEq).symm
      exact eq_of_heq (hmapEq.trans (heq_of_eq hmapCovering))
    simp only [projected]
    rw [hmap, Path.Homotopic.Quotient.cast_cast]
    exact Path.Homotopic.Quotient.cast_rfl_rfl _
  have himage : FundamentalGroup.mapOfEq k hk1 projected = mappedProjection := by
    have hleft : FundamentalGroup.mapOfEq k hk1 projected ≍ (path.map q).map k := by
      simp only [FundamentalGroup.mapOfEq_apply, projected,
        Path.Homotopic.Quotient.map_cast, Path.Homotopic.Quotient.cast_cast]
      exact Path.Homotopic.Quotient.cast_heq _ _
    have hcore : (path.map q).map k ≍ (path.map h).map q := by
      rw [← Path.Homotopic.Quotient.map_comp,
        ← Path.Homotopic.Quotient.map_comp]
      exact quotientMap_heq_of_eq path hcomm
    have hright : mappedProjection ≍ (path.map h).map q := by
      simp only [mappedProjection, mappedPath, Path.Homotopic.Quotient.map_cast,
        Path.Homotopic.Quotient.cast_cast]
      exact Path.Homotopic.Quotient.cast_heq _ _
    -- The square equation identifies the uncast cores; endpoint proofs are irrelevant.
    exact eq_of_heq (hleft.trans hcore |>.trans hright.symm)
  have hmonodromy :
      hqCovering.monodromy mappedProjection e = ⟨(-1 : Circle), hqneg1⟩ := by
    exact coveringMonodromy_map_cast hqCovering hq1 hqneg1 mappedPath
  intro himageRange
  have himageKer : FundamentalGroup.mapOfEq k hk1 g ∈
      (hqCovering.monodromyPerm (1 : Circle)).ker := by
    rw [hqQuotient.ker_monodromyPerm e, hinducedQ]
    simpa only [q] using himageRange
  have hfixed : hqCovering.monodromy (FundamentalGroup.mapOfEq k hk1 g) e = e := by
    have hperm := MonoidHom.mem_ker.mp himageKer
    exact congr_fun (congrArg Equiv.toFun hperm) e
  rw [← hprojected, himage, hmonodromy] at hfixed
  have hfalse := congrArg Subtype.val hfixed
  exact Circle.neg_ne_self 1 hfalse

/-- Helper for Exercise 57.3: pointed fundamental-group maps preserve composition,
including the chosen endpoint equalities. -/
private lemma fundamentalGroupMapOfEq_comp
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) {x : X} {y : Y} {z : Z}
    (hf : f x = y) (hg : g y = z) (hgf : (g.comp f) x = z) :
    (FundamentalGroup.mapOfEq g hg).comp (FundamentalGroup.mapOfEq f hf) =
      FundamentalGroup.mapOfEq (g.comp f) hgf := by
  -- Eliminate the intermediate basepoints before applying functoriality of path mapping.
  subst y
  subst z
  have hgRefl : hg = rfl := Subsingleton.elim _ _
  cases hgRefl
  ext loop
  simp only [MonoidHom.coe_comp, Function.comp_apply, FundamentalGroup.mapOfEq_apply,
    Path.Homotopic.Quotient.cast_rfl_rfl, Path.Homotopic.Quotient.map_comp]
  apply eq_of_heq
  exact Path.Homotopic.Quotient.cast_heq _ _

/-- Helper for Exercise 57.3: a based odd map and its square descendant induce
the same endomorphism of the circle fundamental group. -/
private lemma squareDescendant_inducedMap_eq
    (h k : C(Circle, Circle)) (hh1 : h 1 = 1) (hk1 : k 1 = 1)
    (hcomm : k.comp (CircleMap.zpower (2 : ℤ)) =
      (CircleMap.zpower (2 : ℤ)).comp h) :
    FundamentalGroup.mapOfEq k hk1 = FundamentalGroup.mapOfEq h hh1 := by
  let q := CircleMap.zpower (2 : ℤ)
  have hq1 : q 1 = 1 := CircleMap.zpower_one (2 : ℤ)
  have hkq1 : (k.comp q) 1 = 1 := by
    simp only [ContinuousMap.comp_apply, hq1, hk1]
  have hqh1 : (q.comp h) 1 = 1 := by
    simp only [ContinuousMap.comp_apply, hh1, hq1]
  let inducedK := FundamentalGroup.mapOfEq k hk1
  let inducedH := FundamentalGroup.mapOfEq h hh1
  let inducedQ := FundamentalGroup.mapOfEq q hq1
  have hsquare : inducedK.comp inducedQ = inducedQ.comp inducedH := by
    calc
      inducedK.comp inducedQ = FundamentalGroup.mapOfEq (k.comp q) hkq1 :=
        fundamentalGroupMapOfEq_comp q k hq1 hk1 hkq1
      _ = FundamentalGroup.mapOfEq (q.comp h) hqh1 :=
        fundamentalGroupMapOfEq_congr (k.comp q) (q.comp h) hcomm hkq1 hqh1
      _ = inducedQ.comp inducedH :=
        (fundamentalGroupMapOfEq_comp h q hh1 hq1 hqh1).symm
  ext x
  apply square_inducedMap_injective
  have hsquareAt := DFunLike.congr_fun hsquare x
  -- Rewrite the commutative square pointwise, using that every homomorphism preserves powers.
  calc
    inducedQ (inducedK x) = (inducedK x) ^ (2 : ℤ) :=
      CircleMap.mapOfEq_apply_zpower (2 : ℤ) (inducedK x)
    _ = inducedK (x ^ (2 : ℤ)) := (map_zpow inducedK x (2 : ℤ)).symm
    _ = inducedK (inducedQ x) := by
      rw [CircleMap.mapOfEq_apply_zpower]
    _ = inducedQ (inducedH x) := by
      simpa only [MonoidHom.coe_comp, Function.comp_apply] using hsquareAt

end Circle

/-- Exercise 57.3. A continuous antipode-preserving self-map of `S¹` fixing the
basepoint sends a chosen generator of `π₁(S¹, 1)` to an odd power of itself. -/
theorem oddPowerOfFundamentalGroupGenerator
    (h : C(Circle, Circle)) (h_odd : Function.Odd h) (h_base : h 1 = 1)
    (g : FundamentalGroup Circle 1) (h_generator : Subgroup.zpowers g = ⊤) :
    ∃ n : ℤ, Odd n ∧ FundamentalGroup.mapOfEq h h_base g = g ^ n := by
  -- Descend through the square covering and retain only its based commutative square.
  obtain ⟨k, hk1, hcomm⟩ := Circle.existsSquareDescendant h h_odd h_base
  have hkOutside := Circle.squareDescendant_image_not_mem_squareMapRange
    h k h_odd h_base hk1 hcomm g h_generator
  have hinducedEq := Circle.squareDescendant_inducedMap_eq h k h_base hk1 hcomm
  have himageMem : FundamentalGroup.mapOfEq k hk1 g ∈ Subgroup.zpowers g := by
    rw [h_generator]
    exact Subgroup.mem_top _
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp himageMem
  refine ⟨n, ?_, ?_⟩
  · -- An even exponent would make the descendant's generator image a square.
    by_contra hnodd
    obtain ⟨r, hr⟩ := Int.not_odd_iff_even.mp hnodd
    apply hkOutside
    refine ⟨g ^ r, ?_⟩
    rw [CircleMap.mapOfEq_apply_zpower, ← zpow_mul, mul_two, ← hr, hn]
  · -- The induced maps agree, so the same odd exponent describes the original map.
    rw [← hinducedEq]
    exact hn.symm

end
