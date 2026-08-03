module

public import Topology_Munkres_2000.Book.Definition_81_5.HomeomorphGroup
public import Topology_Munkres_2000.Book.Definition_36_1.TopologicalManifold
public import Topology_Munkres_2000.Book.Definition_81_8.LensSpace
public import Topology_Munkres_2000.Book.Definition_9_0_2
public import Topology_Munkres_2000.Book.Theorem_59_3
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Geometry.Manifold.Instances.Quotient
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Topology.Homeomorph.Quotient
public import Mathlib.Topology.Homotopy.Lifting

public section

open scoped LensSpace

noncomputable section

namespace LensSpace

-- Route correction: the prerequisite replays successfully, so the proof uses `act_apply` and
-- `action_vadd` as stable interfaces instead of unfolding the imported opaque action.

/-- Helper for Exercise 81.5: forgetting the sphere proof exposes the coordinate formula for
the weighted action. -/
private lemma coe_comp_act {n : ℕ} [NeZero n] (k : (ZMod n)ˣ) (j : ZMod n) :
    Subtype.val ∘ act k j = fun x ↦ WithLp.toLp 2 fun i ↦
      if i = 0 then (ZMod.toCircle j : ℂ) * x.1 i
      else (ZMod.toCircle ((k : ZMod n) * j) : ℂ) * x.1 i := by
  -- Compare the ambient vectors coordinatewise using the public computation rule for `act`.
  funext x
  ext i
  exact act_apply k j x i

/-- Helper for Exercise 81.5: every weighted rotation of the complex unit sphere is continuous. -/
private lemma continuous_act {n : ℕ} [NeZero n] (k : (ZMod n)ˣ) (j : ZMod n) :
    Continuous (act k j) := by
  -- Forget the sphere proof and check continuity of the two coordinates.
  apply continuous_induced_rng.mpr
  rw [coe_comp_act]
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  by_cases hi : i = 0
  · simp only [hi, if_pos]
    fun_prop
  · simp only [if_neg hi]
    fun_prop

/-- Helper for Exercise 81.5: rotation by `-j` after rotation by `j` fixes every point. -/
private lemma act_neg_act {n : ℕ} [NeZero n] (k : (ZMod n)ˣ) (j : ZMod n)
    (x : ThreeSphere) :
    act k (-j) (act k j x) = x := by
  -- Express both rotations through the additive action and combine their exponents.
  calc
    act k (-j) (act k j x) =
        (action k).vadd (-j) ((action k).vadd j x) := by
          rw [action_vadd, action_vadd]
    _ = (action k).vadd (-j + j) x := ((action k).add_vadd (-j) j x).symm
    _ = (action k).vadd 0 x := by rw [neg_add_cancel]
    _ = x := (action k).zero_vadd x

/-- Helper for Exercise 81.5: rotation by `j` after rotation by `-j` fixes every point. -/
private lemma act_act_neg {n : ℕ} [NeZero n] (k : (ZMod n)ˣ) (j : ZMod n)
    (x : ThreeSphere) :
    act k j (act k (-j) x) = x := by
  -- Apply the inverse-action identity with exponent `-j`.
  simpa only [neg_neg] using act_neg_act k (-j) x

/-- The homeomorphism generating the weighted cyclic rotations of the complex unit `3`-sphere. -/
def generator {n : ℕ} [NeZero n] (k : (ZMod n)ˣ) : ThreeSphere ≃ₜ ThreeSphere where
  toFun := act k 1
  invFun := act k (-1)
  left_inv := act_neg_act k 1
  right_inv := act_act_neg k 1
  continuous_toFun := continuous_act k 1
  continuous_invFun := continuous_act k (-1)

/-- Helper for Exercise 81.5: evaluation of the generator is rotation by exponent one. -/
private lemma generator_apply_eq_act {n : ℕ} [NeZero n] (k : (ZMod n)ˣ)
    (x : ThreeSphere) :
    generator k x = act k 1 x := by
  -- Read the forward map stored in the generator homeomorphism.
  rfl

/-- Helper for Exercise 81.5: evaluation of the inverse generator is rotation by exponent
negative one. -/
private lemma generator_inv_apply_eq_act {n : ℕ} [NeZero n] (k : (ZMod n)ˣ)
    (x : ThreeSphere) :
    (generator k)⁻¹ x = act k (-1) x := by
  -- Read the inverse map stored in the generator homeomorphism.
  rfl

/-- The generator acts by the two coordinate rotations of weights `1` and `k`. -/
theorem generator_apply {n : ℕ} [NeZero n] (k : (ZMod n)ˣ) (x : ThreeSphere)
    (i : Fin 2) :
    (generator k x).1 i = if i = 0 then (ZMod.toCircle (1 : ZMod n) : ℂ) * x.1 i
      else (ZMod.toCircle (k : ZMod n) : ℂ) * x.1 i := by
  -- Project evaluation to `act`, then simplify the second coordinate's unit exponent.
  rw [generator_apply_eq_act, act_apply, mul_one]

/-- Helper for Exercise 81.5: composing rotations adds their exponents. -/
private lemma act_act {n : ℕ} [NeZero n] (k : (ZMod n)ˣ) (a b : ZMod n)
    (x : ThreeSphere) :
    act k a (act k b x) = act k (a + b) x := by
  -- Translate to the bundled additive action and apply its associativity law.
  calc
    act k a (act k b x) = (action k).vadd a ((action k).vadd b x) := by
      rw [action_vadd, action_vadd]
    _ = (action k).vadd (a + b) x := ((action k).add_vadd a b x).symm
    _ = act k (a + b) x := action_vadd k (a + b) x

/-- Helper for Exercise 81.5: every integer power of the generator is the rotation with the
corresponding residue-class exponent. -/
private lemma generator_zpow_apply {n : ℕ} [NeZero n] (k : (ZMod n)ˣ) (m : ℤ)
    (x : ThreeSphere) :
    ((generator k) ^ m) x = act k (m : ZMod n) x := by
  -- Integer induction propagates the exponent formula through the generator and its inverse.
  induction m using Int.induction_on generalizing x with
  | zero =>
      calc
        ((generator k) ^ (0 : ℤ)) x = x := by
          rw [zpow_zero]
          rfl
        _ = (action k).vadd 0 x := ((action k).zero_vadd x).symm
        _ = act k (0 : ZMod n) x := action_vadd k 0 x
        _ = act k ((0 : ℤ) : ZMod n) x := by norm_num
  | succ m ih =>
      calc
        ((generator k) ^ ((m : ℤ) + 1)) x =
            ((generator k) ^ (m : ℤ)) (generator k x) := by
          rw [zpow_add_one]
          rfl
        _ = act k ((m : ℤ) : ZMod n) (generator k x) := ih (generator k x)
        _ = act k ((m : ℤ) : ZMod n) (act k 1 x) := by rw [generator_apply_eq_act]
        _ = act k (((m : ℤ) : ZMod n) + 1) x :=
          act_act k ((m : ℤ) : ZMod n) 1 x
        _ = act k (((m : ℤ) + 1 : ℤ) : ZMod n) x := by
          rw [Int.cast_add, Int.cast_one]
  | pred m ih =>
      calc
        ((generator k) ^ (-(m : ℤ) - 1)) x =
            ((generator k) ^ (-(m : ℤ))) ((generator k)⁻¹ x) := by
          rw [zpow_sub_one]
          rfl
        _ = act k ((-(m : ℤ) : ℤ) : ZMod n) ((generator k)⁻¹ x) :=
          ih ((generator k)⁻¹ x)
        _ = act k ((-(m : ℤ) : ℤ) : ZMod n) (act k (-1) x) := by
          rw [generator_inv_apply_eq_act]
        _ = act k (((-(m : ℤ) : ℤ) : ZMod n) + (-1)) x :=
          act_act k ((-(m : ℤ) : ℤ) : ZMod n) (-1) x
        _ = act k ((-(m : ℤ) - 1 : ℤ) : ZMod n) x := by
          rw [Int.cast_sub, Int.cast_one]
          congr 2
          rw [sub_eq_add_neg]

/-- Helper for Exercise 81.5: a point of the complex unit sphere has a nonzero coordinate. -/
private lemma threeSphere_exists_ne_zero_coord (x : ThreeSphere) :
    ∃ i : Fin 2, x.1 i ≠ 0 := by
  -- If both coordinates vanished, the ambient unit vector itself would vanish.
  by_contra h
  push Not at h
  apply ne_zero_of_mem_unit_sphere x
  ext i
  exact h i

/-- Helper for Exercise 81.5: the weighted action fixes a sphere point exactly at exponent zero. -/
private lemma act_eq_self_iff {n : ℕ} [NeZero n] (k : (ZMod n)ˣ) (j : ZMod n)
    (x : ThreeSphere) :
    act k j x = x ↔ j = 0 := by
  constructor
  · intro hfixed
    obtain ⟨i, hi⟩ := threeSphere_exists_ne_zero_coord x
    have hcoordinate := congrArg (fun y : ThreeSphere ↦ y.1 i) hfixed
    rw [act_apply] at hcoordinate
    by_cases hfirst : i = 0
    · rw [if_pos hfirst] at hcoordinate
      have hcircle : (ZMod.toCircle j : ℂ) = 1 := by
        apply mul_right_cancel₀ hi
        simpa only [one_mul] using hcoordinate
      apply ZMod.injective_toCircle
      apply Subtype.ext
      simpa only [AddChar.map_zero_eq_one, Circle.coe_one] using hcircle
    · rw [if_neg hfirst] at hcoordinate
      have hcircle : (ZMod.toCircle ((k : ZMod n) * j) : ℂ) = 1 := by
        apply mul_right_cancel₀ hi
        simpa only [one_mul] using hcoordinate
      have hweighted : (k : ZMod n) * j = 0 := by
        apply ZMod.injective_toCircle
        apply Subtype.ext
        simpa only [AddChar.map_zero_eq_one, Circle.coe_one] using hcircle
      have hweighted' : j * (k : ZMod n) = 0 := by
        simpa only [mul_comm] using hweighted
      exact (Units.mul_left_eq_zero k).mp hweighted'
  · intro hj
    rw [hj]
    calc
      act k 0 x = (action k).vadd 0 x := (action_vadd k 0 x).symm
      _ = x := (action k).zero_vadd x

/-- Helper for Exercise 81.5: an integer power is the identity exactly when its exponent
vanishes modulo `n`. -/
private lemma generator_zpow_eq_one_iff {n : ℕ} [NeZero n] (k : (ZMod n)ˣ) (m : ℤ) :
    (generator k) ^ m = 1 ↔ (m : ZMod n) = 0 := by
  constructor
  · intro hpower
    have hradius : (0 : ℝ) ≤ 1 := by norm_num
    obtain ⟨x⟩ : Nonempty ThreeSphere :=
      NormedSpace.sphere_nonempty_rclike ℂ hradius
    apply (act_eq_self_iff k (m : ZMod n) x).mp
    calc
      act k (m : ZMod n) x = ((generator k) ^ m) x :=
        (generator_zpow_apply k m x).symm
      _ = x := by
        rw [hpower]
        rfl
  · intro hm
    apply Homeomorph.ext
    intro x
    rw [generator_zpow_apply, hm]
    calc
      act k 0 x = (action k).vadd 0 x := (action_vadd k 0 x).symm
      _ = x := (action k).zero_vadd x

/-- Helper for Exercise 81.5: the generator has exactly order `n`. -/
private lemma generator_orderOf {n : ℕ} [NeZero n] (k : (ZMod n)ˣ) :
    orderOf (generator k) = n := by
  -- The order criterion reduces both divisibility conditions to arithmetic modulo `n`.
  apply (orderOf_eq_iff (NeZero.pos n)).mpr
  constructor
  · apply (generator_zpow_eq_one_iff k n).mpr
    simp
  · intro m hm_lt hm_pos hpower
    have hmzero : (m : ZMod n) = 0 := by
      simpa using (generator_zpow_eq_one_iff k m).mp hpower
    have hdiv : n ∣ m := (ZMod.natCast_eq_zero_iff m n).mp hmzero
    exact (Nat.not_dvd_of_pos_of_lt hm_pos hm_lt) hdiv

/-- The subgroup of sphere self-homeomorphisms generated by the weighted rotation. -/
def rotationGroup {n : ℕ} [NeZero n] (k : (ZMod n)ˣ) :
    Subgroup (ThreeSphere ≃ₜ ThreeSphere) :=
  Subgroup.zpowers (generator k)

/-- The weighted rotation group associated to positive coprime natural numbers `n` and `k`. -/
abbrev rotationGroupOfCoprime (n k : ℕ) (hn : 0 < n) (hcoprime : Nat.Coprime k n) :
    Subgroup (ThreeSphere ≃ₜ ThreeSphere) :=
  -- Local instance justification (proof-local temporary data): `hn` provides `NeZero n` here.
  letI : NeZero n := NeZero.of_pos hn
  rotationGroup (ZMod.unitOfCoprime k hcoprime)

/-- For Exercise 81.5 (1), the weighted rotation generates a cyclic subgroup of the
self-homeomorphism group of the complex unit `3`-sphere. -/
instance rotationGroup_isCyclic {n : ℕ} [NeZero n] (k : (ZMod n)ˣ) :
    IsCyclic (rotationGroup k) :=
  Subgroup.isCyclic_zpowers (generator k)

/-- For Exercise 81.5 (2), the weighted rotation group for positive coprime `n` and `k` has
order `n`. -/
theorem rotationGroup_card (n k : ℕ) (hn : 0 < n) (hcoprime : Nat.Coprime k n) :
    Nat.card (rotationGroupOfCoprime n k hn hcoprime) = n := by
  -- Replace the source-facing parameters by the canonical unit and count its generated powers.
  letI : NeZero n := NeZero.of_pos hn
  rw [rotationGroupOfCoprime, rotationGroup, Nat.card_zpowers,
    generator_orderOf (ZMod.unitOfCoprime k hcoprime)]

/-- For Exercise 81.5 (3), only the identity weighted rotation has a fixed point on the
complex unit `3`-sphere. -/
theorem rotationGroup_fixedPoint_iff (n k : ℕ) (hn : 0 < n) (hcoprime : Nat.Coprime k n)
    (g : rotationGroupOfCoprime n k hn hcoprime) :
    (∃ x : ThreeSphere, (g : ThreeSphere ≃ₜ ThreeSphere) x = x) ↔ g = 1 := by
  -- Express a subgroup element as a generator power, then use freeness of the `ZMod` action.
  letI : NeZero n := NeZero.of_pos hn
  let unit := ZMod.unitOfCoprime k hcoprime
  constructor
  · rintro ⟨x, hfixed⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.property
    have hpower_fixed : ((generator unit) ^ m) x = x := by
      rw [hm]
      exact hfixed
    have hexponent : (m : ZMod n) = 0 :=
      (act_eq_self_iff unit (m : ZMod n) x).mp <|
        (generator_zpow_apply unit m x).symm.trans hpower_fixed
    apply Subtype.ext
    exact hm.symm.trans ((generator_zpow_eq_one_iff unit m).mpr hexponent)
  · intro hg
    have hradius : (0 : ℝ) ≤ 1 := by norm_num
    obtain ⟨x⟩ : Nonempty ThreeSphere :=
      NormedSpace.sphere_nonempty_rclike ℂ hradius
    refine ⟨x, ?_⟩
    rw [hg]
    rfl

/-- The weighted rotation group acts freely on the complex unit `3`-sphere. -/
instance rotationGroup_isCancelSMul (n k : ℕ) (hn : 0 < n)
    (hcoprime : Nat.Coprime k n) :
    IsCancelSMul (rotationGroupOfCoprime n k hn hcoprime) ThreeSphere :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr fun g x hgx ↦
    (rotationGroup_fixedPoint_iff n k hn hcoprime g).mp ⟨x, hgx⟩

/-- Helper for Exercise 81.5: the generated rotation group and the additive residue-class
action determine the same orbit relation. -/
private lemma rotationOrbitRel_iff_actionOrbitRel
    (n k : ℕ) (hn : 0 < n) (hcoprime : Nat.Coprime k n) (x y : ThreeSphere) :
    MulAction.orbitRel (rotationGroupOfCoprime n k hn hcoprime) ThreeSphere x y ↔
      @AddAction.orbitRel (ZMod n) ThreeSphere _
        (@action n (NeZero.of_pos hn) (ZMod.unitOfCoprime k hcoprime)) x y := by
  -- Normalize both relations to witnesses carrying `y` to `x`.
  letI : NeZero n := NeZero.of_pos hn
  let unit := ZMod.unitOfCoprime k hcoprime
  letI : AddAction (ZMod n) ThreeSphere := action unit
  rw [MulAction.orbitRel_apply, HomeomorphGroup.mem_orbit_iff,
    AddAction.orbitRel_apply, AddAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.property
    refine ⟨(m : ZMod n), ?_⟩
    calc
      (action unit).vadd (m : ZMod n) y = act unit (m : ZMod n) y :=
        action_vadd unit (m : ZMod n) y
      _ = ((generator unit) ^ m) y := (generator_zpow_apply unit m y).symm
      _ = (g : ThreeSphere ≃ₜ ThreeSphere) y :=
        congrArg (fun f : ThreeSphere ≃ₜ ThreeSphere ↦ f y) hm
      _ = x := hg
  · rintro ⟨j, hj⟩
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective j
    have hmember : (generator unit) ^ m ∈ rotationGroup unit :=
      Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩
    let g : rotationGroup unit := ⟨(generator unit) ^ m, hmember⟩
    refine ⟨g, ?_⟩
    calc
      (g : ThreeSphere ≃ₜ ThreeSphere) y = ((generator unit) ^ m) y := rfl
      _ = act unit (m : ZMod n) y := generator_zpow_apply unit m y
      _ = (action unit).vadd (m : ZMod n) y :=
        (action_vadd unit (m : ZMod n) y).symm
      _ = x := hj

/-- For Exercise 81.5 (4), the orbit space of the generated homeomorphism group is the
lens space `L(n, k)`. -/
def orbitSpaceHomeomorph (n k : ℕ) (hn : 0 < n) (hcoprime : Nat.Coprime k n) :
    HomeomorphGroup.OrbitSpace (rotationGroupOfCoprime n k hn hcoprime) ≃ₜ L(n, k) :=
  Homeomorph.Quotient.congrRight
    (rotationOrbitRel_iff_actionOrbitRel n k hn hcoprime)

/-- Helper for Exercise 81.5: the ambient complex two-space has real dimension four. -/
private lemma threeSphere_real_finrank :
    Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1 := by
  -- Count two real dimensions for each complex coordinate.
  rw [finrank_real_of_complex, finrank_euclideanSpace_fin]

/-- Helper for Exercise 81.5: an orthonormal basis identifies the ambient complex two-space
with real four-space. -/
private noncomputable def threeSphereAmbientIsometry :
    EuclideanSpace ℂ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (3 + 1)) :=
  ((stdOrthonormalBasis ℝ (EuclideanSpace ℂ (Fin 2))).reindex
    (finCongr threeSphere_real_finrank)).repr

/-- Helper for Exercise 81.5: the ambient isometry preserves the unit-sphere predicate. -/
private lemma threeSphereAmbientIsometry_mem_iff (x : EuclideanSpace ℂ (Fin 2)) :
    x ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 ↔
      threeSphereAmbientIsometry x ∈
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1 := by
  -- Membership on both sides is the same norm-one equation.
  rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm,
    LinearIsometryEquiv.norm_map]

/-- Helper for Exercise 81.5: the complex unit `3`-sphere is homeomorphic to the standard
real unit `3`-sphere. -/
private noncomputable def threeSphereHomeomorphStandardSphere :
    ThreeSphere ≃ₜ StandardSphere 3 :=
  threeSphereAmbientIsometry.toHomeomorph.subtype
    threeSphereAmbientIsometry_mem_iff

/-- Helper for Exercise 81.5: the standard real unit `3`-sphere is simply connected. -/
private lemma simplyConnectedSpace_standardThreeSphere :
    SimplyConnectedSpace (StandardSphere 3) := by
  -- Dimension three satisfies the standard sphere theorem's lower bound.
  have hdimension : 2 ≤ 3 := by omega
  exact simplyConnectedSpace_standardSphere 3 hdimension

/-- Helper for Exercise 81.5: the complex unit `3`-sphere is simply connected. -/
private lemma simplyConnectedSpace_threeSphere : SimplyConnectedSpace ThreeSphere := by
  -- Transport simple connectedness of the standard `3`-sphere across the sphere homeomorphism.
  letI : SimplyConnectedSpace (StandardSphere 3) :=
    simplyConnectedSpace_standardThreeSphere
  exact threeSphereHomeomorphStandardSphere.toHomotopyEquiv.simplyConnectedSpace

/-- Helper for Exercise 81.5: the bundled additive action is continuous in its sphere input. -/
private lemma continuous_action_vadd {n : ℕ} [NeZero n] (k : (ZMod n)ˣ) (j : ZMod n) :
    Continuous fun x : ThreeSphere ↦ (action k).vadd j x := by
  -- Rewrite the bundled operation to the explicit rotation before applying continuity.
  have hfunctions : (fun x : ThreeSphere ↦ (action k).vadd j x) = act k j := by
    funext x
    exact action_vadd k j x
  rw [hfunctions]
  exact continuous_act k j

/-- Helper for Exercise 81.5: a bundled action element fixing a sphere point is zero. -/
private lemma eq_zero_of_action_vadd_eq {n : ℕ} [NeZero n] (k : (ZMod n)ˣ)
    (j : ZMod n) (x : ThreeSphere) (hfixed : (action k).vadd j x = x) :
    j = 0 := by
  -- Pass from the bundled action to the explicit rotation and apply its freeness criterion.
  apply (act_eq_self_iff k j x).mp
  exact (action_vadd k j x).symm.trans hfixed

/-- Helper for Exercise 81.5: the fundamental group of a lens space has cardinality `n`. -/
private lemma fundamentalGroup_card {n : ℕ} [NeZero n] (k : (ZMod n)ˣ)
    (x : LensSpace n k) :
    Nat.card (FundamentalGroup (LensSpace n k) x) = n := by
  -- Install the explicit continuous free action used in the quotient definition.
  letI : AddAction (ZMod n) ThreeSphere := action k
  letI : ContinuousConstVAdd (ZMod n) ThreeSphere :=
    ⟨continuous_action_vadd k⟩
  letI : IsCancelVAdd (ZMod n) ThreeSphere :=
    isCancelVAdd_iff_eq_zero_of_vadd_eq.mpr (eq_zero_of_action_vadd_eq k)
  letI : SimplyConnectedSpace ThreeSphere := simplyConnectedSpace_threeSphere
  let covering :=
    isAddQuotientCoveringMap_quotientMk_of_properlyDiscontinuousVAdd
      (G := ZMod n) (E := ThreeSphere)
  obtain ⟨y, hy⟩ := covering.surjective x
  have hyfiber : (Quotient.mk (AddAction.orbitRel (ZMod n) ThreeSphere) y :
      LensSpace n k) ∈ ({x} : Set (LensSpace n k)) := by
    -- The chosen representative lies over the requested basepoint.
    simpa only [Set.mem_singleton_iff] using hy
  let fiberPoint :
      (Quotient.mk (AddAction.orbitRel (ZMod n) ThreeSphere)) ⁻¹' ({x} : Set (LensSpace n k)) :=
    ⟨y, hyfiber⟩
  -- The universal-cover equivalence identifies the fundamental group with the finite deck group.
  calc
    Nat.card (FundamentalGroup (LensSpace n k) x) =
        Nat.card (Multiplicative (ZMod n))ᵐᵒᵖ :=
      Nat.card_congr (covering.fundamentalGroupEquiv fiberPoint).toEquiv
    _ = Nat.card (Multiplicative (ZMod n)) :=
      Nat.card_congr MulOpposite.opEquiv.symm
    _ = Nat.card (ZMod n) := Nat.card_congr Multiplicative.toAdd
    _ = n := Nat.card_zmod n

/-- Exercise 81.5 (5). Homeomorphic positive-coprime lens spaces have the same first
parameter. -/
theorem homeomorphic_imp_firstParameter_eq
    (n k n' k' : ℕ) (hn : 0 < n) (hn' : 0 < n')
    (hcoprime : Nat.Coprime k n) (hcoprime' : Nat.Coprime k' n')
    (homeomorph : L(n, k) ≃ₜ L(n', k')) :
    n = n' := by
  -- Compare the cardinalities of the two fundamental groups through the homeomorphism.
  letI : NeZero n := NeZero.of_pos hn
  letI : NeZero n' := NeZero.of_pos hn'
  let unit := ZMod.unitOfCoprime k hcoprime
  let unit' := ZMod.unitOfCoprime k' hcoprime'
  have hradius : (0 : ℝ) ≤ 1 := by norm_num
  obtain ⟨y⟩ : Nonempty ThreeSphere :=
    NormedSpace.sphere_nonempty_rclike ℂ hradius
  let x : L(n, k) := quotientMap unit y
  calc
    n = Nat.card (FundamentalGroup (L(n, k)) x) :=
      (fundamentalGroup_card unit x).symm
    _ = Nat.card (FundamentalGroup (L(n', k')) (homeomorph x)) :=
      Nat.card_congr (homeomorph.fundamentalGroupMulEquiv x).toEquiv
    _ = n' := fundamentalGroup_card unit' (homeomorph x)

/- Exercise 81.5 (6). Every positive-coprime lens space is compact. -/
#check fun (n k : ℕ) (hn : 0 < n) (hcoprime : Nat.Coprime k n) ↦
  (inferInstance : CompactSpace L(n, k))

/-- For Exercise 81.5 (7), every lens space admits the structure of a topological
`3`-manifold. -/
theorem existsThreeManifoldStructure {n : ℕ} [NeZero n] (k : (ZMod n)ˣ) :
    ∃ charts : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (LensSpace n k),
      TopologicalManifold.With 3 charts := by
  -- Equip the sphere with its dimension-three charts and the quotient with the induced charts.
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
    ⟨threeSphere_real_finrank⟩
  letI : AddAction (ZMod n) ThreeSphere := action k
  letI : ContinuousConstVAdd (ZMod n) ThreeSphere :=
    ⟨continuous_action_vadd k⟩
  letI : IsCancelVAdd (ZMod n) ThreeSphere :=
    isCancelVAdd_iff_eq_zero_of_vadd_eq.mpr (eq_zero_of_action_vadd_eq k)
  let charts : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (LensSpace n k) :=
    inferInstance
  refine ⟨charts, ?_⟩
  -- Hausdorffness follows from proper discontinuity; openness of the quotient gives countability.
  rw [TopologicalManifold.with_iff]
  exact ⟨inferInstance, ContinuousConstVAdd.secondCountableTopology⟩

end LensSpace
