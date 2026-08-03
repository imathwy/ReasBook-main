module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.GroupAction.Defs

public section

namespace LensSpace

/-- The complex unit `3`-sphere, modeled as the unit sphere in `ℂ²`. -/
abbrev ThreeSphere : Type :=
  Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1

/-- Helper for Definition 81.8: the ambient weighted diagonal rotation on `ℂ²`. -/
private noncomputable def diagonalRotation {n : ℕ} [NeZero n] (k j : ZMod n)
    (x : EuclideanSpace ℂ (Fin 2)) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 fun i ↦ if i = 0 then (ZMod.toCircle j : ℂ) * x i
    else (ZMod.toCircle (k * j) : ℂ) * x i

/-- Helper for Definition 81.8: weighted diagonal rotations preserve the Euclidean norm. -/
private theorem diagonalRotation_norm {n : ℕ} [NeZero n] (k j : ZMod n)
    (x : EuclideanSpace ℂ (Fin 2)) :
    ‖diagonalRotation k j x‖ = ‖x‖ := by
  -- Compare the coordinatewise squared-norm sums under the common square root.
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply congrArg Real.sqrt
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = 0
  · simp only [diagonalRotation, PiLp.toLp_apply, if_pos hi, norm_mul,
      Circle.norm_coe, one_mul]
  · simp only [diagonalRotation, PiLp.toLp_apply, if_neg hi, norm_mul,
      Circle.norm_coe, one_mul]

/-- Helper for Definition 81.8: weighted diagonal rotations preserve the unit `3`-sphere. -/
private theorem diagonalRotation_mem_sphere {n : ℕ} [NeZero n] (k j : ZMod n)
    (x : ThreeSphere) :
    diagonalRotation k j x.1 ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 := by
  -- Transfer the original unit-norm equation through norm preservation.
  rw [mem_sphere_zero_iff_norm, diagonalRotation_norm]
  exact mem_sphere_zero_iff_norm.mp x.property

/-- The diagonal cyclic rotation with weights `1` and `k` on the complex unit `3`-sphere. -/
noncomputable def act {n : ℕ} [NeZero n] (k : (ZMod n)ˣ) (j : ZMod n)
    (x : ThreeSphere) : ThreeSphere :=
  ⟨diagonalRotation (k : ZMod n) j x.1,
    diagonalRotation_mem_sphere (k : ZMod n) j x⟩

/-- Each coordinate of `act k j x` is given by the corresponding diagonal cyclic rotation. -/
theorem act_apply {n : ℕ} [NeZero n] (k : (ZMod n)ˣ) (j : ZMod n)
    (x : ThreeSphere) (i : Fin 2) :
    (act k j x).1 i = if i = 0 then (ZMod.toCircle j : ℂ) * x.1 i
      else (ZMod.toCircle ((k : ZMod n) * j) : ℂ) * x.1 i := by
  -- Read the requested coordinate from the named ambient rotation.
  rfl

/-- Helper for Definition 81.8: the zero group element acts trivially. -/
private theorem act_zero {n : ℕ} [NeZero n] (k : (ZMod n)ˣ) (x : ThreeSphere) :
    act k 0 x = x := by
  -- Reduce equality in the sphere subtype to the two coordinate formulas.
  apply Subtype.ext
  ext i
  rw [act_apply]
  by_cases hi : i = 0
  · simp only [if_pos hi, AddChar.map_zero_eq_one, Circle.coe_one, one_mul]
  · simp only [if_neg hi, mul_zero, AddChar.map_zero_eq_one, Circle.coe_one, one_mul]

/-- Helper for Definition 81.8: successive rotations add their `ZMod n` parameters. -/
private theorem act_add {n : ℕ} [NeZero n] (k : (ZMod n)ˣ) (a b : ZMod n)
    (x : ThreeSphere) : act k (a + b) x = act k a (act k b x) := by
  -- Check the action law coordinatewise, using additivity of the circle character.
  apply Subtype.ext
  ext i
  simp only [act_apply]
  by_cases hi : i = 0
  · simp only [if_pos hi, AddChar.map_add_eq_mul, Circle.coe_mul, mul_assoc]
  · simp only [if_neg hi, mul_add, AddChar.map_add_eq_mul, Circle.coe_mul, mul_assoc]

/-- The explicit additive action of `ZMod n` underlying the lens-space quotient. -/
@[reducible]
noncomputable def action {n : ℕ} [NeZero n] (k : (ZMod n)ˣ) :
    AddAction (ZMod n) ThreeSphere where
  vadd := act k
  zero_vadd := act_zero k
  add_vadd := act_add k

/-- The bundled action's `+ᵥ` operation agrees with the explicit diagonal rotation. -/
theorem action_vadd {n : ℕ} [NeZero n] (k : (ZMod n)ˣ) (j : ZMod n)
    (x : ThreeSphere) :
    (action k).vadd j x = act k j x := by
  -- The bundled action stores `act k` as its `vadd` field.
  rfl

end LensSpace

/-- Definition 81.8: the orbit quotient of the complex unit `3`-sphere by the
weighted cyclic action is the lens space `L(n, k)`. -/
abbrev LensSpace (n : ℕ) [NeZero n] (k : (ZMod n)ˣ) : Type :=
  @AddAction.orbitRel.Quotient (ZMod n) LensSpace.ThreeSphere _ (LensSpace.action k)

namespace LensSpace

/-- The canonical map from the complex unit `3`-sphere to a lens space. -/
noncomputable def quotientMap {n : ℕ} [NeZero n] (k : (ZMod n)ˣ) :
    ThreeSphere → LensSpace n k :=
  Quotient.mk''

/-- Two points have the same lens-space image exactly when they lie in one cyclic orbit. -/
theorem quotientMap_eq_iff {n : ℕ} [NeZero n] (k : (ZMod n)ˣ)
    (x y : ThreeSphere) :
    quotientMap k x = quotientMap k y ↔ ∃ j : ZMod n, act k j y = x := by
  -- Quotient equality is the orbit relation; expose its witnessing rotation.
  letI : AddAction (ZMod n) ThreeSphere := action k
  rw [quotientMap, Quotient.eq'', AddAction.orbitRel_apply, AddAction.mem_orbit_iff]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    calc
      act k j y = (action k).vadd j y := (action_vadd k j y).symm
      _ = x := hj
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    calc
      (action k).vadd j y = act k j y := action_vadd k j y
      _ = x := hj

/-- The textbook lens space associated to positive coprime natural numbers `n` and `k`. -/
abbrev ofCoprime (n k : ℕ) (hn : 0 < n) (hcoprime : Nat.Coprime k n) : Type :=
  @LensSpace n (NeZero.of_pos hn) (ZMod.unitOfCoprime k hcoprime)

/- The standard source notation for the lens space associated to positive coprime
integers `n` and `k`; the required hypotheses are inferred from the local context. -/
scoped notation "L(" n ", " k ")" =>
  ofCoprime n k (by assumption) (by assumption)

end LensSpace
