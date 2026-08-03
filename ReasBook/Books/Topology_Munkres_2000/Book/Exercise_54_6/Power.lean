module

public import Topology_Munkres_2000.Book.Exercise_52_7.LoopGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.ContinuousMap.Algebra

public section

noncomputable section

open scoped LoopPointwise

namespace CircleMap

/-- The continuous self-map of the complex unit circle given by integer exponentiation. -/
def zpower (k : ℤ) : C(Circle, Circle) :=
  ContinuousMap.id Circle ^ k

/-- Evaluation of the integer-power self-map of the complex unit circle. -/
theorem zpower_apply (k : ℤ) (z : Circle) : zpower k z = z ^ k := by
  rfl

/-- The integer-power self-map fixes the standard basepoint `1` of the unit circle. -/
theorem zpower_one (k : ℤ) : zpower k 1 = 1 := by
  exact one_zpow k

/-- Helper for Exercise 54.6: the based loop obtained by applying integer
exponentiation pointwise to a circle loop. -/
def mappedLoop (k : ℤ) (p : Path (1 : Circle) 1) : Path (1 : Circle) 1 :=
  (p.map (zpower k).continuous).cast (zpower_one k).symm (zpower_one k).symm

/-- Helper for Exercise 54.6: the mapped loop evaluates by integer exponentiation. -/
lemma mappedLoop_apply (k : ℤ) (p : Path (1 : Circle) 1) (t : unitInterval) :
    mappedLoop k p t = (p t) ^ k := by
  rfl

/-- Helper for Exercise 54.6: exponent zero sends every loop to the constant loop. -/
lemma mappedLoop_zero (p : Path (1 : Circle) 1) : mappedLoop 0 p = Path.refl 1 := by
  ext t
  exact congrArg Subtype.val (zpow_zero (p t))

/-- Helper for Exercise 54.6: increasing the exponent corresponds to pointwise
multiplication by the original loop. -/
lemma mappedLoop_add_one (k : ℤ) (p : Path (1 : Circle) 1) :
    mappedLoop (k + 1) p = mappedLoop k p ⊗ p := by
  ext t
  rw [mappedLoop_apply, Path.pointwiseMul_apply, mappedLoop_apply]
  exact congrArg Subtype.val (zpow_add_one (p t) k)

/-- Helper for Exercise 54.6: decreasing the exponent corresponds to pointwise
multiplication by the inverse-power loop. -/
lemma mappedLoop_sub_one (k : ℤ) (p : Path (1 : Circle) 1) :
    mappedLoop (k - 1) p = mappedLoop k p ⊗ mappedLoop (-1) p := by
  ext t
  rw [mappedLoop_apply, Path.pointwiseMul_apply, mappedLoop_apply, mappedLoop_apply]
  simp only [zpow_neg_one]
  exact congrArg Subtype.val (zpow_sub_one (p t) k)

/-- Helper for Exercise 54.6: the class of the inverse-power loop is the inverse
of the original loop class. -/
lemma quotientMk_mappedLoop_neg_one (p : Path (1 : Circle) 1) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (mappedLoop (-1) p)) =
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) :
        FundamentalGroup Circle 1)⁻¹ := by
  -- Both sides are left inverses of the class represented by `p`.
  apply mul_right_cancel (b :=
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) :
      FundamentalGroup Circle 1))
  calc
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (mappedLoop (-1) p)) *
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) =
      FundamentalGroup.pointwiseMul
        (Path.Homotopic.Quotient.mk (mappedLoop (-1) p))
        (Path.Homotopic.Quotient.mk p) :=
      (FundamentalGroup.pointwiseMul_eq_mul _ _).symm
    _ = FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (mappedLoop (-1) p ⊗ p)) := by
      exact congrArg FundamentalGroup.fromPath
        (FundamentalGroup.pointwiseMul_mk _ _)
    _ = FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (mappedLoop 0 p)) := by
      rw [← mappedLoop_add_one (-1) p]
      norm_num
    _ = 1 := by
      rw [mappedLoop_zero]
      exact FundamentalGroup.one_def
    _ = (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) :
          FundamentalGroup Circle 1)⁻¹ *
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) :=
      (inv_mul_cancel _).symm

/-- Helper for Exercise 54.6: the homotopy class of the mapped loop is the
corresponding integer power in the fundamental group. -/
lemma quotientMk_mappedLoop (k : ℤ) (p : Path (1 : Circle) 1) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (mappedLoop k p)) =
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) ^ k := by
  -- Integer induction translates pointwise multiplication into the group law.
  induction k using Int.induction_on with
  | zero =>
      rw [mappedLoop_zero, zpow_zero]
      exact FundamentalGroup.one_def
  | succ k ih =>
      rw [mappedLoop_add_one, zpow_add_one]
      calc
        FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk (mappedLoop (k : ℤ) p ⊗ p)) =
          FundamentalGroup.pointwiseMul
            (Path.Homotopic.Quotient.mk (mappedLoop (k : ℤ) p))
            (Path.Homotopic.Quotient.mk p) :=
          (FundamentalGroup.pointwiseMul_mk _ _).symm
        _ = FundamentalGroup.fromPath
              (Path.Homotopic.Quotient.mk (mappedLoop (k : ℤ) p)) *
            FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) :=
          FundamentalGroup.pointwiseMul_eq_mul _ _
        _ = _ := congrArg₂ (· * ·) ih rfl
  | pred k ih =>
      rw [mappedLoop_sub_one, zpow_sub_one]
      calc
        FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk
              (mappedLoop (-(k : ℤ)) p ⊗ mappedLoop (-1) p)) =
          FundamentalGroup.pointwiseMul
            (Path.Homotopic.Quotient.mk (mappedLoop (-(k : ℤ)) p))
            (Path.Homotopic.Quotient.mk (mappedLoop (-1) p)) :=
          (FundamentalGroup.pointwiseMul_mk _ _).symm
        _ = FundamentalGroup.fromPath
              (Path.Homotopic.Quotient.mk (mappedLoop (-(k : ℤ)) p)) *
            FundamentalGroup.fromPath
              (Path.Homotopic.Quotient.mk (mappedLoop (-1) p)) :=
          FundamentalGroup.pointwiseMul_eq_mul _ _
        _ = _ := congrArg₂ (· * ·) ih (quotientMk_mappedLoop_neg_one p)

/-- Helper for Exercise 54.6: mapping a representative loop and casting endpoints
produces the class of the corresponding mapped loop. -/
lemma quotientMap_zpower_cast (k : ℤ) (p : Path (1 : Circle) 1) :
    (Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk p) (zpower k)).cast
        (zpower_one k).symm (zpower_one k).symm =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (mappedLoop k p)) := by
  rw [← Path.Homotopic.Quotient.mk_map]
  rw [← Path.Homotopic.Quotient.mk_cast]
  rfl

/-- Helper for Exercise 54.6: the induced map of integer exponentiation sends
each fundamental-group class to its integer power. -/
lemma mapOfEq_apply_zpower (k : ℤ) (a : FundamentalGroup Circle 1) :
    FundamentalGroup.mapOfEq (zpower k) (zpower_one k) a = a ^ k := by
  -- Reduce to a representative loop and use the mapped-loop computation.
  rw [FundamentalGroup.mapOfEq_apply]
  induction a using Quotient.inductionOn with
  | _ p =>
      exact (quotientMap_zpower_cast k p).trans (quotientMk_mappedLoop k p)

/-- In integer coordinates, the map on `π₁(S¹, 1)` induced by `z ↦ z ^ k` is the
integer-power endomorphism. -/
theorem induced_zpower (k : ℤ) (e : FundamentalGroup Circle 1 ≃* Multiplicative ℤ) :
    e.toMonoidHom.comp (FundamentalGroup.mapOfEq (zpower k) (zpower_one k)) =
      (zpowGroupHom k).comp e.toMonoidHom := by
  -- Transport the power formula through arbitrary integer coordinates.
  ext a
  simp only [MonoidHom.coe_comp, Function.comp_apply, mapOfEq_apply_zpower,
    map_zpow, zpowGroupHom_apply]


end CircleMap
