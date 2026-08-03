module

public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic.Group

public section

namespace KleinBottle

/-- The free-group word `a * b * a⁻¹ * b` defining the standard Klein-bottle presentation. -/
def relator : FreeGroup (Fin 2) :=
  FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1

/-- The group with presentation `⟨a, b | a * b * a⁻¹ * b = 1⟩`. -/
abbrev Presentation : Type :=
  PresentedGroup ({relator} : Set (FreeGroup (Fin 2)))

/-- The first generator of the standard Klein-bottle presentation. -/
def a : Presentation :=
  PresentedGroup.of 0

/-- The second generator of the standard Klein-bottle presentation. -/
def b : Presentation :=
  PresentedGroup.of 1

/-- Helper for Exercise 74.3: the defining relator makes conjugation by `a` invert `b`. -/
private lemma a_conj_b : a * b * a⁻¹ = b⁻¹ := by
  -- Remove the final factor from the defining relation.
  have hrel := PresentedGroup.one_of_mem (Set.mem_singleton relator)
  change a * b * a⁻¹ * b = 1 at hrel
  exact mul_eq_one_iff_eq_inv.mp hrel

/-- Helper for Exercise 74.3: the square of `a` commutes with `b`. -/
private lemma a_sq_commutes_b : Commute (a ^ (2 : ℤ)) b := by
  -- Applying the conjugation relation twice fixes `b`.
  have hconjInv : a * b⁻¹ * a⁻¹ = b := by
    calc
      a * b⁻¹ * a⁻¹ = (a * b * a⁻¹)⁻¹ := by group
      _ = (b⁻¹)⁻¹ := congrArg Inv.inv a_conj_b
      _ = b := inv_inv b
  have hsquareConj : a ^ (2 : ℤ) * b * (a ^ (2 : ℤ))⁻¹ = b := by
    calc
      a ^ (2 : ℤ) * b * (a ^ (2 : ℤ))⁻¹ =
          a * (a * b * a⁻¹) * a⁻¹ := by
            rw [zpow_two]
            group
      _ = a * b⁻¹ * a⁻¹ := by rw [a_conj_b]
      _ = b := hconjInv
  -- Cancel the inverse square from the conjugation identity.
  calc
    a ^ (2 : ℤ) * b =
        (a ^ (2 : ℤ) * b * (a ^ (2 : ℤ))⁻¹) * a ^ (2 : ℤ) := by group
    _ = b * a ^ (2 : ℤ) := by rw [hsquareConj]

/-- Helper for Exercise 74.3: the formula defining `torusHom` preserves the identity. -/
private lemma torusHom_map_one :
    a ^ (2 * ((1 : Multiplicative ℤ × Multiplicative ℤ).1.toAdd)) *
        b ^ ((1 : Multiplicative ℤ × Multiplicative ℤ).2.toAdd) = 1 := by
  -- Both integer coordinates of the identity are zero.
  simp

/-- Helper for Exercise 74.3: the formula defining `torusHom` preserves multiplication. -/
private lemma torusHom_map_mul
    (x y : Multiplicative ℤ × Multiplicative ℤ) :
    a ^ (2 * (x * y).1.toAdd) * b ^ (x * y).2.toAdd =
      (a ^ (2 * x.1.toAdd) * b ^ x.2.toAdd) *
        (a ^ (2 * y.1.toAdd) * b ^ y.2.toAdd) := by
  -- Powers of `a²` commute with powers of `b`, so the two coordinates multiply separately.
  have hcomm : Commute (a ^ (2 * y.1.toAdd)) (b ^ x.2.toAdd) := by
    simpa only [← zpow_mul] using a_sq_commutes_b.zpow_zpow y.1.toAdd x.2.toAdd
  rw [Prod.fst_mul, Prod.snd_mul, toAdd_mul, toAdd_mul, Int.mul_add, zpow_add, zpow_add]
  calc
    (a ^ (2 * x.1.toAdd) * a ^ (2 * y.1.toAdd)) *
        (b ^ x.2.toAdd * b ^ y.2.toAdd) =
      a ^ (2 * x.1.toAdd) *
        (a ^ (2 * y.1.toAdd) * b ^ x.2.toAdd) * b ^ y.2.toAdd := by
          simp only [mul_assoc]
    _ = a ^ (2 * x.1.toAdd) *
        (b ^ x.2.toAdd * a ^ (2 * y.1.toAdd)) * b ^ y.2.toAdd := by
          rw [hcomm.eq]
    _ = (a ^ (2 * x.1.toAdd) * b ^ x.2.toAdd) *
        (a ^ (2 * y.1.toAdd) * b ^ y.2.toAdd) := by
          simp only [mul_assoc]

/-- The homomorphism sending torus coordinates `(m, n)` to `a ^ (2 * m) * b ^ n`. -/
def torusHom : Multiplicative ℤ × Multiplicative ℤ →* Presentation where
  toFun coordinates := a ^ (2 * coordinates.1.toAdd) * b ^ coordinates.2.toAdd
  map_one' := torusHom_map_one
  map_mul' := torusHom_map_mul

/-- The standard torus homomorphism has the formula `(m, n) ↦ a ^ (2 * m) * b ^ n`. -/
theorem torusHom_apply (m n : Multiplicative ℤ) :
    torusHom (m, n) = a ^ (2 * m.toAdd) * b ^ n.toAdd := by
  -- This is the defining formula of `torusHom`.
  rfl

end KleinBottle
