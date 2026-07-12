import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

/-- Transport a term along an equality of indices. -/
def castHom {α : Sort _} {β : α → Sort _} {a b : α} (h : a = b) : β a → β b :=
  fun x ↦ Eq.ndrec x h

namespace DifferentialGradedCategory

/-- Arithmetic identity used to align the left Leibniz term in degree `(i, j)`. -/
theorem d_comp_left_index (i j : ℤ) : i + (j + 1) = i + j + 1 := by
  omega

/-- Arithmetic identity used to align the right Leibniz term in degree `(i, j)`. -/
theorem d_comp_right_index (i j : ℤ) : (i + 1) + j = i + j + 1 := by
  omega

/-- Arithmetic identity used to align the first Leibniz term in degree `(0, 0)`. -/
theorem zero_add_zero_succ_eq : 0 + (0 + 1 : ℤ) = 0 + 1 := by omega

/-- Arithmetic identity used to align the second Leibniz term in degree `(0, 0)`. -/
theorem zero_succ_add_zero_eq : (0 + 1 : ℤ) + 0 = 0 + 1 := by omega

/-- Arithmetic identity used to align the first Leibniz term in degree `(0, -1)`. -/
theorem negOne_add_zero_succ_eq_zero : -1 + (0 + 1 : ℤ) = 0 := by omega

/-- Arithmetic identity used to align the second Leibniz term in degree `(0, -1)`. -/
theorem negOne_succ_add_zero_eq_zero : (-1 + 1 : ℤ) + 0 = 0 := by omega

/-- Arithmetic identity used to align the first Leibniz term in degree `(-1, 0)`. -/
theorem zero_add_negOne_succ_eq_zero : 0 + (-1 + 1 : ℤ) = 0 := by omega

/-- Arithmetic identity used to align the second Leibniz term in degree `(-1, 0)`. -/
theorem zero_succ_add_negOne_eq_zero : (0 + 1 : ℤ) + -1 = 0 := by omega

/-- Arithmetic identity used to align the first homotopy-composition term in degree `-1`. -/
theorem zero_add_negOne_eq : 0 + (-1 : ℤ) = -1 := by omega

/-- Arithmetic identity used to align the second homotopy-composition term in degree `-1`. -/
theorem negOne_add_zero_eq : (-1 : ℤ) + 0 = -1 := by omega

end DifferentialGradedCategory

open DifferentialGradedCategory

/-- Definition 22.26.1: a differential graded category over `R`, encoded by graded `R`-modules
of morphisms together with differentials, identities, and graded composition. The axioms include
the full homogeneous unit, associativity, and graded Leibniz laws; Chapter 22 later specializes
these to form the categories `Comp(𝒜)` of closed degree-`0` morphisms and `K(𝒜)` modulo
boundaries. -/
@[stacks 09L5]
class DifferentialGradedCategory (R : outParam (Type u)) [CommRing R] (C : Type v) where
  Hom : C → C → ℤ → Type w
  homAddCommGroup (X Y : C) (n : ℤ) : AddCommGroup (Hom X Y n)
  homModule (X Y : C) (n : ℤ) : Module R (Hom X Y n)
  d {X Y : C} (n : ℤ) : Hom X Y n → Hom X Y (n + 1)
  id (X : C) : Hom X X 0
  comp {X Y Z : C} {i j : ℤ} : Hom Y Z j → Hom X Y i → Hom X Z (i + j)
  d_sq {X Y : C} (n : ℤ) (f : Hom X Y n) : d (n + 1) (d n f) = 0
  d_id (X : C) : d 0 (id X) = 0
  id_comp_hom {X Y : C} {i : ℤ} (f : Hom X Y i) :
    castHom (add_zero i) (comp (id Y) f) = f
  comp_id_hom {X Y : C} {i : ℤ} (f : Hom X Y i) :
    castHom (zero_add i) (comp f (id X)) = f
  comp_assoc {W X Y Z : C} {i j k : ℤ} (h : Hom Y Z k) (g : Hom X Y j) (f : Hom W X i) :
    castHom (add_assoc i j k) (comp h (comp g f)) = comp (comp h g) f
  comp_add_left {X Y Z : C} {i j : ℤ} (g₁ g₂ : Hom Y Z j) (f : Hom X Y i) :
    comp (g₁ + g₂) f = comp g₁ f + comp g₂ f
  comp_add_right {X Y Z : C} {i j : ℤ} (g : Hom Y Z j) (f₁ f₂ : Hom X Y i) :
    comp g (f₁ + f₂) = comp g f₁ + comp g f₂
  comp_smul_left {X Y Z : C} {i j : ℤ} (r : R) (g : Hom Y Z j) (f : Hom X Y i) :
    comp (r • g) f = r • comp g f
  comp_smul_right {X Y Z : C} {i j : ℤ} (r : R) (g : Hom Y Z j) (f : Hom X Y i) :
    comp g (r • f) = r • comp g f
  d_add {X Y : C} (n : ℤ) (f g : Hom X Y n) : d n (f + g) = d n f + d n g
  d_smul {X Y : C} (n : ℤ) (r : R) (f : Hom X Y n) : d n (r • f) = r • d n f
  d_comp {X Y Z : C} {i j : ℤ} (g : Hom Y Z j) (f : Hom X Y i) :
    d (i + j) (comp g f) =
      castHom (d_comp_left_index i j) (comp (d j g) f) +
        (j.negOnePow : R) • castHom (d_comp_right_index i j) (comp g (d i f))

attribute [reducible, instance] DifferentialGradedCategory.homAddCommGroup
attribute [reducible, instance] DifferentialGradedCategory.homModule

namespace DifferentialGradedCategory

scoped notation:max X " ⟶[" n "] " Y =>
  DifferentialGradedCategory.Hom X Y n

@[simp] theorem castHom_add {α : Sort _} {β : α → Type _} [∀ a, Add (β a)]
    {a b : α} (h : a = b) (x y : β a) :
    castHom h (x + y) = castHom h x + castHom h y := by
  cases h
  rfl

@[simp] theorem castHom_smul {S : Type _} {α : Sort _} {β : α → Type _}
    [∀ a, SMul S (β a)] {a b : α} (h : a = b) (r : S) (x : β a) :
    castHom h (r • x) = r • castHom h x := by
  cases h
  rfl

variable {R : Type u} [CommRing R]
variable {C : Type v} [D : DifferentialGradedCategory R C]

open scoped DifferentialGradedCategory

@[simp] theorem castHom_rfl {α : Sort _} {β : α → Sort _} {a : α} (x : β a) :
    castHom rfl x = x := rfl

@[simp] theorem castHom_zero {α : Sort _} {β : α → Type _} [∀ a, Zero (β a)]
    {a b : α} (h : a = b) :
    castHom h (0 : β a) = 0 := by
  cases h
  rfl

@[simp] theorem castHom_symm_castHom {α : Sort _} {β : α → Sort _} {a b : α}
    (h : a = b) (x : β a) :
    castHom h.symm (castHom h x) = x := by
  cases h
  rfl

theorem cast_eq_castHom {α : Sort _} {β : α → Type _} {a b : α}
    (h : a = b) (x : β a) :
    cast (congrArg β h) x = castHom h x := by
  cases h
  rfl

theorem castHom_trans {α : Sort _} {β : α → Sort _} {a b c : α}
    (h₁ : a = b) (h₂ : b = c) (x : β a) :
    castHom h₂ (castHom h₁ x) = castHom (h₁.trans h₂) x := by
  cases h₁
  cases h₂
  rfl

theorem castHom_congr {α : Sort _} {β : α → Sort _} {a b : α}
    (h₁ h₂ : a = b) (x : β a) :
    castHom h₁ x = castHom h₂ x := by
  cases h₁
  cases h₂
  rfl

@[simp] theorem d_castHom {X Y : C} {i j : ℤ} (h : i = j) (f : X ⟶[i] Y) :
    D.d j (castHom h f) = castHom (by cases h; rfl) (D.d i f) := by
  cases h
  rfl

theorem comp_castHom_right {X Y Z : C} {i i' j : ℤ}
    (h : i = i') (g : Y ⟶[j] Z) (f : X ⟶[i] Y) :
    castHom (by cases h; rfl) (D.comp g f) = D.comp g (castHom h f) := by
  cases h
  rfl

theorem comp_castHom_left {X Y Z : C} {i j j' : ℤ}
    (h : j = j') (g : Y ⟶[j] Z) (f : X ⟶[i] Y) :
    castHom (by cases h; rfl) (D.comp g f) = D.comp (castHom h g) f := by
  cases h
  rfl

theorem id_comp {X Y : C} (f : X ⟶[0] Y) : D.comp (D.id Y) f = f := by
  cases add_zero (0 : ℤ)
  simpa using (D.id_comp_hom f)

theorem comp_id {X Y : C} (f : X ⟶[0] Y) : D.comp f (D.id X) = f := by
  cases zero_add (0 : ℤ)
  simpa using (D.comp_id_hom f)

theorem comp_assoc_zero {W X Y Z : C} (h : Y ⟶[0] Z) (g : X ⟶[0] Y) (f : W ⟶[0] X) :
    D.comp h (D.comp g f) = D.comp (D.comp h g) f := by
  cases add_assoc (0 : ℤ) 0 0
  simpa using (D.comp_assoc h g f)

theorem d_comp_zero_zero {X Y Z : C} (g : Y ⟶[0] Z) (f : X ⟶[0] Y) :
    D.d 0 (D.comp g f) =
      castHom zero_add_zero_succ_eq (D.comp (D.d 0 g) f) +
        castHom zero_succ_add_zero_eq (D.comp g (D.d 0 f)) := by
  have h := D.d_comp g f
  cases d_comp_left_index (0 : ℤ) 0
  cases zero_add_zero_succ_eq
  cases d_comp_right_index (0 : ℤ) 0
  cases zero_succ_add_zero_eq
  have hsign : ((0 : ℤ).negOnePow : R) = 1 := by
    simp [Int.negOnePow_zero]
  rw [hsign, one_smul] at h
  exact h

theorem d_comp_zero_negOne {X Y Z : C} (g : Y ⟶[0] Z) (f : X ⟶[-1] Y) :
    D.d (-1) (D.comp g f) =
      castHom negOne_add_zero_succ_eq_zero (D.comp (D.d 0 g) f) +
        castHom negOne_succ_add_zero_eq_zero (D.comp g (D.d (-1) f)) := by
  have h := D.d_comp g f
  cases d_comp_left_index (-1 : ℤ) 0
  cases negOne_add_zero_succ_eq_zero
  cases d_comp_right_index (-1 : ℤ) 0
  cases negOne_succ_add_zero_eq_zero
  have hsign : ((0 : ℤ).negOnePow : R) = 1 := by
    simp [Int.negOnePow_zero]
  rw [hsign, one_smul] at h
  exact h

theorem d_comp_negOne_zero {X Y Z : C} (g : Y ⟶[-1] Z) (f : X ⟶[0] Y) :
    D.d (-1) (D.comp g f) =
      castHom zero_add_negOne_succ_eq_zero (D.comp (D.d (-1) g) f) -
        castHom zero_succ_add_negOne_eq_zero (D.comp g (D.d 0 f)) := by
  have h := D.d_comp g f
  cases d_comp_left_index (0 : ℤ) (-1)
  cases zero_add_negOne_succ_eq_zero
  cases d_comp_right_index (0 : ℤ) (-1)
  cases zero_succ_add_negOne_eq_zero
  have hsign : (((-1 : ℤ).negOnePow : R)) = -1 := by
    simp [Int.negOnePow_neg, Int.negOnePow_one]
  rw [hsign, neg_one_smul] at h
  simpa [sub_eq_add_neg] using h

@[simp] theorem d_zero {X Y : C} (n : ℤ) : D.d n (0 : X ⟶[n] Y) = 0 := by
  simpa using (D.d_smul n (0 : R) (0 : X ⟶[n] Y))

theorem d_neg {X Y : C} (n : ℤ) (f : X ⟶[n] Y) : D.d n (-f) = -D.d n f := by
  simpa using (D.d_smul n (-1 : R) f)

theorem d_sub {X Y : C} (n : ℤ) (f g : X ⟶[n] Y) :
    D.d n (f - g) = D.d n f - D.d n g := by
  simp [sub_eq_add_neg, D.d_add, d_neg]

@[simp] theorem comp_zero_left {X Y Z : C} {i j : ℤ} (f : X ⟶[i] Y) :
    D.comp (0 : Y ⟶[j] Z) f = 0 := by
  simpa using (D.comp_smul_left (0 : R) (0 : Y ⟶[j] Z) f)

@[simp] theorem comp_zero_right {X Y Z : C} {i j : ℤ} (g : Y ⟶[j] Z) :
    D.comp g (0 : X ⟶[i] Y) = 0 := by
  simpa using (D.comp_smul_right (0 : R) g (0 : X ⟶[i] Y))

theorem comp_neg_left {X Y Z : C} {i j : ℤ} (g : Y ⟶[j] Z) (f : X ⟶[i] Y) :
    D.comp (-g) f = -D.comp g f := by
  simpa using (D.comp_smul_left (-1 : R) g f)

theorem comp_neg_right {X Y Z : C} {i j : ℤ} (g : Y ⟶[j] Z) (f : X ⟶[i] Y) :
    D.comp g (-f) = -D.comp g f := by
  simpa using (D.comp_smul_right (-1 : R) g f)

theorem comp_sub_left {X Y Z : C} {i j : ℤ} (g₁ g₂ : Y ⟶[j] Z) (f : X ⟶[i] Y) :
    D.comp (g₁ - g₂) f = D.comp g₁ f - D.comp g₂ f := by
  simp [sub_eq_add_neg, D.comp_add_left, comp_neg_left]

theorem comp_sub_right {X Y Z : C} {i j : ℤ} (g : Y ⟶[j] Z) (f₁ f₂ : X ⟶[i] Y) :
    D.comp g (f₁ - f₂) = D.comp g f₁ - D.comp g f₂ := by
  simp [sub_eq_add_neg, D.comp_add_right, comp_neg_right]

end DifferentialGradedCategory
