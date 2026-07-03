import Mathlib
import StacksProject_2024.Chap13.Definition_13_41_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ZeroObject

universe v u

namespace CategoryTheory

section

/-
Domain-style sampling:
- primary domain: Hom-vanishing conditions between shifted objects in a category with shift;
- inspected canonical owner declarations:
  `ShiftedHom`,
  `ComposableArrows`,
  `PostnikovSystem`;
- best owner abstraction: the vanishing hypothesis itself is a source-facing familywise `Subsingleton`
  condition on the relevant `ShiftedHom` types, while the finite-row bookkeeping should be owned by
  the source-facing finite-row owners `ComposableArrows` and `PostnikovSystem`, both derived from a
  single low-level bridge from `Fin (n + 1)`-indexed families to `ℤ`-indexed families;
- layer triage:
  `source-facing`: the familywise condition indexed by `i > j + 1`,
  `core/canonical`: `Subsingleton (ShiftedHom (X i) (X' j) (j + 1 - i))`,
  `bridge/view`: the owner-level `ComposableArrows.intFamily` and `PostnikovSystem.intFamily`
    reformulations;
- primitive data: only the two ℤ-indexed object families `X`, `X'` and the index inequality;
- derived API: the owner-level finite-row views `ComposableArrows.intFamily` and
  `PostnikovSystem.intFamily`, both built from the same internal `Fin`-to-`ℤ` bridge.
-/

variable {D : Type u} [Category.{v} D] [HasShift D ℤ]
variable (X X' : ℤ → D)

/-- 13.41.4.1: the vanishing condition `\mathrm{Hom}(X_i[i - j - 1], X'_j) = 0` for `i > j + 1`,
formalized via `ShiftedHom (X i) (X' j) (j + 1 - i)`, since
`ShiftedHom A B m = (A ⟶ B⟦m⟧) ≃ (A⟦-m⟧ ⟶ B)`. -/
def shifted_hom_vanishes_above_successor : Prop :=
  ∀ ⦃i j : ℤ⦄, i > j + 1 → Subsingleton (ShiftedHom (X i) (X' j) (j + 1 - i))

end

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D]
variable {n : ℕ}

private noncomputable abbrev intFamilyOfFinAux (X : Fin (n + 1) → D) : ℤ → D := fun k ↦
  if 0 ≤ k ∧ k ≤ n then
    X ⟨n - k.toNat, lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self _)⟩
  else
    0

@[simp] private theorem intFamilyOfFinAux_reverse (X : Fin (n + 1) → D) (a : Fin (n + 1)) :
    intFamilyOfFinAux X (((n - a.1 : ℕ) : ℤ)) = X a := by
  have hk : 0 ≤ ((n - a.1 : ℕ) : ℤ) ∧ (((n - a.1 : ℕ) : ℤ) ≤ n) := by
    constructor
    · exact_mod_cast Nat.zero_le (n - a.1)
    · exact_mod_cast Nat.sub_le n a.1
  dsimp [intFamilyOfFinAux]
  rw [if_pos hk]
  have hidx :
      (⟨n - (n - a.1), lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self _)⟩ :
        Fin (n + 1)) = a := by
    apply Fin.ext
    exact Nat.sub_sub_self (Nat.le_of_lt_succ a.2)
  simpa using congrArg X hidx

end

namespace ComposableArrows

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D]
variable {n : ℕ}

/-- The canonical `ℤ`-indexed view of a finite row `X : ComposableArrows D n`, obtained by
reversing the textbook order and extending by the zero object outside `[0, n]`. -/
noncomputable abbrev intFamily (X : ComposableArrows D n) : ℤ → D :=
  intFamilyOfFinAux X.obj

@[simp] theorem intFamily_reverse (X : ComposableArrows D n) (a : Fin (n + 1)) :
    X.intFamily (((n - a.1 : ℕ) : ℤ)) = X.obj a :=
  intFamilyOfFinAux_reverse X.obj a

end

end ComposableArrows

namespace PostnikovSystem

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]
variable {n : ℕ} {X : ComposableArrows D n}

/-- The canonical `ℤ`-indexed view of the auxiliary objects of a Postnikov system. -/
noncomputable abbrev intFamily (P : PostnikovSystem X) : ℤ → D :=
  intFamilyOfFinAux P.Y

@[simp] theorem intFamily_reverse (P : PostnikovSystem X) (a : Fin (n + 1)) :
    P.intFamily (((n - a.1 : ℕ) : ℤ)) = P a :=
  intFamilyOfFinAux_reverse P.Y a

/-- The owner vanishing predicate on `X.intFamily` and `P.intFamily` specializes to the textbook
finite-row statement on the objects `X_a` and the auxiliary objects `Y_b` of `P`. -/
theorem subsingleton_hom_of_shifted_hom_vanishes_above_successor
    {X' : ComposableArrows D n} (P : PostnikovSystem X')
    {X : ComposableArrows D n}
    (h : shifted_hom_vanishes_above_successor X.intFamily P.intFamily)
    {a b : Fin (n + 1)} (hab : a.1 + 1 < b.1) :
    Subsingleton (ShiftedHom (X.obj a) (P b) ((a.1 : ℤ) + 1 - b.1)) := by
  have hshift :
      (((n - b.1 : ℕ) : ℤ) + 1 - ((n - a.1 : ℕ) : ℤ)) = ((a.1 : ℤ) + 1 - b.1) := by
    omega
  have hsub :
      Subsingleton
        (ShiftedHom
          (X.intFamily (((n - a.1 : ℕ) : ℤ)))
          (P.intFamily (((n - b.1 : ℕ) : ℤ)))
          ((((n - b.1 : ℕ) : ℤ) + 1 - ((n - a.1 : ℕ) : ℤ)))) :=
    h (show (((n - a.1 : ℕ) : ℤ) > ((n - b.1 : ℕ) : ℤ) + 1) by omega)
  simpa [ShiftedHom, hshift, X.intFamily_reverse a, P.intFamily_reverse b] using hsub

end

end PostnikovSystem

end CategoryTheory
