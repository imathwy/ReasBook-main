import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import stacks_project.Chap13.Definition_13_6_1

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

open CategoryTheory

namespace CategoryTheory

open Limits ObjectProperty Pretriangulated
open scoped ZeroObject

namespace Functor

/-
Domain-style sampling for Lemma 13.6.4:
- primary domain: full triangulated subcategories cut out by eventual vanishing of the shifted
  values of a homological functor;
- sampled owner declarations:
  `ObjectProperty.FullSubcategory`,
  `ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.IsTriangulated`,
  `Functor.homologicalKernel`;
- best owner abstraction: the source-facing owners are the three Stacks full subcategories
  `D_H^+`, `D_H^-`, and `D_H^b`, each presented as a full subcategory cut out by a canonical
  `ObjectProperty`;
- primitive data: the one-sided eventual-vanishing predicates on the shifted values
  `H.obj (X⟦n⟧)`;
- derived API: the two-sided bounded owner as the intersection of the one-sided owners, together
  with retract stability, triangulatedity, and the induced triangulated structures on the full
  subcategories;
- source/core/bridge triage:
  `source-facing`: the full subcategories
    `H.shiftVanishingPlus.FullSubcategory`,
    `H.shiftVanishingMinus.FullSubcategory`, and
    `H.shiftVanishingBounded.FullSubcategory`;
  `core/canonical`: the owner predicates `H.shiftVanishingPlus`, `H.shiftVanishingMinus`,
    `H.shiftVanishingBounded`;
  `bridge/view`: the `_iff` lemmas translating those owners into the textbook eventual-vanishing
    conditions.

The refinement therefore keeps the object-property layer as the canonical core, and the public
theorem surface uses the corresponding full subcategories directly.
-/

private inductive ShiftVanishingDirection where
  | plus
  | minus

section Basic

variable {D : Type u₁} [Category.{v₁} D] [HasShift D ℤ]
variable {A : Type u₂} [Category.{v₂} A] [HasZeroMorphisms A]

private def oneSidedShiftVanishing (H : D ⥤ A) (direction : ShiftVanishingDirection) :
    ObjectProperty D :=
  fun X ↦
    match direction with
    | .plus =>
        ∃ N : ℤ, ∀ n : ℤ, n ≤ N → IsZero (H.obj (X⟦n⟧))
    | .minus =>
        ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (H.obj (X⟦n⟧))

/-- The source-facing object property defining the Stacks subcategory `D_H^+`: the shifted values
`H(X[n])` vanish for all sufficiently negative shifts `n`. -/
def shiftVanishingPlus (H : D ⥤ A) : ObjectProperty D :=
  oneSidedShiftVanishing H .plus

/-- The source-facing object property defining the Stacks subcategory `D_H^-`: the shifted values
`H(X[n])` vanish for all sufficiently positive shifts `n`. -/
def shiftVanishingMinus (H : D ⥤ A) : ObjectProperty D :=
  oneSidedShiftVanishing H .minus

/-- The source-facing object property defining the Stacks subcategory `D_H^b`: the shifted values
`H(X[n])` vanish for all shifts `n` of sufficiently large absolute value. -/
def shiftVanishingBounded (H : D ⥤ A) : ObjectProperty D :=
  H.shiftVanishingPlus ⊓ H.shiftVanishingMinus

scoped[ShiftVanishingSubcategory] notation3:max "D⁺_{" H "}" =>
  (Functor.shiftVanishingPlus H).FullSubcategory
scoped[ShiftVanishingSubcategory] notation3:max "D⁻_{" H "}" =>
  (Functor.shiftVanishingMinus H).FullSubcategory
scoped[ShiftVanishingSubcategory] notation3:max "Dᵇ_{" H "}" =>
  (Functor.shiftVanishingBounded H).FullSubcategory

/-- The source-facing object property of objects `X` whose shifted `H`-values vanish outside the
interval `[a, b]`. -/
def shiftVanishingIn (H : D ⥤ A) [H.ShiftSequence ℤ] (a b : ℤ) : ObjectProperty D :=
  fun X ↦ ∀ n : ℤ, n ∉ Set.Icc a b → IsZero ((H.shift n).obj X)

omit [HasZeroMorphisms A] in
/-- Unfolding `shiftVanishingPlus` recovers the textbook definition of the full subcategory
`D_H^+`. -/
theorem mem_shiftVanishingPlus_iff (H : D ⥤ A) (X : D) :
    H.shiftVanishingPlus X ↔
      ∃ N : ℤ, ∀ n : ℤ, n ≤ N → IsZero (H.obj (X⟦n⟧)) :=
  Iff.rfl

omit [HasZeroMorphisms A] in
/-- Unfolding `shiftVanishingMinus` recovers the textbook definition of the full subcategory
`D_H^-`. -/
theorem mem_shiftVanishingMinus_iff (H : D ⥤ A) (X : D) :
    H.shiftVanishingMinus X ↔
      ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (H.obj (X⟦n⟧)) :=
  Iff.rfl

omit [HasZeroMorphisms A] in
/-- Unfolding `shiftVanishingBounded` recovers the textbook definition of the full subcategory
`D_H^b`. -/
theorem mem_shiftVanishingBounded_iff (H : D ⥤ A) (X : D) :
    H.shiftVanishingBounded X ↔
      ∃ N : ℕ, ∀ n : ℤ, N ≤ Int.natAbs n → IsZero (H.obj (X⟦n⟧)) := by
  constructor
  · rintro ⟨⟨Nplus, hplus⟩, ⟨Nminus, hminus⟩⟩
    refine ⟨max Nplus.natAbs Nminus.natAbs, fun n hn ↦ ?_⟩
    by_cases hnn : n < 0
    · apply hplus n
      have hnatAbs : Nplus.natAbs ≤ Int.natAbs n := le_trans (le_max_left _ _) hn
      omega
    · apply hminus n
      have hnatAbs : Nminus.natAbs ≤ Int.natAbs n := le_trans (le_max_right _ _) hn
      omega
  · rintro ⟨N, hN⟩
    refine ⟨⟨-(N : ℤ), ?_⟩, ⟨(N : ℤ), ?_⟩⟩
    · intro n hn
      exact hN n <| by
        have hn0 : n ≤ 0 := by omega
        have hnatAbs : (N : ℤ) ≤ (n.natAbs : ℤ) := by
          rw [Int.ofNat_natAbs_of_nonpos hn0]
          omega
        exact_mod_cast hnatAbs
    · intro n hn
      exact hN n <| by
        have hn0 : 0 ≤ n := by omega
        have hnatAbs : (N : ℤ) ≤ (n.natAbs : ℤ) := by
          simpa [Int.natAbs_of_nonneg hn0] using hn
        exact_mod_cast hnatAbs

omit [HasZeroMorphisms A] in
/-- Unfolding `shiftVanishingIn` recovers the exact interval-vanishing condition on shifted
values of `H`. -/
theorem mem_shiftVanishingIn_iff (H : D ⥤ A) [H.ShiftSequence ℤ] (a b : ℤ) (X : D) :
    H.shiftVanishingIn a b X ↔
      ∀ n : ℤ, n ∉ Set.Icc a b → IsZero ((H.shift n).obj X) :=
  Iff.rfl

private lemma isZero_obj_shift_of_retract (H : D ⥤ A) {X Y : D} (r : Retract X Y) (n : ℤ)
    (hY : IsZero (H.obj (Y⟦n⟧))) : IsZero (H.obj (X⟦n⟧)) := by
  letI : IsSplitMono ((shiftFunctor D n ⋙ H).map r.i) :=
    ⟨⟨(r.map (shiftFunctor D n ⋙ H)).splitMono⟩⟩
  exact (IsZero.iff_isSplitMono_eq_zero ((shiftFunctor D n ⋙ H).map r.i)).2
    (hY.eq_of_tgt _ _)

omit [HasZeroMorphisms A] in
private lemma isZero_obj_shift_of_isZero_obj_add_shift (H : D ⥤ A) (X : D) (a n : ℤ)
    (h : IsZero (H.obj (X⟦a + n⟧))) : IsZero (H.obj ((X⟦a⟧)⟦n⟧)) :=
  h.of_iso (H.mapIso ((shiftFunctorAdd D a n).app X).symm)

private theorem oneSidedShiftVanishing_isStableUnderRetracts
    (H : D ⥤ A) (direction : ShiftVanishingDirection) :
    (oneSidedShiftVanishing H direction).IsStableUnderRetracts where
  of_retract r hY := by
    cases direction with
    | plus =>
        rcases hY with ⟨N, hN⟩
        exact ⟨N, fun n hn ↦ isZero_obj_shift_of_retract H r n (hN n hn)⟩
    | minus =>
        rcases hY with ⟨N, hN⟩
        exact ⟨N, fun n hn ↦ isZero_obj_shift_of_retract H r n (hN n hn)⟩

/-- Eventual negative-shift vanishing is stable under retracts. -/
instance shiftVanishingPlus_isStableUnderRetracts (H : D ⥤ A) :
    H.shiftVanishingPlus.IsStableUnderRetracts := by
  simpa [shiftVanishingPlus, oneSidedShiftVanishing] using
    oneSidedShiftVanishing_isStableUnderRetracts H .plus

/-- Eventual positive-shift vanishing is stable under retracts. -/
instance shiftVanishingMinus_isStableUnderRetracts (H : D ⥤ A) :
    H.shiftVanishingMinus.IsStableUnderRetracts := by
  simpa [shiftVanishingMinus, oneSidedShiftVanishing] using
    oneSidedShiftVanishing_isStableUnderRetracts H .minus

/-- Eventual two-sided shift vanishing is stable under retracts. -/
instance shiftVanishingBounded_isStableUnderRetracts (H : D ⥤ A) :
    H.shiftVanishingBounded.IsStableUnderRetracts := by
  simpa [shiftVanishingBounded] using
    (inferInstance :
      (H.shiftVanishingPlus ⊓ H.shiftVanishingMinus).IsStableUnderRetracts)

end Basic

section Triangulated

variable {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable {A : Type u₂} [Category.{v₂} A] [Abelian A]

private lemma isZero_obj₂_of_distinguished (H : D ⥤ A) [H.IsHomological] {T : Triangle D}
    (hT : T ∈ distTriang D) (n : ℤ) (h₁ : IsZero (H.obj (T.obj₁⟦n⟧)))
    (h₃ : IsZero (H.obj (T.obj₃⟦n⟧))) : IsZero (H.obj (T.obj₂⟦n⟧)) :=
  (H.map_distinguished_exact _ (Triangle.shift_distinguished T hT n)).isZero_of_both_zeros
    (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

private theorem oneSidedShiftVanishing_isTriangulated
    (H : D ⥤ A) [H.IsHomological] (direction : ShiftVanishingDirection) :
    (oneSidedShiftVanishing H direction).IsTriangulated := by
  letI : (oneSidedShiftVanishing H direction).IsStableUnderRetracts :=
    oneSidedShiftVanishing_isStableUnderRetracts H direction
  refine
    { exists_zero := ?_
      toIsStableUnderShift := ?_
      toIsTriangulatedClosed₂ := ?_ }
  · refine ⟨0, isZero_zero D, ?_⟩
    cases direction with
    | plus =>
        exact ⟨0, fun n _ ↦ (shiftFunctor D n ⋙ H).map_isZero (isZero_zero D)⟩
    | minus =>
        exact ⟨0, fun n _ ↦ (shiftFunctor D n ⋙ H).map_isZero (isZero_zero D)⟩
  · exact ⟨fun a ↦ ⟨fun X hX ↦ by
      cases direction with
      | plus =>
          rcases hX with ⟨N, hN⟩
          refine ⟨N - a, fun n hn ↦ ?_⟩
          exact isZero_obj_shift_of_isZero_obj_add_shift H X a n (hN (a + n) (by omega))
      | minus =>
          rcases hX with ⟨N, hN⟩
          refine ⟨N - a, fun n hn ↦ ?_⟩
          exact isZero_obj_shift_of_isZero_obj_add_shift H X a n (hN (a + n) (by omega))⟩⟩
  · exact .mk' <| by
      intro T hT h₁ h₃
      cases direction with
      | plus =>
          rcases h₁ with ⟨N₁, h₁⟩
          rcases h₃ with ⟨N₃, h₃⟩
          refine ⟨min N₁ N₃, fun n hn ↦ ?_⟩
          exact isZero_obj₂_of_distinguished H hT n
            (h₁ n (le_trans hn (min_le_left _ _)))
            (h₃ n (le_trans hn (min_le_right _ _)))
      | minus =>
          rcases h₁ with ⟨N₁, h₁⟩
          rcases h₃ with ⟨N₃, h₃⟩
          refine ⟨max N₁ N₃, fun n hn ↦ ?_⟩
          exact isZero_obj₂_of_distinguished H hT n
            (h₁ n (le_trans (le_max_left _ _) hn))
            (h₃ n (le_trans (le_max_right _ _) hn))

/-- The object property defining `D_H^+` is triangulated. -/
instance shiftVanishingPlus_isTriangulated (H : D ⥤ A) [H.IsHomological] :
    H.shiftVanishingPlus.IsTriangulated := by
  simpa [shiftVanishingPlus, oneSidedShiftVanishing] using
    oneSidedShiftVanishing_isTriangulated H .plus

/-- The object property defining `D_H^-` is triangulated. -/
instance shiftVanishingMinus_isTriangulated (H : D ⥤ A) [H.IsHomological] :
    H.shiftVanishingMinus.IsTriangulated := by
  simpa [shiftVanishingMinus, oneSidedShiftVanishing] using
    oneSidedShiftVanishing_isTriangulated H .minus

/-- The object property defining `D_H^b` is triangulated. -/
instance shiftVanishingBounded_isTriangulated (H : D ⥤ A) [H.IsHomological] :
    H.shiftVanishingBounded.IsTriangulated := by
  simpa [shiftVanishingBounded] using
    (inferInstance : (H.shiftVanishingPlus ⊓ H.shiftVanishingMinus).IsTriangulated)

section

variable (H : D ⥤ A) [H.IsHomological] [CategoryTheory.IsTriangulated D]

open scoped ShiftVanishingSubcategory

/- Lemma 13.6.4, source-facing `D_H^+` form: the full subcategory `D⁺_{H}` is triangulated. -/
#check (inferInstance : CategoryTheory.IsTriangulated D⁺_{H})

/- Lemma 13.6.4, source-facing `D_H^-` form: the full subcategory `D⁻_{H}` is triangulated. -/
#check (inferInstance : CategoryTheory.IsTriangulated D⁻_{H})

/- Lemma 13.6.4, source-facing `D_H^b` form: the full subcategory `Dᵇ_{H}` is triangulated. -/
#check (inferInstance : CategoryTheory.IsTriangulated Dᵇ_{H})

end

end Triangulated

end Functor

end CategoryTheory
