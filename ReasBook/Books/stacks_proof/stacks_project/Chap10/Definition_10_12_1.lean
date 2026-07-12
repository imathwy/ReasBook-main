import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w z

variable {R : Type u} {M : Type v} {N : Type w} {P : Type z}
  [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

/- Definition 10.12.1: mathlib records bilinearity of an unbundled function by
`IsBilinearMap R f`, and the preferred bundled bilinear maps are linear maps
`M →ₗ[R] N →ₗ[R] P`, produced by `IsBilinearMap.toLinearMap`. -/
recall IsBilinearMap
recall IsBilinearMap.toLinearMap

/-- A two-variable function is bilinear exactly when each partial map is `R`-linear. -/
theorem isBilinearMap_iff_isLinearMap_left_right {f : M → N → P} :
    IsBilinearMap R f ↔
      (∀ x, IsLinearMap R (f x)) ∧ ∀ y, IsLinearMap R (fun x ↦ f x y) :=
by
  constructor
  · intro hf
    exact ⟨fun x ↦ (hf.toLinearMap x).isLinear, fun y ↦ (hf.toLinearMap.flip y).isLinear⟩
  · rintro ⟨hleft, hright⟩
    exact
      { add_left := fun x₁ x₂ y ↦ (hright y).map_add x₁ x₂
        smul_left := fun c x y ↦ (hright y).map_smul c x
        add_right := fun x y₁ y₂ ↦ (hleft x).map_add y₁ y₂
        smul_right := fun c x y ↦ (hleft x).map_smul c y }

/-- A function on the Cartesian product of two `R`-modules is bilinear exactly when each partial
map is `R`-linear. -/
theorem isBilinearMap_prod_iff_isLinearMap_left_right {f : M × N → P} :
    IsBilinearMap R (Function.curry f) ↔
      (∀ x, IsLinearMap R (fun y ↦ f (x, y))) ∧ ∀ y, IsLinearMap R (fun x ↦ f (x, y)) :=
by
  simpa using
    (show IsBilinearMap R (Function.curry f) ↔
        (∀ x, IsLinearMap R ((Function.curry f) x)) ∧
          ∀ y, IsLinearMap R (fun x ↦ (Function.curry f) x y) from
      isBilinearMap_iff_isLinearMap_left_right)
