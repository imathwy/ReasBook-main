module

public import Mathlib.Data.Set.Restrict

public section

/-- Pointwise restriction of a function `f` to a subset `A₀` of its domain. -/
scoped[FunctionRestriction] notation:50 f:50 " ∣ " A₀:51 => Set.restrict A₀ f

open scoped FunctionRestriction

/- Definition 2.6: For `f : A → B` and `A₀ : Set A`, the restriction of `f`
to `A₀` is the function `A₀ → B` sending `a` to `f a`. In mathlib this is
canonically `Set.restrict`, written here as `f ∣ A₀`. -/
#check Set.restrict

-- The textbook notation has the function before the subset.
#check fun {A B : Type*} (f : A → B) (A₀ : Set A) ↦ f ∣ A₀

-- Evaluation of a restricted function agrees with the original function.
#check Set.restrict_apply

-- Restriction is composition with the inclusion of the subset subtype.
#check Set.restrict_eq
