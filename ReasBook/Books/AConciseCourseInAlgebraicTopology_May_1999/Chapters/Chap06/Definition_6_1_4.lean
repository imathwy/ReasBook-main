import Mathlib.Topology.Homotopy.Basic

open scoped unitInterval

universe u v w

variable {A : Type u} {X : Type v} [TopologicalSpace A] [TopologicalSpace X]

-- Semantic recall: mathlib currently provides `HomotopicalAlgebra.Cofibration` for model
-- categories, but no topological `ContinuousMap` cofibration API based on the homotopy extension
-- property was found in the current environment.

/-- Definition 6.1.4. A map `i : A → X` is a cofibration (at target universe `w`) if every
homotopy on `A` whose time-`0` map is induced from a map `X → Y`, for `Y : Type w`, extends to
a homotopy on `X`.  Keeping the target universe independent of the carrier universes is essential:
the homotopy extension property itself does not require `Y` to live in `max u v`. -/
def IsCofibration (i : C(A, X)) : Prop :=
  ∀ {Y : Type w} [TopologicalSpace Y] (f₀ : C(X, Y)) (g : C(A, Y))
    (H : (f₀.comp i).Homotopy g),
      ∃ G : C(X, Y), ∃ F : f₀.Homotopy G, ∀ z : I × A, F (z.1, i z.2) = H z

/-- A cofibration extends every homotopy on `A` that is compatible with a chosen initial map on
`X`. -/
theorem IsCofibration.exists_homotopy_extension {i : C(A, X)}
    (hi : IsCofibration.{u, v, w} i)
    {Y : Type w} [TopologicalSpace Y] (f₀ : C(X, Y)) (g : C(A, Y))
    (H : (f₀.comp i).Homotopy g) :
    ∃ G : C(X, Y), ∃ F : f₀.Homotopy G, ∀ z : I × A, F (z.1, i z.2) = H z :=
  hi f₀ g H
