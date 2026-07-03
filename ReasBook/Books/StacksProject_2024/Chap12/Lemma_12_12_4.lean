import StacksProject_2024.Chap12.Definition_12_12_1

universe vA vB uA uB

/-
Domain-style sampling:
- primary domain: cohomological `δ`-functors on abelian categories, with weak effaceability as the
  degreewise hypothesis used to prove universality.
- declarations inspected in the nearby owner API and supporting mathlib object-property API:
  `CohomologicalDeltaFunctor`,
  `CohomologicalDeltaFunctor.IsUniversal`,
  `CohomologicalDeltaFunctor.Hom`,
  `CohomologicalDeltaFunctor.universal_delta_functor_unique_up_to_unique_iso`.
- best owner abstraction in this file: `CohomologicalDeltaFunctor.IsUniversal` for the conclusion;
  the weak-effaceability assumption is source-facing data and should stay spelled out directly.
- `source-facing`: the positive-degree effaceability criterion
  `∀ n > 0, ∀ X, ∃ Y, ∃ u : X ⟶ Y, Mono u ∧ Fⁿ(u) = 0`.
- `core/canonical`: `CohomologicalDeltaFunctor.IsUniversal`.
- `bridge/view`: none needed in the public API of this lemma; the additive-functor-to-functor
  forgetful view stays internal to the theorem statement.
- primitive data vs derived API: the primitive datum is the source-level existence, for each
  positive degree and each object, of a monomorphism annihilated by that degree functor; the
  universality conclusion is the derived canonical property.
-/

namespace CategoryTheory

namespace CohomologicalDeltaFunctor

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]

/-- Lemma 12.12.4: if every positive degree of a cohomological `δ`-functor is weakly
effaceable, then the `δ`-functor is universal. -/
-- Proof sketch: extend a degree-zero morphism of `δ`-functors inductively on the degree. For the
-- inductive step, choose a monomorphism `u : X ⟶ Y` killing `F^(n+1)(u)`, use the long exact
-- sequence for `0 ⟶ X ⟶ Y ⟶ Y/X ⟶ 0` to identify `F^(n+1)(X)` with a cokernel built from degree
-- `n`, and define the next component by the universal property of that cokernel; uniqueness comes
-- from the same construction.
theorem isUniversal_of_higherDegreesWeaklyEffaceable
    (F : CohomologicalDeltaFunctor A B)
    (hF : ∀ n : ℕ, n > 0 → ∀ X : A, ∃ (Y : A) (u : X ⟶ Y), Mono u ∧ (F n).obj.map u = 0) :
    F.IsUniversal := sorry

end CohomologicalDeltaFunctor

end CategoryTheory
