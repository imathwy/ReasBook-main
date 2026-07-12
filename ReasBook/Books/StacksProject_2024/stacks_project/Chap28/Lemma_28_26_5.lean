import Mathlib
import StacksProject_2024.Chap28.Definition_28_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Semantic recall: `lean_leansearch` surfaced module tensor-product invertibility and canonical
scheme-module owners, while the local Chapter 28 API represents ampleness by
`Scheme.Modules.IsAmple` and represents source-facing opens `X_t` by
`Invertible.nonvanishingOpen`. Since the local `Invertible` API exposes chosen tensor powers and
their canonical nonvanishing opens, the invertible interface on `L ⊗ M` is supplied explicitly as
in the nearby Chapter 28 statements. -/

variable {X : Scheme.{u}} [MonoidalCategory X.Modules]

/-- Lemma 28.26.5: if `L` and `M` are invertible `\mathcal O_X`-modules, `L` is ample, and
the nonvanishing opens `X_t` for positive tensor powers of `M` cover `X`, then `L ⊗ M` is ample.
The parameter `hLM` supplies the explicit invertible-module interface on the tensor product
required by the local Chapter 28 owner `IsAmple`. -/
@[stacks 0890]
theorem isAmple_tensor_of_isAmple_of_nonvanishing_cover
    (L M : X.Modules) [hL : Invertible L] [hM : Invertible M] [IsAmple L]
    (hcover : ∀ x : X, ∃ m : ℕ, 0 < m ∧ ∃ t : Γ(hM m, ⊤),
      x ∈ (hM.nonvanishingOpen t : Set X))
    (hLM : Invertible (L ⊗ M)) :
    IsAmple (L ⊗ M) := sorry

end AlgebraicGeometry.Scheme.Modules
