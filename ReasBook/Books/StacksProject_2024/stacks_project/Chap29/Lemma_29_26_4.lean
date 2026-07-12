import Mathlib
import StacksProject_2024.Chap17.Definition_17_14_1
import StacksProject_2024.Chap17.Definition_17_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the affine support-side owners
-- `Module.isClosed_support` and `Module.stableUnderSpecialization_support`; local Chapter 17/29
-- precedent fixes the scheme-module owners `moduleSupport`, `IsFlat`, and
-- `IsFiniteLocallyFree`, so this item is recorded directly as the scheme-level equivalence.

/-- Lemma 29.26.4: for a scheme `X`, every finite flat quasi-coherent `\mathcal O_X`-module is
finite locally free if and only if every closed subset `Z ⊆ X` that is closed under
generalizations is open. Here “finite flat quasi-coherent” is represented by the canonical sheaf
owners `[ℱ.IsQuasicoherent] [ℱ.IsFiniteType] [ℱ.IsFlat]`. -/
@[stacks 053N]
theorem finiteFlatQuasiCoherent_isFiniteLocallyFree_iff_closed_generalizationClosed_isOpen
    (X : Scheme.{u}) :
    (∀ (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] [ℱ.IsFlat],
      ℱ.IsFiniteLocallyFree) ↔
      ∀ Z : Set X, IsClosed Z → StableUnderGeneralization Z → IsOpen Z := sorry

end AlgebraicGeometry
