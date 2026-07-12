import Mathlib
import StacksProject_2024.Chap28.Definition_28_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/- Semantic recall: `lean_leansearch` surfaced the affine-open basis API
`Scheme.isBasis_affineOpens`/`IsAffineOpen`. The local source-facing owner for tensor powers and
nonvanishing opens of an invertible module is `Scheme.Modules.Invertible` from
Definition 28.26.1, so this item is stated as a basis refinement for those chosen opens. -/

/-- Lemma 28.26.6: if the positive tensor-power nonvanishing opens `X_s` of an invertible
`\mathcal O_X`-module form a basis for the topology on a scheme `X`, then the affine opens among
those same nonvanishing opens also form a basis. -/
@[stacks 01PX]
theorem nonvanishingOpen_affineSubfamily_isBasis
    (L : X.Modules) [hL : Invertible L]
    (hBasis : TopologicalSpace.Opens.IsBasis
      {U : X.Opens | ∃ n : {n : ℕ // 0 < n}, ∃ s : Γ(hL n, ⊤),
        U = hL.nonvanishingOpen s}) :
    TopologicalSpace.Opens.IsBasis
      {U : X.Opens | ∃ n : {n : ℕ // 0 < n}, ∃ s : Γ(hL n, ⊤),
        U = hL.nonvanishingOpen s ∧ IsAffineOpen U} := sorry

end AlgebraicGeometry.Scheme.Modules
