import Mathlib
import StacksProject_2024.Chap20.Lemma_20_32_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalClosed
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} (U : Opens X.carrier)
variable [MonoidalCategory (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalClosed (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalCategory (DerivedCategory (openSubspaceModuleCategory X U))]
variable [MonoidalClosed (DerivedCategory (openSubspaceModuleCategory X U))]

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "DModU" => DerivedCategory (openSubspaceModuleCategory X U)

-- Proof sketch: first rewrite `H^0(U, R\mathcal H\!\mathit{om}(L, M))` as the degree-zero
-- hypercohomology of the restricted derived internal Hom on the open subspace via
-- `openHypercohomology_isomorphic_restricted`. Then identify the restriction of
-- `R\mathcal H\!\mathit{om}(L, M)` with `R\mathcal H\!\mathit{om}(L|_U, M|_U)` using
-- Lemma `20.42.3`, and finally compute degree-zero hypercohomology of the internal-Hom object on
-- `U` by Lemma `20.41.6`, which gives morphisms in `D(\mathcal O_U)`.
/-- Lemma 20.42.1: for a ringed space `(X, \mathcal O_X)`, an open subset `U ⊆ X`, and objects
`L, M ∈ D(\mathcal O_X)`, the degree-zero hypercohomology group
`H^0(U, R\mathcal H\!\mathit{om}(L, M))` is canonically identified with the morphism group
`\operatorname{Hom}_{D(\mathcal O_U)}(L|_U, M|_U)`. Specializing to `U = X` yields the global
identification `H^0(X, R\mathcal H\!\mathit{om}(L, M)) =
\operatorname{Hom}_{D(\mathcal O_X)}(L, M)`. -/
theorem open_zeroHypercohomology_internalHom_addEquiv_restrictedDerivedHom
    (L M : DModX) :
    Nonempty
      (((moduleOpenHypercohomology X U ((ihom L).obj M) (0 : ℤ)) : Type u) ≃+
        (((moduleRestrictionToOpenDerived X U).obj L : DModU) ⟶
          ((moduleRestrictionToOpenDerived X U).obj M : DModU))) := sorry

end

end AlgebraicGeometry.RingedSpace
