import Mathlib
import StacksProject_2024.stacks_project.Chap30.Definition_30_11_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable (U : X.Opens) (ℱ : X.Modules) [ℱ.IsCoherent]

-- Semantic recall: `lean_leansearch` surfaced the scheme-module open restriction and pushforward
-- owners `Scheme.Modules.restrict`, `Scheme.Modules.pushforward`, and
-- `Scheme.Modules.pullbackPushforwardAdjunction`; local Section 31.5 precedent uses the presheaf
-- map `ℱ.val.map (TopologicalSpace.Opens.leTop U).op` for `Γ(X, ℱ) → Γ(U, ℱ)`.

/-- Lemma 31.5.11 (1): let `X` be a locally Noetherian scheme, let `ℱ` be a coherent
`\mathcal O_X`-module, and let `j : U ⟶ X` be the open subscheme inclusion. If every point
`x ∈ X \ U` has `depth(ℱ_x) ≥ 2`, then the canonical map
`ℱ ⟶ j_* (ℱ|_U)` is an isomorphism. -/
@[stacks 0E9I]
theorem isIso_pullbackPushforward_unit_of_moduleDepth_ge_two_off_open
    (hdepth : ∀ x : X, x ∉ U →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app ℱ) := sorry

/-- Lemma 31.5.11 (2): under the hypotheses of Lemma 31.5.11, the restriction map on sections
`Γ(X, ℱ) → Γ(U, ℱ)` is an isomorphism. -/
@[stacks 0E9I]
theorem isIso_restrictionToOpen_of_moduleDepth_ge_two_off_open
    (hdepth : ∀ x : X, x ∉ U →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)) :
    IsIso (ℱ.val.map (TopologicalSpace.Opens.leTop U).op) := sorry

end AlgebraicGeometry.Scheme.Modules
