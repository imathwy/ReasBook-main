import Mathlib
import StacksProject_2024.stacks_project.Chap30.Definition_30_11_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open scoped ENat

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced `Module.IsReflexive` as the canonical module owner,
-- and local precedent in `Chap30/Definition_30_11_1.lean` uses `RingedSpace.stalkModuleCat` and
-- `moduleDepth` for stalkwise conditions on coherent `\mathcal O_X`-modules.

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable [MonoidalCategory X.Modules] [BraidedCategory X.Modules] [MonoidalClosed X.Modules]
variable (ℱ : X.Modules) [ℱ.IsCoherent]

/-- Lemma 31.12.10: let `X` be an integral locally Noetherian scheme and let `ℱ` be a coherent
`\mathcal O_X`-module. Then `ℱ` is reflexive if and only if, for every point `x : X`, either the
stalk `ℱ_x` is a reflexive `\mathcal O_{X, x}`-module or the stalk `ℱ_x` has depth at least `2`.
-/
@[stacks 0AY5]
theorem isReflexive_iff_stalk_isReflexive_or_moduleDepth_ge_two :
    IsReflexive ℱ ↔
      ∀ x : X,
        Module.IsReflexive (X.presheaf.stalk x) (stalkModuleCat ℱ x) ∨
          (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (stalkModuleCat ℱ x) := sorry

namespace IsReflexive

/-- For a coherent reflexive `\mathcal O_X`-module, every stalk is reflexive or has depth at
least `2`. -/
theorem stalk_isReflexive_or_moduleDepth_ge_two
    {ℱ : X.Modules} [ℱ.IsCoherent] (hℱ : IsReflexive ℱ) (x : X) :
    Module.IsReflexive (X.presheaf.stalk x) (stalkModuleCat ℱ x) ∨
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (stalkModuleCat ℱ x) :=
  (isReflexive_iff_stalk_isReflexive_or_moduleDepth_ge_two ℱ).1 hℱ x

end IsReflexive

/-- Companion bridge: if every stalk of a coherent `\mathcal O_X`-module on an integral locally
Noetherian scheme is reflexive or has depth at least `2`, then the module is reflexive. -/
theorem isReflexive_of_stalk_isReflexive_or_moduleDepth_ge_two
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hℱ : ∀ x : X,
      Module.IsReflexive (X.presheaf.stalk x) (stalkModuleCat ℱ x) ∨
        (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (stalkModuleCat ℱ x)) :
    IsReflexive ℱ :=
  (isReflexive_iff_stalk_isReflexive_or_moduleDepth_ge_two ℱ).2 hℱ

end AlgebraicGeometry.Scheme.Modules
