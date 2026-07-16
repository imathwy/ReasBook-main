import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Stalk
import StacksProject_2024.stacks_project.Chap10.Definition_10_103_1
import StacksProject_2024.stacks_project.Chap10.Definition_10_157_1
import StacksProject_2024.stacks_project.Chap17.Definition_17_12_1
import StacksProject_2024.stacks_project.Chap17.ModuleRestrictionAndStalks

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` was unavailable here (HTTP 429). Local precedents
-- `Scheme.Modules.IsLocallyProjective`, `SheafOfModules.flat_at`, `Module.CohenMacaulay`, and
-- `Module.SerreConditionS` indicate that the owner should be a property class on scheme modules,
-- with the source `(S_k)` wording exposed through a stalkwise companion theorem.

variable {X : Scheme.{u}}

private abbrev stalkModule (ℱ : X.Modules) (x : X) :=
  RingedSpace.stalkModuleCat ℱ x

/-- Definition 30.11.4: for a locally Noetherian scheme `X` and a coherent
`\mathcal{O}_X`-module `ℱ`, the module `ℱ` is Cohen-Macaulay if every stalk `ℱ_x` is a
Cohen-Macaulay module over the local ring `\mathcal{O}_{X, x}`. -/
class CohenMacaulay (ℱ : X.Modules) [IsLocallyNoetherian X] [ℱ.IsCoherent] : Prop where
  /-- Every stalk of a Cohen-Macaulay coherent module is Cohen-Macaulay over the corresponding
  local ring. -/
  stalk : ∀ x : X, Module.CohenMacaulay (X.presheaf.stalk x) (stalkModule ℱ x)

namespace CohenMacaulay

/-- Stalks of a Cohen-Macaulay coherent module inherit the canonical Cohen-Macaulay instance. -/
instance instStalkCohenMacaulay {ℱ : X.Modules} [IsLocallyNoetherian X] [ℱ.IsCoherent]
    [hℱ : CohenMacaulay ℱ] (x : X) :
    Module.CohenMacaulay (X.presheaf.stalk x) (stalkModule ℱ x) :=
  hℱ.stalk x

end CohenMacaulay

variable (ℱ : X.Modules) [IsLocallyNoetherian X] [ℱ.IsCoherent]

/-- A coherent module on a locally Noetherian scheme is Cohen-Macaulay exactly when every stalk
satisfies Serre's condition `(S_k)` for every `k ≥ 0`. -/
theorem cohenMacaulay_iff_forall_serreConditionS :
    CohenMacaulay ℱ ↔
      ∀ x : X, ∀ k : ℕ,
        Module.SerreConditionS (X.presheaf.stalk x) (stalkModule ℱ x) k := sorry

end AlgebraicGeometry.Scheme.Modules
