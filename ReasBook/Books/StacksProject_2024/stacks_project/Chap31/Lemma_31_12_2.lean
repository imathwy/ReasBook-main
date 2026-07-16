import StacksProject_2024.stacks_project.Chap31.Definition_31_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

section

variable {X : Scheme.{u}}
variable [IsIntegral X] [IsLocallyNoetherian X]
variable [MonoidalCategory X.Modules] [BraidedCategory X.Modules] [MonoidalClosed X.Modules]
variable (ℱ : X.Modules) [ℱ.IsCoherent]

-- Semantic recall: Chapter 31 already owns the scheme-side notion as `Scheme.Modules.IsReflexive`
-- in `Definition_31_12_1`, while the source statement here is the affine-open sectionwise
-- characterization of that owner in terms of the canonical module-level predicate
-- `Module.IsReflexive`.

namespace IsReflexive

/-- Affine sections of a reflexive coherent `\mathcal O_X`-module are reflexive over the
corresponding ring of functions. -/
theorem reflexive_sections
    (ℱ : X.Modules) [ℱ.IsCoherent] [IsReflexive ℱ] (U : X.Opens) (hU : IsAffineOpen U) :
    Module.IsReflexive (Γ(X, U)) (Γ(ℱ, U)) := sorry

/-- Affine sections of a reflexive coherent `\mathcal O_X`-module are reflexive over the
corresponding ring of functions, packaged as an element of `X.affineOpens`. -/
theorem reflexive_sections_affineOpen
    (ℱ : X.Modules) [ℱ.IsCoherent] [IsReflexive ℱ] (U : X.affineOpens) :
    Module.IsReflexive (Γ(X, U)) (Γ(ℱ, U)) :=
  reflexive_sections ℱ U.1 U.2

end IsReflexive

/-- Lemma 31.12.2: let `X` be an integral locally Noetherian scheme and let `ℱ` be a coherent
`\mathcal O_X`-module. Then `ℱ` is reflexive if and only if, for every affine open `U ⊆ X`, the
module of sections `Γ(ℱ, U)` is reflexive over `Γ(X, U)`. -/
@[stacks 0AY0]
theorem isReflexive_iff_affineOpen
    (ℱ : X.Modules) :
    IsReflexive ℱ ↔
      ∀ U : X.Opens, IsAffineOpen U → Module.IsReflexive (Γ(X, U)) (Γ(ℱ, U)) := sorry

/-- The reflexive-sheaf owner is exactly affine-open sectionwise reflexivity, packaged over
`X.affineOpens`. -/
theorem isReflexive_iff_affineOpens
    (ℱ : X.Modules) :
    IsReflexive ℱ ↔
      ∀ U : X.affineOpens, Module.IsReflexive (Γ(X, U)) (Γ(ℱ, U)) := by
  constructor
  · intro hℱ U
    exact (isReflexive_iff_affineOpen ℱ).1 hℱ U.1 U.2
  · intro hℱ
    exact (isReflexive_iff_affineOpen ℱ).2 fun U hU ↦ by
      simpa using hℱ ⟨U, hU⟩

end

end AlgebraicGeometry.Scheme.Modules
