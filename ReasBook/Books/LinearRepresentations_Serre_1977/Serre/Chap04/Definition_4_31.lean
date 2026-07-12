import Mathlib.Tactic.Recall
import LinearRepresentations_Serre_1977.Chap02.Theorem_2_2_6_1

open scoped MonoidAlgebra

universe u v w w'

namespace Representation

noncomputable section

section

variable {k : Type u} [Field k]
variable {G : Type v} [Monoid G]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable {W : Type w'} [AddCommGroup W] [Module k W]
variable (ρ : Representation k G V) (π : Representation k G W)

/- Source/core/bridge triage:
- `source-facing`: Definition 4-31 names the `π`-isotypic component of a representation `ρ`.
- `core/canonical`: the underlying owner is the `k[G]`-submodule
  `isotypicComponent k[G] V W`.
- `bridge/view`: the repository already packages that owner as the canonical subrepresentation
  `ρ.isotypicSubrepresentation π`, and its underlying owner-level module can be exposed as
  `ρ.moduleIsotypicComponent π`.

This item is therefore recall-only: introducing a second public owner for the same subrepresentation
would duplicate the Chapter 2 API instead of reusing it, but a thin module-level bridge is useful
for later chapter statements that work with `k[G]`-submodules.
-/

/- Definition 4-31: for representations `ρ` and `π`, the `π`-isotypic component of `ρ` is the
canonical subrepresentation `ρ.isotypicSubrepresentation π`. -/
recall Representation.isotypicSubrepresentation

/-- The underlying `k[G]`-submodule of the canonical `π`-isotypic component of `ρ`. This is the
owner-level bridge used when later statements are expressed in the ambient `k[G]`-module
`ρ.asModule`. -/
abbrev moduleIsotypicComponent (ρ : Representation k G V) (π : Representation k G W) :
    Submodule k[G] ρ.asModule :=
  letI : Module k[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : Module k[G] W := π.instModuleMonoidAlgebraAsModule
  isotypicComponent k[G] V W

@[simp] theorem asSubmodule_isotypicSubrepresentation :
    (ρ.isotypicSubrepresentation π).asSubmodule = ρ.moduleIsotypicComponent π := rfl

@[simp] theorem mem_moduleIsotypicComponent_iff {v : V} :
    v ∈ ρ.moduleIsotypicComponent π ↔ v ∈ (ρ.isotypicSubrepresentation π).toSubmodule := by
  rfl

end

end

end Representation
