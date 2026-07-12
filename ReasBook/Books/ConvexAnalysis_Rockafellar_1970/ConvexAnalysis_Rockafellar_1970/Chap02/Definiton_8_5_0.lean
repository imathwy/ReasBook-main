import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {X α : Type*} [LE α] [Zero α]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 8.5.0 introduces the recession cone of a proper convex function as
  the nonpositive sublevel set of its recession function `f₀`. The canonical public owner for this
  source notion is therefore the object-prefix declaration `Function.recessionCone`.
- `core/canonical`: for Chapter 8 recession functions, the codomain owner layer is
  `WithTopBot α`; no separate owner is needed beyond the direct nonpositive sublevel expression on
  that codomain.
- `bridge/view`: `Function.mem_recessionCone_iff` rewrites membership in that canonical preimage
  back into the textbook inequality `f₀ y ≤ 0`.
- Primitive data vs derived API: the primitive datum is just a function into `WithTopBot α` with
  order and zero induced from `α`; properness and convexity of the underlying function belong to
  the surrounding setup and are not extra fields of this definition.
- Downstream owner discipline: later predicates about "common nonpositive recession directions"
  should reuse `Function.recessionCone` rather than restating the inequality `f₀ y ≤ 0`
  directly.

Domain-style sampling used here:
- the project-local set-valued owner `recessionCone` from `Definition_8_0_2`;
- the chapter-local owner pattern `linealitySpace` from `Definition_8_4_3`, whose public bridge is
  likewise a membership theorem for a source-facing subset;
- the general sublevel-set pattern `f ⁻¹' Set.Iic a` used elsewhere in the project for source
  zero-sublevel and unit-sublevel sets, exposed here via a bridge theorem when a preorder
  structure is present;
- the sampled local mathlib checkout, which exposes the preimage pattern but no separate generic
  owner abstraction for such sublevel sets.
-/

namespace Function

/-- Definition 8.5.0: the recession cone attached to `f₀` is its nonpositive sublevel set. -/
def recessionCone (f₀ : X → WithTopBot α) : Set X :=
  f₀ ⁻¹' {a : WithTopBot α | a ≤ 0}

/-- On the primitive `WithTopBot` codomain layer, the recession cone is the preimage of the
nonpositive set. -/
@[simp] theorem recessionCone_eq_preimage_nonpos (f₀ : X → WithTopBot α) :
    f₀.recessionCone = f₀ ⁻¹' {a : WithTopBot α | a ≤ 0} :=
  rfl

/-- Membership in the recession cone attached to `f₀` is exactly the nonpositivity condition
`f₀ y ≤ 0`. -/
@[simp] theorem mem_recessionCone_iff {f₀ : X → WithTopBot α} {y : X} :
    y ∈ f₀.recessionCone ↔ f₀ y ≤ 0 :=
  Iff.rfl

end Function

end

section

variable {X α : Type*} [Preorder α] [Zero α]

namespace Function

/-- On a preorder codomain, the recession cone is the standard `Set.Iic` preimage at level `0`. -/
@[simp] theorem recessionCone_eq_preimage_Iic (f₀ : X → WithTopBot α) :
    f₀.recessionCone = f₀ ⁻¹' Set.Iic (0 : WithTopBot α) := by
  ext y
  rfl

end Function

end
