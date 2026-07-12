import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open PresheafOfModules.DifferentialsConstruction

universe u v

noncomputable section

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable (O₁ O₂ : Sheaf J CommRingCat)
variable (φ : O₁ ⟶ O₂)
variable (U : Cᵒᵖ)

/-
Domain-style sampling:
- primary domain: objectwise relative Kähler differentials for a morphism of sheaves of
  commutative rings;
- sampled owner declarations:
  `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`,
  `relativeDifferentials'_obj`,
  `KaehlerDifferential.kerTotal_eq`,
  `KaehlerDifferential.quotKerTotalEquiv`;
- owner abstraction: `CommRingCat.KaehlerDifferential (φ.hom.app U)`, equivalently
  `((relativeDifferentials' φ.hom).obj U)`;
- primitive data: only the section-ring morphism `φ.hom.app U`;
- derived API: the objectwise identification of `relativeDifferentials' φ.hom` with that owner,
  together with the canonical kernel and quotient presentation of Kähler differentials.

Source/core/bridge triage:
- `source-facing`: the objectwise module of relative differentials on sections over `U`;
- `core/canonical`: `CommRingCat.KaehlerDifferential (φ.hom.app U)` and its canonical
  presentation API `KaehlerDifferential.kerTotal_eq` and
  `KaehlerDifferential.quotKerTotalEquiv`;
- `bridge/view`: `relativeDifferentials'_obj`, which identifies the presheaf-level owner with the
  objectwise canonical owner.

This item is therefore a bridge/recall file: it should reuse the canonical owner layer rather than
introducing a second presentation map or quotient equivalence. -/

/- 18.33.2.1: at an object `U`, the presheaf of relative differentials for `φ` is objectwise the
canonical module of Kähler differentials of the section-ring morphism `φ.hom.app U`. -/
recall relativeDifferentials'_obj

/- Companion recall: the kernel of the canonical presentation map
`Finsupp.linearCombination (O₂.obj.obj U) (KaehlerDifferential.D (O₁.obj.obj U) (O₂.obj.obj U))`
is exactly `KaehlerDifferential.kerTotal (O₁.obj.obj U) (O₂.obj.obj U)`. -/
recall KaehlerDifferential.kerTotal_eq

/- Companion recall: quotienting `(O₂.obj.obj U →₀ O₂.obj.obj U)` by that canonical relation
submodule recovers the objectwise relative differentials. -/
recall KaehlerDifferential.quotKerTotalEquiv

end
