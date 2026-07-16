import Mathlib
import StacksProject_2024.stacks_project.Chap08.Definition_8_3_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w₁ v₁ v₂ u₁ u₂

namespace CategoryTheory

/- Domain-style sampling for Lemma 8.3.6:
- primary domain: descent data for a fixed-target family in a fibred category with chosen
  pullbacks.
- inspected owner-level declarations:
  `DescentDatum.iso` from 8.3.1,
  `SemiRepresentableFamily.Over.pr0` and `SemiRepresentableFamily.Over.pr1` from 8.3.1,
  `familyDescentFunctor` from 8.3.5,
  `Pseudofunctor.DescentData'.ofDescentData` from mathlib.
- best owner abstraction: the source-facing owner remains the canonical functor
  `familyDescentFunctor hc 𝒰`; the overlap comparison isomorphism attached to its image is derived
  through the owner API `DescentDatum.iso`, not through a fresh local `asIso` shell.
- primitive data: a chosen pullback system `hc`, a family `𝒰`, and a global object `X : p.Fiber U`.
- derived API: the induced family descent datum and its overlap isomorphisms.

Source/core/bridge triage:
- `source-facing`: the explicit formula for the overlap comparison isomorphism of the canonical
  descent datum attached to `X`.
- `core/canonical`: `DescentDatum.iso` on `DescentDatum p hc 𝒰`.
- `bridge/view`: the definitional identification of that canonical isomorphism with the composite
  built from `pullbackCompComponentIso` and the canonical transport isomorphism `eqToIso`.

This file therefore keeps the source-facing formula, but expresses its left-hand side via the
chapter owner API `DescentDatum.iso` instead of the parallel raw `asIso` spelling. -/

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
variable {U : C} {𝒰 : SemiRepresentableFamily.Over U} [HasDescentPullbacks 𝒰]

/-- Lemma 8.3.6: for the canonical descent datum attached to a global object `X`, the overlap
isomorphism on `U_i ×[U] U_{i'}` is the composite of the inverse component of the
pullback-composition comparison, the transport along `pr₀ ≫ f_i = pr₁ ≫ f_{i'}`, and the forward
component of the pullback-composition comparison.
-/
theorem familyDescentFunctor_obj_iso
    (X : p.Fiber U) (i i' : 𝒰.index) :
    ((familyDescentFunctor hc 𝒰).obj X).iso i i' =
      (hc.pullbackCompComponentIso (𝒰.obj i).hom (𝒰.pr0 i i') X).symm ≪≫
        eqToIso (by
          simpa using congrArg (fun f ↦ hc.obj f X) (𝒰.pr0_map_eq_pr1_map i i')) ≪≫
        hc.pullbackCompComponentIso (𝒰.obj i').hom (𝒰.pr1 i i') X := by
  sorry

end CategoryTheory
