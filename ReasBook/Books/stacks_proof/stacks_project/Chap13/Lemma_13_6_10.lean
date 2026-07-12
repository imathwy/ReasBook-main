import Mathlib
import StacksProject_2024.Chap04.Lemma_4_27_21
import StacksProject_2024.Chap13.Lemma_13_5_4
import StacksProject_2024.Chap13.Lemma_13_6_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.ObjectProperty
open CategoryTheory.MorphismProperty
open scoped CategoryTheory.ObjectProperty

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D] [IsTriangulated D]

/-
Domain-style sampling for Lemma `13.6.10`:
- primary domain: Verdier localization of a triangulated category and the correspondence between
  saturated triangulated subcategories and saturated multiplicative systems;
- sampled owner declarations:
  `kernel_triangulatedLocalization_eq_retractClosure`,
  `ObjectProperty.retractClosure_eq_self`,
  `kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor`,
  `MorphismProperty.saturatedClosure_le_iff`;
- best owner abstraction: on the morphism-property side, the canonical owner is
  `S.saturatedClosure`, so the kernel-induced class `(Functor.kernel S.Q).trW` should appear as a
  bridge to that owner rather than as a second parallel "smallest saturated system" API; on the
  object-property side, the canonical intrinsic owner is `P.retractClosure`, with the quotient
  kernel `Functor.kernel P.trW.Q` only the Verdier-localization view on that owner;
- primitive data: an object property `P` or a morphism property `S`;
- derived API: the fixed-point statements for retract-stable triangulated `P` and saturated
  compatible `S`;
- source/core/bridge triage:
  `source-facing`: `kernel_trW_eq_self` and `trW_functorKernel_eq_self`;
  `core/canonical`: `P.retractClosure`, `Functor.kernel`, `ObjectProperty.trW`, and
    `S.saturatedClosure`;
  `bridge/view`: `kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor S.Q` together with the
    owner definition of `S.saturatedClosure`.
-/

-- Proof sketch: apply `kernel_triangulatedLocalization_eq_retractClosure` from Lemma 13.6.9 and
-- then use the owner theorem `ObjectProperty.retractClosure_eq_self`.
section

variable (P : ObjectProperty D) [P.IsTriangulated] [P.IsStableUnderRetracts]

/-- Passing from a saturated triangulated subcategory `P` to its cone-defined multiplicative
system and then back to the kernel subcategory recovers `P`. -/
theorem kernel_trW_eq_self : kernel P.trW.Q = P := by
  rw [kernel_triangulatedLocalization_eq_retractClosure P]
  simpa using P.retractClosure_eq_self

end
end

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable (S : MorphismProperty D) [S.IsCompatibleWithTriangulation]

-- Proof sketch: rewrite `(Functor.kernel S.Q).trW` through the exact-functor bridge
-- `kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor S.Q`, identify the resulting
-- inverse-image class with the owner `S.saturatedClosure`, and then apply the canonical
-- fixed-point inequalities for saturated closure.
/-- Lemma 13.6.10: if `S` is a saturated multiplicative system compatible with the triangulated
structure on `D`, then passing to the kernel of the localization functor `S.Q` and then taking
the associated cone-defined morphism property recovers `S`. Together with `kernel_trW_eq_self`,
this is the mutually inverse correspondence between saturated compatible multiplicative systems
and strictly full saturated triangulated subcategories. -/
@[stacks 05RL]
theorem trW_functorKernel_eq_self
    [IsSaturatedMultiplicativeSystem S] :
    (kernel S.Q).trW = S := by
  rw [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor S.Q]
  exact le_antisymm
    (saturatedClosure_le S le_rfl)
    ((IsInvertedBy.iff_le_inverseImage_isomorphisms S S.Q).1 S.Q_inverts)

end

end CategoryTheory
