import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap04.Example_4_3_4

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open Opposite Limits
open scoped RepresentablePresheaf

variable {C : Type u} [Category.{v} C]
variable {F G : Presheaf C}

/- Source/core/bridge triage for Definition 4.8.2:
- domain-style sampling in the presheaf-representability owner layer:
  `Functor.relativelyRepresentable`,
  `yoneda.relativelyRepresentable`,
  `Functor.IsRepresentable.mk'`,
  `Limits.pullbackObjIso`;
- target layer: canonical recall of the owner `yoneda.relativelyRepresentable`, plus the
  source-facing bridge to representability of fibre products with Yoneda sections;
- core/canonical background: the generic owner `Functor.relativelyRepresentable`, specialized here
  to the Yoneda embedding;
- source-facing sections are maps `ξ : h[U] ⟶ G`, while `yonedaEquiv` remains an internal proof
  bridge to the elementwise view `ξ.app (op U) (𝟙 U) : G.obj (op U)`;
- primitive data: only the presheaf morphism `a : F ⟶ G`;
- derived API: representability of the Yoneda pullbacks of `a`.
-/

/- The generic owner for relative representability of a morphism with respect to a functor is
the canonical definition `Functor.relativelyRepresentable`. -/
recall Functor.relativelyRepresentable

/- Definition 4.8.2: a morphism `a : F ⟶ G` of presheaves is representable, or equivalently `F`
is relatively representable over `G`, precisely when it is relatively representable with respect
to the Yoneda embedding. -/
#check yoneda.relativelyRepresentable

/-- Relative representability of a presheaf morphism is equivalent to representability of each
pullback along a Yoneda section. -/
-- Proof sketch: unfold `Functor.relativelyRepresentable` for a section `ξ : h[U] ⟶ G` and identify
-- the resulting pullback object in the presheaf category with the fibre product presheaf
-- `h[U] ×[G] F`.
theorem relativelyRepresentable_iff_isRepresentable_pullback_yoneda (a : F ⟶ G) :
    yoneda.relativelyRepresentable a ↔
      ∀ (U : C) (ξ : h[U] ⟶ G), (pullback a ξ).IsRepresentable := sorry

end CategoryTheory
