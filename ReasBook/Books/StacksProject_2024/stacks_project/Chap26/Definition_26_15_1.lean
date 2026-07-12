import Mathlib.Tactic.Recall
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Yoneda

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry Opposite

namespace CategoryTheory

/- Source/core/bridge triage for Definition 26.15.1:
- `source-facing`: a contravariant set-valued functor on schemes is representable if it is
  isomorphic to `yoneda.obj X` for some scheme `X`;
- `core/canonical`: the mathlib owner `Functor.IsRepresentable`;
- `bridge/view`: the scheme-specialized Yoneda-isomorphism bridge below.

This Stacks item is a canonical recall of `Functor.IsRepresentable`. Its source-facing existence
form is the standard Yoneda-isomorphism characterization specialized here to `Scheme`. -/

/- Definition 26.15.1: representability of a contravariant set-valued functor on schemes is the
canonical predicate `Functor.IsRepresentable`. -/
recall Functor.IsRepresentable

/- Definition 26.15.1 (source-facing bridge): for a contravariant set-valued functor on schemes,
the Yoneda-isomorphism characterization of representability specializes to the statement
that `F` is representable exactly when `F` is isomorphic to the representable functor of some
scheme `X`. -/
theorem isRepresentable_iff_exists_yoneda_obj_iso (F : Schemeᵒᵖ ⥤ Type) :
    F.IsRepresentable ↔ Nonempty (Σ X : Scheme, yoneda.obj X ≅ F) := by
  sorry

end CategoryTheory
