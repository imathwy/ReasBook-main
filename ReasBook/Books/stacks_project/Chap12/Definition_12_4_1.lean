import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/- Domain-style sampling for Definition 12.4.1:
- primary domain: idempotent completeness of categories, with the preadditive Karoubian criterion;
- sampled owner API:
  `IsIdempotentComplete`,
  `IsIdempotentComplete.idempotents_split`,
  `Idempotents.isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent`,
  `Idempotents.isIdempotentComplete_iff_idempotents_have_kernels`;
- source/core/bridge triage:
  `source-facing`: the textbook notion that a category is Karoubian;
  `core/canonical`: the owner class `IsIdempotentComplete C`;
  `bridge/view`: in the preadditive setting, the kernel criterion
  `isIdempotentComplete_iff_idempotents_have_kernels`.

Primitive data are only the ambient category `C` and, for the companion criterion, the
preadditive structure on `C`. The splitting package and the kernel/equalizer criteria are derived
owner API already provided by mathlib, so this file should recall those declarations directly and
introduce no parallel local wrapper.
-/

/- Definition 12.4.1: the canonical owner notion for a Karoubian category is
`IsIdempotentComplete C`. -/
recall IsIdempotentComplete

open Idempotents

variable [Preadditive C]

/- Companion recall: the source-form criterion for a preadditive category to be Karoubian is the
existing canonical theorem saying that `C` is idempotent complete exactly when every idempotent
endomorphism has a kernel. -/
recall isIdempotentComplete_iff_idempotents_have_kernels

end CategoryTheory
