import Mathlib.FieldTheory.Normal.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Polynomial

universe u v

variable {F : Type u} [Field F]
variable (P : F[X])

/- Lemma 9.16.1: the canonical field `P.SplittingField` is a splitting field of `P` over `F`;
this is exactly the canonical instance `Polynomial.IsSplittingField.splittingField`. -/
recall Polynomial.IsSplittingField.splittingField

variable {E : Type v} [Field E] [Algebra F E]

/- Companion recall for Lemma 9.16.1: a splitting field is normal over the base field, via the
canonical theorem `Normal.of_isSplittingField`. -/
recall Normal.of_isSplittingField

/- Companion recall for Lemma 9.16.1: any splitting field of `P` is `F`-algebra isomorphic to the
canonical splitting field `P.SplittingField`; this is exactly
`Polynomial.IsSplittingField.algEquiv`. -/
recall Polynomial.IsSplittingField.algEquiv
