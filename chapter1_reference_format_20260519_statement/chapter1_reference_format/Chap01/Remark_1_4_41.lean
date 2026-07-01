import Mathlib

open Polynomial

universe u v

-- Declarations for this item will be appended below by the statement pipeline.

/- Remark 1.4.41: the textbook description of a splitting field as a "smallest" field extension is
not literally precise, since field extensions of `K` are only partially ordered by inclusion. The
precise mathematical content is that any two splitting fields of the same polynomial are unique up
to `K`-algebra isomorphism. -/
recall IsSplittingField.algEquiv {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (P : K[X]) [IsSplittingField K L P] :
  L ≃ₐ[K] P.SplittingField
