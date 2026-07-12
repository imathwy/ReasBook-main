import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the exact canonical owner `AlgebraicGeometry.Scheme.IsQuasiAffine`;
- nearby Chapter 28/29 files already use `X.IsQuasiAffine` as the scheme-side API;
- this item is therefore a pure canonical recall rather than a place for a duplicate local alias.
-/

/- Definition 28.18.1: a scheme `X` is quasi-affine if it is quasi-compact and isomorphic to an
open subscheme of an affine scheme. In this project that source-facing notion is exactly the
canonical owner `X.IsQuasiAffine`, so this item is recorded as a recall-only block. -/
recall AlgebraicGeometry.Scheme.IsQuasiAffine

end AlgebraicGeometry
