import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra

universe u v w

/-!
Domain triage:
- `source-facing`: the statement says that tensoring a reduced `k`-algebra with a geometrically
  reduced `k`-algebra over the same field stays reduced.
- `core/canonical`: the owner abstraction on the right factor is `Algebra.IsGeometricallyReduced`.
- `bridge/view`: no extra bridge API is needed here; the source-facing theorem is already the
  canonical tensor-product statement used downstream.
-/

section

variable {k : Type u} {R : Type v} {S : Type w}
variable [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

-- Proof sketch: reduce to finitely generated `k`-subalgebras of `R` using Lemma `10.43.4`, then
-- use Lemmas `10.25.4`, `10.31.6`, and `10.25.1` to embed the resulting reduced Noetherian
-- algebra into a finite product of fields. After reducing to the field case, apply geometric
-- reducedness of `S` from Definition `10.43.1`.
/-- Lemma 10.43.5 (Tag 034N): if `S` is geometrically reduced over the field `k` and `R` is a
reduced `k`-algebra, then `R ⊗[k] S` is reduced. -/
@[stacks 034N, instance]
theorem isReduced_tensorProduct_of_geometricallyReduced
    [IsReduced R] [IsGeometricallyReduced k S] :
    IsReduced (R ⊗[k] S) := sorry

end
