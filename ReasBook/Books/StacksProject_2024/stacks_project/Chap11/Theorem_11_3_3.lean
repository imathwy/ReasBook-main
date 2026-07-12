import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Theorem 11.3.3:
- primary domain: Artin--Wedderburn theory for simple finite-dimensional algebras;
- sampled owner declarations:
  `IsSimpleRing.exists_ringEquiv_matrix_divisionRing`,
  `IsSimpleRing.exists_algEquiv_matrix_divisionRing`,
  `IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite`,
  `IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite`;
- best owner abstraction: this numbered item is a recall-only `core/canonical` entry, owned by
  `IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite`; there is no source-defined extra data
  to package into a local wrapper or bridge;
- primitive data: the ambient assumptions `[Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsSimpleRing A]`;
- derived API: the canonical matrix-over-division-algebra presentation, with the finiteness of the
  division algebra over `k` supplied directly by the owner theorem.

Source/core/bridge triage:
- `source-facing`: the textbook statement that a simple finite-dimensional `k`-algebra is a matrix
  algebra over a finite-dimensional division `k`-algebra;
- `core/canonical`: `IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite`;
- `bridge/view`: none is needed here, because the source statement is exactly the canonical owner
  theorem in the finite-dimensional algebra setting. -/

section

variable {k A : Type*}
variable [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] [IsSimpleRing A]

/- Theorem 11.3.3: a simple finite-dimensional `k`-algebra is `k`-algebra isomorphic to a matrix
algebra `Matrix (Fin n) (Fin n) K` for some positive integer `n` and some skew field `K` over `k`
that is finite over `k`. This is exactly the canonical finite Wedderburn--Artin theorem
`IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite`; in the present context,
`FiniteDimensional k A` supplies the `Module.Finite k A` and `IsArtinianRing A` instances needed
to apply that owner theorem. -/
recall IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite

end
