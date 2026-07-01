import Mathlib
import stacks_project.Chap11.Lemma_11_4_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

namespace CSA

section

variable {k : Type u} [Field k]

/- Domain-style sampling for Lemma 11.5.4:
- primary domain: finite-dimensional central simple algebras and their matrix-algebra
  presentations after scalar extension to an algebraically closed field;
- sampled owner declarations:
  `CSA`,
  `CSA.baseChange`,
  `IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed`,
  `Module.finrank_baseChange`;
- best owner abstraction: the relevant owner object is the base-changed central simple algebra
  `A.baseChange K : CSA K`; the square-dimension statement is derived API on the source-facing owner
  `A : CSA k`, not new primitive data;
- primitive data: a finite central simple algebra `A : CSA k`;
- derived API: the scalar-extension matrix presentation over `AlgebraicClosure k`, the resulting
  square formula for `Module.finrank k A`, and the canonical degree `A.degree` defined as the
  square root of that dimension.

Source/core/bridge triage:
- `source-facing`: the textbook statement that the degree `[A : k]` is a square for a finite
  central simple `k`-algebra;
- `core/canonical`: the owner objects `A : CSA k` and `A.baseChange K : CSA K`;
- `bridge/view`: the passage to `AlgebraicClosure k` and the matrix-algebra presentation given by
  `IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed`. -/

/-- Lemma 11.5.4: the `k`-dimension of a finite central simple algebra is a square natural number.
-/
-- Proof sketch: after extending scalars to an algebraic closure of `k`, apply Lemma 11.5.3 to
-- identify the algebra with a matrix algebra and compute its dimension as `n ^ 2`.
theorem finrank_isSquare (A : CSA.{u, v} k) : IsSquare (Module.finrank k A) := by
  let K := AlgebraicClosure k
  obtain ⟨n, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed K (A.baseChange K)
  have hbase : Module.finrank K (A.baseChange K) = Module.finrank k A := by
    change Module.finrank K (K ⊗[k] A) = Module.finrank k A
    exact Module.finrank_baseChange
  refine ⟨n, ?_⟩
  calc
    Module.finrank k A = Module.finrank K (A.baseChange K) := hbase.symm
    _ = Module.finrank K (Matrix (Fin n) (Fin n) K) := e.toLinearEquiv.finrank_eq
    _ = n * n := by
      simpa using (Module.finrank_matrix K K (Fin n) (Fin n))

/-- The degree of a finite central simple algebra is the square root of its dimension over the
base field. -/
noncomputable def degree (A : CSA.{u, v} k) : ℕ :=
  Nat.sqrt (Module.finrank k A)

-- Proof sketch: by Lemma 11.5.4 the dimension of `A` is a square, so `Nat.sqrt` recovers the
-- unique positive integer whose square is `Module.finrank k A`.
/-- The square of the degree of a finite central simple algebra is its dimension over the base
field. -/
theorem degree_sq_eq_finrank (A : CSA.{u, v} k) :
    A.degree ^ 2 = Module.finrank k A := by
  rcases A.finrank_isSquare with ⟨n, hn⟩
  rw [degree, hn, Nat.sqrt_eq, pow_two]

end

end CSA
