import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {F : Type u} {K : Type v}
variable [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/- Domain-style sampling for Lemma 9.12.11:
- primary domain: finite field extensions, separable degree, and counting `F`-algebra embeddings
  into an algebraic closure;
- sampled owner declarations:
  `Field.finSepDegree`,
  `Field.finSepDegree_eq_of_isAlgClosed`,
  `Field.finSepDegree_le_finrank`,
  `Field.finSepDegree_eq_finrank_iff`;
- best owner abstraction: the numerical owner `Field.finSepDegree F K`;
- primitive data: only the finite field extension `K/F`;
- derived API: the source-facing embedding count in `AlgebraicClosure F`, obtained by the canonical
  algebraically-closed bridge `Field.finSepDegree_eq_of_isAlgClosed`.

Source/core/bridge triage:
- `source-facing`: the combined inequality and equality criterion for
  `Nat.card (K →ₐ[F] AlgebraicClosure F)`;
- `core/canonical`: `Field.finSepDegree F K` and its finrank comparison theorems;
- `bridge/view`: `Field.finSepDegree_eq_of_isAlgClosed`, which identifies the embedding count with
  the canonical owner. -/

/-- Lemma 9.12.11: for a finite field extension `K/F`, the number of `F`-algebra morphisms
`K → AlgebraicClosure F` is at most `[K : F]`, and equality holds exactly when `K/F` is
separable. -/
-- Proof sketch: identify `Nat.card (K →ₐ[F] AlgebraicClosure F)` with `finSepDegree F K` via
-- `finSepDegree_eq_of_isAlgClosed`, then combine `finSepDegree_le_finrank` with
-- `finSepDegree_eq_finrank_iff`.
theorem algHom_natCard_to_algebraicClosure_le_finrank_and_eq_iff_isSeparable :
    Nat.card (K →ₐ[F] AlgebraicClosure F) ≤ Module.finrank F K ∧
      (Nat.card (K →ₐ[F] AlgebraicClosure F) = Module.finrank F K ↔
        Algebra.IsSeparable F K) := by
  rw [← Field.finSepDegree_eq_of_isAlgClosed F K (AlgebraicClosure F)]
  exact ⟨Field.finSepDegree_le_finrank F K, Field.finSepDegree_eq_finrank_iff F K⟩

end
