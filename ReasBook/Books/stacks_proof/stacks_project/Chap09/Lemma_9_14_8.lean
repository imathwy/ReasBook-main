import Mathlib
import stacks_proof.stacks_project.Chap09.Definition_9_14_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open scoped FieldExtensionDegree

variable {F : Type u} {K : Type v}
variable [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/- Domain-style sampling for Lemma 9.14.8:
- primary domain: finite field extensions, separable degree, and counting `F`-algebra
  morphisms into an algebraic closure;
- sampled owner declarations:
  `Field.sepDegree`,
  `Field.sepDegree_le_rank`,
  `Cardinal.cast_toNat_of_lt_aleph0`,
  `Field.finSepDegree_eq`,
  `Field.finSepDegree_eq_of_isAlgClosed`;
- best owner abstraction: the chapter owner notation `[K : F]_s`, i.e. the canonical cardinal
  owner `Field.sepDegree F K` introduced in Definition 9.14.7;
- primitive data: only the finite extension `K/F`;
- derived API: the finite count of `F`-algebra morphisms `K →ₐ[F] AlgebraicClosure F`,
  obtained by passing through the auxiliary numerical bridge `Field.finSepDegree F K` and then
  identifying `[K : F]_s` with its finite `toNat`.

Source/core/bridge triage:
- `source-facing`: the finite-extension formula that the separable degree `[K : F]_s` equals the
  number of `F`-algebra morphisms from `K` to an algebraic closure of `F`;
- `core/canonical`: the chapter owner `[K : F]_s = Field.sepDegree F K`;
- `bridge/view`: `Field.finSepDegree_eq` and `Field.finSepDegree_eq_of_isAlgClosed`, together with
  the finiteness bridge `Cardinal.cast_toNat_of_lt_aleph0`.

This file should therefore keep the source-facing finite theorem on `[K : F]_s`, not collapse it
to the auxiliary numerical theorem whose main owner is `Field.finSepDegree`.
-/

/-- Helper for Lemma 9.14.8: the separable degree cardinal of a finite extension is finite. -/
lemma sepDegree_lt_aleph0_of_finiteDimensional :
    [K : F]_s < Cardinal.aleph0 := by
  -- The separable degree is bounded by the rank, and finite-dimensionality makes the rank finite.
  exact (Field.sepDegree_le_rank F K).trans_lt (Module.rank_lt_aleph0 F K)

/-- Helper for Lemma 9.14.8: `Field.finSepDegree` is the finite cardinality of `[K : F]_s`. -/
lemma sepDegree_toNat_eq_finSepDegree :
    Cardinal.toNat [K : F]_s = Field.finSepDegree F K := by
  -- This is the canonical bridge from the separable degree cardinal to a natural number.
  simpa using (Field.finSepDegree_eq F K).symm

/-- Lemma 9.14.8: for a finite extension `K/F`, the separable degree `[K : F]_s` equals the
number of `F`-algebra morphisms from `K` to an algebraic closure of `F`. -/
@[stacks 09HJ]
theorem sepDegree_eq_natCard_algHom :
    [K : F]_s = Nat.card (K →ₐ[F] AlgebraicClosure F) := by
  -- First realize the separable degree as a finite cardinal.
  calc
    [K : F]_s = Cardinal.toNat [K : F]_s := by
      -- Finite-dimensionality guarantees that the separable degree cardinal is finite.
      symm
      exact Cardinal.cast_toNat_of_lt_aleph0
        (sepDegree_lt_aleph0_of_finiteDimensional (F := F) (K := K))
    -- Next pass to the canonical numerical owner `Field.finSepDegree`.
    _ = Field.finSepDegree F K := by
      simpa using congrArg (fun n : ℕ ↦ (n : Cardinal.{v}))
        (sepDegree_toNat_eq_finSepDegree (F := F) (K := K))
    -- Finally identify that numerical invariant with the number of embeddings into
    -- an algebraic closure.
    _ = Nat.card (K →ₐ[F] AlgebraicClosure F) := by
      simpa using Field.finSepDegree_eq_of_isAlgClosed F K (AlgebraicClosure F)

end
