import Mathlib
import stacks_project.Chap09.Definition_9_14_7

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

/-- Lemma 9.14.8: for a finite extension `K/F`, the separable degree `[K : F]_s` equals the
number of `F`-algebra morphisms from `K` to an algebraic closure of `F`. -/
theorem sepDegree_eq_natCard_algHom :
    [K : F]_s = Nat.card (K →ₐ[F] AlgebraicClosure F) := by
  calc
    [K : F]_s = Cardinal.toNat [K : F]_s := by
      symm
      exact Cardinal.cast_toNat_of_lt_aleph0 <|
        (Field.sepDegree_le_rank F K).trans_lt (Module.rank_lt_aleph0 F K)
    _ = Field.finSepDegree F K := by
      exact congrArg (fun n : ℕ ↦ (n : Cardinal)) (Field.finSepDegree_eq F K).symm
    _ = Nat.card (K →ₐ[F] AlgebraicClosure F) := by
      exact congrArg (fun n : ℕ ↦ (n : Cardinal))
        (Field.finSepDegree_eq_of_isAlgClosed F K (AlgebraicClosure F))

end
