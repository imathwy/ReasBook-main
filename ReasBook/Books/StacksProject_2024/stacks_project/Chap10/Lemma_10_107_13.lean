import StacksProject_2024.stacks_project.Chap10.Remark_10_107_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Domain-style sampling for this item:
-- - primary domain: commutative algebra of ring epimorphisms, controlled via the tensor-product
--   criterion and finite matrix witnesses over the base ring;
-- - sampled owner API: `Algebra.isEpi_iff_forall_one_tmul_eq`,
--   `tmul_one_eq_one_tmul_iff_exists_finite_matrix_expression`, and the source-facing bridge
--   `exists_associated_matrix_triple_of_tmul_one_eq_one_tmul`;
-- - `source-facing`: the cardinality comparison `|S| ≤ |R|`;
-- - `core/canonical`: Lemma `10.107.11`, which organizes the epicity relation `g ⊗ 1 = 1 ⊗ g`
--   by finite matrix data over `R`;
-- - `bridge/view`: Remark `10.107.12`, which repackages those matrix witnesses as an associated
--   triple `(P, U, V)` with row and column data landing in the image of `R`.
--
-- Proof sketch: by `Algebra.isEpi_iff_forall_one_tmul_eq`, epimorphy gives
-- `g ⊗ₜ[R] 1 = 1 ⊗ₜ[R] g` for every `g : S`. The owner theorem
-- `tmul_one_eq_one_tmul_iff_exists_finite_matrix_expression` supplies finite matrix witness data
-- over `R`, and Remark `10.107.12` compresses that data to an associated triple `(P, U, V)`. The
-- source uniqueness argument shows that one triple cannot be associated to two different elements
-- of `S`, so `S` injects into the set of finite triples over `R`. That set has cardinality at
-- most `|R|`; in the finite-ring case the source reduces to surjectivity of an epimorphism from an
-- Artinian ring.
/-- Lemma 10.107.13: if `R → S` is an epimorphism of commutative rings, then the cardinality of
`S` is at most the cardinality of `R`. -/
theorem cardinalMk_le_of_isEpi [Algebra.IsEpi R S] :
    Cardinal.lift.{u} (Cardinal.mk S) ≤ Cardinal.lift.{v} (Cardinal.mk R) := sorry

end
