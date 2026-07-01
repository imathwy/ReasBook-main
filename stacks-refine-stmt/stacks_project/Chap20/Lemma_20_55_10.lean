import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

noncomputable section

universe u v w z

section

variable {R : Type u} [CommRing R] [Nontrivial R]
variable {L : Type v} [AddCommGroup L] [Module R L]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {N : Type z} [AddCommGroup N] [Module R N]

/-- A module over `R` is finite free when it is both free and finite. -/
def IsFiniteFreeModule (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P] : Prop :=
  Module.Free R P ∧ Module.Finite R P

/-- A module over `R` is finite free of rank `1` when it is finite free and has module rank `1`.
-/
def IsFiniteFreeRankOne (R : Type u) [CommRing R] [Nontrivial R]
    (P : Type v) [AddCommGroup P] [Module R P] : Prop :=
  IsFiniteFreeModule R P ∧ Module.rank R P = 1

-- Proof sketch: apply Lemma `20.55.5` on the stalk to identify
-- `H^i(L\eta_\mathcal I M)_x` with `\mathcal I_x^{\otimes i} \otimes H^i(M)_x`. In Situation
-- `20.55.2` the tensor power `\mathcal I_x^{\otimes i}` is free of rank `1`, so after choosing a
-- basis of that rank-one module the tensor product is linearly equivalent to `H^i(M)_x` itself.
-- Transport finite freeness and the rank across the resulting linear equivalences.
/-- A linear equivalence with `L ⊗[R] M`, where `L` is finite free of rank `1` and `M` is finite
free, makes `N` finite free. -/
-- Proof sketch: choose a basis of the rank-one module `L`; then `L ⊗[R] M` is linearly
-- equivalent to `M`. Transport finite freeness across that equivalence and then across `e`.
theorem finiteFree_of_linearEquiv_tensor_rankOne
    (hL : IsFiniteFreeRankOne R L)
    (hM : IsFiniteFreeModule R M)
    (e : N ≃ₗ[R] L ⊗[R] M) :
    IsFiniteFreeModule R N := sorry

/-- Lemma 20.55.10: after the stalkwise comparison from Lemma `20.55.5`, the target cohomology
stalk is of the form `L ⊗[R] M` where `L` is finite free of rank `1`. Hence the comparison target
has the same module rank as `M`; because `M` and `N` may live in different universes, Lean records
this as an equality of lifted cardinals. The companion theorem
`finiteFree_of_linearEquiv_tensor_rankOne` records the finite-freeness conclusion. -/
-- Proof sketch: use the rank-one hypothesis on `L` to rewrite
-- `Module.rank R (L ⊗[R] M) = Module.rank R M`, via `rank_tensorProduct` and
-- `Module.rank R L = 1`, and then transport rank across the linear equivalence `e`.
theorem finiteFree_sameRank_of_linearEquiv_tensor_rankOne
    (hL : IsFiniteFreeRankOne R L)
    (e : N ≃ₗ[R] L ⊗[R] M) :
    Cardinal.lift.{max w z} (Module.rank R N) = Cardinal.lift.{max w z} (Module.rank R M) := sorry

end
