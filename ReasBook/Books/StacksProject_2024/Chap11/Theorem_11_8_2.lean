import Mathlib
import stacks_project.Chap11.Definition_11_8_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Theorem 11.8.2:
- primary domain: splitting fields of finite central simple algebras, organized on the owner
  `CSA k` and its scalar-extension predicate `CSA.IsSplitBy`;
- sampled owner declarations:
  `CSA`,
  `CSA.baseChange`,
  `CSA.IsSplitBy`,
  `IsBrauerEquivalent`;
- best owner abstraction: this theorem is `source-facing`; its core/canonical owner remains the
  base-changed algebra `A.baseChange K`, while Brauer equivalence on representatives is the right
  bridge language for the criterion and its invariance consequences;
- primitive data: a representative `B : CSA k`, the canonical relation `IsBrauerEquivalent A B`,
  a `k`-algebra embedding `K →ₐ[k] B`, and the square-dimension condition
  `Module.finrank k B = Module.finrank k K ^ 2`;
- derived API: Brauer-invariance of `CSA.IsSplitBy`, which should be exposed once at the owner
  level rather than re-derived in downstream files.

Source/core/bridge triage:
- `source-facing`: the splitting criterion itself for `A.IsSplitBy K`;
- `core/canonical`: the base-changed owner `A.baseChange K : CSA K`;
- `bridge/view`: Brauer-equivalence invariance of `IsSplitBy`, derived from the main criterion. -/

universe u v w

namespace CSA

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k)
variable (K : Type w) [Field K] [Algebra k K] [FiniteDimensional k K]

-- Proof sketch: for the forward implication, realize the split algebra as `End_K(V)`, take the
-- commutant of `A` in `End_k(V)`, and use the double-centralizer dimension formula to obtain a
-- Brauer-equivalent algebra containing `K` with `k`-dimension `[K : k]^2`. For the reverse
-- implication, use the embedded copy of `K` in `B`, identify `B ⊗[k] K` with the corresponding
-- centralizer in `End_k(B)`, and apply the centralizer criterion from the previous subsection.
/-- Theorem 11.8.2: a finite extension `K/k` splits the finite central simple `k`-algebra `A` if
and only if there exists a finite central simple `k`-algebra `B` Brauer equivalent to `A` that
contains `K` as a `k`-subalgebra and has `k`-dimension `[K : k]^2`. -/
theorem isSplitBy_iff_exists_brauerEquivalent_with_subfield_finrank_sq :
    A.IsSplitBy K ↔
      ∃ B : CSA.{u, v} k,
        IsBrauerEquivalent A B ∧
          Nonempty (K →ₐ[k] B) ∧
          Module.finrank k B = Module.finrank k K ^ 2 := sorry

/-- Brauer-equivalent finite central simple algebras have the same finite splitting fields. -/
theorem isSplitBy_iff_of_isBrauerEquivalent {B : CSA.{u, v} k}
    (hAB : IsBrauerEquivalent A B) :
    A.IsSplitBy K ↔ B.IsSplitBy K := by
  constructor
  · intro hA
    rcases (A.isSplitBy_iff_exists_brauerEquivalent_with_subfield_finrank_sq K).1 hA with
      ⟨C, hAC, hK, hdim⟩
    refine (B.isSplitBy_iff_exists_brauerEquivalent_with_subfield_finrank_sq K).2 ?_
    exact ⟨C, IsBrauerEquivalent.trans (IsBrauerEquivalent.symm hAB) hAC, hK, hdim⟩
  · intro hB
    rcases (B.isSplitBy_iff_exists_brauerEquivalent_with_subfield_finrank_sq K).1 hB with
      ⟨C, hBC, hK, hdim⟩
    refine (A.isSplitBy_iff_exists_brauerEquivalent_with_subfield_finrank_sq K).2 ?_
    exact ⟨C, IsBrauerEquivalent.trans hAB hBC, hK, hdim⟩

end CSA
