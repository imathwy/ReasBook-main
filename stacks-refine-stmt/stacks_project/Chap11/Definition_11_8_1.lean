import Mathlib
import stacks_project.Chap11.Lemma_11_4_9

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Definition 11.8.1:
- primary domain: splitting fields of finite central simple algebras via scalar extension;
- sampled owner declarations:
  `CSA`,
  `CSA.baseChange`,
  `CSA.mk`,
  `IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite`;
- best owner abstraction: this item is `source-facing`, but its core/canonical owner object is the
  base-changed algebra `A.baseChange K : CSA K`; the splitting predicate should be defined by a
  matrix-algebra presentation of that owner, not by a separate wrapper carrying extra data.
- primitive data: existence of a `K`-algebra equivalence from `A.baseChange K` to a full matrix
  algebra over `K`.
- derived API: the positive-size reformulation is better exposed via the canonical positive natural
  numbers `ℕ+`, rather than by storing a separate `n ≠ 0` proof.

Source/core/bridge triage:
- `source-facing`: `CSA.IsSplitBy`, expressing that the field extension `K/k` splits `A`;
- `core/canonical`: the owner object `A.baseChange K : CSA K`;
- `bridge/view`: the companion positive-index reformulation below, which repackages the same matrix
  presentation using `ℕ+`. -/

universe u v w

variable {k : Type u} [Field k]

namespace CSA

variable (A : CSA.{u, v} k) (K : Type w) [Field K] [Algebra k K]

/-- Definition 11.8.1: a field extension `K/k` splits the finite central simple `k`-algebra `A`
if the scalar extension, viewed as the canonical base-changed central simple `K`-algebra
`A.baseChange K`, is `K`-algebra isomorphic to a full matrix algebra over `K`. -/
def IsSplitBy : Prop :=
  ∃ n : ℕ, Nonempty ((A.baseChange K) ≃ₐ[K] Matrix (Fin n) (Fin n) K)

/-- Textbook-positive reformulation of `IsSplitBy`: the matrix size may be indexed by a positive
natural number. -/
theorem isSplitBy_iff_exists_pnat_algEquiv_matrix :
    A.IsSplitBy K ↔
      ∃ n : ℕ+, Nonempty ((A.baseChange K) ≃ₐ[K] Matrix (Fin n) (Fin n) K) := by
  constructor
  · rintro ⟨n, h⟩
    by_cases hn : n = 0
    · exfalso
      subst hn
      rcases h with ⟨e⟩
      exact zero_ne_one <| e.injective <| Subsingleton.elim _ _
    · exact ⟨⟨n, Nat.pos_of_ne_zero hn⟩, by simpa using h⟩
  · rintro ⟨n, h⟩
    exact ⟨(n : ℕ), by simpa using h⟩

end CSA
