import Mathlib
import StacksProject_2024.Chap11.Definition_11_5_2
import StacksProject_2024.Chap11.Definition_11_8_1
import StacksProject_2024.Chap11.Lemma_11_7_4
import StacksProject_2024.Chap11.Theorem_11_8_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

/- Domain-style sampling for Proposition 11.8.5:
- primary domain: separable maximal subfields and finite separable splitting fields for finite
  central simple algebras and their Brauer classes;
- sampled owner declarations:
  `Br`,
  `IsMaximalSubfield`,
  `CSA.IsSplitBy`,
  `CSA.isSplitBy_iff_of_isBrauerEquivalent`,
  `BrauerGroup.IsSplitBy`;
- best owner abstraction: the representative-level splitting notion is canonically owned by
  `CSA.IsSplitBy`, while the source-facing Brauer-class surface in this chapter is `Br(k)`;
  the Brauer-group statement should therefore be a quotient-level bridge on `Br(k)` built from
  the representative owner, rather than a parallel wrapper vocabulary;
- primitive data: a maximal subfield `K : Subalgebra k D` in the division-algebra case, and the
  owner predicate `A.IsSplitBy L` for scalar extensions of a representative `A : CSA k`;
- derived API: the quotient-level bridge `BrauerGroup.IsSplitBy` and the induced existence theorem
  for classes `A : Br(k)`.

Source/core/bridge triage:
- `source-facing`: existence of a separable maximal subfield and existence of a finite separable
  splitting field;
- `core/canonical`: `CSA.IsSplitBy`;
- `bridge/view`: the quotient-level predicate `BrauerGroup.IsSplitBy` and the descent from
  representatives to Brauer classes. -/

section

variable {k : Type u} [Field k]
variable {D : Type v} [DivisionRing D] [Algebra k D] [FiniteDimensional k D]
  [Algebra.IsCentral k D]

-- Proof sketch: among the separable `k`-subfields of `D`, choose one maximal by inclusion. If it
-- were not maximal among commutative `k`-subalgebras, enlarging it would produce an element of `D`
-- separable over `k`, contradicting maximality of the separable subfield.
/-- Proposition 11.8.5 (1): a finite central skew field over `k` contains a maximal subfield that
is separable over `k`. -/
theorem exists_separable_maximal_subfield :
    ∃ K : Subalgebra k D, Algebra.IsSeparable k K ∧ IsMaximalSubfield K := sorry

namespace CSA

variable (A : CSA.{u, v} k)

-- Proof sketch: choose a Brauer-equivalent finite central skew field representing `A`, apply the
-- first part to obtain a separable maximal subfield, and then use Lemma 11.8.3 to see that this
-- maximal subfield splits the division algebra. Brauer equivalence preserves the splitting-field
-- condition, so the same finite separable extension splits `A`.
/-- Proposition 11.8.5 (2), representative form: every finite central simple `k`-algebra is split
by some finite separable extension of `k`. -/
theorem exists_finite_separable_splitting_field :
    ∃ (L : Type w) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L)
      (_ : Algebra.IsSeparable k L),
      A.IsSplitBy L := sorry

end CSA

namespace BrauerGroup

variable (A : Br(k))
variable (L : Type w) [Field L] [Algebra k L]

/-- A Brauer class is split by `L` if it admits a finite central simple representative split by
`L`. -/
def IsSplitBy : Prop :=
  ∃ B : CSA.{u, max u v} k, (Quotient.mk _ B : Br(k)) = A ∧ B.IsSplitBy L

@[simp] theorem isSplitBy_mk [FiniteDimensional k L] (A : CSA.{u, max u v} k) :
    BrauerGroup.IsSplitBy (Quotient.mk _ A : Br(k)) L ↔ A.IsSplitBy L := by
  constructor
  · rintro ⟨B, hBA, hB⟩
    have hiff : A.IsSplitBy L ↔ B.IsSplitBy L := by
      exact A.isSplitBy_iff_of_isBrauerEquivalent L <| Quotient.exact hBA.symm
    exact hiff.2 hB
  · intro hA
    exact ⟨A, rfl, hA⟩

/- Layer note: Proposition 11.8.5 (2) is `source-facing`, but its owner abstraction is
`BrauerGroup k`; the representative-level `CSA` statement is retained only as a bridge. -/
/-- Proposition 11.8.5 (2): every Brauer class over `k` admits a finite separable splitting
field. -/
theorem exists_finite_separable_splitting_field :
    ∃ (L : Type w) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L)
      (_ : Algebra.IsSeparable k L), A.IsSplitBy L := by
  refine Quotient.inductionOn A fun B ↦ ?_
  rcases B.exists_finite_separable_splitting_field with ⟨L, _, _, _, _, hL⟩
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨B, rfl, hL⟩⟩

end BrauerGroup

end
