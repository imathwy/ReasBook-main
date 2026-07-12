import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u v w

/-- The subfield `K^p` of `p`-th powers in `K`. -/
abbrev frobeniusSubfield (p : ℕ) (K : Type u) [Field K] [ExpChar K p] : Subfield K :=
  (_root_.frobenius K p).fieldRange

namespace FrobeniusSubfield

/- Textbook notation for the subfield `K^p` of `p`-th powers in `K`. -/
scoped notation:max K "^[" p "]" => frobeniusSubfield p K

end FrobeniusSubfield

open scoped FrobeniusSubfield

/-- The `p`-restricted monomials attached to a family in a field. -/
abbrev pMonomial (p : ℕ) {K : Type v} [CommMonoidWithZero K] [NeZero p] {ι : Type w}
    (x : ι → K) :
    (ι →₀ Fin p) → K :=
  fun e ↦ e.support.prod fun i ↦ x i ^ (e i : ℕ)

section

variable (p : ℕ) (k : Type u) (K : Type v) {ι : Type w}
variable [Field k] [Field K] [Algebra k K]
variable [Fact p.Prime] [CharP K p]

/-- The compositum `kK^p` of `k` and `K^p` inside `K`. -/
abbrev pPowerCompositum : IntermediateField k K :=
  IntermediateField.adjoin k (K^[p] : Set K)

/-- Definition 15.46.1 (1): a family in `K` is `p`-independent over `k` when its
`p`-restricted monomials are linearly independent over the compositum `kK^p`. -/
abbrev PIndependent (x : ι → K) : Prop :=
  LinearIndependent (pPowerCompositum p k K) (pMonomial p x)

/-- Definition 15.46.1 (2): a family in `K` is a `p`-basis of `K` over `k` when its
`p`-restricted monomials are linearly independent and the family generates `K` over the
compositum `kK^p`. -/
def IsPBasis (x : ι → K) : Prop :=
  PIndependent p k K x ∧
    IntermediateField.adjoin (pPowerCompositum p k K) (Set.range x) = ⊤

end
