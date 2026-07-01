import Mathlib
import Serre.GroupTheory.PSolvable
import Serre.Chap16.Proposition_16_16_3_3
import Serre.Chap16.Remark_16_16_3_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Representation

namespace Representation

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [CharP (IsLocalRing.ResidueField A) p]

/- Domain-style sampling for Theorem 16-16.3-6:
* primary domain: modular representation-theoretic lifting criteria for finite `p`-solvable
  groups, expressed through the Chapter `16` owner predicates `SatisfiesConditionR` and
  `SatisfiesConditionRPrime`;
* relevant owner declarations inspected in this domain:
  `IsPSolvableOfHeight`,
  `SatisfiesConditionR`,
  `FDRep.HasRPrimeLift`,
  `SatisfiesConditionRPrime`,
  `IsPSolvable`;
* best owner abstraction: the source-facing conjunction asserting that the fixed
  fraction-field/local-ring setting `K/A` satisfies Serre's conditions `(R)` and `(R')` under the
  canonical group-theoretic owner predicate `IsPSolvable p G`;
* primitive data: the owner predicates `IsPSolvable p G`, `SatisfiesConditionR (R⁺[K](G)) A`, and
  `SatisfiesConditionRPrime A K G`;
* derived API: the two projection theorems below extracting `(R)` and `(R')` separately from the
  source-facing Fong-Swan conjunction.

Source/core/bridge triage:
* source-facing: `fong_swan_of_isPSolvable`;
* core/canonical: `IsPSolvable`, `SatisfiesConditionR`, and `SatisfiesConditionRPrime`;
* bridge/view: the two projection lemmas, which do not introduce any new owner data.
-/

-- Proof sketch: argue by induction on a `p`-solvable height witness for `G`; the induction step
-- combines the recursive normal-subgroup structure with the Chapter 16 descent criteria for
-- condition `(R)` and the lattice-lifting statement `(R')`.
/-- Theorem 16-16.3-6: if the finite group `G` is `p`-solvable, then it satisfies Serre's
conditions `(R)` and `(R')`: the actual positive cone `R_K^+(G)` satisfies condition `(R)`, and
every simple finite-dimensional representation over the residue field of `A` lifts from a stable
lattice in an irreducible finite-dimensional `K`-representation of `G`. -/
theorem fong_swan_of_isPSolvable
    (hp : Nat.Prime p) (hG : IsPSolvable p G) :
    SatisfiesConditionR (R⁺[K](G)) A ∧
      SatisfiesConditionRPrime A K G := sorry

/-- The `(R')` half of Theorem `16-16.3-6`, obtained by projecting the Fong-Swan conjunction. -/
theorem satisfiesConditionRPrime_of_isPSolvable
    (hp : Nat.Prime p) (hG : IsPSolvable p G) :
    SatisfiesConditionRPrime A K G :=
  (fong_swan_of_isPSolvable hp hG).2

/-- The `(R)` half of Theorem `16-16.3-6`, obtained by projecting the Fong-Swan conjunction: a
`p`-solvable finite group satisfies Serre's condition `(R)` for actual `K[G]`-representation
classes. -/
theorem satisfiesConditionR_of_isPSolvable
    (hp : Nat.Prime p) (hG : IsPSolvable p G) :
    SatisfiesConditionR (R⁺[K](G)) A :=
  (fong_swan_of_isPSolvable hp hG).1

end

end Representation
