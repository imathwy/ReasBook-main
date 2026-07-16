import Mathlib
import StacksProject_2024.stacks_project.Chap15.Definition_15_105_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (K : Type u) [Field K]
variable (A : Type v) [CommRing A] [Algebra K A]

/- Domain-style sampling for Lemma 15.106.2:
- primary domain: commutative algebra of weakly étale `K`-subalgebras of `A`, ordered by
  inclusion in `Subalgebra K A`;
- sampled owner declarations:
  `Algebra.IsWeaklyEtale`,
  `Subalgebra`'s complete lattice structure,
  `le_sSup`,
  `IsGreatest`;
- target layer: `source-facing`, since the Stacks lemma asserts that the supremum of all weakly
  étale `K`-subalgebras is itself the greatest such subalgebra;
- core/canonical owner abstraction: the complete lattice `Subalgebra K A` together with the owner
  predicate `Algebra.IsWeaklyEtale K B`;
- primitive data: the supremum subalgebra `maximalWeaklyEtaleSubalgebra K A`;
- derived API: its weak étaleness and the universal upper-bound property, both obtained from the
  single source-facing `IsGreatest` statement below.

This file should therefore keep the `sSup` construction as the owner object and avoid presenting
projection lemmas as independent primitive data.
-/

/-- The supremum of all weakly étale `K`-subalgebras of `A`. -/
def maximalWeaklyEtaleSubalgebra : Subalgebra K A :=
  sSup {B : Subalgebra K A | Algebra.IsWeaklyEtale K B}

namespace MaximalWeaklyEtaleSubalgebraNotation

/- The textbook surface is `B_max(A/K)`. As elsewhere in the project, the scoped Lean notation
uses `⁄` for the parameterized owner form. -/
@[inherit_doc maximalWeaklyEtaleSubalgebra]
scoped notation:max "B_max(" A "⁄" K ")" => maximalWeaklyEtaleSubalgebra K A

end MaximalWeaklyEtaleSubalgebraNotation

open scoped MaximalWeaklyEtaleSubalgebraNotation

-- Proof sketch: the collection of weakly étale `K`-subalgebras of `A` is directed because the
-- image in `A` of the tensor product of two such subalgebras is again weakly étale. Lemma
-- `15.105.14` then shows that the filtered colimit, identified with the supremum subalgebra, is
-- weakly étale over `K`, and `le_sSup` gives the universal upper-bound property in the lattice of
-- `K`-subalgebras.
/-- Lemma 15.106.2: the supremum of all weakly étale `K`-subalgebras of `A` is a greatest weakly
étale `K`-subalgebra of `A`. -/
theorem isGreatest_maximalWeaklyEtaleSubalgebra :
    IsGreatest {B : Subalgebra K A | Algebra.IsWeaklyEtale K B}
      B_max(A⁄K) := sorry

/-- The supremum of weakly étale `K`-subalgebras of `A` is weakly étale over `K`. -/
theorem isWeaklyEtale_maximalWeaklyEtaleSubalgebra :
    Algebra.IsWeaklyEtale K B_max(A⁄K) :=
  (isGreatest_maximalWeaklyEtaleSubalgebra K A).1

/-- Every weakly étale `K`-subalgebra of `A` is contained in the maximal weakly étale
`K`-subalgebra. -/
theorem le_maximalWeaklyEtaleSubalgebra
    (B : Subalgebra K A) (hB : Algebra.IsWeaklyEtale K B) :
    B ≤ B_max(A⁄K) :=
  (isGreatest_maximalWeaklyEtaleSubalgebra K A).2 <|
    show B ∈ {B : Subalgebra K A | Algebra.IsWeaklyEtale K B} from hB

end
