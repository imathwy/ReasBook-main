import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.RingTheory.TensorProduct.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Construction_22_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Definition_22_5_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_2_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Theorem_24_4_7.Comparison

open CategoryTheory Opposite HomotopicalAlgebra
open scoped ComplexKTheory TensorProduct

noncomputable section

universe v

local notation "BasedSpace" => Under (⊤_ TopCat)
local notation "BasedCWComplex" =>
  CategoryTheory.ObjectProperty.FullSubcategory IsBasedCWComplex

section

variable [CategoryWithCofibrations BasedSpace]
variable [CategoryWithCofibrations BasedCWComplex]
variable [CategoryWithWeakEquivalences BasedCWComplex]

/- Theorem 24.4.7. For a finite based CW complex, the reduced Chern character identifies
`K̃^0(X) ⊗ ℚ` and `K̃^1(X) ⊗ ℚ` with the corresponding even and odd reduced rational cohomology
groups. On the current repository surface, the reduced Chern character is a degree-`0` stable
cohomology operation from the represented reduced complex `K`-theory of a complex
`K`-theory prespectrum `KU` to the represented reduced rational cohomology theory carried by `R`.
The theorem records that its degree-`0` and degree-`1` components induce bijections after
rationalization. -/

/-- The even part of Theorem 24.4.7: on a finite based CW complex, the reduced Chern character
induces a bijection from `K̃^0(X) ⊗ ℚ` to the represented reduced rational cohomology group
`H̃^0(X; ℚ)` named by `R`. On the current repository surface, this is recorded by the existence of
an induced represented-group map
`reducedEvenComplexKTheoryGroup R.setup KU X ⊗[ℤ] ℚ → H̃^0(X; ℚ)` satisfying the pure-tensor
formula of `IsReducedChernCharacterEvenRationalizedMap R KU reducedCh X`; the source-facing
comparison with `K̃(X.obj.right, underTopBasepoint X.obj)` is
`IsReducedChernCharacterEvenRationalizedMap.viaComparison_tmul_one`. -/
theorem finiteBasedCWComplex_reducedChernCharacter_even
    (KU : Prespectrum.{v, 0}) [ComplexKTheoryPrespectrum KU]
    (R : ReducedCohomologyEilenbergMacLaneRepresentation ℚ 0)
    (X : BasedCWComplex)
    [Topology.CWComplex (Set.univ : Set X.obj.right)]
    [Topology.CWComplex.Finite (Set.univ : Set X.obj.right)]
    (reducedCh : ReducedChernCharacter R KU) :
    ∃ chEven :
      (reducedEvenComplexKTheoryGroup R.setup KU X ⊗[ℤ] ℚ) →+
        reducedEvenRationalCohomologyGroup R X,
      IsReducedChernCharacterEvenRationalizedMap R KU reducedCh X chEven ∧
        Function.Bijective chEven := by
  sorry

/-- Any chosen even rationalized reduced Chern-character map on the represented degree-`0`
reduced `K`-theory group is bijective. -/
theorem finiteBasedCWComplex_reducedChernCharacter_even_map_bijective
    (KU : Prespectrum.{v, 0}) [ComplexKTheoryPrespectrum KU]
    (R : ReducedCohomologyEilenbergMacLaneRepresentation ℚ 0)
    (X : BasedCWComplex)
    [Topology.CWComplex (Set.univ : Set X.obj.right)]
    [Topology.CWComplex.Finite (Set.univ : Set X.obj.right)]
    (reducedCh : ReducedChernCharacter R KU)
    (chEven :
      (reducedEvenComplexKTheoryGroup R.setup KU X ⊗[ℤ] ℚ) →+
        reducedEvenRationalCohomologyGroup R X)
    (hchEven : IsReducedChernCharacterEvenRationalizedMap R KU reducedCh X chEven) :
    Function.Bijective chEven := by
  sorry

/-- The odd part of Theorem 24.4.7: on a finite based CW complex, the reduced Chern character
induces a bijection from the rationalized degree-`1` represented reduced complex `K`-theory group
to the represented reduced rational cohomology group `H̃^1(X; ℚ)` named by `R`. On the current
repository surface, this is recorded by the existence of an induced represented-group map
`reducedOddComplexKTheoryGroup R.setup KU X ⊗[ℤ] ℚ → H̃^1(X; ℚ)` satisfying the pure-tensor
formula of `IsReducedChernCharacterOddRationalizedMap R KU reducedCh X`. -/
theorem finiteBasedCWComplex_reducedChernCharacter_odd
    (R : ReducedCohomologyEilenbergMacLaneRepresentation ℚ 1)
    (KU : Prespectrum.{v, 0}) [ComplexKTheoryPrespectrum KU]
    (X : BasedCWComplex)
    [Topology.CWComplex (Set.univ : Set X.obj.right)]
    [Topology.CWComplex.Finite (Set.univ : Set X.obj.right)]
    (reducedCh : ReducedChernCharacter R KU) :
    ∃ chOdd :
      (reducedOddComplexKTheoryGroup R.setup KU X ⊗[ℤ] ℚ) →+
        reducedOddRationalCohomologyGroup R X,
      IsReducedChernCharacterOddRationalizedMap R KU reducedCh X chOdd ∧
        Function.Bijective chOdd := by
  sorry

/-- Any chosen odd rationalized reduced Chern-character map on the represented degree-`1`
reduced `K`-theory group is bijective. -/
theorem finiteBasedCWComplex_reducedChernCharacter_odd_map_bijective
    (R : ReducedCohomologyEilenbergMacLaneRepresentation ℚ 1)
    (KU : Prespectrum.{v, 0}) [ComplexKTheoryPrespectrum KU]
    (X : BasedCWComplex)
    [Topology.CWComplex (Set.univ : Set X.obj.right)]
    [Topology.CWComplex.Finite (Set.univ : Set X.obj.right)]
    (reducedCh : ReducedChernCharacter R KU)
    (chOdd :
      (reducedOddComplexKTheoryGroup R.setup KU X ⊗[ℤ] ℚ) →+
        reducedOddRationalCohomologyGroup R X)
    (hchOdd : IsReducedChernCharacterOddRationalizedMap R KU reducedCh X chOdd) :
    Function.Bijective chOdd := by
  sorry

end
