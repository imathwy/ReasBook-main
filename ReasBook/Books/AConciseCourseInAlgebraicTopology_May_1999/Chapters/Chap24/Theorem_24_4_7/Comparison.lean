import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Topology.CWComplex.Classical.Finite
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Construction_22_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Definition_22_5_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_2_5

open CategoryTheory Opposite HomotopicalAlgebra
open scoped ComplexKTheory TensorProduct

noncomputable section

universe v

local notation "BasedSpace" => Under (⊤_ TopCat)
local notation "BasedCWComplex" =>
  CategoryTheory.ObjectProperty.FullSubcategory IsBasedCWComplex

/-- The degree-`n` reduced rational cohomology group of a based CW complex `X`, named through a
chosen Chapter 22 representation datum `R` for coefficients `ℚ`. -/
abbrev reducedRationalCohomologyGroup
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    {n : ℕ} (R : ReducedCohomologyEilenbergMacLaneRepresentation ℚ n)
    (X : BasedCWComplex) :=
  representedReducedCohomologyGroup R X

/-- The even reduced rational cohomology group `H̃^0(X; ℚ)` of a based CW complex `X`, named by an
explicit Chapter 22 degree-`0` representation datum `R`. -/
abbrev reducedEvenRationalCohomologyGroup
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (R : ReducedCohomologyEilenbergMacLaneRepresentation ℚ 0)
    (X : BasedCWComplex) :=
  reducedRationalCohomologyGroup R X

/-- The odd reduced rational cohomology group `H̃^1(X; ℚ)` of a based CW complex `X`, named by an
explicit Chapter 22 degree-`1` representation datum `R`. -/
abbrev reducedOddRationalCohomologyGroup
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (R : ReducedCohomologyEilenbergMacLaneRepresentation ℚ 1)
    (X : BasedCWComplex) :=
  reducedRationalCohomologyGroup R X

/-- The degree-`q` reduced complex `K`-theory group of a based CW complex `X`, named by the
packaged reduced theory represented by a chosen complex `K`-theory prespectrum `KU`. -/
abbrev reducedComplexKTheoryGroup
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (setup : BasedCWReducedSuspensionCofiberSetup)
    (KU : Prespectrum.{v, 0}) [ComplexKTheoryPrespectrum KU]
    (q : ℤ) (X : BasedCWComplex) :=
  ((omegaPrespectrumRepresentsReducedCohomologyTheory setup KU).cohomology q).obj (Opposite.op X)

/-- The even reduced complex `K`-theory group `K̃^0(X)` of a based CW complex `X`, named by a
chosen Chapter 22 reduced-theory setup and a complex `K`-theory prespectrum `KU`. -/
abbrev reducedEvenComplexKTheoryGroup
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (setup : BasedCWReducedSuspensionCofiberSetup)
    (KU : Prespectrum.{v, 0}) [ComplexKTheoryPrespectrum KU]
    (X : BasedCWComplex) :=
  reducedComplexKTheoryGroup setup KU 0 X

/-- The odd reduced complex `K`-theory group `K̃^1(X)` of a based CW complex `X`, named by a
chosen Chapter 22 reduced-theory setup and a complex `K`-theory prespectrum `KU`. -/
abbrev reducedOddComplexKTheoryGroup
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (setup : BasedCWReducedSuspensionCofiberSetup)
    (KU : Prespectrum.{v, 0}) [ComplexKTheoryPrespectrum KU]
    (X : BasedCWComplex) :=
  reducedComplexKTheoryGroup setup KU 1 X

/-- A reduced Chern character on the current Chapter 22/24 surface is a degree-`0` stable
cohomology operation from the reduced complex `K`-theory represented by `KU` on the setup carried
by `R` to the reduced rational cohomology theory carried by `R`. -/
abbrev ReducedChernCharacter
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    {n : ℕ} (R : ReducedCohomologyEilenbergMacLaneRepresentation ℚ n)
    (KU : Prespectrum.{v, 0}) [ComplexKTheoryPrespectrum KU] :=
  StableCohomologyOperation R.setup
    (omegaPrespectrumRepresentsReducedCohomologyTheory R.setup KU).cohomology
    R.theory.cohomology 0

/-- The degree-`q` component of a reduced Chern character evaluated on a based CW complex `X`. -/
abbrev reducedChernCharacterComponent
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    {n : ℕ} (R : ReducedCohomologyEilenbergMacLaneRepresentation ℚ n)
    (KU : Prespectrum.{v, 0}) [ComplexKTheoryPrespectrum KU]
    (ch : ReducedChernCharacter R KU) (q : ℤ) (X : BasedCWComplex) :
    reducedComplexKTheoryGroup R.setup KU q X ⟶
      (R.theory.cohomology (q + 0)).obj (Opposite.op X) :=
  (ch q).app (Opposite.op X)

/-- The degree-`0` component of a reduced Chern character lands in the represented reduced
rational cohomology group `H̃^0(X; ℚ)` named by `R`. -/
abbrev reducedChernCharacterEvenComponent
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (R : ReducedCohomologyEilenbergMacLaneRepresentation ℚ 0)
    (KU : Prespectrum.{v, 0}) [ComplexKTheoryPrespectrum KU]
    (ch : ReducedChernCharacter R KU) (X : BasedCWComplex) :
    reducedComplexKTheoryGroup R.setup KU 0 X ⟶
      reducedEvenRationalCohomologyGroup R X :=
  reducedChernCharacterComponent R KU ch 0 X

/-- The degree-`1` component of a reduced Chern character lands in the represented reduced
rational cohomology group `H̃^1(X; ℚ)` named by `R`. -/
abbrev reducedChernCharacterOddComponent
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (R : ReducedCohomologyEilenbergMacLaneRepresentation ℚ 1)
    (KU : Prespectrum.{v, 0}) [ComplexKTheoryPrespectrum KU]
    (ch : ReducedChernCharacter R KU) (X : BasedCWComplex) :
    reducedOddComplexKTheoryGroup R.setup KU X ⟶
      reducedOddRationalCohomologyGroup R X :=
  reducedChernCharacterComponent R KU ch 1 X

/-- A homomorphism
`reducedEvenComplexKTheoryGroup R.setup KU X ⊗[ℤ] ℚ → H̃^0(X; ℚ)` is an even rationalized reduced
Chern-character map when it agrees with the degree-`0` component of `ch` on pure tensors
`ξ ⊗ 1`. The comparison with the source-facing group `K̃(X.obj.right, underTopBasepoint X.obj)` is
recorded separately by `IsReducedChernCharacterEvenRationalizedMap.viaComparison_tmul_one`. -/
def IsReducedChernCharacterEvenRationalizedMap
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (R : ReducedCohomologyEilenbergMacLaneRepresentation ℚ 0)
    (KU : Prespectrum.{v, 0}) [ComplexKTheoryPrespectrum KU]
    (ch : ReducedChernCharacter R KU) (X : BasedCWComplex)
    (chEven : (reducedEvenComplexKTheoryGroup R.setup KU X ⊗[ℤ] ℚ) →+
      reducedEvenRationalCohomologyGroup R X) : Prop :=
  ∀ ξ : reducedEvenComplexKTheoryGroup R.setup KU X,
    chEven (ξ ⊗ₜ[ℤ] (1 : ℚ)) = reducedChernCharacterEvenComponent R KU ch X ξ

/-- The defining source-facing pure-tensor formula for an even rationalized reduced
Chern-character map. -/
theorem IsReducedChernCharacterEvenRationalizedMap.tmul_one
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (R : ReducedCohomologyEilenbergMacLaneRepresentation ℚ 0)
    (KU : Prespectrum.{v, 0}) [ComplexKTheoryPrespectrum KU]
    (ch : ReducedChernCharacter R KU) (X : BasedCWComplex)
    {chEven : (reducedEvenComplexKTheoryGroup R.setup KU X ⊗[ℤ] ℚ) →+
      reducedEvenRationalCohomologyGroup R X}
    (hchEven : IsReducedChernCharacterEvenRationalizedMap R KU ch X chEven)
    (ξ : reducedEvenComplexKTheoryGroup R.setup KU X) :
    chEven (ξ ⊗ₜ[ℤ] (1 : ℚ)) = reducedChernCharacterEvenComponent R KU ch X ξ :=
  hchEven ξ

/-- Rewriting the defining pure-tensor formula for an even rationalized reduced Chern-character
map through `ComplexKTheoryPrespectrum.reducedTheoryComparison R.setup X` recovers the source-facing
formula on `K̃(X.obj.right, underTopBasepoint X.obj)`. -/
theorem IsReducedChernCharacterEvenRationalizedMap.viaComparison_tmul_one
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (R : ReducedCohomologyEilenbergMacLaneRepresentation ℚ 0)
    (KU : Prespectrum.{v, 0}) [ComplexKTheoryPrespectrum KU]
    (ch : ReducedChernCharacter R KU) (X : BasedCWComplex)
    {chEven : (reducedEvenComplexKTheoryGroup R.setup KU X ⊗[ℤ] ℚ) →+
      reducedEvenRationalCohomologyGroup R X}
    (hchEven : IsReducedChernCharacterEvenRationalizedMap R KU ch X chEven)
    (ξ : K̃(X.obj.right, underTopBasepoint X.obj)) :
    chEven
        (((ComplexKTheoryPrespectrum.reducedTheoryComparison R.setup X).symm ξ) ⊗ₜ[ℤ]
          (1 : ℚ)) =
      reducedChernCharacterEvenComponent R KU ch X
        ((ComplexKTheoryPrespectrum.reducedTheoryComparison R.setup X).symm ξ) :=
  hchEven.tmul_one R KU ch X ((ComplexKTheoryPrespectrum.reducedTheoryComparison R.setup X).symm ξ)

/-- A homomorphism `K̃^1(X) ⊗ ℚ → H̃^1(X; ℚ)` is an odd rationalized reduced Chern-character map
when it agrees with the degree-`1` component of `ch` on pure tensors `ξ ⊗ 1`. -/
def IsReducedChernCharacterOddRationalizedMap
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (R : ReducedCohomologyEilenbergMacLaneRepresentation ℚ 1)
    (KU : Prespectrum.{v, 0}) [ComplexKTheoryPrespectrum KU]
    (ch : ReducedChernCharacter R KU) (X : BasedCWComplex)
    (chOdd :
      (reducedOddComplexKTheoryGroup R.setup KU X ⊗[ℤ] ℚ) →+
        reducedOddRationalCohomologyGroup R X) : Prop :=
  ∀ ξ : reducedOddComplexKTheoryGroup R.setup KU X,
    chOdd (ξ ⊗ₜ[ℤ] (1 : ℚ)) = reducedChernCharacterOddComponent R KU ch X ξ

/-- The defining source-facing pure-tensor formula for an odd rationalized reduced Chern-character
map. -/
theorem IsReducedChernCharacterOddRationalizedMap.tmul_one
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (R : ReducedCohomologyEilenbergMacLaneRepresentation ℚ 1)
    (KU : Prespectrum.{v, 0}) [ComplexKTheoryPrespectrum KU]
    (ch : ReducedChernCharacter R KU) (X : BasedCWComplex)
    {chOdd :
      (reducedOddComplexKTheoryGroup R.setup KU X ⊗[ℤ] ℚ) →+
        reducedOddRationalCohomologyGroup R X}
    (hchOdd : IsReducedChernCharacterOddRationalizedMap R KU ch X chOdd)
    (ξ : reducedOddComplexKTheoryGroup R.setup KU X) :
    chOdd (ξ ⊗ₜ[ℤ] (1 : ℚ)) = reducedChernCharacterOddComponent R KU ch X ξ :=
  hchOdd ξ
