import Mathlib.RingTheory.PowerSeries.Exp
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u v w

section

variable {X : Type u} [TopologicalSpace X]
variable {n : ℕ} {E : X → Type v}
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E)]
variable [(x : X) → TopologicalSpace (E x)] [FiberBundle (Fin n → ℂ) E]
variable [(x : X) → AddCommGroup (E x)] [(x : X) → Module ℂ (E x)]
variable [VectorBundle ℂ (Fin n → ℂ) E]
variable {A : Type w}

/-- A chosen model of the even rational cohomology ring `H^even(X; ℚ)`, equipped with the first
Chern classes of complex line bundles on `X`. -/
class EvenRationalCohomology (X : Type u) [TopologicalSpace X] (A : Type w)
    extends CharacteristicClassTarget.{u, w, v} X A where
  /-- The chosen even rational cohomology ring is a `ℚ`-algebra. -/
  toAlgebra : Algebra ℚ A

instance
    {X : Type u} [TopologicalSpace X] {A : Type w} [H : EvenRationalCohomology X A] :
    Algebra ℚ A :=
  H.toAlgebra

/-- Definition 24.4.3. Given a split-bundle datum for `E` in a chosen model `A` of
`H^even(X; ℚ)`, `chernCharacter D` is the class in `A` given by the split-root formula
`∑ i, exp(x_i)`, where the roots `x_i` are the first Chern classes of the summands. -/
def chernCharacter
    [EvenRationalCohomology X A] (D : SplitBundleDatum A n E) : A :=
  ∑ i : Fin n, PowerSeries.aeval (D.cRoot_hasEval i) (PowerSeries.exp A)

/-- Unfolding `chernCharacter` recovers the split-root formula `∑ i, exp(x_i)`. -/
theorem chernCharacter_eq_sum_aeval_exp_cRoot
    [EvenRationalCohomology X A] (D : SplitBundleDatum A n E) :
    chernCharacter D =
      ∑ i : Fin n, PowerSeries.aeval (D.cRoot_hasEval i) (PowerSeries.exp A) := rfl

/-- A splitting-principle well-definedness hypothesis for the Chapter 24 Chern character:
for every split bundle presentation of `E`, the split-root formula `∑ i, exp(x_i)` depends only
on the underlying bundle and not on the chosen split-bundle datum. -/
class HasWellDefinedChernCharacter (X : Type u) [TopologicalSpace X] (A : Type w)
    [EvenRationalCohomology X A] : Prop where
  /-- The split-root formula defining the Chern character is independent of the chosen
  split-bundle datum. -/
  chernCharacter_eq {n : ℕ} {E : X → Type v}
      [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E)]
      [(x : X) → TopologicalSpace (E x)] [FiberBundle (Fin n → ℂ) E]
      [(x : X) → AddCommGroup (E x)] [(x : X) → Module ℂ (E x)]
      [VectorBundle ℂ (Fin n → ℂ) E] (D₀ D : SplitBundleDatum A n E) :
      chernCharacter D₀ = chernCharacter D

/-- The Chern character class is independent of the chosen split-bundle datum once the chosen
even rational cohomology model is equipped with the splitting-principle well-definedness property
for the split-root formula. -/
theorem chernCharacter_eq
    [EvenRationalCohomology X A] [HasWellDefinedChernCharacter X A]
    (D₀ D : SplitBundleDatum A n E) :
    chernCharacter D₀ = chernCharacter D :=
  HasWellDefinedChernCharacter.chernCharacter_eq D₀ D

end
