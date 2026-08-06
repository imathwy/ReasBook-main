import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_4_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ComplexKTheory

noncomputable section

-- Semantic recall via `lean_leansearch` did not surface an imported Chern-character ring-hom
-- owner for the local Chapter 24 `complexKTheory` and `EvenRationalCohomology` surfaces, so this
-- file records the source-faithful existence statement together with its split-bundle
-- compatibility specification.

section

variable {X : Type} [TopologicalSpace X]
variable {A : Type} [EvenRationalCohomology X A]

namespace SplitBundleDatum

/-- The complex `K`-theory class of the split bundle underlying `D`. -/
abbrev toComplexKTheory
    {n : ℕ} {E : X → Type}
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E)]
    [(x : X) → TopologicalSpace (E x)] [FiberBundle (Fin n → ℂ) E]
    [(x : X) → AddCommGroup (E x)] [(x : X) → Module ℂ (E x)]
    [VectorBundle ℂ (Fin n → ℂ) E] (D : SplitBundleDatum A n E) :
    K(X) :=
  let _ : SplitBundleDatum A n E := D
  ComplexVectorBundle.toVirtualPresentation
    (ComplexVectorBundle.Presentation.ofFamily (Fin n → ℂ) E)

/-- The `K`-theory class attached to a bundle depends only on the underlying bundle family, not on
the chosen split-bundle datum. -/
theorem toComplexKTheory_eq
    {n : ℕ} {E : X → Type}
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E)]
    [(x : X) → TopologicalSpace (E x)] [FiberBundle (Fin n → ℂ) E]
    [(x : X) → AddCommGroup (E x)] [(x : X) → Module ℂ (E x)]
    [VectorBundle ℂ (Fin n → ℂ) E] (D₀ D : SplitBundleDatum A n E) :
    D₀.toComplexKTheory = D.toComplexKTheory := rfl

end SplitBundleDatum

/-- A ring homomorphism `ch : K(X) → A` is a Chern character when `A` is a chosen model of
`H^even(X; ℚ)` and, on every split complex vector bundle, `ch` agrees with the split-root formula of
Definition 24.4.3. -/
class IsComplexKTheoryChernCharacter (ch : K(X) →+* A) : Prop where
  /-- On a split rank-`n` complex vector bundle, `ch` evaluates to the sum `∑ i, exp(x_i)` in
  the chosen even rational cohomology ring, where `x_i` is the first Chern class of the `i`th
  summand. -/
  on_splitDatum {n : ℕ} {E : X → Type}
      [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E)]
      [(x : X) → TopologicalSpace (E x)] [FiberBundle (Fin n → ℂ) E]
      [(x : X) → AddCommGroup (E x)] [(x : X) → Module ℂ (E x)]
      [VectorBundle ℂ (Fin n → ℂ) E] (D : SplitBundleDatum A n E) :
      ch D.toComplexKTheory = chernCharacter D

namespace IsComplexKTheoryChernCharacter

section

variable {n : ℕ} {E : X → Type}
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E)]
variable [(x : X) → TopologicalSpace (E x)] [FiberBundle (Fin n → ℂ) E]
variable [(x : X) → AddCommGroup (E x)] [(x : X) → Module ℂ (E x)]
variable [VectorBundle ℂ (Fin n → ℂ) E]

/-- Evaluating a Chapter 24 Chern character on the `K`-theory class of a split bundle recovers
the split-root formula from Definition 24.4.3. -/
theorem on_splitBundle
    {ch : K(X) →+* A} [hch : IsComplexKTheoryChernCharacter ch]
    (D : SplitBundleDatum A n E) :
    ch D.toComplexKTheory = chernCharacter D :=
  hch.on_splitDatum D

/-- A Chapter 24 Chern character takes the same value on any two split presentations of the same
bundle, so the split-root formula is independent of the chosen split-bundle datum. -/
theorem chernCharacter_eq
    {ch : K(X) →+* A} [hch : IsComplexKTheoryChernCharacter ch]
    (D₀ D : SplitBundleDatum A n E) :
    chernCharacter D₀ = chernCharacter D := by
  calc
    chernCharacter D₀ = ch D₀.toComplexKTheory := by
      exact (on_splitBundle D₀).symm
    _ = ch D.toComplexKTheory := by
      exact congrArg ch (SplitBundleDatum.toComplexKTheory_eq D₀ D)
    _ = chernCharacter D := by
      exact on_splitBundle D

end

set_option synthInstance.checkSynthOrder false in
/-- A Chapter 24 Chern character determines the well-definedness property from
Definition 24.4.3: the split-root formula is independent of the chosen split-bundle datum. -/
instance hasWellDefinedChernCharacter
    {ch : K(X) →+* A} [hch : IsComplexKTheoryChernCharacter ch] :
    HasWellDefinedChernCharacter X A := by
  refine ⟨?_⟩
  intro n E _ _ _ _ _ _ D₀ D
  calc
    chernCharacter D₀ = ch D₀.toComplexKTheory := by
      exact (hch.on_splitDatum D₀).symm
    _ = ch D.toComplexKTheory := by
      exact congrArg ch (SplitBundleDatum.toComplexKTheory_eq D₀ D)
    _ = chernCharacter D := by
      exact hch.on_splitDatum D

end IsComplexKTheoryChernCharacter

/-- Lemma 24.4.4. For a compact space `X` and a chosen model `A` of `H^even(X; ℚ)`, there exists
a ring homomorphism `ch : K(X) → A` whose value on every split bundle is given by the Chern-root
formula of Definition 24.4.3. -/
theorem complexKTheoryChernCharacter_exists [CompactSpace X] :
    ∃ ch : K(X) →+* A, IsComplexKTheoryChernCharacter ch := sorry

end
