import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap17.Construction_17_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap17.Theorem_17_1_3

noncomputable section

open CategoryTheory MonoidalCategory

universe u

-- Semantic recall via local mathlib inspection: `ShortComplex.Splitting.map` is the canonical API
-- for transporting a chosen splitting through `tensorRight`, and
-- `universalCoefficientHomologyShortExact` already packages the fixed-degree universal
-- coefficient sequence inside a coefficient-natural family.

/-- Tensoring a chosen splitting of the cycle-boundary short complex
`0 ⟶ X.cycles n ⟶ X.X n ⟶ boundaryModule R X n ⟶ 0`
with a coefficient module `M` again yields a split short complex. -/
def splitCycleBoundaryTensorSplitting
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    (s : (cycleBoundaryShortComplex R X n).Splitting) :
    ((cycleBoundaryShortComplex R X n).map (tensorRight M)).Splitting :=
  s.map (tensorRight M)

/-- Under the free/PID hypothesis from Construction 17.4.1, tensoring the split cycle-boundary
short complex
`0 ⟶ X.cycles n ⟶ X.X n ⟶ boundaryModule R X n ⟶ 0`
with a coefficient module `M` again yields a split short complex. -/
theorem splitCycleBoundaryTensorSplitting_of_free
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Free R (X.X i)) :
    Nonempty (((cycleBoundaryShortComplex R X n).map (tensorRight M)).Splitting) := by
  rcases cycleBoundaryShortComplex_splitting R X n hX with ⟨s⟩
  exact ⟨splitCycleBoundaryTensorSplitting R X M n s⟩

/-- Proof step 17.4.2. Under the same free/PID hypothesis, tensoring the split
cycle-boundary sequences and identifying the resulting connecting term with
`Tor(H_n(X), M)` yields the degree-`n + 1` universal coefficient short exact sequence for the
fixed coefficient module `M`. -/
theorem universalCoefficientHomologySequenceOfSplitCycleBoundary
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Free R (X.X i)) :
    Nonempty (UniversalCoefficientHomologySequence R X M n) := by
  let hXFlat : ∀ i : ℕ, Module.Flat R (X.X i) := fun i ↦ by
    letI := hX i
    infer_instance
  rcases universalCoefficientHomologyShortExact R X n hXFlat with ⟨S⟩
  exact ⟨S M⟩
