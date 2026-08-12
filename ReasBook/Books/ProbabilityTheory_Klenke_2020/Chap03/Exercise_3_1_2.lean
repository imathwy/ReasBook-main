import Mathlib
import ProbabilityTheory_Klenke_2020.Chap03.Definition_3_1

-- Declarations for this item will be appended below by the statement pipeline.

/-- Two probability generating functions agree on an injective sequence of points in `(0,1)`. -/
def ProbabilityGeneratingFunctionsAgreeOnInjectiveSequence (p q : PMF ℕ) : Prop :=
  ∃ x : ℕ → Set.Ioo (0 : ℝ) 1,
    Function.Injective x ∧
      ∀ n : ℕ,
        probabilityGeneratingFunctionReal p (x n) =
          probabilityGeneratingFunctionReal q (x n)

-- Proof sketch: choose two explicit `ℕ`-valued laws whose generating functions have radius of
-- convergence exactly `1`, and use a standard analytic construction so that their difference has
-- infinitely many zeros accumulating only at the boundary point `1`.
/-- Exercise 3.1.2: There exist two distinct real-valued probability generating functions that
agree on an injective sequence of points in `(0,1)`, showing that the extra hypothesis
`ψ z < ∞` for some `z > 1` in Theorem 3.2 (iii) cannot be omitted. -/
theorem distinct_probabilityGeneratingFunctions_agree_on_countably_many_points :
    ∃ p q : PMF ℕ,
      probabilityGeneratingFunctionReal p ≠ probabilityGeneratingFunctionReal q ∧
        ProbabilityGeneratingFunctionsAgreeOnInjectiveSequence p q := sorry
