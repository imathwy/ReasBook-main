import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_7_43 (from Items/Chap07) -/
/- Theorem 7.43: Every signed measure `φ` admits a Hahn decomposition: there is a measurable set
`Ω⁺` such that `0 ≤[Ω⁺] φ` and `φ ≤[Ω⁺ᶜ] 0`, equivalently every measurable subset of `Ω⁺` has
nonnegative `φ`-mass and every measurable subset of `Ω⁺ᶜ` has nonpositive `φ`-mass. -/
recall MeasureTheory.SignedMeasure.exists_compl_positive_negative
