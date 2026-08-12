import Mathlib
import ProbabilityTheory_Klenke_2020.Chap20.Definition_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E] [StandardBorelSpace E]

/-- Restrict a two-sided path to its nonnegative coordinates. -/
def nonnegativePathRestriction : (ℤ → E) → ℕ → E :=
  fun ω n ↦ ω n

-- Proof sketch: realize the extension on the path space `ℤ → E`, define the finite-dimensional
-- marginals on left-infinite coordinate sets by stationarity of `X`, check consistency, and apply
-- the countable projective-limit theorem to obtain a probability measure on `E^ℤ`.
/-- Lemma 20.4: a stationary process indexed by `ℕ₀` admits a stationary extension indexed by
`ℤ`; equivalently, there exists a probability law on the two-sided path space whose canonical
coordinate process is stationary and whose restriction to the nonnegative coordinates has the same
law as the original process. -/
theorem exists_two_sided_stationary_extension
    (X : ℕ → Ω → E) (P : ProbabilityMeasure Ω)
    (hX : IsStationaryProcess X P) :
    ∃ Pext : ProbabilityMeasure (ℤ → E),
      IsStationaryProcess (fun n ω ↦ ω n) (Pext : Measure (ℤ → E)) ∧
        IdentDistrib
          nonnegativePathRestriction
          (fun ω n ↦ X n ω)
          (Pext : Measure (ℤ → E))
          (P : Measure Ω) := sorry
