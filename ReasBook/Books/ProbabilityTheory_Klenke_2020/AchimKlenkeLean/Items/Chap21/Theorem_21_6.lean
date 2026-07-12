import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_1
import ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_2

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [PseudoEMetricSpace E]
variable {μ : Measure Ω}

variable (μ)

/-- The source-facing Kolmogorov condition on the finite interval `[0,T]`: the exponents `α` and
`β` are strictly positive, and the restricted process satisfies the canonical mathlib owner
`ProbabilityTheory.IsKolmogorovProcess` with exponents `α` and `1 + β`. This is the thin bridge
from the textbook finite-interval formulation to the global owner abstraction. -/
def IsKolmogorovProcessOnIcc (X : NNReal → Ω → E) (T α β C : ℝ≥0) : Prop :=
  0 < α ∧
    0 < β ∧
      IsKolmogorovProcess (fun t : Set.Icc (0 : NNReal) T ↦ X t) μ (α : ℝ) (1 + (β : ℝ)) C

theorem IsKolmogorovProcessOnIcc.alpha_pos
    {X : NNReal → Ω → E} {T α β C : ℝ≥0}
    (h : IsKolmogorovProcessOnIcc μ X T α β C) :
    0 < α := by
  rcases h with ⟨hα, -, -⟩
  exact hα

theorem IsKolmogorovProcessOnIcc.beta_pos
    {X : NNReal → Ω → E} {T α β C : ℝ≥0}
    (h : IsKolmogorovProcessOnIcc μ X T α β C) :
    0 < β := by
  rcases h with ⟨-, hβ, -⟩
  exact hβ

theorem IsKolmogorovProcessOnIcc.isKolmogorovProcess
    {X : NNReal → Ω → E} {T α β C : ℝ≥0}
    (h : IsKolmogorovProcessOnIcc μ X T α β C) :
    IsKolmogorovProcess (fun t : Set.Icc (0 : NNReal) T ↦ X t) μ (α : ℝ) (1 + (β : ℝ)) C := by
  rcases h with ⟨-, -, hX⟩
  exact hX

variable {μ}

-- Proof sketch: apply the owner lemma `IsKolmogorovProcess.kolmogorovCondition` to the restricted
-- process on `Set.Icc (0, T)` and then simplify the subtype coercions.
/-- A finite-interval Kolmogorov condition gives the stated increment estimate on `[0,T]`. -/
theorem IsKolmogorovProcessOnIcc.increment_lintegral_le
    {X : NNReal → Ω → E} {T α β C : ℝ≥0}
    (h : IsKolmogorovProcessOnIcc μ X T α β C)
    {s t : NNReal} (hs : s ≤ T) (ht : t ≤ T) :
    ∫⁻ ω, edist (X t ω) (X s ω) ^ (α : ℝ) ∂μ ≤
      (C : ℝ≥0∞) * edist t s ^ (1 + (β : ℝ)) := by
  have hs' : s ∈ Set.Icc (0 : NNReal) T := by simpa using hs
  have ht' : t ∈ Set.Icc (0 : NNReal) T := by simpa using ht
  simpa [edist_comm] using h.isKolmogorovProcess.kolmogorovCondition ⟨s, hs'⟩ ⟨t, ht'⟩

variable [IsProbabilityMeasure μ]

-- Proof sketch: on each finite interval `[0,T]`, apply the Kolmogorov--Chentsov construction for
-- every admissible exponent `γ < β / α`, then patch the finite-interval modifications together
-- using indistinguishability on overlaps to obtain one global modification on `[0,∞)`. The same
-- modification also satisfies the deterministic Hölder-constant probability estimate from part
-- (ii) on each fixed interval.
/-- Theorem 21.6: if every finite interval `[0,T]` admits a Kolmogorov--Chentsov moment bound,
then the process has a single modification `Xtilde` such that:

1. every exponent `γ > 0` that is admissible on each finite interval yields locally
   `γ`-Hölder sample paths on `ℝ≥0`;
2. for the same `Xtilde`, on every fixed interval `[0,T]` and for every `ε > 0`, there is a
   deterministic Hölder constant `K` such that the path is `γ`-Hölder on `[0,T]` with
   probability at least `1 - ε`. -/
theorem exists_modification_with_locally_holder_paths
    {X : NNReal → Ω → ℝ}
    (hbound :
      ∀ T : NNReal,
        ∃ α β C : ℝ≥0, IsKolmogorovProcessOnIcc μ X T α β C) :
    ∃ Xtilde : NNReal → Ω → ℝ,
      AreModifications μ X Xtilde ∧
        (∀ γ : ℝ≥0, 0 < γ →
          (∀ T : NNReal,
            ∃ α β C : ℝ≥0, IsKolmogorovProcessOnIcc μ X T α β C ∧ (γ : ℝ) < β / α) →
              ∀ ω : Ω, LocallyHolderWith γ (fun t : NNReal ↦ Xtilde t ω)) ∧
        ∀ (T α β C γ : ℝ≥0),
          IsKolmogorovProcessOnIcc μ X T α β C →
          0 < γ →
            (γ : ℝ) < β / α →
              ∀ ε : ℝ, 0 < ε → ∃ K : ℝ≥0,
                ENNReal.ofReal (1 - ε) ≤
                  μ {
                    ω | HolderOnWith K γ (fun t : NNReal ↦ Xtilde t ω) (Set.Icc (0 : NNReal) T)
                  } := sorry
