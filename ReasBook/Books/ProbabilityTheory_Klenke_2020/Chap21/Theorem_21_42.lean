import ProbabilityTheory_Klenke_2020.Chap21.Theorem_21_40
import ProbabilityTheory_Klenke_2020.Chap21.Theorem_21_6

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory Set

noncomputable section

universe u v

local instance theorem2142MeasurableSpaceBrownianPathSpace : MeasurableSpace BrownianPathSpace :=
  borel _

local instance theorem2142BorelSpaceBrownianPathSpace : BorelSpace BrownianPathSpace := ⟨rfl⟩

-- Proof sketch: use the Kolmogorov--Chentsov Hölder-probability estimate on each compact time
-- interval to verify the oscillation tightness criterion from Theorem 21.40 for the family of
-- path laws, then apply that criterion together with the assumed tightness of the initial-value
-- laws.
/-- Theorem 21.42: tight initial laws together with Kolmogorov moment bounds on every bounded time
interval imply weak relative compactness of the family of path laws in `C([0, ∞), ℝ)`. -/
theorem isCompact_closure_range_pathLaw_of_tight_initialLaws_of_kolmogorovCriterion
    {Ω : Type u} {I : Type v} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (X : I → Ω → BrownianPathSpace)
    (hX : ∀ i, Measurable (X i))
    (h0_tight :
      initial_value_laws_tight (fun i ↦ P.map (hX i).aemeasurable))
    (hmoment :
      ∀ N : NNReal, 0 < N →
        ∃ α β C : NNReal,
          ∀ i,
            IsKolmogorovProcessOnIcc
              (P : Measure Ω) (fun t ω ↦ X i ω t) N α β C) :
    IsCompact (closure (Set.range fun i ↦ P.map (hX i).aemeasurable)) := sorry
