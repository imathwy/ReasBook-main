import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap09.Definition_9_10
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap09.Definition_9_42

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped BigOperators

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

section

variable {T : ℕ} {X : Fin (T + 1) → Ω → ℝ} (hBinary : IsBinaryModel X)

local notation "ℱX" => generatedFiltration X hBinary.isStochasticProcess

-- Proof sketch: argue by backward induction on time. At each step, an
-- `generatedFiltration X hBinary.isStochasticProcess i.succ`-measurable claim has two branch
-- values over the two successors of the binary model, so solving the resulting two-point linear
-- system produces the next predictable stake and a new
-- `generatedFiltration X hBinary.isStochasticProcess i.castSucc`-measurable continuation value.
/-- Theorem 9.43: in a binary model, every terminal payoff measurable with respect to the terminal
generated filtration is replicated by an initial capital and a bounded predictable strategy whose
finite gain sum matches the terminal payoff at time `T`. -/
theorem binary_model_representation {V_T : Ω → ℝ}
    (hV_T : Measurable[ℱX (Fin.last T)] V_T) :
    ∃ H : Fin (T + 1) → Ω → ℝ,
      IsPredictable ℱX H ∧
        (∀ n : Fin (T + 1), ∃ R : ℝ, 0 ≤ R ∧ ∀ ω, |H n ω| ≤ R) ∧
        ∃ initialCapital : ℝ,
          V_T = fun ω ↦ initialCapital +
            ∑ k : Fin T, H k.succ ω * (X k.succ ω - X k.castSucc ω) :=
      sorry

end

end ProbabilityTheory
