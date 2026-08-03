import BauschkeLean.Chap23.Proposition_23_39
import BauschkeLean.Chap26.Problem_26_28
import BauschkeLean.Chap26.Problem_26_30
import BauschkeLean.Chap26.Proposition_26_32

open scoped InnerProductSpace Pointwise SetValuedOperator

universe u v

noncomputable section

namespace SetValuedOperator

-- Semantic recall note: `lean_leansearch` surfaced only generic closed/convex and projection
-- lemmas, so this item uses the verified local Chapter 26 owners
-- `composite_kuhn_tucker_points`, `composite_primal_inclusion_solution_set`, and
-- `composite_dual_inclusion_solution_set`; the source projections `Q_ℋ` and `Q_𝒦` are realized
-- canonically by `Prod.fst` and `Prod.snd`.
--
-- Source/core/bridge triage:
-- - `source-facing`: Proposition 26.33 records the geometry of the Kuhn--Tucker point set and
--   its projections onto the primal and dual composite-inclusion solution sets.
-- - `core/canonical`: the owner abstractions are `composite_kuhn_tucker_points`,
--   `composite_kuhn_tucker_operator_add_skewCouplingMap_maximal`, `Maximal.zeros_isClosed`,
--   `Maximal.zeros_convex`, and the product projections `Prod.fst` and `Prod.snd`.
-- - `bridge/view`: the primal and dual projections are expressed through the source-facing
--   solution-set owners from Problem 26.28, rather than through new product-space wrappers.

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

section

variable (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
variable (L : H →L[ℝ] K)

local notation "𝓟" => composite_primal_inclusion_solution_set z A r B L
local notation "𝓓" => composite_dual_inclusion_solution_set z A r B L

/-- Proposition 26.33 (1): if `A` and `B` are maximally monotone, then the Kuhn--Tucker point
set `composite_kuhn_tucker_points z A r B L` is closed. -/
theorem composite_kuhn_tucker_points_isClosed
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B) :
    IsClosed (composite_kuhn_tucker_points z A r B L) := sorry

/-- Proposition 26.33 (2): if `A` and `B` are maximally monotone, then the Kuhn--Tucker point
set `composite_kuhn_tucker_points z A r B L` is convex. -/
theorem composite_kuhn_tucker_points_convex
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B) :
    Convex ℝ (composite_kuhn_tucker_points z A r B L) := sorry

/-- Proposition 26.33 (3): every Kuhn--Tucker pair belongs to the product of the primal and dual
solution sets. -/
theorem composite_kuhn_tucker_points_subset_product_solution_sets :
    composite_kuhn_tucker_points z A r B L ⊆
      𝓟 ×ˢ 𝓓 := sorry

/-- Proposition 26.33 (4): the source projection `Q_ℋ : H × K → H` sends the Kuhn--Tucker set
onto the primal solution set; canonically, this is the image under `Prod.fst`. -/
theorem image_fst_composite_kuhn_tucker_points_eq_composite_primal_inclusion_solution_set :
    Prod.fst '' composite_kuhn_tucker_points z A r B L = 𝓟 := sorry

/-- Proposition 26.33 (5): the source projection `Q_𝒦 : H × K → K` sends the Kuhn--Tucker set
onto the dual solution set; canonically, this is the image under `Prod.snd`. -/
theorem image_snd_composite_kuhn_tucker_points_eq_composite_dual_inclusion_solution_set :
    Prod.snd '' composite_kuhn_tucker_points z A r B L = 𝓓 := sorry

/-- Proposition 26.33 (6): the primal solution set is nonempty exactly when the Kuhn--Tucker
point set is nonempty. -/
theorem composite_primal_nonempty_iff_composite_kuhn_tucker_points_nonempty :
    (𝓟).Nonempty ↔
      (composite_kuhn_tucker_points z A r B L).Nonempty := sorry

/-- Proposition 26.33 (7): the Kuhn--Tucker point set is nonempty exactly when the dual solution
set is nonempty. -/
theorem composite_kuhn_tucker_points_nonempty_iff_composite_dual_nonempty :
    (composite_kuhn_tucker_points z A r B L).Nonempty ↔
      (𝓓).Nonempty := sorry

end

end SetValuedOperator
