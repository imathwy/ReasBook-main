import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Construction_22_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Theorem_22_4_3

-- Chapter 22 already fixes the source-facing owners for this remark: `PostnikovSystem`, its
-- existence theorem for simple spaces of CW type, and the stagewise `k`-invariant construction
-- from Construction 22.4.2.

/- Remark 22.4.4. Postnikov systems decompose a space into its homotopy groups plus
cohomological `k`-invariants. In this repository, that decomposition is recalled by the existence
of a `PostnikovSystem` for spaces satisfying the hypotheses of Theorem 22.4.3, together with the
stagewise construction identifying each bonding map with a fibration whose fiber is the relevant
Eilenberg-MacLane space and whose homotopy-fiber model is governed by a chosen `k`-invariant.
Accordingly, this expository item is formalized as a labeled recall block pointing to those
existing Chapter 22 owners. -/

#check PostnikovSystem
#check exists_postnikov_system_of_simple_space_of_cw_type
#check PostnikovStageConstruction
#check postnikov_stage_has_fibration_and_k_invariant
