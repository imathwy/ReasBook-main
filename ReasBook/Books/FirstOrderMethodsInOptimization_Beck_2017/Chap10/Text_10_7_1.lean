import Books.FirstOrderMethodsInOptimization_Beck_2017.Chap01.Definition_1_18
import Books.FirstOrderMethodsInOptimization_Beck_2017.Chap03.Proposition_3_13
import Books.FirstOrderMethodsInOptimization_Beck_2017.Chap10.Algorithm_10_6
import Books.FirstOrderMethodsInOptimization_Beck_2017.Chap10.Definition_10_8
import Books.FirstOrderMethodsInOptimization_Beck_2017.Chap10.Theorem_10_34_pass2_complete

-- Declarations for this item will be appended below by the statement pipeline.

/- Text 10.7.1 (1): the weighted `Q`-norm and weighted gradient on `ℝ^n` are read through the
existing Chapter 1 and Chapter 3 bridge APIs. -/
#check Matrix.qNorm
#check Matrix.qGradient
#check gradient_eq_inv_mulVec_of_posDef_matrix_inner

/- Text 10.7.1 (2): the weighted-FISTA recursion is read from the generic FISTA update rules and
the proximal-gradient stepsize bridge. -/
#check proximal_gradient_step_eq_stepsize_form
#check fista_x_succ
#check fista_t_succ
#check fista_y_succ

/- Text 10.7.1 (3): the constant-schedule weighted `O(1 / k^2)` rate is read from the generic
FISTA rate theorem together with the constant-schedule rule. -/
#check uses_proximal_gradient_Lf_stepsize_rule
#check fista_objective_gap_le_two_alpha_Lf_dist_sq_div_sq
