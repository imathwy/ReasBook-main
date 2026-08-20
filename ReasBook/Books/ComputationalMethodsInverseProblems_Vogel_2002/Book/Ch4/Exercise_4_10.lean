module

public import ComputationalMethodsInverseProblems_Vogel_2002.Book.Ch4.Remark_4_36

public section

/- Exercise 4.10. In the Chapter 4 linear-Gaussian progression, Exercise 4.9 already
records the precision-form MAP estimator, while Exercise 4.11 specializes the same formula
to the isotropic Tikhonov identity `(4.22)`. The intervening displayed formula `(4.21)` is
therefore the Chapter 4 bridge identifying the covariance-form minimum-variance estimator
with the precision-form estimator, formalized canonically in Remark 4.36 by
`ProbabilityTheory.covarianceFormulaEstimator_eq_precisionEstimator`. -/

#check ProbabilityTheory.covarianceFormulaEstimator_eq_precisionEstimator
