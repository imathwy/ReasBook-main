module

public import ComputationalMethodsInverseProblems_Vogel_2002.Book.Ch4.Example_4_16.GaussianMean

public section

/- Exercise 4.16 (1). Equation `(4.43)` is verified by the existing Gaussian-mean
quadratic-form rewrite. -/

#check GaussianMean.negLogLikelihood_eq_quadraticFunctional

/- Exercise 4.16 (2). Equation `(4.44)` is verified by the existing Gaussian-mean
MLE attainment statement. -/

#check GaussianMean.isMeanMLE_observation

/- Exercise 4.16 (3). Equation `(4.45)` is verified by the existing Gaussian-mean
equality statement `μ = d` for any Gaussian mean MLE. -/

#check GaussianMean.eq_observation_of_isMeanMLE
