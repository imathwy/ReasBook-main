module

public import ComputationalMethodsInverseProblems_Vogel_2002.Book.Ch7.Theorem_7_27

public section

/- Exercise 7.22. The source asks the reader to prove Theorem 7.27. In this
repository, Theorem 7.27 is already formalized as the three source-facing
Chapter 7 discrepancy-principle clauses below, so this exercise is recorded by
direct reuse of that existing surface rather than by introducing an
exercise-specific wrapper theorem.
-/
#check TikhonovDiscrepancy.isEquivalent_nonsaturated
#check TikhonovDiscrepancy.isEquivalent_critical
#check TikhonovDiscrepancy.isEquivalent_saturated
