module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_15
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_21

public section

/- Exercise 2.16. The source asks only to confirm the displayed inequality
`(2.31)` for Landweber iteration. Chapter 2 already formalizes that displayed
inequality as `landweberInverseBound`, so this exercise is a direct canonical
reuse entry. -/

#check landweberInverseBound

/- The Chapter 1 bridge below records the source-facing passage from Landweber
iteration to the scalar filter formulation used by `landweberInverseBound`. -/

#check Landweber.iterate_eq_filterRepresentation
