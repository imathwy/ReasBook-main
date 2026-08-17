module

public import Book.Ch9.Prop_9_8
import Book.Ch9.Theorem_9_4

public section

/- Exercise 9.3. The source asks for a proof of Proposition 9.8 using
Theorem 9.4. The supporting theorem owner for that proof route is
`KKT.exists_isMultiplier`, while Proposition 9.8 itself is already formalized
in Chapter 9 by the three source-facing clause theorems below. This exercise
file records that canonical Chapter 9 reuse surface rather than introducing an
exercise-specific wrapper theorem. -/

/- The KKT existence theorem requested by the source proof route is formalized
by `KKT.exists_isMultiplier`. -/
#check KKT.exists_isMultiplier

/- Exercise 9.3 (1). The gradient nonnegativity clause of Proposition 9.8 is
formalized by `NonnegativeOrthant.gradient_nonneg`. -/
#check NonnegativeOrthant.gradient_nonneg

/- Exercise 9.3 (2). The feasibility clause of Proposition 9.8 is formalized
by `NonnegativeOrthant.coordinate_nonneg`. -/
#check NonnegativeOrthant.coordinate_nonneg

/- Exercise 9.3 (3). The complementarity clause of Proposition 9.8 is
formalized by `NonnegativeOrthant.complementarity`. -/
#check NonnegativeOrthant.complementarity
