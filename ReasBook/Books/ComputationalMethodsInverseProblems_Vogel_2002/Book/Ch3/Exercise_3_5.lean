module

public import Book.Ch3.Cor_3_8

public section

/- Exercise 3.5. Prove Corollary 3.8.

This exercise is a check-only reuse surface: Corollary 3.8 is already
formalized in `Book.Ch3.Cor_3_8` as
`ConjugateGradient.terminates_at_exact_solution_from_any_initial_guess`, the
finite-step exact-termination statement for conjugate gradient with a
positive-definite matrix `A`, arbitrary right-hand side `b`, and arbitrary
initial guess `f₀`.

The already-formalized companion consequence
`ConjugateGradient.solves_system_from_any_initial_guess` remains available in
`Book.Ch3.Cor_3_8`, but it is not repeated here as a second labeled entry.
-/
#check ConjugateGradient.terminates_at_exact_solution_from_any_initial_guess
