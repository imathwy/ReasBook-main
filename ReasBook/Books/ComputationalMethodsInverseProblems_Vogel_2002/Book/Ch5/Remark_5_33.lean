module

public import Book.Ch5.Exercise_5_31.DirichletLaplacian
public import Book.Ch5.Remark_5_33.PeriodicLaplacian

public section

/-!
Source-facing API for Remark 5.33.

The Chapter 5 regularization matrix `L` from `(5.69)` is the new periodic owner
`Matrix.periodicLaplacian`. Its BCCB realization is recorded by
`Matrix.periodicLaplacian_eq_bccb`, and its sparse five-point wrapped stencil is
recorded by `Matrix.periodicLaplacian_apply` and
`Matrix.periodicLaplacian_apply_eq_zero_of_not_stencil`. These are the checked
surfaces behind the remark's `5 * n_x * n_y + O(1)` matrix-vector-cost clause.

The existing Dirichlet replacement from Remark 5.32 remains the checked
nonperiodic comparison owner available in the current repository snapshot.
-/

/- Remark 5.33. The periodic Chapter 5 regularization matrix `L` from `(5.69)`
is realized by `Matrix.periodicLaplacian`; its BCCB bridge and sparse
five-offset entry formula are the source-facing checked surfaces for the
remark. -/
#check Matrix.periodicLaplacian
#check Matrix.periodicLaplacian_eq_bccb
#check Matrix.periodicLaplacian_apply
#check Matrix.periodicLaplacian_apply_eq_zero_of_not_stencil

/- Remark 5.33 comparison surface: `Matrix.dirichletLaplacian` remains the
checked homogeneous Dirichlet replacement of the same Chapter 5 stencil. -/
#check Matrix.dirichletLaplacian
