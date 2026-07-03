import Serre.Chap18.Remark_18_18_6_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for this item:
* primary domain: modular representation theory of finite groups, specialized here to the explicit
  `A₅` decomposition and Cartan matrices recorded in Remark `18-18.6-1`;
* relevant owner declarations inspected in this domain:
  `alternating_group_five_decomposition_matrix_mod_three`,
  `alternating_group_five_cartan_matrix_mod_three_det`,
  `alternating_group_five_decomposition_matrix_mod_five`,
  `alternating_group_five_cartan_matrix_mod_five_det`;
* best owner abstraction: the decomposition matrices are the primitive source-facing data in the
  owning remark, and the determinant assertions for the derived Cartan matrices already live there
  as the canonical owner theorems for parts `(b)` and `(c)` of this exercise;
* primitive data vs. derived API:
  primitive data stay upstream as the explicit decomposition matrices, while the Cartan matrices
  and their determinant computations are derived matrix-level API and should not be duplicated
  here.

Source/core/bridge triage:
* source-facing: Exercise `18-18.6-2` only points back to Serre's recorded determinant assertions.
* core/canonical: the owner theorems are
  `alternating_group_five_cartan_matrix_mod_three_det` and
  `alternating_group_five_cartan_matrix_mod_five_det`.
* bridge/view: there is no extra bridge construction in this file.

This item should therefore remain a direct recall of the upstream canonical theorems rather than a
parallel local wrapper or restatement. -/

/- Exercise 18-18.6-2 (1): assertion `(b)` of Remark `18-18.6-1` is the already recorded
statement that the determinant of the `p = 3` Cartan matrix for Serre's modular-character example
for `A₅` is `3`. -/
recall alternating_group_five_cartan_matrix_mod_three_det

/- Exercise 18-18.6-2 (2): assertion `(c)` of Remark `18-18.6-1` is the already recorded
statement that the determinant of the `p = 5` Cartan matrix for Serre's modular-character example
for `A₅` is `5`. -/
recall alternating_group_five_cartan_matrix_mod_five_det
