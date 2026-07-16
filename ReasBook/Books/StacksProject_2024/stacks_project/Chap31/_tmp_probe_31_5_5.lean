import StacksProject_2024.stacks_project.Chap26.Lemma_26_11_2

open AlgebraicGeometry

universe u

variable (X : Scheme.{u})

#check (Scheme.isBasis_affineOpens X)
#check (Scheme.isBasis_affineOpens X).exists_subset_of_mem_open
#check (Scheme.isBasis_affineOpens X).mem_nhds_iff
#check TopCat.Sheaf.eq_of_locally_eq
