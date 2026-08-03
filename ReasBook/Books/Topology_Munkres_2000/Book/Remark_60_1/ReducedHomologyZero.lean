module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

public section

namespace AlgebraicTopology

open CategoryTheory CategoryTheory.Limits

/-- Helper for Remark 60.1: reduced integral singular homology in degree zero is the
kernel of the canonical augmentation. -/
noncomputable abbrev ReducedSingularHomologyZero (X : TopCat) :=
  kernel (X.singularHomology₀ε (ModuleCat.of ℤ ℤ))

end AlgebraicTopology
