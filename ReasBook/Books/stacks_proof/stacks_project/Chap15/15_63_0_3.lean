import Mathlib
import stacks_proof.stacks_project.Chap15.«15_60_1_1»
import stacks_proof.stacks_project.Chap15.«15_63_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ModuleCat.MonoidalCategory
open scoped DerivedTensorProduct DerivedTensorWithAlgebra TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {X Y : ModuleCat R}
variable (n m : ℕ)

local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)
local notation "single0" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/- Domain-style sampling for 15.63.0.3:
- primary domain: cohomological pairings and scalar extension in derived categories of module
  categories;
- sampled owner declarations:
  `derivedCohomologyProduct`,
  `DerivedCategory.homologyFunctor`,
  `DerivedTensorWithAlgebra`,
  `derivedCategory_tensorObj_iso_derivedTensorProduct`;
  best owner abstraction: this file is a `bridge/view`; the owner morphism is the upstream
  canonical pairing `derivedCohomologyProduct`, specialized to the scalar-extended objects
  `X[0] ⊗[R]^L[A]` and `Y[0] ⊗[R]^L[A]` in `D(A)`, while the reindexing from
  `-(n : ℤ) + -(m : ℤ)` to `-((n + m : ℕ) : ℤ)` is proof-level bookkeeping rather than new
  product data;
- primitive data: the `R`-modules `X` and `Y`, the `R`-algebra `A`, and the degrees `n` and `m`;
- derived API: the specialized recall term of `derivedCohomologyProduct` on these canonical
  homology objects.

Source/core/bridge triage:
  `source-facing`: the product morphism
  `H^{-n}(X[0] ⊗_R^{\mathbf L} A) ⊗_A H^{-m}(Y[0] ⊗_R^{\mathbf L} A) ⟶
  H^{-(n+m)}((X[0] ⊗_R^{\mathbf L} A) ⊗_A^{\mathbf L} (Y[0] ⊗_R^{\mathbf L} A))`, written
  as the chapter’s scalar-extension specialization of the canonical cohomology product;
- `core/canonical`: `derivedCohomologyProduct`, `DerivedCategory.homologyFunctor`, and the
  scalar-extension notation `⊗[R]^L[A]`;
- `bridge/view`: the further base-change tensor rewrite from `15.63.0.2`. -/

private theorem product_degree_eq :
    (-(n : ℤ) + -(m : ℤ)) = -((n + m : ℕ) : ℤ) := by
  calc
    (-(n : ℤ) + -(m : ℤ)) = -((n : ℤ) + (m : ℤ)) := by
      simpa using (neg_add (n : ℤ) (m : ℤ)).symm
    _ = -((n + m : ℕ) : ℤ) := by
      norm_num

private theorem product_reindex_eq (X Y : ModuleCat R) (n m : ℕ) :
    (H (-(n : ℤ) + -(m : ℤ))).obj
        ((Functor.obj single0 X ⊗[R]^L[A]) ⊗[A]^L (Functor.obj single0 Y ⊗[R]^L[A])) =
      (H (-((n + m : ℕ) : ℤ))).obj
        ((Functor.obj single0 X ⊗[R]^L[A]) ⊗[A]^L (Functor.obj single0 Y ⊗[R]^L[A])) := by
  simpa using congrArg
    (fun i : ℤ ↦
      (H i).obj
        ((Functor.obj single0 X ⊗[R]^L[A]) ⊗[A]^L (Functor.obj single0 Y ⊗[R]^L[A])))
    (product_degree_eq n m)

/- 15.63.0.3: the source-facing product morphism on scalar-extended homology objects is the
specialization of the upstream owner `derivedCohomologyProduct` to the objects
`X[0] ⊗[R]^L[A]` and `Y[0] ⊗[R]^L[A]`, followed by the canonical reindexing
`-(n : ℤ) + -(m : ℤ) = -((n + m : ℕ) : ℤ)`. -/
#check
  (show
    (((H (-(n : ℤ))).obj (Functor.obj single0 X ⊗[R]^L[A]) ⊗
        (H (-(m : ℤ))).obj (Functor.obj single0 Y ⊗[R]^L[A]) : ModuleCat A) ⟶
      (H (-((n + m : ℕ) : ℤ))).obj
        ((Functor.obj single0 X ⊗[R]^L[A]) ⊗[A]^L (Functor.obj single0 Y ⊗[R]^L[A])))
    from
      derivedCohomologyProduct
          (-(n : ℤ))
          (-(m : ℤ))
          (Functor.obj single0 X ⊗[R]^L[A])
          (Functor.obj single0 Y ⊗[R]^L[A]) ≫
        eqToHom (product_reindex_eq X Y n m))

end

end CategoryTheory
