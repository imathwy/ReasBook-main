import Mathlib
import StacksProject_2024.Chap15.Definition_15_84_1
import StacksProject_2024.Chap15.Definition_15_75_1

noncomputable section

open CategoryTheory
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.84.3:
- primary domain: relative perfectness in derived categories of modules over a base algebra, and
  its behavior under the canonical derived tensor product over that algebra;
- sampled owner declarations:
  `DerivedCategory.IsPerfectOver`,
  `DerivedCategory.IsPerfect`,
  `isPerfect_restrictScalars_of_module_isPerfect`,
  `(ModuleCat.of R A).IsPerfect`;
- best owner abstraction: the theorem is `source-facing` on the chapter owner
  `DerivedCategory.IsPerfectOver R`, while absolute perfectness of `K` should be fed into that
  owner through the existing restriction-of-scalars bridge with the primitive perfectness
  hypothesis on `A` as an `R`-module, rather than through a local duplicate helper or a stronger
  ring-map hypothesis package;
- primitive vs. derived:
  primitive data are the perfect `R`-module `(ModuleCat.of R A)`, the absolute perfect object
  `K : D(A)`, and the relatively perfect object `M : D(A)`;
  pseudo-coherence and finite tor dimension over `R` are derived ingredients supplied by the
  existing owner API, not primitive public data for this file;
- source/core/bridge triage:
  `source-facing`: the tensor-stability theorem below for `DerivedCategory.IsPerfectOver R`;
  `core/canonical`: `DerivedCategory.IsPerfectOver`, `DerivedCategory.IsPerfect`, the tensor
    object `K ⊗[A]^L M`, and the perfect `R`-module `(ModuleCat.of R A)`;
  `bridge/view`: the canonical restriction-of-scalars theorem
    `isPerfect_restrictScalars_of_module_isPerfect`, which upgrades absolute perfectness over `A`
    to relative perfectness over `R` without introducing a new local owner.
-/

-- Proof sketch: first pass from `hK : K.IsPerfect` to `DerivedCategory.IsPerfectOver R K` through
-- the canonical restriction-of-scalars bridge `isPerfect_restrictScalars_of_module_isPerfect`,
-- using the primitive hypothesis that `A`, viewed as an `R`-module, is perfect. Then
-- unfold `DerivedCategory.IsPerfectOver` for `M`, use Lemma `15.65.16` to propagate
-- pseudo-coherence through `K ⊗[A]^L M`, and combine the tor-amplitude interval extracted from
-- the perfect complex `K` with the finite tor-dimension interval of `M` via Lemma `15.67.10`.
/-- Lemma 15.84.3: if `K, M ∈ D(A)`, then `K ⊗_A^{\mathbf L} M` is perfect relative to `R`
whenever `K` is perfect and `M` is perfect relative to `R`. -/
theorem isPerfectOver_derivedTensorProduct
    (K M : DModA)
    (hA : (ModuleCat.of R A).IsPerfect)
    (hK : K.IsPerfect)
    (hM : DerivedCategory.IsPerfectOver R M) :
    DerivedCategory.IsPerfectOver R (K ⊗[A]^L M) := sorry

end

end CategoryTheory
